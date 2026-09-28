//===- LLLexer.cpp - Lexer for .ll Files ----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implement the Lexer for .ll files.
//
//===----------------------------------------------------------------------===//

#include "llvm/AsmParser/LLLexer.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SourceMgr.h"
#include <cassert>
#include <cctype>
#include <cstdio>

using namespace llvm;

// Both the lexer and parser can issue error messages. If the lexer issues a
// lexer error, since we do not terminate execution immediately, usually that
// is followed by the parser issuing a parser error. However, the error issued
// by the lexer is more relevant in that case as opposed to potentially more
// generic parser error. So instead of always recording the last error message
// use the `Priority` to establish a priority, with Lexer > Parser > None. We
// record the issued message only if the message has same or higher priority
// than the existing one. This prevents lexer errors from being overwritten by
// parser errors.
void LLLexer::Error(LocTy ErrorLoc, const Twine &Msg,
                    LLLexer::ErrorPriority Priority) {
  if (Priority < ErrorInfo.Priority)
    return;
  ErrorInfo.Error = SM.GetMessage(ErrorLoc, SourceMgr::DK_Error, Msg);
  ErrorInfo.Priority = Priority;
}

void LLLexer::Warning(LocTy WarningLoc, const Twine &Msg) const {
  SM.PrintMessage(WarningLoc, SourceMgr::DK_Warning, Msg);
}

//===----------------------------------------------------------------------===//
// Helper functions.
//===----------------------------------------------------------------------===//

// atoull - Convert an ascii string of decimal digits into the unsigned long
// long representation... this does not have to do input error checking,
// because we know that the input will be matched by a suitable regex...
//
uint64_t LLLexer::atoull(const char *Buffer, const char *End) {
  uint64_t Result = 0;
  for (; Buffer != End; Buffer++) {
    uint64_t OldRes = Result;
    Result *= 10;
    Result += *Buffer-'0';
    if (Result < OldRes) { // overflow detected.
      LexError("constant bigger than 64 bits detected");
      return 0;
    }
  }
  return Result;
}

uint64_t LLLexer::HexIntToVal(const char *Buffer, const char *End) {
  uint64_t Result = 0;
  for (; Buffer != End; ++Buffer) {
    uint64_t OldRes = Result;
    Result *= 16;
    Result += hexDigitValue(*Buffer);

    if (Result < OldRes) { // overflow detected.
      LexError("constant bigger than 64 bits detected");
      return 0;
    }
  }
  return Result;
}

void LLLexer::HexToIntPair(const char *Buffer, const char *End,
                           uint64_t Pair[2]) {
  Pair[0] = 0;
  if (End - Buffer >= 16) {
    for (int i = 0; i < 16; i++, Buffer++) {
      assert(Buffer != End);
      Pair[0] *= 16;
      Pair[0] += hexDigitValue(*Buffer);
    }
  }
  Pair[1] = 0;
  for (int i = 0; i < 16 && Buffer != End; i++, Buffer++) {
    Pair[1] *= 16;
    Pair[1] += hexDigitValue(*Buffer);
  }
  if (Buffer != End)
    LexError("constant bigger than 128 bits detected");
}

/// FP80HexToIntPair - translate an 80 bit FP80 number (20 hexits) into
/// { low64, high16 } as usual for an APInt.
void LLLexer::FP80HexToIntPair(const char *Buffer, const char *End,
                           uint64_t Pair[2]) {
  Pair[1] = 0;
  for (int i=0; i<4 && Buffer != End; i++, Buffer++) {
    assert(Buffer != End);
    Pair[1] *= 16;
    Pair[1] += hexDigitValue(*Buffer);
  }
  Pair[0] = 0;
  for (int i = 0; i < 16 && Buffer != End; i++, Buffer++) {
    Pair[0] *= 16;
    Pair[0] += hexDigitValue(*Buffer);
  }
  if (Buffer != End)
    LexError("constant bigger than 128 bits detected");
}

// UnEscapeLexed - Run through the specified buffer and change \xx codes to the
// appropriate character.
static void UnEscapeLexed(std::string &Str) {
  if (Str.empty()) return;

  char *Buffer = &Str[0], *EndBuffer = Buffer+Str.size();
  char *BOut = Buffer;
  for (char *BIn = Buffer; BIn != EndBuffer; ) {
    if (BIn[0] == '\\') {
      if (BIn < EndBuffer-1 && BIn[1] == '\\') {
        *BOut++ = '\\'; // Two \ becomes one
        BIn += 2;
      } else if (BIn < EndBuffer-2 &&
                 isxdigit(static_cast<unsigned char>(BIn[1])) &&
                 isxdigit(static_cast<unsigned char>(BIn[2]))) {
        *BOut = hexDigitValue(BIn[1]) * 16 + hexDigitValue(BIn[2]);
        BIn += 3;                           // Skip over handled chars
        ++BOut;
      } else {
        *BOut++ = *BIn++;
      }
    } else {
      *BOut++ = *BIn++;
    }
  }
  Str.resize(BOut-Buffer);
}

/// isLabelChar - Return true for [-a-zA-Z$._0-9].
static bool isLabelChar(char C) {
  return isalnum(static_cast<unsigned char>(C)) || C == '-' || C == '$' ||
         C == '.' || C == '_';
}

/// isLabelTail - Return true if this pointer points to a valid end of a label.
static const char *isLabelTail(const char *CurPtr) {
  while (true) {
    if (CurPtr[0] == ':') return CurPtr+1;
    if (!isLabelChar(CurPtr[0])) return nullptr;
    ++CurPtr;
  }
}

//===----------------------------------------------------------------------===//
// Lexer definition.
//===----------------------------------------------------------------------===//

LLLexer::LLLexer(StringRef StartBuf, SourceMgr &SM, SMDiagnostic &Err,
                 LLVMContext &C)
    : CurBuf(StartBuf), ErrorInfo(Err), SM(SM), Context(C) {
  CurPtr = CurBuf.begin();
}

int LLLexer::getNextChar() {
  char CurChar = *CurPtr++;
  switch (CurChar) {
  default: return (unsigned char)CurChar;
  case 0:
    // A nul character in the stream is either the end of the current buffer or
    // a random nul in the file.  Disambiguate that here.
    if (CurPtr-1 != CurBuf.end())
      return 0;  // Just whitespace.

    // Otherwise, return end of file.
    --CurPtr;  // Another call to lex will return EOF again.
    return EOF;
  }
}

lltok::Kind LLLexer::LexToken() {
  // Set token end to next location, since the end is exclusive.
  PrevTokEnd = CurPtr;
  while (true) {
    TokStart = CurPtr;

    int CurChar = getNextChar();
    switch (CurChar) {
    default:
      // Handle letters: [a-zA-Z_]
      if (isalpha(static_cast<unsigned char>(CurChar)) || CurChar == '_')
        return LexIdentifier();
      return lltok::Error;
    case EOF: return lltok::Eof;
    case 0:
    case ' ':
    case '\t':
    case '\n':
    case '\r':
      // Ignore whitespace.
      continue;
    case '+': return LexPositive();
    case '@': return LexAt();
    case '$': return LexDollar();
    case '%': return LexPercent();
    case '"': return LexQuote();
    case '.':
      if (const char *Ptr = isLabelTail(CurPtr)) {
        CurPtr = Ptr;
        StrVal.assign(TokStart, CurPtr-1);
        return lltok::LabelStr;
      }
      if (CurPtr[0] == '.' && CurPtr[1] == '.') {
        CurPtr += 2;
        return lltok::dotdotdot;
      }
      return lltok::Error;
    case ';':
      SkipLineComment();
      continue;
    case '!': return LexExclaim();
    case '^':
      return LexCaret();
    case ':':
      return lltok::colon;
    case '#': return LexHash();
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9':
    case '-':
      return LexDigitOrNegative();
    case '=': return lltok::equal;
    case '[': return lltok::lsquare;
    case ']': return lltok::rsquare;
    case '{': return lltok::lbrace;
    case '}': return lltok::rbrace;
    case '<': return lltok::less;
    case '>': return lltok::greater;
    case '(': return lltok::lparen;
    case ')': return lltok::rparen;
    case ',': return lltok::comma;
    case '*': return lltok::star;
    case '|': return lltok::bar;
    case '/':
      if (getNextChar() != '*')
        return lltok::Error;
      if (SkipCComment())
        return lltok::Error;
      continue;
    }
  }
}

void LLLexer::SkipLineComment() {
  while (true) {
    if (CurPtr[0] == '\n' || CurPtr[0] == '\r' || getNextChar() == EOF)
      return;
  }
}

/// This skips C-style /**/ comments. Returns true if there
/// was an error.
bool LLLexer::SkipCComment() {
  while (true) {
    int CurChar = getNextChar();
    switch (CurChar) {
    case EOF:
      LexError("unterminated comment");
      return true;
    case '*':
      // End of the comment?
      CurChar = getNextChar();
      if (CurChar == '/')
        return false;
      if (CurChar == EOF) {
        LexError("unterminated comment");
        return true;
      }
    }
  }
}

/// Lex all tokens that start with an @ character.
///   GlobalVar   @\"[^\"]*\"
///   GlobalVar   @[-a-zA-Z$._][-a-zA-Z$._0-9]*
///   GlobalVarID @[0-9]+
lltok::Kind LLLexer::LexAt() {
  return LexVar(lltok::GlobalVar, lltok::GlobalID);
}

lltok::Kind LLLexer::LexDollar() {
  if (const char *Ptr = isLabelTail(TokStart)) {
    CurPtr = Ptr;
    StrVal.assign(TokStart, CurPtr - 1);
    return lltok::LabelStr;
  }

  // Handle DollarStringConstant: $\"[^\"]*\"
  if (CurPtr[0] == '"') {
    ++CurPtr;

    while (true) {
      int CurChar = getNextChar();

      if (CurChar == EOF) {
        LexError("end of file in COMDAT variable name");
        return lltok::Error;
      }
      if (CurChar == '"') {
        StrVal.assign(TokStart + 2, CurPtr - 1);
        UnEscapeLexed(StrVal);
        if (StringRef(StrVal).contains(0)) {
          LexError("NUL character is not allowed in names");
          return lltok::Error;
        }
        return lltok::ComdatVar;
      }
    }
  }

  // Handle ComdatVarName: $[-a-zA-Z$._][-a-zA-Z$._0-9]*
  if (ReadVarName())
    return lltok::ComdatVar;

  return lltok::Error;
}

/// ReadString - Read a string until the closing quote.
lltok::Kind LLLexer::ReadString(lltok::Kind kind) {
  const char *Start = CurPtr;
  while (true) {
    int CurChar = getNextChar();

    if (CurChar == EOF) {
      LexError("end of file in string constant");
      return lltok::Error;
    }
    if (CurChar == '"') {
      StrVal.assign(Start, CurPtr-1);
      UnEscapeLexed(StrVal);
      return kind;
    }
  }
}

/// ReadVarName - Read the rest of a token containing a variable name.
bool LLLexer::ReadVarName() {
  const char *NameStart = CurPtr;
  if (isalpha(static_cast<unsigned char>(CurPtr[0])) ||
      CurPtr[0] == '-' || CurPtr[0] == '$' ||
      CurPtr[0] == '.' || CurPtr[0] == '_') {
    ++CurPtr;
    while (isalnum(static_cast<unsigned char>(CurPtr[0])) ||
           CurPtr[0] == '-' || CurPtr[0] == '$' ||
           CurPtr[0] == '.' || CurPtr[0] == '_')
      ++CurPtr;

    StrVal.assign(NameStart, CurPtr);
    return true;
  }
  return false;
}

// Lex an ID: [0-9]+. On success, the ID is stored in UIntVal and Token is
// returned, otherwise the Error token is returned.
lltok::Kind LLLexer::LexUIntID(lltok::Kind Token) {
  if (!isdigit(static_cast<unsigned char>(CurPtr[0])))
    return lltok::Error;

  for (++CurPtr; isdigit(static_cast<unsigned char>(CurPtr[0])); ++CurPtr)
    /*empty*/;

  uint64_t Val = atoull(TokStart + 1, CurPtr);
  if ((unsigned)Val != Val)
    LexError("invalid value number (too large)");
  UIntVal = unsigned(Val);
  return Token;
}

lltok::Kind LLLexer::LexVar(lltok::Kind Var, lltok::Kind VarID) {
  // Handle StringConstant: \"[^\"]*\"
  if (CurPtr[0] == '"') {
    ++CurPtr;

    while (true) {
      int CurChar = getNextChar();

      if (CurChar == EOF) {
        LexError("end of file in global variable name");
        return lltok::Error;
      }
      if (CurChar == '"') {
        StrVal.assign(TokStart+2, CurPtr-1);
        UnEscapeLexed(StrVal);
        if (StringRef(StrVal).contains(0)) {
          LexError("NUL character is not allowed in names");
          return lltok::Error;
        }
        return Var;
      }
    }
  }

  // Handle VarName: [-a-zA-Z$._][-a-zA-Z$._0-9]*
  if (ReadVarName())
    return Var;

  // Handle VarID: [0-9]+
  return LexUIntID(VarID);
}

/// Lex all tokens that start with a % character.
///   LocalVar   ::= %\"[^\"]*\"
///   LocalVar   ::= %[-a-zA-Z$._][-a-zA-Z$._0-9]*
///   LocalVarID ::= %[0-9]+
lltok::Kind LLLexer::LexPercent() {
  return LexVar(lltok::LocalVar, lltok::LocalVarID);
}

/// Lex all tokens that start with a " character.
///   QuoteLabel        "[^"]+":
///   StringConstant    "[^"]*"
lltok::Kind LLLexer::LexQuote() {
  lltok::Kind kind = ReadString(lltok::StringConstant);
  if (kind == lltok::Error || kind == lltok::Eof)
    return kind;

  if (CurPtr[0] == ':') {
    ++CurPtr;
    if (StringRef(StrVal).contains(0)) {
      LexError("NUL character is not allowed in names");
      kind = lltok::Error;
    } else {
      kind = lltok::LabelStr;
    }
  }

  return kind;
}

/// Lex all tokens that start with a ! character.
///    !foo
///    !
lltok::Kind LLLexer::LexExclaim() {
  // Lex a metadata name as a MetadataVar.
  if (isalpha(static_cast<unsigned char>(CurPtr[0])) ||
      CurPtr[0] == '-' || CurPtr[0] == '$' ||
      CurPtr[0] == '.' || CurPtr[0] == '_' || CurPtr[0] == '\\') {
    ++CurPtr;
    while (isalnum(static_cast<unsigned char>(CurPtr[0])) ||
           CurPtr[0] == '-' || CurPtr[0] == '$' ||
           CurPtr[0] == '.' || CurPtr[0] == '_' || CurPtr[0] == '\\')
      ++CurPtr;

    StrVal.assign(TokStart+1, CurPtr);   // Skip !
    UnEscapeLexed(StrVal);
    return lltok::MetadataVar;
  }
  return lltok::exclaim;
}

/// Lex all tokens that start with a ^ character.
///    SummaryID ::= ^[0-9]+
lltok::Kind LLLexer::LexCaret() {
  // Handle SummaryID: ^[0-9]+
  return LexUIntID(lltok::SummaryID);
}

/// Lex all tokens that start with a # character.
///    AttrGrpID ::= #[0-9]+
///    Hash ::= #
lltok::Kind LLLexer::LexHash() {
  // Handle AttrGrpID: #[0-9]+
  if (isdigit(static_cast<unsigned char>(CurPtr[0])))
    return LexUIntID(lltok::AttrGrpID);
  return lltok::hash;
}

/// Lex a label, integer or byte types, keyword, or hexadecimal integer
/// constant.
///    Label           [-a-zA-Z$._0-9]+:
///    ByteType        b[0-9]+
///    IntegerType     i[0-9]+
///    Keyword         sdiv, float, ...
///    HexIntConstant  [us]0x[0-9A-Fa-f]+
///    HexFloatConstant f0x[0-9A-Fa-f]+
lltok::Kind LLLexer::LexIdentifier() {
  const char *StartChar = CurPtr;
  const char IntOrByteIdentifier = CurPtr[-1];
  const char *IntOrByteEnd =
      (IntOrByteIdentifier == 'i' || IntOrByteIdentifier == 'b') ? nullptr
                                                                 : StartChar;
  const char *KeywordEnd = nullptr;

  for (; isLabelChar(*CurPtr); ++CurPtr) {
    // If we decide this is a byte or an integer, remember the end of the
    // sequence.
    if (!IntOrByteEnd && !isdigit(static_cast<unsigned char>(*CurPtr)))
      IntOrByteEnd = CurPtr;
    if (!KeywordEnd && !isalnum(static_cast<unsigned char>(*CurPtr)) &&
        *CurPtr != '_')
      KeywordEnd = CurPtr;
  }

  // If we stopped due to a colon, unless we were directed to ignore it,
  // this really is a label.
  if (!IgnoreColonInIdentifiers && *CurPtr == ':') {
    StrVal.assign(StartChar-1, CurPtr++);
    return lltok::LabelStr;
  }

  // Otherwise, this wasn't a label. If this was valid as a byte or an integer
  // type, return it.
  if (!IntOrByteEnd)
    IntOrByteEnd = CurPtr;
  if (IntOrByteEnd != StartChar) {
    CurPtr = IntOrByteEnd;
    uint64_t NumBits = atoull(StartChar, CurPtr);
    if (NumBits < IntegerType::MIN_INT_BITS ||
        NumBits > IntegerType::MAX_INT_BITS) {
      LexError("bitwidth for integer or byte type out of range");
      return lltok::Error;
    }
    if (IntOrByteIdentifier == 'i')
      TyVal = IntegerType::get(Context, NumBits);
    else
      TyVal = ByteType::get(Context, NumBits);

    return lltok::Type;
  }

  // Otherwise, this was a letter sequence.  See which keyword this is.
  if (!KeywordEnd) KeywordEnd = CurPtr;
  CurPtr = KeywordEnd;
  --StartChar;
  StringRef Keyword(StartChar, CurPtr - StartChar);

switch (Keyword.size()) {
case 1:
  switch (Keyword[0]) {
  case 'c':
    return lltok::kw_c;

  case 'x':
    return lltok::kw_x;

  }
  break;
case 2:
  switch (Keyword[0]) {
  case 'b':
    if (memcmp(Keyword.data() + 1, "r", 1) == 0) {
      return lltok::kw_br;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "c", 1) == 0) {
      return lltok::kw_cc;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "q", 1) == 0) {
      return lltok::kw_eq;
    }
    break;
  case 'g':
    switch (Keyword[1]) {
    case 'c':
      return lltok::kw_gc;

    case 'v':
      return lltok::kw_gv;

    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "e", 1) == 0) {
      return lltok::kw_ne;
    }
    break;
  case 'o':
    if (memcmp(Keyword.data() + 1, "r", 1) == 0) {
      UIntVal = Instruction::Or;
      return lltok::kw_or;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "o", 1) == 0) {
      return lltok::kw_to;
    }
    break;
  }
  break;
case 3:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "d", 1) == 0) {
        UIntVal = Instruction::Add;
        return lltok::kw_add;
      }
      break;
    case 'f':
      if (memcmp(Keyword.data() + 2, "n", 1) == 0) {
        return lltok::kw_afn;
      }
      break;
    case 'l':
      if (memcmp(Keyword.data() + 2, "l", 1) == 0) {
        return lltok::kw_all;
      }
      break;
    case 'n':
      switch (Keyword[2]) {
      case 'd':
        UIntVal = Instruction::And;
        return lltok::kw_and;

      case 'y':
        return lltok::kw_any;

      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "m", 1) == 0) {
        return lltok::kw_asm;
      }
      break;
    }
    break;
  case 'b':
    if (memcmp(Keyword.data() + 1, "it", 2) == 0) {
      return lltok::kw_bit;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "cc", 2) == 0) {
      return lltok::kw_ccc;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "nf", 2) == 0) {
      return lltok::kw_inf;
    }
    break;
  case 'm':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "x", 1) == 0) {
        return lltok::kw_max;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "n", 1) == 0) {
        return lltok::kw_min;
      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "l", 1) == 0) {
        UIntVal = Instruction::Mul;
        return lltok::kw_mul;
      }
      break;
    }
    break;
  case 'n':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "n", 1) == 0) {
        return lltok::kw_nan;
      }
      break;
    case 's':
      switch (Keyword[2]) {
      case 'w':
        return lltok::kw_nsw;

      case 'z':
        return lltok::kw_nsz;

      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "w", 1) == 0) {
        return lltok::kw_nuw;
      }
      break;
    }
    break;
  case 'o':
    switch (Keyword[1]) {
    case 'e':
      if (memcmp(Keyword.data() + 2, "q", 1) == 0) {
        return lltok::kw_oeq;
      }
      break;
    case 'g':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_oge;

      case 't':
        return lltok::kw_ogt;

      }
      break;
    case 'l':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_ole;

      case 't':
        return lltok::kw_olt;

      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "e", 1) == 0) {
        return lltok::kw_one;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "d", 1) == 0) {
        return lltok::kw_ord;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'h':
      if (memcmp(Keyword.data() + 2, "i", 1) == 0) {
        UIntVal = Instruction::PHI;
        return lltok::kw_phi;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "r", 1) == 0) {
        TyVal = PointerType::getUnqual(Context);
        return lltok::Type;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "et", 2) == 0) {
      UIntVal = Instruction::Ret;
      return lltok::kw_ret;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'g':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_sge;

      case 't':
        return lltok::kw_sgt;

      }
      break;
    case 'h':
      if (memcmp(Keyword.data() + 2, "l", 1) == 0) {
        UIntVal = Instruction::Shl;
        return lltok::kw_shl;
      }
      break;
    case 'l':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_sle;

      case 't':
        return lltok::kw_slt;

      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "b", 1) == 0) {
        UIntVal = Instruction::Sub;
        return lltok::kw_sub;
      }
      break;
    }
    break;
  case 'u':
    switch (Keyword[1]) {
    case 'e':
      if (memcmp(Keyword.data() + 2, "q", 1) == 0) {
        return lltok::kw_ueq;
      }
      break;
    case 'g':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_uge;

      case 't':
        return lltok::kw_ugt;

      }
      break;
    case 'l':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_ule;

      case 't':
        return lltok::kw_ult;

      }
      break;
    case 'n':
      switch (Keyword[2]) {
      case 'e':
        return lltok::kw_une;

      case 'o':
        return lltok::kw_uno;

      }
      break;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "or", 2) == 0) {
      UIntVal = Instruction::Xor;
      return lltok::kw_xor;
    }
    break;
  }
  break;
case 4:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'r':
      switch (Keyword[2]) {
      case 'c':
        if (memcmp(Keyword.data() + 3, "p", 1) == 0) {
          return lltok::kw_arcp;
        }
        break;
      case 'g':
        if (memcmp(Keyword.data() + 3, "s", 1) == 0) {
          return lltok::kw_args;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "hr", 2) == 0) {
        UIntVal = Instruction::AShr;
        return lltok::kw_ashr;
      }
      break;
    }
    break;
  case 'b':
    if (memcmp(Keyword.data() + 1, "yte", 3) == 0) {
      return lltok::kw_byte;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "all", 3) == 0) {
      UIntVal = Instruction::Call;
      return lltok::kw_call;
    }
    break;
  case 'f':
    switch (Keyword[1]) {
    case 'a':
      switch (Keyword[2]) {
      case 'd':
        if (memcmp(Keyword.data() + 3, "d", 1) == 0) {
          UIntVal = Instruction::FAdd;
          return lltok::kw_fadd;
        }
        break;
      case 's':
        if (memcmp(Keyword.data() + 3, "t", 1) == 0) {
          return lltok::kw_fast;
        }
        break;
      }
      break;
    case 'c':
      if (memcmp(Keyword.data() + 2, "mp", 2) == 0) {
        UIntVal = Instruction::FCmp;
        return lltok::kw_fcmp;
      }
      break;
    case 'd':
      if (memcmp(Keyword.data() + 2, "iv", 2) == 0) {
        UIntVal = Instruction::FDiv;
        return lltok::kw_fdiv;
      }
      break;
    case 'm':
      switch (Keyword[2]) {
      case 'a':
        if (memcmp(Keyword.data() + 3, "x", 1) == 0) {
          return lltok::kw_fmax;
        }
        break;
      case 'i':
        if (memcmp(Keyword.data() + 3, "n", 1) == 0) {
          return lltok::kw_fmin;
        }
        break;
      case 'u':
        if (memcmp(Keyword.data() + 3, "l", 1) == 0) {
          UIntVal = Instruction::FMul;
          return lltok::kw_fmul;
        }
        break;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "eg", 2) == 0) {
        UIntVal = Instruction::FNeg;
        return lltok::kw_fneg;
      }
      break;
    case 'r':
      switch (Keyword[2]) {
      case 'e':
        if (memcmp(Keyword.data() + 3, "m", 1) == 0) {
          UIntVal = Instruction::FRem;
          return lltok::kw_frem;
        }
        break;
      case 'o':
        if (memcmp(Keyword.data() + 3, "m", 1) == 0) {
          return lltok::kw_from;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "ub", 2) == 0) {
        UIntVal = Instruction::FSub;
        return lltok::kw_fsub;
      }
      break;
    }
    break;
  case 'g':
    if (memcmp(Keyword.data() + 1, "uid", 3) == 0) {
      return lltok::kw_guid;
    }
    break;
  case 'h':
    if (memcmp(Keyword.data() + 1, "a", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'l':
      if (memcmp(Keyword.data() + 3, "f", 1) == 0) {
        TyVal = Type::getHalfTy(Context);
        return lltok::Type;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 3, "h", 1) == 0) {
        return lltok::kw_hash;
      }
      break;
    }
    break;
  case 'i':
    switch (Keyword[1]) {
    case 'c':
      if (memcmp(Keyword.data() + 2, "mp", 2) == 0) {
        UIntVal = Instruction::ICmp;
        return lltok::kw_icmp;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "ee", 2) == 0) {
        return lltok::kw_ieee;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "fo", 2) == 0) {
        return lltok::kw_info;
      }
      break;
    }
    break;
  case 'k':
    if (memcmp(Keyword.data() + 1, "ind", 3) == 0) {
      return lltok::kw_kind;
    }
    break;
  case 'l':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "ve", 2) == 0) {
        return lltok::kw_live;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "ad", 2) == 0) {
        UIntVal = Instruction::Load;
        return lltok::kw_load;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "hr", 2) == 0) {
        UIntVal = Instruction::LShr;
        return lltok::kw_lshr;
      }
      break;
    }
    break;
  case 'n':
    switch (Keyword[1]) {
    case 'a':
      switch (Keyword[2]) {
      case 'm':
        if (memcmp(Keyword.data() + 3, "e", 1) == 0) {
          return lltok::kw_name;
        }
        break;
      case 'n':
        if (memcmp(Keyword.data() + 3, "d", 1) == 0) {
          return lltok::kw_nand;
        }
        break;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "nf", 2) == 0) {
        return lltok::kw_ninf;
      }
      break;
    case 'n':
      switch (Keyword[2]) {
      case 'a':
        if (memcmp(Keyword.data() + 3, "n", 1) == 0) {
          return lltok::kw_nnan;
        }
        break;
      case 'e':
        if (memcmp(Keyword.data() + 3, "g", 1) == 0) {
          return lltok::kw_nneg;
        }
        break;
      }
      break;
    case 'o':
      switch (Keyword[2]) {
      case 'n':
        if (memcmp(Keyword.data() + 3, "e", 1) == 0) {
          return lltok::kw_none;
        }
        break;
      case 'r':
        if (memcmp(Keyword.data() + 3, "m", 1) == 0) {
          return lltok::kw_norm;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "ub", 2) == 0) {
        return lltok::kw_nsub;
      }
      break;
    case 'u':
      switch (Keyword[2]) {
      case 'l':
        if (memcmp(Keyword.data() + 3, "l", 1) == 0) {
          return lltok::kw_null;
        }
        break;
      case 's':
        if (memcmp(Keyword.data() + 3, "w", 1) == 0) {
          return lltok::kw_nusw;
        }
        break;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "th", 2) == 0) {
        return lltok::kw_path;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "nf", 2) == 0) {
        return lltok::kw_pinf;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "ub", 2) == 0) {
        return lltok::kw_psub;
      }
      break;
    }
    break;
  case 'q':
    if (memcmp(Keyword.data() + 1, "nan", 3) == 0) {
      return lltok::kw_qnan;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "e", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'a':
      if (memcmp(Keyword.data() + 3, "d", 1) == 0) {
        return lltok::kw_read;
      }
      break;
    case 'f':
      if (memcmp(Keyword.data() + 3, "s", 1) == 0) {
        return lltok::kw_refs;
      }
      break;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "iv", 2) == 0) {
        UIntVal = Instruction::SDiv;
        return lltok::kw_sdiv;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "xt", 2) == 0) {
        UIntVal = Instruction::SExt;
        return lltok::kw_sext;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "an", 2) == 0) {
        return lltok::kw_snan;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "em", 2) == 0) {
        UIntVal = Instruction::SRem;
        return lltok::kw_srem;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "nc", 2) == 0) {
        return lltok::kw_sync;
      }
      break;
    }
    break;
  case 't':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "il", 2) == 0) {
        return lltok::kw_tail;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "ue", 2) == 0) {
        return lltok::kw_true;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "pe", 2) == 0) {
        return lltok::kw_type;
      }
      break;
    }
    break;
  case 'u':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "iv", 2) == 0) {
        UIntVal = Instruction::UDiv;
        return lltok::kw_udiv;
      }
      break;
    case 'm':
      switch (Keyword[2]) {
      case 'a':
        if (memcmp(Keyword.data() + 3, "x", 1) == 0) {
          return lltok::kw_umax;
        }
        break;
      case 'i':
        if (memcmp(Keyword.data() + 3, "n", 1) == 0) {
          return lltok::kw_umin;
        }
        break;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "em", 2) == 0) {
        UIntVal = Instruction::URem;
        return lltok::kw_urem;
      }
      break;
    }
    break;
  case 'v':
    if (memcmp(Keyword.data() + 1, "oid", 3) == 0) {
      TyVal = Type::getVoidTy(Context);
      return lltok::Type;
    }
    break;
  case 'w':
    if (memcmp(Keyword.data() + 1, "eak", 3) == 0) {
      return lltok::kw_weak;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "chg", 3) == 0) {
      return lltok::kw_xchg;
    }
    break;
  case 'z':
    if (memcmp(Keyword.data() + 1, "e", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'r':
      if (memcmp(Keyword.data() + 3, "o", 1) == 0) {
        return lltok::kw_zero;
      }
      break;
    case 'x':
      if (memcmp(Keyword.data() + 3, "t", 1) == 0) {
        UIntVal = Instruction::ZExt;
        return lltok::kw_zext;
      }
      break;
    }
    break;
  }
  break;
case 5:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "ias", 3) == 0) {
        return lltok::kw_alias;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "ync", 3) == 0) {
        return lltok::kw_async;
      }
      break;
    }
    break;
  case 'b':
    if (memcmp(Keyword.data() + 1, "yArg", 4) == 0) {
      return lltok::kw_byArg;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "a", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'l':
      if (memcmp(Keyword.data() + 3, "ls", 2) == 0) {
        return lltok::kw_calls;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 3, "ch", 2) == 0) {
        return lltok::kw_catch;
      }
      break;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "xact", 4) == 0) {
      return lltok::kw_exact;
    }
    break;
  case 'f':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "lse", 3) == 0) {
        return lltok::kw_false;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "nce", 3) == 0) {
        UIntVal = Instruction::Fence;
        return lltok::kw_fence;
      }
      break;
    case 'l':
      switch (Keyword[2]) {
      case 'a':
        if (memcmp(Keyword.data() + 3, "gs", 2) == 0) {
          return lltok::kw_flags;
        }
        break;
      case 'o':
        if (memcmp(Keyword.data() + 3, "at", 2) == 0) {
          TyVal = Type::getFloatTy(Context);
          return lltok::Type;
        }
        break;
      }
      break;
    case 'p':
      switch (Keyword[2]) {
      case '1':
        if (memcmp(Keyword.data() + 3, "28", 2) == 0) {
          TyVal = Type::getFP128Ty(Context);
          return lltok::Type;
        }
        break;
      case 'e':
        if (memcmp(Keyword.data() + 3, "xt", 2) == 0) {
          UIntVal = Instruction::FPExt;
          return lltok::kw_fpext;
        }
        break;
      }
      break;
    }
    break;
  case 'g':
    if (memcmp(Keyword.data() + 1, "hccc", 4) == 0) {
      return lltok::kw_ghccc;
    }
    break;
  case 'i':
    switch (Keyword[1]) {
    case 'f':
      if (memcmp(Keyword.data() + 2, "unc", 3) == 0) {
        return lltok::kw_ifunc;
      }
      break;
    case 'n':
      switch (Keyword[2]) {
      case 'd':
        if (memcmp(Keyword.data() + 3, "ir", 2) == 0) {
          return lltok::kw_indir;
        }
        break;
      case 's':
        if (memcmp(Keyword.data() + 3, "ts", 2) == 0) {
          return lltok::kw_insts;
        }
        break;
      }
      break;
    }
    break;
  case 'l':
    if (memcmp(Keyword.data() + 1, "abel", 4) == 0) {
      TyVal = Type::getLabelTy(Context);
      return lltok::Type;
    }
    break;
  case 'n':
    switch (Keyword[1]) {
    case 'n':
      if (memcmp(Keyword.data() + 2, "orm", 3) == 0) {
        return lltok::kw_nnorm;
      }
      break;
    case 'z':
      if (memcmp(Keyword.data() + 2, "ero", 3) == 0) {
        return lltok::kw_nzero;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "ram", 3) == 0) {
        return lltok::kw_param;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "orm", 3) == 0) {
        return lltok::kw_pnorm;
      }
      break;
    case 'z':
      if (memcmp(Keyword.data() + 2, "ero", 3) == 0) {
        return lltok::kw_pzero;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "elbf", 4) == 0) {
      return lltok::kw_relbf;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'p':
      if (memcmp(Keyword.data() + 2, "lat", 3) == 0) {
        return lltok::kw_splat;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "ore", 3) == 0) {
        UIntVal = Instruction::Store;
        return lltok::kw_store;
      }
      break;
    }
    break;
  case 't':
    switch (Keyword[1]) {
    case 'o':
      if (memcmp(Keyword.data() + 2, "ken", 3) == 0) {
        TyVal = Type::getTokenTy(Context);
        return lltok::Type;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "unc", 3) == 0) {
        UIntVal = Instruction::Trunc;
        return lltok::kw_trunc;
      }
      break;
    }
    break;
  case 'u':
    if (memcmp(Keyword.data() + 1, "n", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'd':
      if (memcmp(Keyword.data() + 3, "ef", 2) == 0) {
        return lltok::kw_undef;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 3, "at", 2) == 0) {
        return lltok::kw_unsat;
      }
      break;
    }
    break;
  case 'w':
    if (memcmp(Keyword.data() + 1, "rite", 4) == 0) {
      return lltok::kw_write;
    }
    break;
  }
  break;
case 6:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "loc", 3) != 0)
        break;
      switch (Keyword[5]) {
      case 'a':
        UIntVal = Instruction::Alloca;
        return lltok::kw_alloca;

      case 's':
        return lltok::kw_allocs;

      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "gmem", 4) == 0) {
        return lltok::kw_argmem;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "omic", 4) == 0) {
        return lltok::kw_atomic;
      }
      break;
    }
    break;
  case 'b':
    if (memcmp(Keyword.data() + 1, "float", 5) == 0) {
      TyVal = Type::getBFloatTy(Context);
      return lltok::Type;
    }
    break;
  case 'c':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "ll", 2) != 0)
        break;
      switch (Keyword[4]) {
      case 'b':
        if (memcmp(Keyword.data() + 5, "r", 1) == 0) {
          UIntVal = Instruction::CallBr;
          return lltok::kw_callbr;
        }
        break;
      case 'e':
        switch (Keyword[5]) {
        case 'e':
          return lltok::kw_callee;

        case 'r':
          return lltok::kw_caller;

        }
        break;
      }
      break;
    case 'l':
      if (memcmp(Keyword.data() + 2, "ones", 4) == 0) {
        return lltok::kw_clones;
      }
      break;
    case 'o':
      switch (Keyword[2]) {
      case 'l':
        if (memcmp(Keyword.data() + 3, "dcc", 3) == 0) {
          return lltok::kw_coldcc;
        }
        break;
      case 'm':
        switch (Keyword[3]) {
        case 'd':
          if (memcmp(Keyword.data() + 4, "at", 2) == 0) {
            return lltok::kw_comdat;
          }
          break;
        case 'm':
          if (memcmp(Keyword.data() + 4, "on", 2) == 0) {
            return lltok::kw_common;
          }
          break;
        }
        break;
      }
      break;
    }
    break;
  case 'd':
    switch (Keyword[1]) {
    case 'e':
      if (memcmp(Keyword.data() + 2, "fine", 4) == 0) {
        return lltok::kw_define;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "uble", 4) == 0) {
        TyVal = Type::getDoubleTy(Context);
        return lltok::Type;
      }
      break;
    }
    break;
  case 'f':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "stcc", 4) == 0) {
        return lltok::kw_fastcc;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "lter", 4) == 0) {
        return lltok::kw_filter;
      }
      break;
    case 'p':
      if (memcmp(Keyword.data() + 2, "to", 2) != 0)
        break;
      switch (Keyword[4]) {
      case 's':
        if (memcmp(Keyword.data() + 5, "i", 1) == 0) {
          UIntVal = Instruction::FPToSI;
          return lltok::kw_fptosi;
        }
        break;
      case 'u':
        if (memcmp(Keyword.data() + 5, "i", 1) == 0) {
          UIntVal = Instruction::FPToUI;
          return lltok::kw_fptoui;
        }
        break;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "eeze", 4) == 0) {
        UIntVal = Instruction::Freeze;
        return lltok::kw_freeze;
      }
      break;
    }
    break;
  case 'g':
    if (memcmp(Keyword.data() + 1, "lobal", 5) == 0) {
      return lltok::kw_global;
    }
    break;
  case 'h':
    switch (Keyword[1]) {
    case 'h':
      if (memcmp(Keyword.data() + 2, "vmcc", 4) == 0) {
        return lltok::kw_hhvmcc;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "dden", 4) == 0) {
        return lltok::kw_hidden;
      }
      break;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "n", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'l':
      if (memcmp(Keyword.data() + 3, "ine", 3) == 0) {
        return lltok::kw_inline;
      }
      break;
    case 'v':
      if (memcmp(Keyword.data() + 3, "oke", 3) == 0) {
        UIntVal = Instruction::Invoke;
        return lltok::kw_invoke;
      }
      break;
    }
    break;
  case 'm':
    if (memcmp(Keyword.data() + 1, "odule", 5) == 0) {
      return lltok::kw_module;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "o", 1) != 0)
      break;
    switch (Keyword[2]) {
    case '_':
      if (memcmp(Keyword.data() + 3, "cfi", 3) == 0) {
        return lltok::kw_no_cfi;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 3, "ail", 3) == 0) {
        return lltok::kw_notail;
      }
      break;
    }
    break;
  case 'o':
    switch (Keyword[1]) {
    case 'f':
      if (memcmp(Keyword.data() + 2, "fset", 4) == 0) {
        return lltok::kw_offset;
      }
      break;
    case 'p':
      if (memcmp(Keyword.data() + 2, "aque", 4) == 0) {
        return lltok::kw_opaque;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "rams", 4) == 0) {
        return lltok::kw_params;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "ison", 4) == 0) {
        return lltok::kw_poison;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "efix", 4) == 0) {
        return lltok::kw_prefix;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "esume", 5) == 0) {
      UIntVal = Instruction::Resume;
      return lltok::kw_resume;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'e':
      if (memcmp(Keyword.data() + 2, "lect", 4) == 0) {
        UIntVal = Instruction::Select;
        return lltok::kw_select;
      }
      break;
    case 'i':
      switch (Keyword[2]) {
      case 'n':
        if (memcmp(Keyword.data() + 3, "gle", 3) == 0) {
          return lltok::kw_single;
        }
        break;
      case 't':
        if (memcmp(Keyword.data() + 3, "ofp", 3) == 0) {
          UIntVal = Instruction::SIToFP;
          return lltok::kw_sitofp;
        }
        break;
      case 'z':
        if (memcmp(Keyword.data() + 3, "eM1", 3) == 0) {
          return lltok::kw_sizeM1;
        }
        break;
      }
      break;
    case 'w':
      if (memcmp(Keyword.data() + 2, "itch", 4) == 0) {
        UIntVal = Instruction::Switch;
        return lltok::kw_switch;
      }
      break;
    }
    break;
  case 't':
    switch (Keyword[1]) {
    case 'a':
      switch (Keyword[2]) {
      case 'i':
        if (memcmp(Keyword.data() + 3, "lcc", 3) == 0) {
          return lltok::kw_tailcc;
        }
        break;
      case 'r':
        if (memcmp(Keyword.data() + 3, "get", 3) == 0) {
          return lltok::kw_target;
        }
        break;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "iple", 4) == 0) {
        return lltok::kw_triple;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "peid", 4) == 0) {
        return lltok::kw_typeid;
      }
      break;
    }
    break;
  case 'u':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "tofp", 4) == 0) {
        UIntVal = Instruction::UIToFP;
        return lltok::kw_uitofp;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "wind", 4) == 0) {
        return lltok::kw_unwind;
      }
      break;
    }
    break;
  case 'v':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "_arg", 4) == 0) {
        UIntVal = Instruction::VAArg;
        return lltok::kw_va_arg;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "cale", 4) == 0) {
        return lltok::kw_vscale;
      }
      break;
    }
    break;
  case 'w':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "thin", 4) == 0) {
        return lltok::kw_within;
      }
      break;
    case 'p':
      if (memcmp(Keyword.data() + 2, "dRes", 4) == 0) {
        return lltok::kw_wpdRes;
      }
      break;
    }
    break;
  }
  break;
case 7:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'c':
      if (memcmp(Keyword.data() + 2, "q", 1) != 0)
        break;
      switch (Keyword[3]) {
      case '_':
        if (memcmp(Keyword.data() + 4, "rel", 3) == 0) {
          return lltok::kw_acq_rel;
        }
        break;
      case 'u':
        if (memcmp(Keyword.data() + 4, "ire", 3) == 0) {
          return lltok::kw_acquire;
        }
        break;
      }
      break;
    case 'd':
      if (memcmp(Keyword.data() + 2, "dress", 5) == 0) {
        return lltok::kw_address;
      }
      break;
    case 'l':
      switch (Keyword[2]) {
      case 'i':
        if (memcmp(Keyword.data() + 3, "asee", 4) == 0) {
          return lltok::kw_aliasee;
        }
        break;
      case 'l':
        if (memcmp(Keyword.data() + 3, "Ones", 4) == 0) {
          return lltok::kw_allOnes;
        }
        break;
      }
      break;
    }
    break;
  case 'b':
    if (memcmp(Keyword.data() + 1, "it", 2) != 0)
      break;
    switch (Keyword[3]) {
    case 'M':
      if (memcmp(Keyword.data() + 4, "ask", 3) == 0) {
        return lltok::kw_bitMask;
      }
      break;
    case 'c':
      if (memcmp(Keyword.data() + 4, "ast", 3) == 0) {
        UIntVal = Instruction::BitCast;
        return lltok::kw_bitcast;
      }
      break;
    }
    break;
  case 'c':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "eanup", 5) == 0) {
        return lltok::kw_cleanup;
      }
      break;
    case 'm':
      if (memcmp(Keyword.data() + 2, "pxchg", 5) == 0) {
        UIntVal = Instruction::AtomicCmpXchg;
        return lltok::kw_cmpxchg;
      }
      break;
    }
    break;
  case 'd':
    switch (Keyword[1]) {
    case 'e':
      switch (Keyword[2]) {
      case 'c':
        if (memcmp(Keyword.data() + 3, "lare", 4) == 0) {
          return lltok::kw_declare;
        }
        break;
      case 'f':
        if (memcmp(Keyword.data() + 3, "ault", 4) == 0) {
          return lltok::kw_default;
        }
        break;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "namic", 5) == 0) {
        return lltok::kw_dynamic;
      }
      break;
    }
    break;
  case 'f':
    if (memcmp(Keyword.data() + 1, "ptrunc", 6) == 0) {
      UIntVal = Instruction::FPTrunc;
      return lltok::kw_fptrunc;
    }
    break;
  case 'g':
    if (memcmp(Keyword.data() + 1, "raalcc", 6) == 0) {
      return lltok::kw_graalcc;
    }
    break;
  case 'h':
    if (memcmp(Keyword.data() + 1, "otness", 6) == 0) {
      return lltok::kw_hotness;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "nrange", 6) == 0) {
      return lltok::kw_inrange;
    }
    break;
  case 'l':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "rgest", 5) == 0) {
        return lltok::kw_largest;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "nkage", 5) == 0) {
        return lltok::kw_linkage;
      }
      break;
    }
    break;
  case 'm':
    if (memcmp(Keyword.data() + 1, "emProf", 6) == 0) {
      return lltok::kw_memProf;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "otcold", 6) == 0) {
      return lltok::kw_notcold;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'r':
      if (memcmp(Keyword.data() + 2, "ivate", 5) == 0) {
        return lltok::kw_private;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "rauth", 5) == 0) {
        return lltok::kw_ptrauth;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "e", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'a':
      if (memcmp(Keyword.data() + 3, "ssoc", 4) == 0) {
        return lltok::kw_reassoc;
      }
      break;
    case 'l':
      if (memcmp(Keyword.data() + 3, "ease", 4) == 0) {
        return lltok::kw_release;
      }
      break;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'e':
      switch (Keyword[2]) {
      case 'c':
        if (memcmp(Keyword.data() + 3, "tion", 4) == 0) {
          return lltok::kw_section;
        }
        break;
      case 'q':
        if (memcmp(Keyword.data() + 3, "_cst", 4) == 0) {
          return lltok::kw_seq_cst;
        }
        break;
      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "mmary", 5) == 0) {
        return lltok::kw_summary;
      }
      break;
    case 'w':
      if (memcmp(Keyword.data() + 2, "iftcc", 5) == 0) {
        return lltok::kw_swiftcc;
      }
      break;
    }
    break;
  case 'u':
    if (memcmp(Keyword.data() + 1, "nknown", 6) == 0) {
      return lltok::kw_unknown;
    }
    break;
  case 'v':
    if (memcmp(Keyword.data() + 1, "FuncId", 6) == 0) {
      return lltok::kw_vFuncId;
    }
    break;
  case 'w':
    if (memcmp(Keyword.data() + 1, "in64cc", 6) == 0) {
      return lltok::kw_win64cc;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_amx", 6) == 0) {
      TyVal = Type::getX86_AMXTy(Context);
      return lltok::Type;
    }
    break;
  }
  break;
case 8:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "nyregcc", 7) == 0) {
      return lltok::kw_anyregcc;
    }
    break;
  case 'c':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "tch", 3) != 0)
        break;
      switch (Keyword[5]) {
      case 'p':
        if (memcmp(Keyword.data() + 6, "ad", 2) == 0) {
          UIntVal = Instruction::CatchPad;
          return lltok::kw_catchpad;
        }
        break;
      case 'r':
        if (memcmp(Keyword.data() + 6, "et", 2) == 0) {
          UIntVal = Instruction::CatchRet;
          return lltok::kw_catchret;
        }
        break;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "n", 1) != 0)
        break;
      switch (Keyword[3]) {
      case 's':
        if (memcmp(Keyword.data() + 4, "tant", 4) == 0) {
          return lltok::kw_constant;
        }
        break;
      case 't':
        if (memcmp(Keyword.data() + 4, "ract", 4) == 0) {
          return lltok::kw_contract;
        }
        break;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "itical", 6) == 0) {
        return lltok::kw_critical;
      }
      break;
    }
    break;
  case 'd':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "s", 1) != 0)
        break;
      switch (Keyword[3]) {
      case 'j':
        if (memcmp(Keyword.data() + 4, "oint", 4) == 0) {
          return lltok::kw_disjoint;
        }
        break;
      case 't':
        if (memcmp(Keyword.data() + 4, "inct", 4) == 0) {
          return lltok::kw_distinct;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "oLocal", 6) == 0) {
        return lltok::kw_dsoLocal;
      }
      break;
    }
    break;
  case 'e':
    switch (Keyword[1]) {
    case 'r':
      if (memcmp(Keyword.data() + 2, "rnomem", 6) == 0) {
        return lltok::kw_errnomem;
      }
      break;
    case 'x':
      if (memcmp(Keyword.data() + 2, "ternal", 6) == 0) {
        return lltok::kw_external;
      }
      break;
    }
    break;
  case 'f':
    switch (Keyword[1]) {
    case 'm':
      switch (Keyword[2]) {
      case 'a':
        if (memcmp(Keyword.data() + 3, "ximum", 5) == 0) {
          return lltok::kw_fmaximum;
        }
        break;
      case 'i':
        if (memcmp(Keyword.data() + 3, "nimum", 5) == 0) {
          return lltok::kw_fminimum;
        }
        break;
      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "nction", 6) == 0) {
        return lltok::kw_function;
      }
      break;
    }
    break;
  case 'h':
    if (memcmp(Keyword.data() + 1, "hvm_ccc", 7) == 0) {
      return lltok::kw_hhvm_ccc;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "n", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'b':
      if (memcmp(Keyword.data() + 3, "ounds", 5) == 0) {
        return lltok::kw_inbounds;
      }
      break;
    case 't':
      switch (Keyword[3]) {
      case 'e':
        if (memcmp(Keyword.data() + 4, "rnal", 4) == 0) {
          return lltok::kw_internal;
        }
        break;
      case 't':
        if (memcmp(Keyword.data() + 4, "optr", 4) == 0) {
          UIntVal = Instruction::IntToPtr;
          return lltok::kw_inttoptr;
        }
        break;
      }
      break;
    }
    break;
  case 'l':
    if (memcmp(Keyword.data() + 1, "inkonce", 7) == 0) {
      return lltok::kw_linkonce;
    }
    break;
  case 'm':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "yThrow", 6) == 0) {
        return lltok::kw_mayThrow;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "tadata", 6) == 0) {
        TyVal = Type::getMetadataTy(Context);
        return lltok::Type;
      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "sttail", 6) == 0) {
        return lltok::kw_musttail;
      }
      break;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "o", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'I':
      if (memcmp(Keyword.data() + 3, "nline", 5) == 0) {
        return lltok::kw_noInline;
      }
      break;
    case 'U':
      if (memcmp(Keyword.data() + 3, "nwind", 5) == 0) {
        return lltok::kw_noUnwind;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'r':
      if (memcmp(Keyword.data() + 2, "ologue", 6) == 0) {
        return lltok::kw_prologue;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "rtoint", 6) == 0) {
        UIntVal = Instruction::PtrToInt;
        return lltok::kw_ptrtoint;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "e", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'a':
      if (memcmp(Keyword.data() + 3, "d", 1) != 0)
        break;
      switch (Keyword[4]) {
      case 'N':
        if (memcmp(Keyword.data() + 5, "one", 3) == 0) {
          return lltok::kw_readNone;
        }
        break;
      case 'O':
        if (memcmp(Keyword.data() + 5, "nly", 3) == 0) {
          return lltok::kw_readOnly;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 3, "ByArg", 5) == 0) {
        return lltok::kw_resByArg;
      }
      break;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "mesi", 4) != 0)
        break;
      switch (Keyword[6]) {
      case 'g':
        if (memcmp(Keyword.data() + 7, "n", 1) == 0) {
          return lltok::kw_samesign;
        }
        break;
      case 'z':
        if (memcmp(Keyword.data() + 7, "e", 1) == 0) {
          return lltok::kw_samesize;
        }
        break;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "ackIds", 6) == 0) {
        return lltok::kw_stackIds;
      }
      break;
    }
    break;
  case 'u':
    if (memcmp(Keyword.data() + 1, "sub_sat", 7) == 0) {
      return lltok::kw_usub_sat;
    }
    break;
  case 'v':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "r", 1) != 0)
        break;
      switch (Keyword[3]) {
      case 'F':
        if (memcmp(Keyword.data() + 4, "lags", 4) == 0) {
          return lltok::kw_varFlags;
        }
        break;
      case 'i':
        if (memcmp(Keyword.data() + 4, "able", 4) == 0) {
          return lltok::kw_variable;
        }
        break;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "rsions", 6) == 0) {
        return lltok::kw_versions;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "rtFunc", 6) == 0) {
        return lltok::kw_virtFunc;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "latile", 6) == 0) {
        return lltok::kw_volatile;
      }
      break;
    }
    break;
  case 'w':
    if (memcmp(Keyword.data() + 1, "eak_odr", 7) == 0) {
      return lltok::kw_weak_odr;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_fp80", 7) == 0) {
      TyVal = Type::getX86_FP80Ty(Context);
      return lltok::Type;
    }
    break;
  }
  break;
case 9:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "drspace", 7) == 0) {
        return lltok::kw_addrspace;
      }
      break;
    case 'l':
      if (memcmp(Keyword.data() + 2, "ignLog2", 7) == 0) {
        return lltok::kw_alignLog2;
      }
      break;
    case 'm':
      if (memcmp(Keyword.data() + 2, "dgpu_", 5) != 0)
        break;
      switch (Keyword[7]) {
      case 'c':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_cs;
        }
        break;
      case 'e':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_es;
        }
        break;
      case 'g':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_gs;
        }
        break;
      case 'h':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_hs;
        }
        break;
      case 'l':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_ls;
        }
        break;
      case 'p':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_ps;
        }
        break;
      case 'v':
        if (memcmp(Keyword.data() + 8, "s", 1) == 0) {
          return lltok::kw_amdgpu_vs;
        }
        break;
      }
      break;
    case 'p':
      if (memcmp(Keyword.data() + 2, "pending", 7) == 0) {
        return lltok::kw_appending;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "omicrmw", 7) == 0) {
        UIntVal = Instruction::AtomicRMW;
        return lltok::kw_atomicrmw;
      }
      break;
    }
    break;
  case 'b':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "tinsert", 7) == 0) {
        UIntVal = Instruction::BitInsert;
        return lltok::kw_bitinsert;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "teArray", 7) == 0) {
        return lltok::kw_byteArray;
      }
      break;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "allsites", 8) == 0) {
      return lltok::kw_callsites;
    }
    break;
  case 'd':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "l", 1) != 0)
        break;
      switch (Keyword[3]) {
      case 'e':
        if (memcmp(Keyword.data() + 4, "xport", 5) == 0) {
          return lltok::kw_dllexport;
        }
        break;
      case 'i':
        if (memcmp(Keyword.data() + 4, "mport", 5) == 0) {
          return lltok::kw_dllimport;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "o_local", 7) == 0) {
        return lltok::kw_dso_local;
      }
      break;
    }
    break;
  case 'f':
    if (memcmp(Keyword.data() + 1, "uncFlags", 8) == 0) {
      return lltok::kw_funcFlags;
    }
    break;
  case 'l':
    if (memcmp(Keyword.data() + 1, "ocalexec", 8) == 0) {
      return lltok::kw_localexec;
    }
    break;
  case 'm':
    if (memcmp(Keyword.data() + 1, "onotonic", 8) == 0) {
      return lltok::kw_monotonic;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "o", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'R':
      if (memcmp(Keyword.data() + 3, "ecurse", 6) == 0) {
        return lltok::kw_noRecurse;
      }
      break;
    case 'c':
      if (memcmp(Keyword.data() + 3, "apture", 6) == 0) {
        return lltok::kw_nocapture;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "rtition", 7) == 0) {
        return lltok::kw_partition;
      }
      break;
    case 'p':
      if (memcmp(Keyword.data() + 2, "c_fp128", 7) == 0) {
        TyVal = Type::getPPC_FP128Ty(Context);
        return lltok::Type;
      }
      break;
    case 'r':
      switch (Keyword[2]) {
      case 'e':
        if (memcmp(Keyword.data() + 3, "falign", 6) == 0) {
          return lltok::kw_prefalign;
        }
        break;
      case 'o':
        if (memcmp(Keyword.data() + 3, "tected", 6) == 0) {
          return lltok::kw_protected;
        }
        break;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "rtoaddr", 7) == 0) {
        UIntVal = Instruction::PtrToAddr;
        return lltok::kw_ptrtoaddr;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "eadwrite", 8) == 0) {
      return lltok::kw_readwrite;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'p':
      if (memcmp(Keyword.data() + 2, "ir_func", 7) == 0) {
        return lltok::kw_spir_func;
      }
      break;
    case 'u':
      if (memcmp(Keyword.data() + 2, "mmaries", 7) == 0) {
        return lltok::kw_summaries;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "ncscope", 7) == 0) {
        return lltok::kw_syncscope;
      }
      break;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "ypeTests", 8) == 0) {
      return lltok::kw_typeTests;
    }
    break;
  case 'u':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "ec_wrap", 7) == 0) {
        return lltok::kw_udec_wrap;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "nc_wrap", 7) == 0) {
        return lltok::kw_uinc_wrap;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 2, "ordered", 7) == 0) {
        return lltok::kw_unordered;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "ub_cond", 7) == 0) {
        return lltok::kw_usub_cond;
      }
      break;
    }
    break;
  }
  break;
case 10:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'm':
      if (memcmp(Keyword.data() + 2, "dgpu_gfx", 8) == 0) {
        return lltok::kw_amdgpu_gfx;
      }
      break;
    case 'r':
      switch (Keyword[2]) {
      case 'g':
        if (memcmp(Keyword.data() + 3, "memonly", 7) == 0) {
          return lltok::kw_argmemonly;
        }
        break;
      case 'm':
        if (memcmp(Keyword.data() + 3, "_apcscc", 7) == 0) {
          return lltok::kw_arm_apcscc;
        }
        break;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "tributes", 8) == 0) {
        return lltok::kw_attributes;
      }
      break;
    case 'v':
      if (memcmp(Keyword.data() + 2, "r_intrcc", 8) == 0) {
        return lltok::kw_avr_intrcc;
      }
      break;
    }
    break;
  case 'b':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "textract", 8) == 0) {
        UIntVal = Instruction::BitExtract;
        return lltok::kw_bitextract;
      }
      break;
    case 'l':
      if (memcmp(Keyword.data() + 2, "ockcount", 8) == 0) {
        return lltok::kw_blockcount;
      }
      break;
    }
    break;
  case 'c':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "eanup", 5) != 0)
        break;
      switch (Keyword[7]) {
      case 'p':
        if (memcmp(Keyword.data() + 8, "ad", 2) == 0) {
          UIntVal = Instruction::CleanupPad;
          return lltok::kw_cleanuppad;
        }
        break;
      case 'r':
        if (memcmp(Keyword.data() + 8, "et", 2) == 0) {
          UIntVal = Instruction::CleanupRet;
          return lltok::kw_cleanupret;
        }
        break;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "de_model", 8) == 0) {
        return lltok::kw_code_model;
      }
      break;
    }
    break;
  case 'd':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "talayout", 8) == 0) {
        return lltok::kw_datalayout;
      }
      break;
    case 'e':
      if (memcmp(Keyword.data() + 2, "finition", 8) == 0) {
        return lltok::kw_definition;
      }
      break;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "xactmatch", 9) == 0) {
      return lltok::kw_exactmatch;
    }
    break;
  case 'i':
    switch (Keyword[1]) {
    case 'm':
      if (memcmp(Keyword.data() + 2, "portType", 8) == 0) {
        return lltok::kw_importType;
      }
      break;
    case 'n':
      switch (Keyword[2]) {
      case 'd':
        if (memcmp(Keyword.data() + 3, "irectbr", 7) == 0) {
          UIntVal = Instruction::IndirectBr;
          return lltok::kw_indirectbr;
        }
        break;
      case 'l':
        if (memcmp(Keyword.data() + 3, "ineBits", 7) == 0) {
          return lltok::kw_inlineBits;
        }
        break;
      }
      break;
    }
    break;
  case 'l':
    if (memcmp(Keyword.data() + 1, "andingpad", 9) == 0) {
      UIntVal = Instruction::LandingPad;
      return lltok::kw_landingpad;
    }
    break;
  case 'm':
    if (memcmp(Keyword.data() + 1, "68k_rtdcc", 9) == 0) {
      return lltok::kw_m68k_rtdcc;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'r':
      if (memcmp(Keyword.data() + 2, "ovenance", 8) == 0) {
        return lltok::kw_provenance;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 2, "x_", 2) != 0)
        break;
      switch (Keyword[4]) {
      case 'd':
        if (memcmp(Keyword.data() + 5, "evice", 5) == 0) {
          return lltok::kw_ptx_device;
        }
        break;
      case 'k':
        if (memcmp(Keyword.data() + 5, "ernel", 5) == 0) {
          return lltok::kw_ptx_kernel;
        }
        break;
      }
      break;
    }
    break;
  case 's':
    if (memcmp(Keyword.data() + 1, "i", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'd':
      if (memcmp(Keyword.data() + 3, "eeffect", 7) == 0) {
        return lltok::kw_sideeffect;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 3, "gleImpl", 7) == 0) {
        return lltok::kw_singleImpl;
      }
      break;
    }
    break;
  case 't':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "rget_mem", 8) == 0) {
        return lltok::kw_target_mem;
      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "peIdInfo", 8) == 0) {
        return lltok::kw_typeIdInfo;
      }
      break;
    }
    break;
  case 'v':
    if (memcmp(Keyword.data() + 1, "isibility", 9) == 0) {
      return lltok::kw_visibility;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_intrcc", 9) == 0) {
      return lltok::kw_x86_intrcc;
    }
    break;
  }
  break;
case 11:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "rm_aapcscc", 10) == 0) {
      return lltok::kw_arm_aapcscc;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "a", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'n':
      if (memcmp(Keyword.data() + 3, "AutoHide", 8) == 0) {
        return lltok::kw_canAutoHide;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 3, "chswitch", 8) == 0) {
        UIntVal = Instruction::CatchSwitch;
        return lltok::kw_catchswitch;
      }
      break;
    }
    break;
  case 'd':
    if (memcmp(Keyword.data() + 1, "eclaration", 10) == 0) {
      return lltok::kw_declaration;
    }
    break;
  case 'e':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "ementwise", 9) == 0) {
        return lltok::kw_elementwise;
      }
      break;
    case 'x':
      if (memcmp(Keyword.data() + 2, "tern_weak", 9) == 0) {
        return lltok::kw_extern_weak;
      }
      break;
    }
    break;
  case 'f':
    if (memcmp(Keyword.data() + 1, "m", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'a':
      if (memcmp(Keyword.data() + 3, "ximumnum", 8) == 0) {
        return lltok::kw_fmaximumnum;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 3, "nimumnum", 8) == 0) {
        return lltok::kw_fminimumnum;
      }
      break;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "n", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'i':
      if (memcmp(Keyword.data() + 3, "tialexec", 8) == 0) {
        return lltok::kw_initialexec;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 3, "ertvalue", 8) == 0) {
        UIntVal = Instruction::InsertValue;
        return lltok::kw_insertvalue;
      }
      break;
    }
    break;
  case 'p':
    if (memcmp(Keyword.data() + 1, "ersonality", 10) == 0) {
      return lltok::kw_personality;
    }
    break;
  case 's':
    switch (Keyword[1]) {
    case 'p':
      if (memcmp(Keyword.data() + 2, "ir_kernel", 9) == 0) {
        return lltok::kw_spir_kernel;
      }
      break;
    case 'w':
      if (memcmp(Keyword.data() + 2, "ifttailcc", 9) == 0) {
        return lltok::kw_swifttailcc;
      }
      break;
    }
    break;
  case 't':
    switch (Keyword[1]) {
    case 'a':
      if (memcmp(Keyword.data() + 2, "rget_mem", 8) != 0)
        break;
      switch (Keyword[10]) {
      case '0':
        return lltok::kw_target_mem0;

      case '1':
        return lltok::kw_target_mem1;

      }
      break;
    case 'y':
      if (memcmp(Keyword.data() + 2, "peTestRes", 9) == 0) {
        return lltok::kw_typeTestRes;
      }
      break;
    }
    break;
  case 'u':
    if (memcmp(Keyword.data() + 1, "nreachable", 10) == 0) {
      UIntVal = Instruction::Unreachable;
      return lltok::kw_unreachable;
    }
    break;
  case 'v':
    if (memcmp(Keyword.data() + 1, "TableFuncs", 10) == 0) {
      return lltok::kw_vTableFuncs;
    }
    break;
  }
  break;
case 12:
  switch (Keyword[0]) {
  case 'D':
    if (memcmp(Keyword.data() + 1, "ISPLAY_NAME", 11) == 0) {
      return lltok::kw_DISPLAY_NAME;
    }
    break;
  case 'a':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "waysInline", 10) == 0) {
        return lltok::kw_alwaysInline;
      }
      break;
    case 'v':
      if (memcmp(Keyword.data() + 2, "r_signalcc", 10) == 0) {
        return lltok::kw_avr_signalcc;
      }
      break;
    }
    break;
  case 'b':
    switch (Keyword[1]) {
    case 'l':
      if (memcmp(Keyword.data() + 2, "ockaddress", 10) == 0) {
        return lltok::kw_blockaddress;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "anchFunnel", 10) == 0) {
        return lltok::kw_branchFunnel;
      }
      break;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "xtractvalue", 11) == 0) {
      UIntVal = Instruction::ExtractValue;
      return lltok::kw_extractvalue;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "nteldialect", 11) == 0) {
      return lltok::kw_inteldialect;
    }
    break;
  case 'l':
    switch (Keyword[1]) {
    case 'i':
      if (memcmp(Keyword.data() + 2, "nkonce_odr", 10) == 0) {
        return lltok::kw_linkonce_odr;
      }
      break;
    case 'o':
      if (memcmp(Keyword.data() + 2, "caldynamic", 10) == 0) {
        return lltok::kw_localdynamic;
      }
      break;
    }
    break;
  case 'p':
    switch (Keyword[1]) {
    case 'o':
      if (memcmp(Keyword.data() + 2, "sitivezero", 10) == 0) {
        return lltok::kw_positivezero;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "eservesign", 10) == 0) {
        return lltok::kw_preservesign;
      }
      break;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "iscv_vls_cc", 11) == 0) {
      return lltok::kw_riscv_vls_cc;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "hread_local", 11) == 0) {
      return lltok::kw_thread_local;
    }
    break;
  case 'u':
    switch (Keyword[1]) {
    case 'n':
      switch (Keyword[2]) {
      case 'i':
        if (memcmp(Keyword.data() + 3, "queRetVal", 9) == 0) {
          return lltok::kw_uniqueRetVal;
        }
        break;
      case 'n':
        if (memcmp(Keyword.data() + 3, "amed_addr", 9) == 0) {
          return lltok::kw_unnamed_addr;
        }
        break;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 2, "elistorder", 10) == 0) {
        return lltok::kw_uselistorder;
      }
      break;
    }
    break;
  }
  break;
case 13:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "drspacecast", 11) == 0) {
        UIntVal = Instruction::AddrSpaceCast;
        return lltok::kw_addrspacecast;
      }
      break;
    case 'm':
      if (memcmp(Keyword.data() + 2, "dgpu_kernel", 11) == 0) {
        return lltok::kw_amdgpu_kernel;
      }
      break;
    }
    break;
  case 'g':
    if (memcmp(Keyword.data() + 1, "etelementptr", 12) == 0) {
      UIntVal = Instruction::GetElementPtr;
      return lltok::kw_getelementptr;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "nsertelement", 12) == 0) {
      UIntVal = Instruction::InsertElement;
      return lltok::kw_insertelement;
    }
    break;
  case 'm':
    if (memcmp(Keyword.data() + 1, "sp430_intrcc", 12) == 0) {
      return lltok::kw_msp430_intrcc;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "odeduplicate", 12) == 0) {
      return lltok::kw_nodeduplicate;
    }
    break;
  case 's':
    if (memcmp(Keyword.data() + 1, "hufflevector", 12) == 0) {
      UIntVal = Instruction::ShuffleVector;
      return lltok::kw_shufflevector;
    }
    break;
  case 'u':
    if (memcmp(Keyword.data() + 1, "niformRetVal", 12) == 0) {
      return lltok::kw_uniformRetVal;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_", 3) != 0)
      break;
    switch (Keyword[4]) {
    case '6':
      if (memcmp(Keyword.data() + 5, "4_sysvcc", 8) == 0) {
        return lltok::kw_x86_64_sysvcc;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 5, "egcallcc", 8) == 0) {
        return lltok::kw_x86_regcallcc;
      }
      break;
    case 's':
      if (memcmp(Keyword.data() + 5, "tdcallcc", 8) == 0) {
        return lltok::kw_x86_stdcallcc;
      }
      break;
    }
    break;
  }
  break;
case 14:
  switch (Keyword[0]) {
  case 'c':
    if (memcmp(Keyword.data() + 1, "xx_fast_tlscc", 13) == 0) {
      return lltok::kw_cxx_fast_tlscc;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "xtractelement", 13) == 0) {
      UIntVal = Instruction::ExtractElement;
      return lltok::kw_extractelement;
    }
    break;
  case 'h':
    if (memcmp(Keyword.data() + 1, "asUnknownCall", 13) == 0) {
      return lltok::kw_hasUnknownCall;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "ntel_ocl_bicc", 13) == 0) {
      return lltok::kw_intel_ocl_bicc;
    }
    break;
  case 'p':
    if (memcmp(Keyword.data() + 1, "reserve_allcc", 13) == 0) {
      return lltok::kw_preserve_allcc;
    }
    break;
  case 's':
    if (memcmp(Keyword.data() + 1, "i", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'n':
      if (memcmp(Keyword.data() + 3, "gleImplName", 11) == 0) {
        return lltok::kw_singleImplName;
      }
      break;
    case 'z':
      if (memcmp(Keyword.data() + 3, "eM1BitWidth", 11) == 0) {
        return lltok::kw_sizeM1BitWidth;
      }
      break;
    }
    break;
  case 'w':
    if (memcmp(Keyword.data() + 1, "pdResolutions", 13) == 0) {
      return lltok::kw_wpdResolutions;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_", 3) != 0)
      break;
    switch (Keyword[4]) {
    case 'f':
      if (memcmp(Keyword.data() + 5, "astcallcc", 9) == 0) {
        return lltok::kw_x86_fastcallcc;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 5, "hiscallcc", 9) == 0) {
        return lltok::kw_x86_thiscallcc;
      }
      break;
    }
    break;
  }
  break;
case 15:
  switch (Keyword[0]) {
  case 'a':
    switch (Keyword[1]) {
    case 'd':
      if (memcmp(Keyword.data() + 2, "dress_is_null", 13) == 0) {
        return lltok::kw_address_is_null;
      }
      break;
    case 'm':
      if (memcmp(Keyword.data() + 2, "dgpu_cs_chain", 13) == 0) {
        return lltok::kw_amdgpu_cs_chain;
      }
      break;
    case 'r':
      if (memcmp(Keyword.data() + 2, "m_aapcs_vfpcc", 13) == 0) {
        return lltok::kw_arm_aapcs_vfpcc;
      }
      break;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "fguard_checkcc", 14) == 0) {
      return lltok::kw_cfguard_checkcc;
    }
    break;
  case 'd':
    if (memcmp(Keyword.data() + 1, "so_preemptable", 14) == 0) {
      return lltok::kw_dso_preemptable;
    }
    break;
  case 'i':
    if (memcmp(Keyword.data() + 1, "naccessiblemem", 14) == 0) {
      return lltok::kw_inaccessiblemem;
    }
    break;
  case 'p':
    if (memcmp(Keyword.data() + 1, "reserve_", 8) != 0)
      break;
    switch (Keyword[9]) {
    case 'm':
      if (memcmp(Keyword.data() + 10, "ostcc", 5) == 0) {
        return lltok::kw_preserve_mostcc;
      }
      break;
    case 'n':
      if (memcmp(Keyword.data() + 10, "onecc", 5) == 0) {
        return lltok::kw_preserve_nonecc;
      }
      break;
    }
    break;
  case 'r':
    switch (Keyword[1]) {
    case 'e':
      if (memcmp(Keyword.data() + 2, "ad_provenance", 13) == 0) {
        return lltok::kw_read_provenance;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "scv_vector_cc", 13) == 0) {
        return lltok::kw_riscv_vector_cc;
      }
      break;
    }
    break;
  case 's':
    if (memcmp(Keyword.data() + 1, "ource_filename", 14) == 0) {
      return lltok::kw_source_filename;
    }
    break;
  case 'z':
    if (memcmp(Keyword.data() + 1, "eroinitializer", 14) == 0) {
      return lltok::kw_zeroinitializer;
    }
    break;
  }
  break;
case 16:
  switch (Keyword[0]) {
  case 'v':
    switch (Keyword[1]) {
    case 'c':
      if (memcmp(Keyword.data() + 2, "all_visibility", 14) == 0) {
        return lltok::kw_vcall_visibility;
      }
      break;
    case 'i':
      if (memcmp(Keyword.data() + 2, "rtualConstProp", 14) == 0) {
        return lltok::kw_virtualConstProp;
      }
      break;
    }
    break;
  case 'x':
    if (memcmp(Keyword.data() + 1, "86_vectorcallcc", 15) == 0) {
      return lltok::kw_x86_vectorcallcc;
    }
    break;
  }
  break;
case 17:
  if (memcmp(Keyword.data() + 0, "mustBeUnreachable", 17) == 0) {
    return lltok::kw_mustBeUnreachable;
  }
  break;
case 18:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "arch64_vector_pcs", 17) == 0) {
      return lltok::kw_aarch64_vector_pcs;
    }
    break;
  case 'l':
    if (memcmp(Keyword.data() + 1, "ocal_unnamed_addr", 17) == 0) {
      return lltok::kw_local_unnamed_addr;
    }
    break;
  case 'r':
    if (memcmp(Keyword.data() + 1, "eturnDoesNotAlias", 17) == 0) {
      return lltok::kw_returnDoesNotAlias;
    }
    break;
  }
  break;
case 19:
  switch (Keyword[0]) {
  case 'i':
    if (memcmp(Keyword.data() + 1, "naccessiblememonly", 18) == 0) {
      return lltok::kw_inaccessiblememonly;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "o", 1) != 0)
      break;
    switch (Keyword[2]) {
    case 'R':
      if (memcmp(Keyword.data() + 3, "enameOnPromotion", 16) == 0) {
        return lltok::kw_noRenameOnPromotion;
      }
      break;
    case '_':
      if (memcmp(Keyword.data() + 3, "sanitize_address", 16) == 0) {
        return lltok::kw_no_sanitize_address;
      }
      break;
    case 't':
      if (memcmp(Keyword.data() + 3, "EligibleToImport", 16) == 0) {
        return lltok::kw_notEligibleToImport;
      }
      break;
    }
    break;
  }
  break;
case 20:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "vailable_externally", 19) == 0) {
      return lltok::kw_available_externally;
    }
    break;
  case 'd':
    if (memcmp(Keyword.data() + 1, "so_local_equivalent", 19) == 0) {
      return lltok::kw_dso_local_equivalent;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "ypeTestAssumeVCalls", 19) == 0) {
      return lltok::kw_typeTestAssumeVCalls;
    }
    break;
  }
  break;
case 21:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "mdgpu_gfx_whole_wave", 20) == 0) {
      return lltok::kw_amdgpu_gfx_whole_wave;
    }
    break;
  case 'c':
    if (memcmp(Keyword.data() + 1, "heriot_librarycallcc", 20) == 0) {
      return lltok::kw_cheriot_librarycallcc;
    }
    break;
  case 'n':
    if (memcmp(Keyword.data() + 1, "o_sanitize_hwaddress", 20) == 0) {
      return lltok::kw_no_sanitize_hwaddress;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "ypeCheckedLoadVCalls", 20) == 0) {
      return lltok::kw_typeCheckedLoadVCalls;
    }
    break;
  }
  break;
case 22:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "arch64_sve_vector_pcs", 21) == 0) {
      return lltok::kw_aarch64_sve_vector_pcs;
    }
    break;
  case 'e':
    if (memcmp(Keyword.data() + 1, "xternally_initialized", 21) == 0) {
      return lltok::kw_externally_initialized;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "ypeidCompatibleVTable", 21) == 0) {
      return lltok::kw_typeidCompatibleVTable;
    }
    break;
  }
  break;
case 24:
  switch (Keyword[0]) {
  case 'a':
    if (memcmp(Keyword.data() + 1, "mdgpu_cs_chain_preserve", 23) == 0) {
      return lltok::kw_amdgpu_cs_chain_preserve;
    }
    break;
  case 's':
    if (memcmp(Keyword.data() + 1, "anitize_address_dyninit", 23) == 0) {
      return lltok::kw_sanitize_address_dyninit;
    }
    break;
  }
  break;
case 25:
  switch (Keyword[0]) {
  case 'c':
    if (memcmp(Keyword.data() + 1, "heriot_compartmentcallcc", 24) == 0) {
      return lltok::kw_cheriot_compartmentcallcc;
    }
    break;
  case 't':
    if (memcmp(Keyword.data() + 1, "ypeTestAssumeConstVCalls", 24) == 0) {
      return lltok::kw_typeTestAssumeConstVCalls;
    }
    break;
  }
  break;
case 26:
  if (memcmp(Keyword.data() + 0, "typeCheckedLoadConstVCalls", 26) == 0) {
    return lltok::kw_typeCheckedLoadConstVCalls;
  }
  break;
case 27:
  if (memcmp(Keyword.data() + 0, "cheriot_compartmentcalleecc", 27) == 0) {
    return lltok::kw_cheriot_compartmentcalleecc;
  }
  break;
case 29:
  if (memcmp(Keyword.data() + 0, "inaccessiblemem_or_argmemonly", 29) == 0) {
    return lltok::kw_inaccessiblemem_or_argmemonly;
  }
  break;
case 32:
  if (memcmp(Keyword.data() + 0, "aarch64_sme_preservemost_from_x", 31) != 0)
    break;
  switch (Keyword[31]) {
  case '0':
    return lltok::kw_aarch64_sme_preservemost_from_x0;

  case '1':
    return lltok::kw_aarch64_sme_preservemost_from_x1;

  case '2':
    return lltok::kw_aarch64_sme_preservemost_from_x2;

  }
  break;
}



#define DWKEYWORD(TYPE, TOKEN)                                                 \
  do {                                                                         \
    if (Keyword.starts_with("DW_" #TYPE "_")) {                                \
      StrVal.assign(Keyword.begin(), Keyword.end());                           \
      return lltok::TOKEN;                                                     \
    }                                                                          \
  } while (false)

  DWKEYWORD(TAG, DwarfTag);
  DWKEYWORD(ATE, DwarfAttEncoding);
  DWKEYWORD(VIRTUALITY, DwarfVirtuality);
  DWKEYWORD(LLVM_LANG_DIALECT, DwarfLangDialect);
  DWKEYWORD(LANG, DwarfLang);
  DWKEYWORD(LNAME, DwarfSourceLangName);
  DWKEYWORD(CC, DwarfCC);
  DWKEYWORD(OP, DwarfOp);
  DWKEYWORD(MACINFO, DwarfMacinfo);
  DWKEYWORD(APPLE_ENUM_KIND, DwarfEnumKind);

#undef DWKEYWORD

// Keywords for debug record types.
#define DBGRECORDTYPEKEYWORD(STR)                                              \
  do {                                                                         \
    if (Keyword == "dbg_" #STR) {                                              \
      StrVal = #STR;                                                           \
      return lltok::DbgRecordType;                                             \
    }                                                                          \
  } while (false)

  DBGRECORDTYPEKEYWORD(value);
  DBGRECORDTYPEKEYWORD(declare);
  DBGRECORDTYPEKEYWORD(assign);
  DBGRECORDTYPEKEYWORD(label);
  DBGRECORDTYPEKEYWORD(declare_value);
#undef DBGRECORDTYPEKEYWORD

  if (Keyword.starts_with("DIFlag")) {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::DIFlag;
  }

  if (Keyword.starts_with("DISPFlag")) {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::DISPFlag;
  }

  if (Keyword.starts_with("CSK_")) {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::ChecksumKind;
  }

  if (Keyword == "NoDebug" || Keyword == "FullDebug" ||
      Keyword == "LineTablesOnly" || Keyword == "DebugDirectivesOnly") {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::EmissionKind;
  }

  if (Keyword == "GNU" || Keyword == "Apple" || Keyword == "None" ||
      Keyword == "Default") {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::NameTableKind;
  }

  if (Keyword == "Binary" || Keyword == "Decimal" || Keyword == "Rational") {
    StrVal.assign(Keyword.begin(), Keyword.end());
    return lltok::FixedPointKind;
  }

  // Check for [us]0x[0-9A-Fa-f]+ which are Hexadecimal constant generated by
  // the CFE to avoid forcing it to deal with 64-bit numbers. Also check for
  // f0x[0-9A-Fa-f]+, which is the floating-point hexadecimal literal constant.
  if ((TokStart[0] == 'u' || TokStart[0] == 's' || TokStart[0] == 'f') &&
      TokStart[1] == '0' && TokStart[2] == 'x' &&
      isxdigit(static_cast<unsigned char>(TokStart[3]))) {
    bool IsFloatConst = TokStart[0] == 'f';
    size_t Len = CurPtr - TokStart - 3;
    uint32_t Bits = Len * 4;
    StringRef HexStr(TokStart + 3, Len);
    if (!all_of(HexStr, isxdigit)) {
      // Bad token, return it as an error.
      CurPtr = TokStart + 3;
      return lltok::Error;
    }
    APInt Tmp(Bits, HexStr, 16);
    uint32_t ActiveBits = Tmp.getActiveBits();
    if (!IsFloatConst && ActiveBits > 0 && ActiveBits < Bits)
      Tmp = Tmp.trunc(ActiveBits);
    APSIntVal = APSInt(Tmp, TokStart[0] != 's');
    return IsFloatConst ? lltok::FloatHexLiteral : lltok::APSInt;
  }

  // If this is "cc1234", return this as just "cc".
  if (TokStart[0] == 'c' && TokStart[1] == 'c') {
    CurPtr = TokStart+2;
    return lltok::kw_cc;
  }

  // Finally, if this isn't known, return an error.
  CurPtr = TokStart+1;
  return lltok::Error;
}

/// Lex all tokens that start with a 0x prefix, knowing they match and are not
/// labels.
///    HexFPLiteral      [-+]?0x[0-9A-Fa-f]+.[0-9A-Fa-f]*[pP][-+]?[0-9]+
///    HexFPConstant     0x[0-9A-Fa-f]+
///    HexFP80Constant   0xK[0-9A-Fa-f]+
///    HexFP128Constant  0xL[0-9A-Fa-f]+
///    HexPPC128Constant 0xM[0-9A-Fa-f]+
///    HexHalfConstant   0xH[0-9A-Fa-f]+
///    HexBFloatConstant 0xR[0-9A-Fa-f]+
lltok::Kind LLLexer::Lex0x() {
  CurPtr = TokStart + 2;

  char Kind;
  if ((CurPtr[0] >= 'K' && CurPtr[0] <= 'M') || CurPtr[0] == 'H' ||
      CurPtr[0] == 'R') {
    Kind = *CurPtr++;
  } else {
    Kind = 'J';
  }

  if (!isxdigit(static_cast<unsigned char>(CurPtr[0]))) {
    // Bad token, return it as an error.
    CurPtr = TokStart+1;
    return lltok::Error;
  }

  while (isxdigit(static_cast<unsigned char>(CurPtr[0])))
    ++CurPtr;

  if (*CurPtr == '.') {
    // HexFPLiteral, following C's %a syntax
    return LexFloatStr();
  }

  if (Kind == 'J') {
    // HexFPConstant - Floating point constant represented in IEEE format as a
    // hexadecimal number for when exponential notation is not precise enough.
    // Half, BFloat, Float, and double only.
    APFloatVal = APFloat(APFloat::IEEEdouble(),
                         APInt(64, HexIntToVal(TokStart + 2, CurPtr)));
    return lltok::APFloat;
  }

  uint64_t Pair[2];
  switch (Kind) {
  default:
    llvm_unreachable("Unknown kind!");
  case 'K':
    // F80HexFPConstant - x87 long double in hexadecimal format (10 bytes)
    FP80HexToIntPair(TokStart + 3, CurPtr, Pair);
    APSIntVal = APInt(80, Pair);
    return lltok::FloatHexLiteral;
  case 'L':
    // F128HexFPConstant - IEEE 128-bit in hexadecimal format (16 bytes)
    HexToIntPair(TokStart + 3, CurPtr, Pair);
    APSIntVal = APInt(128, Pair);
    return lltok::FloatHexLiteral;
  case 'M':
    // PPC128HexFPConstant - PowerPC 128-bit in hexadecimal format (16 bytes)
    HexToIntPair(TokStart + 3, CurPtr, Pair);
    APSIntVal = APInt(128, Pair);
    return lltok::FloatHexLiteral;
  case 'H': {
    uint64_t Val = HexIntToVal(TokStart + 3, CurPtr);
    if (!llvm::isUInt<16>(Val)) {
      LexError("hexadecimal constant too large for half (16-bit)");
      return lltok::Error;
    }
    APSIntVal = APInt(16, Val);
    return lltok::FloatHexLiteral;
  }
  case 'R': {
    // Brain floating point
    uint64_t Val = HexIntToVal(TokStart + 3, CurPtr);
    if (!llvm::isUInt<16>(Val)) {
      LexError("hexadecimal constant too large for bfloat (16-bit)");
      return lltok::Error;
    }
    APSIntVal = APInt(16, Val);
    return lltok::FloatHexLiteral;
  }
  }
}

/// Lex tokens for a label or a numeric constant, possibly starting with -.
///    Label             [-a-zA-Z$._0-9]+:
///    NInteger          -[0-9]+
///    FPConstant        [-+]?[0-9]+[.][0-9]*([eE][-+]?[0-9]+)?
///    PInteger          [0-9]+
///    HexFPLiteral      [-+]?0x[0-9A-Fa-f]+.[0-9A-Fa-f]*[pP][-+]?[0-9]+
///    HexFPConstant     0x[0-9A-Fa-f]+
///    HexFP80Constant   0xK[0-9A-Fa-f]+
///    HexFP128Constant  0xL[0-9A-Fa-f]+
///    HexPPC128Constant 0xM[0-9A-Fa-f]+
lltok::Kind LLLexer::LexDigitOrNegative() {
  // If the letter after the negative is not a number, this is probably a label.
  if (!isdigit(static_cast<unsigned char>(TokStart[0])) &&
      !isdigit(static_cast<unsigned char>(CurPtr[0]))) {
    // Okay, this is not a number after the -, it's probably a label.
    if (const char *End = isLabelTail(CurPtr)) {
      StrVal.assign(TokStart, End-1);
      CurPtr = End;
      return lltok::LabelStr;
    }

    // It might be a -inf, -nan, etc. Check if it's a float string (which will
    // also handle error conditions there).
    return LexFloatStr();
  }

  // At this point, it is either a label, int or fp constant.

  // Skip digits, we have at least one.
  for (; isdigit(static_cast<unsigned char>(CurPtr[0])); ++CurPtr)
    /*empty*/;

  // Check if this is a fully-numeric label:
  if (isdigit(TokStart[0]) && CurPtr[0] == ':') {
    uint64_t Val = atoull(TokStart, CurPtr);
    ++CurPtr; // Skip the colon.
    if ((unsigned)Val != Val)
      LexError("invalid value number (too large)");
    UIntVal = unsigned(Val);
    return lltok::LabelID;
  }

  // Check to see if this really is a string label, e.g. "-1:".
  if (isLabelChar(CurPtr[0]) || CurPtr[0] == ':') {
    if (const char *End = isLabelTail(CurPtr)) {
      StrVal.assign(TokStart, End-1);
      CurPtr = End;
      return lltok::LabelStr;
    }
  }

  // If the next character is a '.', then it is a fp value, otherwise its
  // integer.
  if (CurPtr[0] != '.') {
    if (TokStart[0] == '0' && TokStart[1] == 'x')
      return Lex0x();
    if (TokStart[0] == '-' && TokStart[1] == '0' && TokStart[2] == 'x')
      return LexFloatStr();

    APSIntVal = APSInt(StringRef(TokStart, CurPtr - TokStart));
    return lltok::APSInt;
  }

  ++CurPtr;

  // Skip over [0-9]*([eE][-+]?[0-9]+)?
  while (isdigit(static_cast<unsigned char>(CurPtr[0]))) ++CurPtr;

  if (CurPtr[0] == 'e' || CurPtr[0] == 'E') {
    if (isdigit(static_cast<unsigned char>(CurPtr[1])) ||
        ((CurPtr[1] == '-' || CurPtr[1] == '+') &&
          isdigit(static_cast<unsigned char>(CurPtr[2])))) {
      CurPtr += 2;
      while (isdigit(static_cast<unsigned char>(CurPtr[0]))) ++CurPtr;
    }
  }

  StrVal.assign(TokStart, CurPtr - TokStart);
  return lltok::FloatLiteral;
}

/// Lex a floating point constant starting with +.
///    FPConstant   [-+]?[0-9]+[.][0-9]*([eE][-+]?[0-9]+)?
///    HexFPLiteral [-+]?0x[0-9A-Fa-f]+.[0-9A-Fa-f]*[pP][-+]?[0-9]+
///    HexFPSpecial [-+](inf|qnan|s?nan\(0x[0-9A-Fa-f]+\))
lltok::Kind LLLexer::LexPositive() {
  // If it's not numeric, check for special floating-point values.
  if (!isdigit(static_cast<unsigned char>(CurPtr[0])))
    return LexFloatStr();

  // Skip digits.
  for (++CurPtr; isdigit(static_cast<unsigned char>(CurPtr[0])); ++CurPtr)
    /*empty*/;

  // If the first non-digit is an x, check if it's a hex FP literal. LexFloatStr
  // will reanalyze TokStr..CurPtr to make sure that it's 0x and not 413x.
  if (CurPtr[0] == 'x')
    return LexFloatStr();

  // At this point, we need a '.'.
  if (CurPtr[0] != '.') {
    CurPtr = TokStart + 1;
    return lltok::Error;
  }

  ++CurPtr;

  // Skip over [0-9]*([eE][-+]?[0-9]+)?
  while (isdigit(static_cast<unsigned char>(CurPtr[0]))) ++CurPtr;

  if (CurPtr[0] == 'e' || CurPtr[0] == 'E') {
    if (isdigit(static_cast<unsigned char>(CurPtr[1])) ||
        ((CurPtr[1] == '-' || CurPtr[1] == '+') &&
        isdigit(static_cast<unsigned char>(CurPtr[2])))) {
      CurPtr += 2;
      while (isdigit(static_cast<unsigned char>(CurPtr[0]))) ++CurPtr;
    }
  }

  StrVal.assign(TokStart, CurPtr - TokStart);
  return lltok::FloatLiteral;
}

/// Lex all tokens that start with a + or - that could be a float literal.
///    HexFPLiteral      [-+]?0x[0-9A-Fa-f]+.[0-9A-Fa-f]*[pP][-+]?[0-9]+
///    HexFPSpecial      [-+](inf|qnan|s?nan\(0x[0-9A-Fa-f]+\))
lltok::Kind LLLexer::LexFloatStr() {
  // At the point we enter this function, we may have seen a few characters
  // already, but how many differs based on the entry point. Rewind to the
  // beginning just in case.
  CurPtr = TokStart;

  // Check for optional sign.
  if (*CurPtr == '-' || *CurPtr == '+')
    ++CurPtr;

  if (*CurPtr != '0') {
    // Check for keywords.
    const char *LabelStart = CurPtr;
    while (isLabelChar(*CurPtr))
      ++CurPtr;
    StringRef Label(LabelStart, CurPtr - LabelStart);

    // Basic special values.
    if (Label == "inf") {
      // Copy from the beginning, to include the sign.
      StrVal.assign(TokStart, CurPtr - TokStart);
      return lltok::FloatLiteral;
    }

    // APFloat::convertFromString doesn't support qnan, so translate it to a
    // nan payload string it does support.
    if (Label == "qnan") {
      StrVal = *TokStart == '-' ? "-nan(0)" : "nan(0)";
      return lltok::FloatLiteral;
    }

    // NaN with payload.
    if ((Label == "nan" || Label == "snan") && *CurPtr == '(') {
      const char *Payload = ++CurPtr;
      while (*CurPtr && *CurPtr != ')')
        ++CurPtr;

      // If no close parenthesis, it's a bad token, return it as an error.
      if (*CurPtr++ != ')') {
        CurPtr = TokStart + 1;
        LexError("unclosed nan literal");
        return lltok::Error;
      }

      StringRef PayloadStr(Payload, CurPtr - Payload);
      APInt Val;
      if (PayloadStr.consume_front("0x") && PayloadStr.getAsInteger(16, Val)) {
        StrVal.assign(TokStart, CurPtr - TokStart);
        // Drop the leading + from the string, as APFloat::convertFromString
        // doesn't support leading + sign.
        if (StrVal[0] == '+')
          StrVal.erase(0, 1);
        return lltok::FloatLiteral;
      }
    }

    // Bad token, return it as an error.
    LexError("bad payload format for nan literal");
    CurPtr = TokStart + 1;
    return lltok::Error;
  }
  ++CurPtr;

  if (*CurPtr++ != 'x') {
    // Bad token, return it as an error.
    CurPtr = TokStart + 1;
    return lltok::Error;
  }

  if (!isxdigit(static_cast<unsigned char>(CurPtr[0]))) {
    // Bad token, return it as an error.
    CurPtr = TokStart + 1;
    return lltok::Error;
  }

  while (isxdigit(static_cast<unsigned char>(CurPtr[0])))
    ++CurPtr;

  if (*CurPtr != '.') {
    // Bad token, return it as an error.
    CurPtr = TokStart + 1;
    return lltok::Error;
  }

  ++CurPtr; // Eat the .
  while (isxdigit(static_cast<unsigned char>(CurPtr[0])))
    ++CurPtr;

  if (*CurPtr != 'p' && *CurPtr != 'P') {
    // Bad token, return it as an error.
    CurPtr = TokStart + 1;
    return lltok::Error;
  }

  ++CurPtr;
  if (*CurPtr == '+' || *CurPtr == '-')
    ++CurPtr;
  while (isdigit(static_cast<unsigned char>(CurPtr[0])))
    ++CurPtr;

  StrVal.assign(TokStart, CurPtr - TokStart);
  return lltok::FloatLiteral;
}
