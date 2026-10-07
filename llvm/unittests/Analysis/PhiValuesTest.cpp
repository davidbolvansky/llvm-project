//===- PhiValuesTest.cpp - PhiValues unit tests ---------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/PhiValues.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "gtest/gtest.h"

using namespace llvm;

TEST(PhiValuesTest, SimplePhi) {
  LLVMContext C;
  Module M("PhiValuesTest", C);

  Type *VoidTy = Type::getVoidTy(C);
  Type *I1Ty = Type::getInt1Ty(C);
  Type *I32Ty = Type::getInt32Ty(C);
  Type *PtrTy = PointerType::get(C, 0);

  // Create a function with phis that do not have other phis as incoming values
  Function *F = Function::Create(FunctionType::get(VoidTy, false),
                                 Function::ExternalLinkage, "f", M);

  BasicBlock *Entry = BasicBlock::Create(C, "entry", F);
  BasicBlock *If = BasicBlock::Create(C, "if", F);
  BasicBlock *Else = BasicBlock::Create(C, "else", F);
  BasicBlock *Then = BasicBlock::Create(C, "then", F);
  CondBrInst::Create(PoisonValue::get(I1Ty), If, Else, Entry);
  UncondBrInst::Create(Then, If);
  UncondBrInst::Create(Then, Else);

  Value *Val1 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val1", Entry);
  Value *Val2 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val2", Entry);
  Value *Val3 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val3", Entry);
  Value *Val4 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val4", Entry);

  PHINode *Phi1 = PHINode::Create(I32Ty, 2, "phi1", Then);
  Phi1->addIncoming(Val1, If);
  Phi1->addIncoming(Val2, Else);
  PHINode *Phi2 = PHINode::Create(I32Ty, 2, "phi2", Then);
  Phi2->addIncoming(Val1, If);
  Phi2->addIncoming(Val3, Else);

  PhiValues PV(*F);
  PhiValues::ValueSet Vals;

  // Check that simple usage works
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that values are updated when one value is replaced with another
  Val1->replaceAllUsesWith(Val4);
  PV.invalidateValue(Val1);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that setting in incoming value directly updates the values
  Phi1->setIncomingValue(0, Val1);
  PV.invalidateValue(Phi1);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
}

TEST(PhiValuesTest, DependentPhi) {
  LLVMContext C;
  Module M("PhiValuesTest", C);

  Type *VoidTy = Type::getVoidTy(C);
  Type *I1Ty = Type::getInt1Ty(C);
  Type *I32Ty = Type::getInt32Ty(C);
  Type *PtrTy = PointerType::get(C, 0);

  // Create a function with a phi that has another phi as an incoming value
  Function *F = Function::Create(FunctionType::get(VoidTy, false),
                                 Function::ExternalLinkage, "f", M);

  BasicBlock *Entry = BasicBlock::Create(C, "entry", F);
  BasicBlock *If1 = BasicBlock::Create(C, "if1", F);
  BasicBlock *Else1 = BasicBlock::Create(C, "else1", F);
  BasicBlock *Then = BasicBlock::Create(C, "then", F);
  BasicBlock *If2 = BasicBlock::Create(C, "if2", F);
  BasicBlock *Else2 = BasicBlock::Create(C, "else2", F);
  BasicBlock *End = BasicBlock::Create(C, "then", F);
  CondBrInst::Create(PoisonValue::get(I1Ty), If1, Else1, Entry);
  UncondBrInst::Create(Then, If1);
  UncondBrInst::Create(Then, Else1);
  CondBrInst::Create(PoisonValue::get(I1Ty), If2, Else2, Then);
  UncondBrInst::Create(End, If2);
  UncondBrInst::Create(End, Else2);

  Value *Val1 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val1", Entry);
  Value *Val2 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val2", Entry);
  Value *Val3 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val3", Entry);
  Value *Val4 = new LoadInst(I32Ty, PoisonValue::get(PtrTy), "val4", Entry);

  PHINode *Phi1 = PHINode::Create(I32Ty, 2, "phi1", Then);
  Phi1->addIncoming(Val1, If1);
  Phi1->addIncoming(Val2, Else1);
  PHINode *Phi2 = PHINode::Create(I32Ty, 2, "phi2", Then);
  Phi2->addIncoming(Val2, If1);
  Phi2->addIncoming(Val3, Else1);
  PHINode *Phi3 = PHINode::Create(I32Ty, 2, "phi3", End);
  Phi3->addIncoming(Phi1, If2);
  Phi3->addIncoming(Val3, Else2);

  PhiValues PV(*F);
  PhiValues::ValueSet Vals;

  // Check that simple usage works
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));
  Vals = PV.getValuesForPhi(Phi3);
  EXPECT_EQ(Vals.size(), 3u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that changing an incoming value in the dependent phi changes the depending phi
  Phi1->setIncomingValue(0, Val4);
  PV.invalidateValue(Phi1);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));
  Vals = PV.getValuesForPhi(Phi3);
  EXPECT_EQ(Vals.size(), 3u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that replacing an incoming phi with a value works
  Phi3->setIncomingValue(0, Val1);
  PV.invalidateValue(Phi3);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));
  Vals = PV.getValuesForPhi(Phi3);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that adding a phi as an incoming value works
  Phi3->setIncomingValue(1, Phi2);
  PV.invalidateValue(Phi3);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi2);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));
  Vals = PV.getValuesForPhi(Phi3);
  EXPECT_EQ(Vals.size(), 3u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
  EXPECT_TRUE(Vals.count(Val3));

  // Check that replacing an incoming phi then deleting it works
  Phi3->setIncomingValue(1, Val2);
  PV.invalidateValue(Phi2);
  Phi2->eraseFromParent();
  PV.invalidateValue(Phi3);
  Vals = PV.getValuesForPhi(Phi1);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val4));
  EXPECT_TRUE(Vals.count(Val2));
  Vals = PV.getValuesForPhi(Phi3);
  EXPECT_EQ(Vals.size(), 2u);
  EXPECT_TRUE(Vals.count(Val1));
  EXPECT_TRUE(Vals.count(Val2));
}

TEST(PhiValuesTest, CyclicComponentsAndInvalidation) {
  LLVMContext C;
  Module M("PhiValuesTest", C);
  Type *I32Ty = Type::getInt32Ty(C);
  Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), false),
                                 Function::ExternalLinkage, "f", M);
  BasicBlock *Entry = BasicBlock::Create(C, "entry", F);
  BasicBlock *Header = BasicBlock::Create(C, "loop.header", F);
  BasicBlock *Latch = BasicBlock::Create(C, "loop.latch", F);
  UncondBrInst::Create(Header, Entry);
  UncondBrInst::Create(Latch, Header);
  UncondBrInst::Create(Header, Latch);

  SmallVector<PHINode *> Phis;
  SmallVector<Constant *> Values;
  for (unsigned I = 0; I != 5; ++I) {
    Phis.push_back(PHINode::Create(I32Ty, 2, "phi",
                                   Header->getTerminator()->getIterator()));
    Values.push_back(ConstantInt::get(I32Ty, I + 1));
    Phis.back()->addIncoming(Values.back(), Entry);
  }
  Phis[0]->addIncoming(Phis[1], Latch);
  Phis[1]->addIncoming(Phis[2], Latch);
  Phis[2]->addIncoming(Phis[0], Latch);
  Phis[3]->addIncoming(Phis[3], Latch);
  Phis[4]->addIncoming(Phis[3], Latch);

  PhiValues PV(*F);
  for (unsigned I = 0; I != 3; ++I) {
    const auto &Reachable = PV.getValuesForPhi(Phis[I]);
    EXPECT_EQ(Reachable.size(), 3u);
    for (unsigned J = 0; J != 3; ++J)
      EXPECT_TRUE(Reachable.count(Values[J]));
  }
  EXPECT_EQ(PV.getValuesForPhi(Phis[3]).size(), 1u);
  const auto &Dependent = PV.getValuesForPhi(Phis[4]);
  EXPECT_EQ(Dependent.size(), 2u);
  EXPECT_TRUE(Dependent.count(Values[3]));
  EXPECT_TRUE(Dependent.count(Values[4]));

  Phis[2]->setIncomingValue(0, Values[4]);
  PV.invalidateValue(Phis[2]);
  for (unsigned I = 0; I != 3; ++I) {
    const auto &Reachable = PV.getValuesForPhi(Phis[I]);
    EXPECT_EQ(Reachable.size(), 3u);
    EXPECT_TRUE(Reachable.count(Values[0]));
    EXPECT_TRUE(Reachable.count(Values[1]));
    EXPECT_TRUE(Reachable.count(Values[4]));
    EXPECT_FALSE(Reachable.count(Values[2]));
  }
  EXPECT_EQ(PV.getValuesForPhi(Phis[3]).size(), 1u);
  EXPECT_EQ(PV.getValuesForPhi(Phis[4]).size(), 2u);
}
