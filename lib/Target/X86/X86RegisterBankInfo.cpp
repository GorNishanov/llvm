//===- X86RegisterBankInfo.cpp -----------------------------------*- C++ -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// This file implements the targeting of the RegisterBankInfo class for X86.
/// \todo This should be generated by TableGen.
//===----------------------------------------------------------------------===//

#include "X86RegisterBankInfo.h"
#include "X86InstrInfo.h"
#include "llvm/CodeGen/GlobalISel/RegisterBank.h"
#include "llvm/CodeGen/GlobalISel/RegisterBankInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/Target/TargetRegisterInfo.h"

#define GET_TARGET_REGBANK_IMPL
#include "X86GenRegisterBank.inc"

// This file will be TableGen'ed at some point.
#include "X86GenRegisterBankInfo.def"

using namespace llvm;

#ifndef LLVM_BUILD_GLOBAL_ISEL
#error "You shouldn't build this"
#endif

X86RegisterBankInfo::X86RegisterBankInfo(const TargetRegisterInfo &TRI)
    : X86GenRegisterBankInfo() {

  // validate RegBank initialization.
  const RegisterBank &RBGPR = getRegBank(X86::GPRRegBankID);
  (void)RBGPR;
  assert(&X86::GPRRegBank == &RBGPR && "Incorrect RegBanks inizalization.");

  // The GPR register bank is fully defined by all the registers in
  // GR64 + its subclasses.
  assert(RBGPR.covers(*TRI.getRegClass(X86::GR64RegClassID)) &&
         "Subclass not added?");
  assert(RBGPR.getSize() == 64 && "GPRs should hold up to 64-bit");
}

const RegisterBank &X86RegisterBankInfo::getRegBankFromRegClass(
    const TargetRegisterClass &RC) const {

  if (X86::GR8RegClass.hasSubClassEq(&RC) ||
      X86::GR16RegClass.hasSubClassEq(&RC) ||
      X86::GR32RegClass.hasSubClassEq(&RC) ||
      X86::GR64RegClass.hasSubClassEq(&RC))
    return getRegBank(X86::GPRRegBankID);

  if (X86::FR32XRegClass.hasSubClassEq(&RC) ||
      X86::FR64XRegClass.hasSubClassEq(&RC) ||
      X86::VR128XRegClass.hasSubClassEq(&RC) ||
      X86::VR256XRegClass.hasSubClassEq(&RC) ||
      X86::VR512RegClass.hasSubClassEq(&RC))
    return getRegBank(X86::VECRRegBankID);

  llvm_unreachable("Unsupported register kind yet.");
}

RegisterBankInfo::InstructionMapping
X86RegisterBankInfo::getOperandsMapping(const MachineInstr &MI, bool isFP) {
  const MachineFunction &MF = *MI.getParent()->getParent();
  const MachineRegisterInfo &MRI = MF.getRegInfo();

  unsigned NumOperands = MI.getNumOperands();
  LLT Ty = MRI.getType(MI.getOperand(0).getReg());

  if (NumOperands != 3 ||
      (Ty != MRI.getType(MI.getOperand(1).getReg())) ||
      (Ty != MRI.getType(MI.getOperand(2).getReg())))
    llvm_unreachable("Unsupported operand maping yet.");

  ValueMappingIdx ValMapIdx = VMI_None;

  if (Ty.isScalar()) {
    if (!isFP) {
      switch (Ty.getSizeInBits()) {
      case 8:
        ValMapIdx = VMI_3OpsGpr8Idx;
        break;
      case 16:
        ValMapIdx = VMI_3OpsGpr16Idx;
        break;
      case 32:
        ValMapIdx = VMI_3OpsGpr32Idx;
        break;
      case 64:
        ValMapIdx = VMI_3OpsGpr64Idx;
        break;
      default:
        llvm_unreachable("Unsupported register size.");
      }
    } else {
      switch (Ty.getSizeInBits()) {
      case 32:
        ValMapIdx = VMI_3OpsFp32Idx;
        break;
      case 64:
        ValMapIdx = VMI_3OpsFp64Idx;
        break;
      default:
          llvm_unreachable("Unsupported register size.");
      }
    }
  } else {
    switch (Ty.getSizeInBits()) {
    case 128:
      ValMapIdx = VMI_3OpsVec128Idx;
      break;
    case 256:
      ValMapIdx = VMI_3OpsVec256Idx;
      break;
    case 512:
      ValMapIdx = VMI_3OpsVec512Idx;
      break;
    default:
      llvm_unreachable("Unsupported register size.");
    }
  }

  return InstructionMapping{DefaultMappingID, 1, &ValMappings[ValMapIdx],
                            NumOperands};
}

RegisterBankInfo::InstructionMapping
X86RegisterBankInfo::getInstrMapping(const MachineInstr &MI) const {
  auto Opc = MI.getOpcode();

  // Try the default logic for non-generic instructions that are either copies
  // or already have some operands assigned to banks.
  if (!isPreISelGenericOpcode(Opc)) {
    InstructionMapping Mapping = getInstrMappingImpl(MI);
    if (Mapping.isValid())
      return Mapping;
  }

  switch (Opc) {
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
    return getOperandsMapping(MI, false);
    break;
  case TargetOpcode::G_FADD:
  case TargetOpcode::G_FSUB:
  case TargetOpcode::G_FMUL:
  case TargetOpcode::G_FDIV:
    return getOperandsMapping(MI, true);
    break;
  default:
    return InstructionMapping{};
  }

  return InstructionMapping{};
}
