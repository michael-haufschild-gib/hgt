/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AdicTameMilnorResidue
import GaloisForLFunctions.HTGeometry.ABHN.CompletionResidueFieldEquiv
import GaloisForLFunctions.HTGeometry.FiniteMilnorKTwoCharacterReciprocity

/-!
# Norm-normalized tame phases at completed finite places of `F(t)`

Global projective-line reciprocity does not use an independently chosen character of every finite
residue field.  Its local term is the base-field character after the Bass--Tate norm.  This module
transports exactly that norm-normalized residue character through completion and composes it with
the concrete adic tame residue.

The resulting local phase is therefore normalized exactly as the finite terms in the proven global
Milnor reciprocity law.  This is a tame Milnor analogue of the normalization compatibility required
by Albert--Brauer--Hasse--Noether.  It does not identify Milnor `K₂` with a Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

/-- The global norm-normalized residue character transported to the completed residue field. -/
noncomputable def rationalFunctionFiniteAdicNormResidueStdAddChar
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    AddChar (MilnorKDeg (IsLocalRing.ResidueField
      ((Valued.v : Valuation
        ((polyPlace q.2.1).adicCompletion (RatFunc F)) ℤᵐ⁰).valuationSubring)) 1) ℂ :=
  (finiteMilnorKOneStdAddChar F).compAddMonoidHom
    ((milnorNormAt q 1).comp
      (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
        F (polyPlace q.2.1) 1).symm.toAddMonoidHom)

/-- Transporting a global-place residue and then evaluating the completed residue character gives
exactly the finite norm phase occurring in global reciprocity. -/
theorem rationalFunctionFiniteAdicNormResidueStdAddChar_apply_equiv
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg (polyResidueField q.2.1) 1) :
    rationalFunctionFiniteAdicNormResidueStdAddChar F q
        (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
          F (polyPlace q.2.1) 1 x) =
      finiteMilnorKOneStdAddChar F (milnorNormAt q 1 x) := by
  change finiteMilnorKOneStdAddChar F
    (milnorNormAt q 1
      ((rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
        F (polyPlace q.2.1) 1).symm
          (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
            F (polyPlace q.2.1) 1 x))) = _
  rw [AddEquiv.symm_apply_apply]

/-- Norm of the transported concrete adic tame residue.  This is the completed local additive
invariant whose circle character is globally normalized. -/
noncomputable def rationalFunctionFiniteAdicNormTameMilnorInvariant
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2 →+
      MilnorKDeg F 1 :=
  (milnorNormAt q 1).comp
    ((rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
      F (polyPlace q.2.1) 1).symm.toAddMonoidHom.comp
        (rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1)))

/-- The norm-normalized completed tame phase at `q`. -/
noncomputable def rationalFunctionFiniteAdicNormTameStdAddChar
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    AddChar (MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) ℂ :=
  (finiteMilnorKOneStdAddChar F).compAddMonoidHom
    (rationalFunctionFiniteAdicNormTameMilnorInvariant F q)

/-- Evaluation formula for the norm-normalized completed tame phase. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_apply
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q x =
      finiteMilnorKOneStdAddChar F
        (milnorNormAt q 1
          ((rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
            F (polyPlace q.2.1) 1).symm
              (rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1) x))) :=
  rfl

/-- Phase one means exactly that the norm of the transported tame residue vanishes. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_eq_one_iff_norm_tameResidue_eq_zero
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q x = 1 ↔
      milnorNormAt q 1
        ((rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv
          F (polyPlace q.2.1) 1).symm
            (rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1) x)) = 0 := by
  rw [rationalFunctionFiniteAdicNormTameStdAddChar_apply]
  exact finiteMilnorKOneStdAddChar_eq_one_iff_eq_zero F _

/-- Kernel form of the norm-normalized completed tame Hasse test. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_eq_one_iff_mem_ker
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q x = 1 ↔
      x ∈ (rationalFunctionFiniteAdicNormTameMilnorInvariant F q).ker := by
  rw [rationalFunctionFiniteAdicNormTameStdAddChar_eq_one_iff_norm_tameResidue_eq_zero]
  rfl

/-- Two completed local classes have the same globally normalized phase exactly when their
difference lies in the norm-tame kernel. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_eq_iff_sub_mem_ker
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x y : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q x =
        rationalFunctionFiniteAdicNormTameStdAddChar F q y ↔
      x - y ∈ (rationalFunctionFiniteAdicNormTameMilnorInvariant F q).ker := by
  constructor
  · intro hphase
    change rationalFunctionFiniteAdicNormTameMilnorInvariant F q (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((finiteMilnorKOneStdAddChar_injective F) hphase)
  · intro hkernel
    change finiteMilnorKOneStdAddChar F
        (rationalFunctionFiniteAdicNormTameMilnorInvariant F q x) =
      finiteMilnorKOneStdAddChar F
        (rationalFunctionFiniteAdicNormTameMilnorInvariant F q y)
    apply congrArg (finiteMilnorKOneStdAddChar F)
    apply sub_eq_zero.mp
    rw [← (rationalFunctionFiniteAdicNormTameMilnorInvariant F q).map_sub]
    exact hkernel

end

end GaloisForLFunctions.HTGeometry.ABHN
