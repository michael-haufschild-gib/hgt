/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AdicTameMilnorResidue
import GaloisForLFunctions.HTGeometry.ABHN.CompletionResidueFieldEquiv

/-!
# Completed local tame quotients are global-place residue groups

The concrete tame residue at an adic completion is surjective.  Its first-isomorphism quotient is
therefore the completed residue `K₁ᴹ`; completion residue-field transport then identifies this with
the residue `K₁ᴹ` of the original global place.  These equivalences replace choice-dependent local
sections by canonical quotient coordinates.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

/-- At a finite number-field place, completed local `K₂ᴹ` modulo the concrete tame kernel is the
global-place residue `K₁ᴹ`. -/
noncomputable def numberFieldFiniteAdicTameQuotientEquivGlobalResidue
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    MilnorKDeg (v.maximalIdeal.adicCompletion K) 2 ⧸
        (numberFieldFiniteAdicTameMilnorResidue K v).ker ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((v.maximalIdeal.valuation K).valuationSubring)) 1 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (numberFieldFiniteAdicTameMilnorResidue K v)
    (numberFieldFiniteAdicTameMilnorResidue_surjective K v)).trans
      (numberFieldAdicCompletion_valuationResidueMilnorKDegAddEquiv K v 1).symm

/-- The number-field quotient equivalence sends a local class to its transported tame residue. -/
theorem numberFieldFiniteAdicTameQuotientEquivGlobalResidue_mk
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (v.maximalIdeal.adicCompletion K) 2) :
    numberFieldFiniteAdicTameQuotientEquivGlobalResidue K v (QuotientAddGroup.mk x) =
      (numberFieldAdicCompletion_valuationResidueMilnorKDegAddEquiv K v 1).symm
        (numberFieldFiniteAdicTameMilnorResidue K v x) := by
  rfl

/-- At a finite place of `F(t)`, completed local `K₂ᴹ` modulo the concrete tame kernel is the
global-place residue `K₁ᴹ`. -/
noncomputable def rationalFunctionFiniteAdicTameQuotientEquivGlobalResidue
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    MilnorKDeg (v.adicCompletion (RatFunc F)) 2 ⧸
        (rationalFunctionFiniteAdicTameMilnorResidue F v).ker ≃+
      MilnorKDeg (IsLocalRing.ResidueField
        ((v.valuation (RatFunc F)).valuationSubring)) 1 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (rationalFunctionFiniteAdicTameMilnorResidue F v)
    (rationalFunctionFiniteAdicTameMilnorResidue_surjective F v)).trans
      (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv F v 1).symm

/-- The `F(t)` quotient equivalence sends a local class to its transported tame residue. -/
theorem rationalFunctionFiniteAdicTameQuotientEquivGlobalResidue_mk
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (v.adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicTameQuotientEquivGlobalResidue F v
        (QuotientAddGroup.mk x) =
      (rationalFunctionAdicCompletion_valuationResidueMilnorKDegAddEquiv F v 1).symm
        (rationalFunctionFiniteAdicTameMilnorResidue F v x) := by
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
