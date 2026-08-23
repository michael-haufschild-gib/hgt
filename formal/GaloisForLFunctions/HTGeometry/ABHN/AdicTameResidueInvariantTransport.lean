/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AdicTameMilnorResidue
import GaloisForLFunctions.HTGeometry.ABHN.CompletionResidueFieldEquiv
import GaloisForLFunctions.HTGeometry.FiniteMilnorKOneRatModIntInvariant

/-!
# Globally transported tame invariants at concrete adic completions

At a finite global place, completion identifies the global valuation residue field with the residue
field of the actual extended adic valuation.  Transporting the faithful finite-field `K₁ᴹ`
invariant across this equivalence and composing with the concrete tame residue gives local circle
and `ℚ/ℤ` invariants at number-field and rational-function completions.

Unlike the intrinsic normalized-local-field character, these constructions retain the explicit
global residue-field coordinate.  They are therefore suitable inputs for local/global comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

/-- Tame circle phase at a finite number-field completion, transported from the global residue
field. -/
noncomputable def numberFieldFiniteAdicTameResidueStdAddChar
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    AddChar (MilnorKDeg (v.maximalIdeal.adicCompletion K) 2) ℂ :=
  (finiteMilnorKOneStdAddCharTransport
    (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)).compAddMonoidHom
      (numberFieldFiniteAdicTameMilnorResidue K v)

/-- The transported number-field tame phase is one exactly on the concrete tame kernel. -/
theorem numberFieldFiniteAdicTameResidueStdAddChar_eq_one_iff_mem_ker
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (v.maximalIdeal.adicCompletion K) 2) :
    numberFieldFiniteAdicTameResidueStdAddChar K v x = 1 ↔
      x ∈ (numberFieldFiniteAdicTameMilnorResidue K v).ker := by
  change finiteMilnorKOneStdAddCharTransport
      (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)
        (numberFieldFiniteAdicTameMilnorResidue K v x) = 1 ↔ _
  rw [finiteMilnorKOneStdAddCharTransport_eq_one_iff_eq_zero]
  rfl

/-- Equality of transported number-field tame phases is equality modulo the tame kernel. -/
theorem numberFieldFiniteAdicTameResidueStdAddChar_eq_iff_sub_mem_ker
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x y : MilnorKDeg (v.maximalIdeal.adicCompletion K) 2) :
    numberFieldFiniteAdicTameResidueStdAddChar K v x =
        numberFieldFiniteAdicTameResidueStdAddChar K v y ↔
      x - y ∈ (numberFieldFiniteAdicTameMilnorResidue K v).ker := by
  constructor
  · intro hphase
    change numberFieldFiniteAdicTameMilnorResidue K v (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr
      ((finiteMilnorKOneStdAddCharTransport_injective
        (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)) hphase)
  · intro hkernel
    change finiteMilnorKOneStdAddCharTransport
        (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)
          (numberFieldFiniteAdicTameMilnorResidue K v x) =
      finiteMilnorKOneStdAddCharTransport
        (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)
          (numberFieldFiniteAdicTameMilnorResidue K v y)
    apply congrArg (finiteMilnorKOneStdAddCharTransport
      (numberFieldAdicCompletion_valuationResidueFieldEquiv K v))
    apply sub_eq_zero.mp
    rw [← (numberFieldFiniteAdicTameMilnorResidue K v).map_sub]
    exact hkernel

/-- `ℚ/ℤ`-valued tame invariant at a finite number-field completion, transported from the global
residue field. -/
noncomputable def numberFieldFiniteAdicTameResidueRatModIntInvariant
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    MilnorKDeg (v.maximalIdeal.adicCompletion K) 2 →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariantTransport
    (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)).comp
      (numberFieldFiniteAdicTameMilnorResidue K v)

/-- The transported number-field `ℚ/ℤ` invariant vanishes exactly on the tame kernel. -/
theorem numberFieldFiniteAdicTameResidueRatModIntInvariant_eq_zero_iff_mem_ker
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (x : MilnorKDeg (v.maximalIdeal.adicCompletion K) 2) :
    numberFieldFiniteAdicTameResidueRatModIntInvariant K v x = 0 ↔
      x ∈ (numberFieldFiniteAdicTameMilnorResidue K v).ker := by
  change finiteMilnorKOneStdRatModIntInvariantTransport
      (numberFieldAdicCompletion_valuationResidueFieldEquiv K v)
        (numberFieldFiniteAdicTameMilnorResidue K v x) = 0 ↔ _
  rw [finiteMilnorKOneStdRatModIntInvariantTransport_eq_zero_iff]
  rfl

/-- The number-field tame circle phase is the standard character of its additive invariant. -/
theorem numberFieldFiniteAdicTameResidueStdAddChar_eq_ratModInt_comp
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :
    numberFieldFiniteAdicTameResidueStdAddChar K v =
      ratModIntStdAddChar.compAddMonoidHom
        (numberFieldFiniteAdicTameResidueRatModIntInvariant K v) :=
  rfl

/-- Tame circle phase at a finite `F(t)` completion, transported from the global residue field. -/
noncomputable def rationalFunctionFiniteAdicTameResidueStdAddChar
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    AddChar (MilnorKDeg (v.adicCompletion (RatFunc F)) 2) ℂ :=
  (finiteMilnorKOneStdAddCharTransport
    (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)).compAddMonoidHom
      (rationalFunctionFiniteAdicTameMilnorResidue F v)

/-- The transported finite `F(t)`-adic tame phase is one exactly on the tame kernel. -/
theorem rationalFunctionFiniteAdicTameResidueStdAddChar_eq_one_iff_mem_ker
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (v.adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicTameResidueStdAddChar F v x = 1 ↔
      x ∈ (rationalFunctionFiniteAdicTameMilnorResidue F v).ker := by
  change finiteMilnorKOneStdAddCharTransport
      (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)
        (rationalFunctionFiniteAdicTameMilnorResidue F v x) = 1 ↔ _
  rw [finiteMilnorKOneStdAddCharTransport_eq_one_iff_eq_zero]
  rfl

/-- Equality of transported finite `F(t)`-adic phases is equality modulo the tame kernel. -/
theorem rationalFunctionFiniteAdicTameResidueStdAddChar_eq_iff_sub_mem_ker
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x y : MilnorKDeg (v.adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicTameResidueStdAddChar F v x =
        rationalFunctionFiniteAdicTameResidueStdAddChar F v y ↔
      x - y ∈ (rationalFunctionFiniteAdicTameMilnorResidue F v).ker := by
  constructor
  · intro hphase
    change rationalFunctionFiniteAdicTameMilnorResidue F v (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr
      ((finiteMilnorKOneStdAddCharTransport_injective
        (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)) hphase)
  · intro hkernel
    change finiteMilnorKOneStdAddCharTransport
        (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)
          (rationalFunctionFiniteAdicTameMilnorResidue F v x) =
      finiteMilnorKOneStdAddCharTransport
        (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)
          (rationalFunctionFiniteAdicTameMilnorResidue F v y)
    apply congrArg (finiteMilnorKOneStdAddCharTransport
      (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v))
    apply sub_eq_zero.mp
    rw [← (rationalFunctionFiniteAdicTameMilnorResidue F v).map_sub]
    exact hkernel

/-- `ℚ/ℤ`-valued tame invariant at a finite `F(t)` completion, transported from the global residue
field. -/
noncomputable def rationalFunctionFiniteAdicTameResidueRatModIntInvariant
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    MilnorKDeg (v.adicCompletion (RatFunc F)) 2 →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariantTransport
    (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)).comp
      (rationalFunctionFiniteAdicTameMilnorResidue F v)

/-- The transported finite `F(t)`-adic `ℚ/ℤ` invariant vanishes exactly on the tame kernel. -/
theorem rationalFunctionFiniteAdicTameResidueRatModIntInvariant_eq_zero_iff_mem_ker
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (x : MilnorKDeg (v.adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicTameResidueRatModIntInvariant F v x = 0 ↔
      x ∈ (rationalFunctionFiniteAdicTameMilnorResidue F v).ker := by
  change finiteMilnorKOneStdRatModIntInvariantTransport
      (rationalFunctionAdicCompletion_valuationResidueFieldEquiv F v)
        (rationalFunctionFiniteAdicTameMilnorResidue F v x) = 0 ↔ _
  rw [finiteMilnorKOneStdRatModIntInvariantTransport_eq_zero_iff]
  rfl

/-- The finite `F(t)`-adic tame circle phase is the standard character of its additive invariant. -/
theorem rationalFunctionFiniteAdicTameResidueStdAddChar_eq_ratModInt_comp
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    rationalFunctionFiniteAdicTameResidueStdAddChar F v =
      ratModIntStdAddChar.compAddMonoidHom
        (rationalFunctionFiniteAdicTameResidueRatModIntInvariant F v) :=
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
