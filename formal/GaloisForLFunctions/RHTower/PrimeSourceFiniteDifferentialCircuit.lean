import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.PrimeDirichletConstraintCarrier
import GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank

/-!
# A finite differential circuit cannot manufacture a signed-prime source

Every signed-prime carrier is already proved differentially independent over the complex
constants.  Applying the general finite-circuit source theorem shows that any finite
symbolic, learned, genomic, or physical formula that exactly reconstructs this arithmetic source
must contain a hypertranscendental atom of its own.

This is a source audit for RH architectures.  A finite circuit may reorganize the prime source,
but it cannot be credited with producing the source unless one of its input atoms already carries
infinite differential complexity.  The positive residue identifies that atom existentially; it
does not merely reject a proposed architecture.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Every oriented signed-prime source is hypertranscendental over the complex constants. -/
theorem signedPrimeSource_hypertranscendentalOver
    (epsilon : Nat.Primes → Bool) :
    HypertranscendentalOver ℂ
      (signedPrimeNaturalShiftPalette epsilon 0) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette := signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon
  have hsource := hpalette.comp (fun _ : Unit => 0) (by
    intro u v h
    exact Subsingleton.elim u v)
  simpa only [Function.comp_apply] using hsource

/-- **Oriented arithmetic source extraction.**  Every finite differential circuit reconstructing
any signed-prime source contains a hypertranscendental atom over `ℂ`. -/
theorem signedPrimeSource_finiteDifferentialCircuit_contains_HTAtom
    (epsilon : Nat.Primes → Bool)
    (Atom : arithmeticFunctionRationalCoordinateField → Prop)
    (hcircuit : FiniteDifferentialCircuit Atom
      (signedPrimeNaturalShiftPalette epsilon 0)) :
    ∃ a : arithmeticFunctionRationalCoordinateField,
      Atom a ∧ HypertranscendentalOver ℂ a := by
  letI : Differential ℂ := ⟨0⟩
  letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
    ⟨fun c => by
      rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
      change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
      rw [map_zero]⟩
  letI : CharZero arithmeticFunctionRationalCoordinateField :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
  exact exists_hypertranscendental_atom_of_finiteDifferentialCircuit
    (signedPrimeSource_hypertranscendentalOver epsilon) hcircuit

/-- **Oriented linear-observation stability.**  Every nonzero constant-coefficient differential
filter of a signed-prime source remains hypertranscendental.  The filter changes which jet
combination is observed but cannot hide the source's infinite differential rank. -/
theorem signedPrimeSource_differentialOperator_hypertranscendentalOver
    (epsilon : Nat.Primes → Bool)
    {P : Polynomial ℂ} (hP : P ≠ 0) :
    HypertranscendentalOver ℂ
      (differentialOperatorApply P (signedPrimeNaturalShiftPalette epsilon 0)) := by
  let L : Unit → Unit → Polynomial ℂ := fun _ _ => P
  let source : Unit → arithmeticFunctionRationalCoordinateField :=
    fun _ => signedPrimeNaturalShiftPalette epsilon 0
  have hsource : DifferentialIndependent ℂ source := by
    simpa only [source] using
      (hypertranscendentalOver_iff_differentialIndependent_singleton ℂ
        (signedPrimeNaturalShiftPalette epsilon 0)).mp
          (signedPrimeSource_hypertranscendentalOver epsilon)
  have hL : LinearIndependent (Polynomial ℂ) L := by
    apply linearIndependent_unique_iff.mpr
    intro hzero
    apply hP
    exact congrFun hzero Unit.unit
  have hout := differentialIndependent_differentialOperatorRows
    (C := ℂ) (K := arithmeticFunctionRationalCoordinateField)
    (fun c => arithmeticFunctionRationalCoordinateField_deriv_complexConstant c)
    L hL source hsource
  apply (hypertranscendentalOver_iff_differentialIndependent_singleton
    ℂ (differentialOperatorApply P
      (signedPrimeNaturalShiftPalette epsilon 0))).mpr
  have hrow : differentialOperatorRowApply L source =
      fun _ : Unit => differentialOperatorApply P
        (signedPrimeNaturalShiftPalette epsilon 0) := by
    funext i
    cases i
    simp [differentialOperatorRowApply, L, source]
  rw [hrow] at hout
  exact hout

/-- The canonical all-positive source is the distinguished unsigned specialization. -/
theorem allPositiveSignedPrimeSource_finiteDifferentialCircuit_contains_HTAtom
    (Atom : arithmeticFunctionRationalCoordinateField → Prop)
    (hcircuit : FiniteDifferentialCircuit Atom
      (signedPrimeNaturalShiftPalette (fun _ : Nat.Primes => false) 0)) :
    ∃ a : arithmeticFunctionRationalCoordinateField,
      Atom a ∧ HypertranscendentalOver ℂ a :=
  signedPrimeSource_finiteDifferentialCircuit_contains_HTAtom
    (fun _ : Nat.Primes => false) Atom hcircuit

end

end RHTower
