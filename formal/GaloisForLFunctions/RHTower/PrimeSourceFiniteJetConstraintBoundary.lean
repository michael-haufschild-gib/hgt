import GaloisForLFunctions.HTGeometry.FiniteJetConstraintSourceBoundary
import GaloisForLFunctions.HTGeometry.PrimeDirichletConstraintCarrier
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicObservationFilter

/-!
# Finite jet constraints on signed-prime clock observations

Every oriented signed-prime source in the corpus is hypertranscendental over `ℂ`.  Combining
that fact with the general finite-jet constraint boundary gives two exact alternatives for a
finite physical, genomic, or learned observation law:

* a derivation-closed coefficient reservoir must have transcendence degree at least `aleph0`; or
* if the reservoir is generated differentially by one latent input, that input is itself
  hypertranscendental.

These are source-complexity theorems, not an RH proof.  They rule out finite differential models
of the signed-prime observation while positively locating where infinite differential complexity
must enter.  They do not select or orient a sign sequence.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Any derivation-closed coefficient field supporting a nonzero finite jet constraint on an
oriented signed-prime source has infinite transcendence degree over `ℂ`. -/
theorem signedPrimeSource_finiteJetConstraint_forces_infinite_trdeg
    (epsilon : Nat.Primes → Bool)
    (S : IntermediateField ℂ arithmeticFunctionRationalCoordinateField)
    (hSclosed : DerivationClosed S)
    {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) S}
    (hQ : Q ≠ 0)
    (hann : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (signedPrimeNaturalShiftPalette epsilon 0)) Q = 0) :
    Cardinal.aleph0 ≤ Algebra.trdeg ℂ S := by
  letI : Differential ℂ := ⟨0⟩
  letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
    ⟨fun c => by
      rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
      change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
      rw [map_zero]⟩
  letI : CharZero arithmeticFunctionRationalCoordinateField :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
  apply infinite_trdeg_of_hypertranscendentalOver_finiteJetConstraint
    _ S hSclosed hQ hann
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette := signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon
  have hsource := hpalette.comp (fun _ : Unit => 0) (by
    intro u v huv
    exact Subsingleton.elim u v)
  simpa only [Function.comp_apply] using! hsource

/-- If the coefficients of a finite jet constraint on an oriented signed-prime source come from
the differential field of one input `h`, then `h` is hypertranscendental over `ℂ`. -/
theorem signedPrimeSource_finiteJetConstraint_forces_HT_input
    (epsilon : Nat.Primes → Bool)
    {h : arithmeticFunctionRationalCoordinateField}
    {n : ℕ}
    {Q : MvPolynomial (Fin (n + 1))
      (differentialAdjoin ℂ
        ({h} : Set arithmeticFunctionRationalCoordinateField))}
    (hQ : Q ≠ 0)
    (hann : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (signedPrimeNaturalShiftPalette epsilon 0)) Q = 0) :
    HypertranscendentalOver ℂ h := by
  letI : Differential ℂ := ⟨0⟩
  letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
    ⟨fun c => by
      rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
      change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
      rw [map_zero]⟩
  letI : CharZero arithmeticFunctionRationalCoordinateField :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
  apply hypertranscendentalOver_input_of_finiteJetConstraint _ hQ hann
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette := signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon
  have hsource := hpalette.comp (fun _ : Unit => 0) (by
    intro u v huv
    exact Subsingleton.elim u v)
  simpa only [Function.comp_apply] using! hsource

/-- A nonzero finite variable-coefficient differential filter cannot reduce an oriented
signed-prime source to a differentially algebraic observation when all coefficients live in a
derivation-closed reservoir of finite transcendence degree. -/
theorem signedPrimeSource_finsuppLinearDifferentialObservation_hypertranscendentalOver
    (epsilon : Nat.Primes → Bool)
    (S : IntermediateField ℂ arithmeticFunctionRationalCoordinateField)
    (hSclosed : DerivationClosed S)
    (hSfinite : Algebra.trdeg ℂ S < Cardinal.aleph0)
    (c : (Unit × ℕ) →₀ S) (hc : c ≠ 0) :
    HypertranscendentalOver ℂ
      (finsuppLinearDifferentialObservation S c
        (signedPrimeNaturalShiftPalette epsilon 0)) := by
  letI : Differential ℂ := ⟨0⟩
  letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
    ⟨fun a => by
      rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
      change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
      rw [map_zero]⟩
  letI : CharZero arithmeticFunctionRationalCoordinateField :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
  apply hypertranscendentalOver_finsuppLinearDifferentialObservation_of_finiteTrdeg
    S hSclosed hSfinite c hc
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette := signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon
  have hsource := hpalette.comp (fun _ : Unit => 0) (by
    intro u v huv
    exact Subsingleton.elim u v)
  simpa only [Function.comp_apply] using! hsource

end

end RHTower
