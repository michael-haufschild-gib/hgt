import GaloisForLFunctions.RHTower.XiHedenmalmSymmetricMultiplicity
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Canonical local Jordan matrices for the Hedenmalm divided chain

At a centered Xi zero, the quotient by the common source turns the canonical divided chain into a
finite Jordan block whose size is the analytic multiplicity. This file defines that block and proves
that the complete family of local blocks is Hermitian exactly when RH holds and every Xi zero is
simple. The theorem is assumption-free and exposes the terminal multiplicity-exact normal form.
-/

open Complex

noncomputable section

namespace RHTower

/-- The local root-module matrix: centered spectral point on the diagonal and the canonical
divided-chain shift on the first superdiagonal. -/
def xiLocalJordanMatrix (rho : XiDivisorSupport) :
    Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho)) ℂ :=
  fun i j =>
    if i = j then xiSpectralPointSupport rho
    else if i.val + 1 = j.val then 1 else 0

/-- One local divided-chain block is Hermitian exactly when its spectral point is real and its
analytic multiplicity is one. -/
theorem xiLocalJordanMatrix_isHermitian_iff
    (rho : XiDivisorSupport) :
    (xiLocalJordanMatrix rho).IsHermitian ↔
      (starRingEnd ℂ) (xiSpectralPointSupport rho) = xiSpectralPointSupport rho ∧
        xiSupportMultiplicity rho = 1 := by
  constructor
  · intro hherm
    have hmpos := xiSupportMultiplicity_pos rho
    let i0 : Fin (xiSupportMultiplicity rho) := ⟨0, hmpos⟩
    have hdiag := hherm.apply i0 i0
    have hreal : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
        xiSpectralPointSupport rho := by
      simpa [xiLocalJordanMatrix] using hdiag
    refine ⟨hreal, ?_⟩
    by_contra hne
    have hm2 : 2 ≤ xiSupportMultiplicity rho := by omega
    let i1 : Fin (xiSupportMultiplicity rho) := ⟨1, hm2⟩
    have hoff := hherm.apply i0 i1
    have hi01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    have hi10 : i1 ≠ i0 := Ne.symm hi01
    simp [xiLocalJordanMatrix, i0, i1, hi01, hi10] at hoff
  · rintro ⟨hreal, hm⟩
    change (xiLocalJordanMatrix rho).conjTranspose = xiLocalJordanMatrix rho
    ext i j
    haveI : Subsingleton (Fin (xiSupportMultiplicity rho)) := by
      rw [hm]
      infer_instance
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [xiLocalJordanMatrix, hreal]

/-- Assumption-free global normal form: every canonical local Hedenmalm root block is Hermitian
exactly when RH and simplicity both hold. -/
theorem all_xiLocalJordanMatrix_isHermitian_iff_rh_and_simple :
    (∀ rho : XiDivisorSupport, (xiLocalJordanMatrix rho).IsHermitian) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  constructor
  · intro hall
    have hlocal : ∀ rho : XiDivisorSupport,
        (starRingEnd ℂ) (xiSpectralPointSupport rho) = xiSpectralPointSupport rho ∧
          xiSupportMultiplicity rho = 1 := fun rho =>
      (xiLocalJordanMatrix_isHermitian_iff rho).mp (hall rho)
    constructor
    · apply riemannHypothesis_of_xiSpectralPoint_real
      intro q
      refine ⟨(xiSpectralPointSupport q.1).re, ?_⟩
      have hreal := RCLike.conj_eq_iff_re.mp (hlocal q.1).1
      simpa only [xiSpectralPoint_eq_support] using hreal.symm
    · intro alpha halpha
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
      have hm := (hlocal q.1).2
      have hvalue : xiThetaEigenFourier (xiSpectralPointSupport q.1)
          (xiSpectralPointSupport q.1) ≠ 0 :=
        (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one q.1).mpr hm
      have hderiv : deriv XiC (xiSpectralPointSupport q.1) ≠ 0 := by
        intro hzero
        apply hvalue
        rw [xiThetaEigenFourier_self, hzero, mul_zero]
      have hsupp : xiSpectralPointSupport q.1 = alpha := by
        simpa only [xiSpectralPoint_eq_support] using hq
      simpa only [hsupp] using hderiv
  · rintro ⟨hRH, hsimple⟩ rho
    rw [xiLocalJordanMatrix_isHermitian_iff]
    constructor
    · have hmpos := xiSupportMultiplicity_pos rho
      let q : XiZeroCopy := ⟨rho, ⟨0, hmpos⟩⟩
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      have hsupp : xiSpectralPointSupport rho = (t : ℂ) := by
        simpa only [q, xiSpectralPoint_eq_support] using ht
      rw [hsupp]
      exact Complex.conj_ofReal t
    · simpa only [xiSupportMultiplicity] using
        xiDivisorMultiplicity_eq_one_of_simple hsimple rho

end RHTower
