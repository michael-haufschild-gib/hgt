import GaloisForLFunctions.RHTower.SelbergScatteringPolynomialSeparation
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.ThetaCuspHawkingOpticalCuspScatteringIncidence

/-!
# Actual Xi scattering poles obstruct fixed polynomial spectral transport

The unconditional Hardy theorem supplies arbitrarily high critical-line zeros.
Their multiplicity-marked Xi copies are genuine poles of the normalized modular
scattering coefficient. Every nonconstant complex polynomial of the native
Casimir sends such poles beyond any fixed distance from the entire real axis.
Reality at all Xi copies, or just all critical-line zeros, therefore characterizes
exactly the real constant polynomials.
-/

open Complex Polynomial Set

namespace RHTower.SelbergScatteringPolynomialReality

noncomputable section


/-- The parabola is exactly the Casimir of the original modular resonance parameter. -/
theorem criticalCasimir_eq_resonance (z : ℂ) :
    criticalCasimir z = thetaCuspHawkingOpticalCuspResonanceParameter z *
      (1 - thetaCuspHawkingOpticalCuspResonanceParameter z) := by
  unfold criticalCasimir thetaCuspHawkingOpticalCuspResonanceParameter
  ring_nf
  rw [I_sq]
  ring

/-- The same native Casimir expressed at the actual uncentered zeta argument. -/
theorem criticalCasimir_eq_half_linePt (t : ℝ) :
    criticalCasimir t = (linePt t / 2) * (1 - linePt t / 2) := by
  unfold criticalCasimir linePt
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Every genuine critical-line zeta zero supplies a multiplicity-marked Xi copy. -/
theorem exists_copy_of_line_zero {t : ℝ} (ht : riemannZeta (linePt t) = 0) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = (t : ℂ) := by
  have hxi : xi (linePt t) = 0 := by
    rw [xi_line_eq_zero_iff_hardyZ]
    have hnorm := norm_riemannZeta_line_eq_abs_hardyZ t
    rw [ht, norm_zero] at hnorm
    exact abs_eq_zero.mp hnorm.symm
  apply (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp
  simpa [XiC, linePt] using hxi

/-- Reality on every actual critical-line zeta zero allows exactly real constants. -/
theorem real_on_critical_zeros_iff (P : Polynomial ℂ) :
    (∀ t : ℝ, riemannZeta (linePt t) = 0 →
      (P.eval (criticalCasimir t)).im = 0) ↔ ∃ c : ℝ, P = C (c : ℂ) := by
  constructor
  · intro hreal
    apply constant_of_infinite_real_locus P
    apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    obtain ⟨T0, _hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
    obtain ⟨t, ht, hz⟩ := hHardy (max T0 (B + 1)) (le_max_left _ _)
    have hle := hB (hreal t hz)
    have hgt : B + 1 ≤ t := (le_max_right _ _).trans ht.1
    linarith
  · rintro ⟨c, rfl⟩ t _ht
    simp

/-- Every fixed nonconstant polynomial is nonreal on all sufficiently high native critical Casimirs. -/
theorem eventually_nonreal (P : Polynomial ℂ) (hP : 0 < P.natDegree) :
    ∃ B : ℝ, ∀ t : ℝ, B < t → (P.eval (criticalCasimir t)).im ≠ 0 := by
  obtain ⟨B, hB⟩ := (finite_real_locus P hP).bddAbove
  refine ⟨B, fun t ht hz => ?_⟩
  exact not_le_of_gt ht (hB hz)

/-- Above every height, an actual critical-line scattering pole defeats the fixed polynomial transport. -/
theorem exists_critical_pole_nonreal_above (P : Polynomial ℂ) (hP : 0 < P.natDegree)
    (H : ℝ) :
    ∃ t : ℝ, H < t ∧ riemannZeta (linePt t) = 0 ∧
      meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (t : ℂ) < 0 ∧
      (P.eval (criticalCasimir t)).im ≠ 0 := by
  obtain ⟨B, hB⟩ := eventually_nonreal P hP
  obtain ⟨T0, _hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨t, ht, hz⟩ := hHardy (max T0 (max B H + 1)) (le_max_left _ _)
  have hlarge : max B H + 1 ≤ t := (le_max_right _ _).trans ht.1
  have htB : B < t := by linarith [le_max_left B H]
  have htH : H < t := by linarith [le_max_right B H]
  obtain ⟨q, hq⟩ := exists_copy_of_line_zero hz
  refine ⟨t, htH, hz, ?_, hB t htB⟩
  simpa only [hq] using thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q

/-- Genuine critical-line scattering poles escape every fixed distance from the entire real axis after any nonconstant polynomial transport. -/
theorem exists_critical_pole_far_from_real_above (P : Polynomial ℂ)
    (hP : 0 < P.natDegree) (H M : ℝ) :
    ∃ t : ℝ, H < t ∧ riemannZeta (linePt t) = 0 ∧
      meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (t : ℂ) < 0 ∧
      ∀ r : ℝ, M < ‖P.eval (criticalCasimir t) - (r : ℂ)‖ := by
  obtain ⟨B, hB⟩ := eventually_far_from_real P hP M
  obtain ⟨T0, _hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨t, ht, hz⟩ := hHardy (max T0 (max B H + 1)) (le_max_left _ _)
  have hlarge : max B H + 1 ≤ t := (le_max_right _ _).trans ht.1
  have htB : B ≤ t := by linarith [le_max_left B H]
  have htH : H < t := by linarith [le_max_right B H]
  obtain ⟨q, hq⟩ := exists_copy_of_line_zero hz
  refine ⟨t, htH, hz, ?_, hB t htB⟩
  simpa only [hq] using thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q

/-- Full actual Xi-divisor classification of fixed polynomial transports into a real spectrum. -/
theorem real_on_all_xi_copies_iff (P : Polynomial ℂ) :
    (∀ q : XiZeroCopy, (P.eval (criticalCasimir (xiSpectralPoint q))).im = 0) ↔
      ∃ c : ℝ, P = C (c : ℂ) := by
  constructor
  · intro h
    apply (real_on_critical_zeros_iff P).mp
    intro t ht
    obtain ⟨q, hq⟩ := exists_copy_of_line_zero ht
    simpa only [hq] using h q
  · rintro ⟨c, rfl⟩ q
    simp

end
end RHTower.SelbergScatteringPolynomialReality
