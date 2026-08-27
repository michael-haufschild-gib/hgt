import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekCompleteEvaporationAggregateNoGo

/-!
# Parikh--Wilczek scalar-history classification

This module closes every summable scalar mass-shell dressing of the PW recoil reporter.  Both
oriented phase and faithful quadratic reflection-orbit energy factor through one number: total
history weight.  Zero-total histories are identically blind.  Every nonzero-total history preserves
the exact critical-wall zero locus, so universal flatness remains exactly RH.

Consequently shell-dependent scalar greybody factors, clocks, and amplitudes cannot produce PW-B
balance.  The remaining dynamics must be genuinely channel-relative or matrix-valued, mix Borel
grades, or carry nonlocal/singular memory.

`[NEW] [CLASSIFICATION] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Arbitrary summable scalar shell dressing of oriented PW recoil phase. -/
def schwarzschildParikhWilczekScalarHistoryPhase
    (w : ℕ → ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, w n *
    (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im

/-- Arbitrary summable scalar dressing retains only total history weight. -/
theorem schwarzschildParikhWilczekScalarHistoryPhase_eq
    {w : ℕ → ℝ} (hw : Summable w) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekScalarHistoryPhase w s k =
      (∑' n : ℕ, w n) *
        (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im := by
  rw [schwarzschildParikhWilczekScalarHistoryPhase,
    Summable.tsum_mul_right _ hw]

/-- Complete scalar-history phase classification: zero total is blind; otherwise wall is exact. -/
theorem schwarzschildParikhWilczekScalarHistoryPhase_eq_zero_iff
    {w : ℕ → ℝ} (hw : Summable w) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekScalarHistoryPhase w s k = 0 ↔
      (∑' n : ℕ, w n) = 0 ∨ s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekScalarHistoryPhase_eq hw, mul_eq_zero,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
      s k hs0 hs1 hsim]

/-- Scalar shell dressing of faithful quadratic reflection-orbit energy. -/
def schwarzschildParikhWilczekScalarHistoryQuadraticEnergy
    (w : ℕ → ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, w n * schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k

theorem schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq
    {w : ℕ → ℝ} (hw : Summable w) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekScalarHistoryQuadraticEnergy w s k =
      (∑' n : ℕ, w n) *
        schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k := by
  rw [schwarzschildParikhWilczekScalarHistoryQuadraticEnergy,
    Summable.tsum_mul_right _ hw]

/-- Complete scalar-history energy classification. -/
theorem schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff
    {w : ℕ → ℝ} (hw : Summable w) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekScalarHistoryQuadraticEnergy w s k = 0 ↔
      (∑' n : ℕ, w n) = 0 ∨ s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq hw, mul_eq_zero,
    schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq_zero_iff
      s k hs0 hs1 hsim]

/-- Any nonzero-total summable scalar history preserves exact critical-wall zero locus. -/
theorem schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff_of_total_ne_zero
    {w : ℕ → ℝ} (hw : Summable w) (htotal : (∑' n : ℕ, w n) ≠ 0)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekScalarHistoryQuadraticEnergy w s k = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff
    hw s k hs0 hs1 hsim]
  simp [htotal]

/-- For every nonzero-total scalar shell history, universal quadratic flatness is exactly RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_zero
    {w : ℕ → ℝ} (hw : Summable w) (htotal : (∑' n : ℕ, w n) ≠ 0) (k : ℕ) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        schwarzschildParikhWilczekScalarHistoryQuadraticEnergy w (rho : ℂ) k = 0 := by
  constructor
  · intro hRH rho
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
    exact (schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff_of_total_ne_zero
      hw htotal (rho : ℂ) k h0 h1 (xi_divisor_support_im_ne_zero rho)).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
      exact (schwarzschildParikhWilczekScalarHistoryQuadraticEnergy_eq_zero_iff_of_total_ne_zero
        hw htotal (rho : ℂ) k h0 h1 (xi_divisor_support_im_ne_zero rho)).mp (h rho)

end

end RHTower
