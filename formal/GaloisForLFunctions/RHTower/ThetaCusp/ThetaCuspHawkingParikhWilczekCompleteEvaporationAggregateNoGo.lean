import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekReflectionOrbitAggregateNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint

/-!
# Parikh--Wilczek complete-evaporation aggregate no-go

Exact dyadic Schwarzschild shell durations sum to total remaining lifetime `1/(3 alpha)`.
Parikh--Wilczek Borel recoil holonomy is dimensionless and independent of mass shell, so complete
evaporation integration only multiplies its oriented phase and faithful quadratic orbit energy by
this positive lifetime.  Neither can cancel off critical wall.

Thus self-similar finite-mass evaporation cannot produce PW-B partner balance or holonomy flatness.
It preserves the exact wall receiver.  Any viable physical producer must break shell-independent
self-similarity through genuine mass-dependent channel mixing, memory/nonlocality, or singular
boundary incidence.

`[NEW] [NO-GO] [EXACT GLOBAL AGGREGATE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Exact total duration of all normalized dyadic Schwarzschild evaporation shells. -/
theorem tsum_schwarzschildEvaporationDyadicShellDuration
    {alpha : ℝ} (halpha : alpha ≠ 0) :
    ∑' n : ℕ, schwarzschildEvaporationDyadicShellDuration alpha n =
      1 / (3 * alpha) := by
  calc
    (∑' n : ℕ, schwarzschildEvaporationDyadicShellDuration alpha n) =
        ∑' n : ℕ, (7 / (24 * alpha)) * (1 / 8 : ℝ) ^ n := by
      apply tsum_congr
      intro n
      rw [schwarzschildEvaporationDyadicShellDuration_eq halpha,
        schwarzschildEvaporationDyadicMass]
      congr 1
      calc
        ((1 / 2 : ℝ) ^ n) ^ (3 : ℕ) = (1 / 2 : ℝ) ^ (n * 3) := (pow_mul _ _ _).symm
        _ = (1 / 2 : ℝ) ^ (3 * n) := by rw [Nat.mul_comm]
        _ = ((1 / 2 : ℝ) ^ (3 : ℕ)) ^ n := pow_mul _ _ _
        _ = (1 / 8 : ℝ) ^ n := by norm_num
    _ = (7 / (24 * alpha)) * ∑' n : ℕ, (1 / 8 : ℝ) ^ n := by
      rw [tsum_mul_left]
    _ = 1 / (3 * alpha) := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      field_simp
      ring

theorem summable_schwarzschildEvaporationDyadicShellDuration
    {alpha : ℝ} (halpha : alpha ≠ 0) :
    Summable (schwarzschildEvaporationDyadicShellDuration alpha) := by
  rw [show schwarzschildEvaporationDyadicShellDuration alpha =
      fun n : ℕ => (7 / (24 * alpha)) * (1 / 8 : ℝ) ^ n by
    funext n
    rw [schwarzschildEvaporationDyadicShellDuration_eq halpha,
      schwarzschildEvaporationDyadicMass]
    congr 1
    calc
      ((1 / 2 : ℝ) ^ n) ^ (3 : ℕ) = (1 / 2 : ℝ) ^ (n * 3) := (pow_mul _ _ _).symm
      _ = (1 / 2 : ℝ) ^ (3 * n) := by rw [Nat.mul_comm]
      _ = ((1 / 2 : ℝ) ^ (3 : ℕ)) ^ n := pow_mul _ _ _
      _ = (1 / 8 : ℝ) ^ n := by norm_num]
  exact (summable_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 8 : ℝ)‖ < 1)).mul_left _

/-- Time-integrated oriented recoil phase through complete dyadic evaporation. -/
def schwarzschildParikhWilczekCompleteEvaporationPhase
    (alpha : ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, schwarzschildEvaporationDyadicShellDuration alpha n *
    (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im

/-- Complete evaporation only multiplies dimensionless recoil phase by total lifetime. -/
theorem schwarzschildParikhWilczekCompleteEvaporationPhase_eq
    {alpha : ℝ} (halpha : alpha ≠ 0) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekCompleteEvaporationPhase alpha s k =
      (1 / (3 * alpha)) *
        (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im := by
  rw [schwarzschildParikhWilczekCompleteEvaporationPhase,
    tsum_mul_right, tsum_schwarzschildEvaporationDyadicShellDuration halpha]

/-- Time-integrated faithful quadratic recoil energy through complete evaporation. -/
def schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy
    (alpha : ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, schwarzschildEvaporationDyadicShellDuration alpha n *
    schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k

/-- Quadratic recoil energy likewise persists as positive lifetime multiple. -/
theorem schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq
    {alpha : ℝ} (halpha : alpha ≠ 0) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy alpha s k =
      (1 / (3 * alpha)) *
        schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k := by
  rw [schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy,
    tsum_mul_right, tsum_schwarzschildEvaporationDyadicShellDuration halpha]

/-- With positive mass-loss coefficient, complete evaporation phase is flat exactly on wall. -/
theorem schwarzschildParikhWilczekCompleteEvaporationPhase_eq_zero_iff
    {alpha : ℝ} (halpha : 0 < alpha) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekCompleteEvaporationPhase alpha s k = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekCompleteEvaporationPhase_eq halpha.ne', mul_eq_zero]
  have htime : 1 / (3 * alpha) ≠ 0 := by positivity
  simp only [htime, false_or]
  exact schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
    s k hs0 hs1 hsim

/-- Positive dyadic time integration cannot dissipate quadratic orbit energy off wall. -/
theorem schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq_zero_iff
    {alpha : ℝ} (halpha : 0 < alpha) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy alpha s k = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq halpha.ne',
    mul_eq_zero]
  have htime : 1 / (3 * alpha) ≠ 0 := by positivity
  simp only [htime, false_or]
  exact schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq_zero_iff
    s k hs0 hs1 hsim

/-- Universal complete-evaporation quadratic flatness at any physical rate and one grade is RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_zero
    {alpha : ℝ} (halpha : 0 < alpha) (k : ℕ) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy
          alpha (rho : ℂ) k = 0 := by
  constructor
  · intro hRH rho
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
    exact (schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq_zero_iff
      halpha (rho : ℂ) k h0 h1 (xi_divisor_support_im_ne_zero rho)).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
      exact (schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq_zero_iff
        halpha (rho : ℂ) k h0 h1 (xi_divisor_support_im_ne_zero rho)).mp (h rho)

end

end RHTower
