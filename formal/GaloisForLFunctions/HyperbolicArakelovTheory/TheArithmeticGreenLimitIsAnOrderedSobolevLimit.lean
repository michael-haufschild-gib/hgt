import GaloisForLFunctions.HyperbolicArakelovTheory.TheSobolevErrorOfTheHyperbolicGreenDamping
import GaloisForLFunctions.HyperbolicArakelovTheory.TheArithmeticClockLocksTheContinuumGreenChannels

/-!
# A uniform ordered approximation to Weil's form

Every packet supported in a fixed interval has the same arithmetic saturation
threshold. Beyond it, the coupled Green energy increases to Weil's form from
below, with error at most `(1-r²) ∫ |f'|² / 2`. Thus the convergence is uniform
on smooth packets with common support and bounded derivative energy.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Classical BigOperators Topology CompactlySupported

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open SpacingScaleHarmonicAnalysis SurfaceOfSpecZ

/-- A support window fixes the horizon of all prime correlations simultaneously. -/
theorem primeCorrelation_eq_zero_of_supportedIn {R : ℝ} {f : ℝ → ℝ}
    (hfR : SupportedIn R f) {p : ℕ} (hp : p.Prime) (hpR : lagRange R ≤ p) :
    primeCorrelation p f = 0 := by
  have hz (k : ℕ) : correlationCoefficient p f k = 0 := by
    have hpk : p ≤ p ^ (k + 1) :=
      Nat.le_of_dvd (pow_pos hp.pos _) (dvd_pow_self p (Nat.succ_ne_zero k))
    have hl := two_mul_lt_abs_log_of_lagRange_le (hpR.trans hpk)
    rw [Nat.cast_pow, Real.log_pow] at hl
    have hc : autocorr f (((k + 1 : ℕ) : ℝ) * Real.log p) = 0 := by
      simp only [autocorr, mul_shift_eq_zero_of_supportedIn hfR hfR hl, integral_zero]
    rw [correlationCoefficient, hc, mul_zero]
  simp only [primeCorrelation, hz, finsum_zero, mul_zero]

/-- The prime identity is exact at a threshold depending only on the support window. -/
theorem clockedPrimeChannel_sub_mass_of_supportedIn {R S : ℝ} {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hfR : SupportedIn R f)
    (hS : cumulativeCapacity (lagRange R) ≤ S) :
    clockedPrimeChannel S f - S * (∫ u, f u ^ 2) = -primeSum f := by
  obtain ⟨N, hsum, htail⟩ := primeSum_eq_finite_channels hfc
  have hS0 := (cumulativeCapacity_nonneg (lagRange R)).trans hS
  obtain ⟨Q₀, hQ₀⟩ :=
    (tendsto_cumulativeCapacity_atTop.eventually (eventually_ge_atTop S)).exists
  let Q := max Q₀ (N + 1)
  have hSQ : S ≤ cumulativeCapacity Q := hQ₀.trans (cumulativeCapacity_mono (le_max_left _ _))
  have hNQ : N + 1 ≤ Q := le_max_right _ _
  have hwn (p : ℕ) (hp : ¬p.Prime) : clockWeight S p = 0 := by
    simp only [clockWeight, primeCapacity, if_neg hp, div_zero]
  have hfinite : clockedPrimeChannel S f =
      ∑ p ∈ Finset.range Q, clockWeight S p * continuumChannel p f := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    by_contra hmem
    have hQp : Q ≤ p := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
    exact hp (by
      change clockWeight S p * continuumChannel p f = 0
      rw [clockWeight, filledCapacity_eq_zero hSQ hQp, zero_div, zero_mul])
  have hterm (p : ℕ) : clockWeight S p * continuumChannel p f =
      filledCapacity S p * (∫ u, f u ^ 2) - clockWeight S p * primeCorrelation p f := by
    by_cases hp : p.Prime
    · have hm := clockWeight_mul_capacity S p
      rw [primeCapacity, if_pos hp] at hm
      rw [continuumChannel, mul_sub, ← mul_assoc, hm]
    · have hw := hwn p hp
      have hc : filledCapacity S p = 0 := by
        simpa only [hw, zero_mul] using (clockWeight_mul_capacity S p).symm
      rw [hw, hc, zero_mul, zero_mul, zero_mul, sub_zero]
  have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.range Q := by
    intro p hp
    have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact Finset.mem_range.mpr (lt_of_le_of_lt hpN (lt_of_lt_of_le (Nat.lt_succ_self N) hNQ))
  have hcorr : (∑ p ∈ Finset.range Q, clockWeight S p * primeCorrelation p f) = primeSum f := by
    calc
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, clockWeight S p * primeCorrelation p f := by
        symm
        apply Finset.sum_subset hsub
        intro p hp hpnot
        by_cases hpp : p.Prime
        · have hNp : N < p := by
            by_contra h
            exact hpnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_le, not_lt.mp h⟩, hpp⟩)
          rw [htail p hpp hNp, mul_zero]
        · rw [hwn p hpp, zero_mul]
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, primeCorrelation p f := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpp := (Finset.mem_filter.mp hp).2
        by_cases hpR : p < lagRange R
        · rw [clockWeight_eq_one hpp ((cumulativeCapacity_mono hpR).trans hS), one_mul]
        · rw [primeCorrelation_eq_zero_of_supportedIn hfR hpp (not_lt.mp hpR), mul_zero]
      _ = _ := hsum.symm
  rw [hfinite]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_filledCapacity,
    min_eq_left hSQ, min_eq_right hS0, sub_zero, hcorr]
  ring

/-- After arithmetic saturation, the only remaining error is the hyperbolic jump deficit. -/
theorem weilQuad_sub_coupledGreenEnergy_eq {R r : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hclock : cumulativeCapacity (lagRange R) ≤ arithmeticClock r) :
    weilQuad f - coupledGreenEnergy r f = levyEnergy f - dampedJumpEnergy r f := by
  have hp := clockedPrimeChannel_sub_mass_of_supportedIn hfc hfR hclock
  rw [weilQuad_eq hf hfc, ← geometricScalar_eq, dampedJumpEnergy_eq hf hfc hr0 hr1]
  dsimp only [coupledGreenEnergy, arithmeticClock] at hp ⊢
  linear_combination -hp

/-- A common arithmetic cutoff gives a signed Sobolev error bound for every packet in a window. -/
theorem coupledGreenEnergy_error_bounds (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {R r : ℝ} (hfR : SupportedIn R f)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hclock : cumulativeCapacity (lagRange R) ≤ arithmeticClock r) :
    0 ≤ weilQuad f - coupledGreenEnergy r f ∧
      weilQuad f - coupledGreenEnergy r f ≤
        (1 - r ^ 2) / 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  rw [weilQuad_sub_coupledGreenEnergy_eq hf f.hasCompactSupport hfR hr0 hr1 hclock]
  exact levyEnergy_sub_dampedJump_bounds f hf hr0 hr1

theorem arithmeticClock_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1) :
    arithmeticClock r ≤ arithmeticClock s := by
  have h : selfEnergy r ≤ selfEnergy s :=
    integral_mono (integrable_archDamped hr0 (hrs.trans_lt hs1))
      (integrable_archDamped (hr0.trans hrs) hs1) (archDamped_mono hr0 hrs hs1)
  change selfEnergy r + geometricScalar ≤ selfEnergy s + geometricScalar
  linarith only [h]

/-- Once saturated, the full Green coupling is increasing in its damping parameter. -/
theorem coupledGreenEnergy_mono {R r s : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1)
    (hclock : cumulativeCapacity (lagRange R) ≤ arithmeticClock r) :
    coupledGreenEnergy r f ≤ coupledGreenEnergy s f := by
  have hcr := weilQuad_sub_coupledGreenEnergy_eq hf hfc hfR hr0 (hrs.trans_lt hs1) hclock
  have hcs := weilQuad_sub_coupledGreenEnergy_eq hf hfc hfR (hr0.trans hrs) hs1
    (hclock.trans (arithmeticClock_mono hr0 hrs hs1))
  have hm := dampedJumpEnergy_mono hf hfc hr0 hrs hs1
  linarith only [hcr, hcs, hm]

/-- The cutoff precedes the packet quantifier: the bound is uniform on each support window. -/
theorem eventually_coupledGreenEnergy_error_bounds (R : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ f : C_c(ℝ, ℝ),
      ContDiff ℝ 2 (f : ℝ → ℝ) → SupportedIn R f →
      0 ≤ weilQuad f - coupledGreenEnergy r f ∧
        weilQuad f - coupledGreenEnergy r f ≤
          (1 - r ^ 2) / 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  have hc := tendsto_arithmeticClock_atTop.eventually
    (eventually_ge_atTop (cumulativeCapacity (lagRange R)))
  have h0 : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hc, h0, self_mem_nhdsWithin] with r hr hr0 hr1 f hf hfR
  exact coupledGreenEnergy_error_bounds f hf hfR hr0.le hr1 hr

/-- Uniform convergence on smooth packets with common support and bounded derivative energy. -/
theorem coupledGreenEnergy_uniform_sobolev (R M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ f : C_c(ℝ, ℝ),
      ContDiff ℝ 2 (f : ℝ → ℝ) → SupportedIn R f →
      (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) ≤ M →
      |weilQuad f - coupledGreenEnergy r f| < ε := by
  have hc : Continuous (fun r : ℝ => (1 - r ^ 2) / 2 * M) := by fun_prop
  have ht : Tendsto (fun r : ℝ => (1 - r ^ 2) / 2 * M) (𝓝[<] 1) (𝓝 0) := by
    simpa only [one_pow, sub_self, zero_div, zero_mul] using
      (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hsmall := ht.eventually (gt_mem_nhds hε)
  have h0 : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_coupledGreenEnergy_error_bounds R, hsmall, h0,
    self_mem_nhdsWithin] with r hb hs hr0 hr1 f hf hfR hM
  have h := hb f hf hfR
  rw [abs_of_nonneg h.1]
  have hr2 : r ^ 2 < 1 := by
    have hr1' : r < 1 := hr1
    nlinarith only [hr1', mul_nonneg hr0.le (sub_pos.mpr hr1').le]
  exact (h.2.trans (mul_le_mul_of_nonneg_left hM (by positivity))).trans_lt hs

#print axioms clockedPrimeChannel_sub_mass_of_supportedIn
#print axioms coupledGreenEnergy_error_bounds
#print axioms coupledGreenEnergy_mono
#print axioms coupledGreenEnergy_uniform_sobolev

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
