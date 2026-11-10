import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeGreenCapacityHasSquareRootGrowth
import GaloisForLFunctions.HyperbolicArakelovTheory.TheArithmeticGreenLimitIsAnOrderedSobolevLimit

/-!
# The sharp spatial horizon of the arithmetic Green clock

At damping `r_N = √(1-exp(-κ√N))`, the clock mass is `κ√N + O(1)`.
The prime capacity through `N` is `4√N + o(√N)`, so every `κ>4` eventually
fills that horizon, while `0<κ<4` leaves a prime unfilled. Above the threshold,
the Weil error on packets of support radius `(log N)/2` is bounded by
`exp(-κ√N) ∫ |f'|² / 2`, uniformly even when the derivative energy grows
like `exp(η√N)` for any `η<κ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Classical BigOperators Topology CompactlySupported

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open SpacingScaleHarmonicAnalysis SurfaceOfSpecZ

/-- Damping indexed by the spatial prime horizon, rather than by an individual packet. -/
def spatialDamping (κ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (1 - Real.exp (-(κ * Real.sqrt N)))

theorem spatialDamping_spec {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) :
    0 ≤ spatialDamping κ N ∧ spatialDamping κ N < 1 ∧
      1 - spatialDamping κ N ^ 2 = Real.exp (-(κ * Real.sqrt N)) := by
  have he := Real.exp_pos (-(κ * Real.sqrt N))
  have he1 : Real.exp (-(κ * Real.sqrt N)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ (Real.sqrt_nonneg _)))
  have hh : 0 ≤ 1 - Real.exp (-(κ * Real.sqrt N)) := sub_nonneg.mpr he1
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩
  · have hlt : 1 - Real.exp (-(κ * Real.sqrt N)) < (1 : ℝ) := by linarith only [he]
    simpa only [spatialDamping, Real.sqrt_one] using Real.sqrt_lt_sqrt hh hlt
  · rw [spatialDamping, Real.sq_sqrt hh]
    ring

/-- The clock differs from `κ√N` by bounded geometric constants. -/
theorem spatialClock_bounds {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) :
    κ * Real.sqrt N + (4 - Real.pi ^ 2 / 24 + geometricScalar) ≤
        arithmeticClock (spatialDamping κ N) ∧
      arithmeticClock (spatialDamping κ N) ≤ κ * Real.sqrt N + (4 + geometricScalar) := by
  have hr := spatialDamping_spec hκ N
  have hb := selfEnergy_bounds hr.1 hr.2.1
  rw [hr.2.2, Real.log_exp] at hb
  dsimp only [arithmeticClock]
  constructor <;> linarith only [hb.1, hb.2]

/-- The normalized arithmetic clock has the same coefficient as its damping exponent. -/
theorem tendsto_spatialClock_div_sqrt {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun N : ℕ => arithmeticClock (spatialDamping κ N) / Real.sqrt N)
      atTop (𝓝 κ) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hc (A : ℝ) : Tendsto (fun N : ℕ => κ + A / Real.sqrt N) atTop (𝓝 κ) := by
    have h : Tendsto (fun N : ℕ => κ + A / Real.sqrt N) atTop (𝓝 (κ + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsqrt)
    simpa only [add_zero] using h
  have hb : ∀ᶠ N : ℕ in atTop,
      κ + (4 - Real.pi ^ 2 / 24 + geometricScalar) / Real.sqrt N ≤
          arithmeticClock (spatialDamping κ N) / Real.sqrt N ∧
        arithmeticClock (spatialDamping κ N) / Real.sqrt N ≤
          κ + (4 + geometricScalar) / Real.sqrt N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hs := Real.sqrt_pos.mpr hN0
    have h := spatialClock_bounds hκ N
    have hl := div_le_div_of_nonneg_right h.1 hs.le
    have hu := div_le_div_of_nonneg_right h.2 hs.le
    rw [add_div, mul_div_assoc, div_self hs.ne', mul_one] at hl hu
    exact ⟨hl, hu⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hc (4 - Real.pi ^ 2 / 24 + geometricScalar)) (hc (4 + geometricScalar))
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- Above the coefficient four, the clock fills the complete prime horizon through `N`. -/
theorem eventually_spatialClock_covers_capacity {κ : ℝ} (hκ : 4 < κ) :
    ∀ᶠ N : ℕ in atTop,
      cumulativeCapacity (N + 1) ≤ arithmeticClock (spatialDamping κ N) := by
  have hκ0 : 0 ≤ κ := le_of_lt (lt_trans (by norm_num) hκ)
  have h := tendsto_cumulativeCapacity_div_sqrt.eventually_lt
    (tendsto_spatialClock_div_sqrt hκ0) hκ
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with N hN hpos
  have hs : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact ((div_lt_div_iff_of_pos_right hs).mp hN).le

/-- Below the coefficient four, the clock cannot fill the complete spatial prime horizon. -/
theorem eventually_spatialClock_below_capacity {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) :
    ∀ᶠ N : ℕ in atTop,
      arithmeticClock (spatialDamping κ N) < cumulativeCapacity (N + 1) := by
  have h := (tendsto_spatialClock_div_sqrt hκ0.le).eventually_lt
    tendsto_cumulativeCapacity_div_sqrt hκ4
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with N hN hpos
  have hs : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact (div_lt_div_iff_of_pos_right hs).mp hN

private theorem exists_unfilled_prime {S : ℝ} {N : ℕ} (hS0 : 0 ≤ S)
    (hS : S < cumulativeCapacity (N + 1)) :
    ∃ p ∈ Nat.primesLE N, clockWeight S p < 1 := by
  by_contra hn
  push Not at hn
  have hterm (p : ℕ) (hp : p ∈ Finset.range (N + 1)) :
      filledCapacity S p = primeCapacity p := by
    by_cases hpp : p.Prime
    · have hmem : p ∈ Nat.primesLE N := by
        rw [Nat.primesLE, Nat.primesBelow]
        exact Finset.mem_filter.mpr ⟨hp, hpp⟩
      have hw : clockWeight S p = 1 :=
        le_antisymm (clockWeight_le_one S p) (hn p hmem)
      rw [← clockWeight_mul_capacity, hw, one_mul]
    · rw [primeCapacity, if_neg hpp]
      simpa only [primeCapacity, if_neg hpp, mul_zero] using (clockWeight_mul_capacity S p).symm
  have hfull : (∑ p ∈ Finset.range (N + 1), filledCapacity S p) =
      cumulativeCapacity (N + 1) := Finset.sum_congr rfl hterm
  rw [sum_filledCapacity, min_eq_left hS.le, min_eq_right hS0, sub_zero] at hfull
  exact hS.ne hfull

/-- Subcritical damping leaves an actual prime channel unsaturated at every sufficiently large horizon. -/
theorem eventually_spatialDamping_has_unfilled_prime {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) :
    ∀ᶠ N : ℕ in atTop, ∃ p ∈ Nat.primesLE N,
      clockWeight (arithmeticClock (spatialDamping κ N)) p < 1 := by
  have hp := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).eventually_lt
    (tendsto_spatialClock_div_sqrt hκ0.le) hκ0
  filter_upwards [eventually_spatialClock_below_capacity hκ0 hκ4, hp,
    eventually_ge_atTop (1 : ℕ)] with N hN hpos hN1
  have hs : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1))
  have hm := mul_pos hpos hs
  rw [div_mul_cancel₀ _ hs.ne'] at hm
  exact exists_unfilled_prime hm.le hN

private theorem lagRange_half_log {N : ℕ} (hN : 0 < N) :
    lagRange (Real.log N / 2) = N + 1 := by
  rw [lagRange, show 2 * (Real.log N / 2) = Real.log N by ring,
    Real.exp_log (by exact_mod_cast hN : (0 : ℝ) < N), Nat.ceil_natCast]

/-- The error bound holds simultaneously on support windows whose radius grows like `log N / 2`. -/
theorem eventually_growingWindow_Green_error {κ : ℝ} (hκ : 4 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ f : C_c(ℝ, ℝ),
      ContDiff ℝ 2 (f : ℝ → ℝ) → SupportedIn (Real.log N / 2) f →
      0 ≤ weilQuad f - coupledGreenEnergy (spatialDamping κ N) f ∧
        weilQuad f - coupledGreenEnergy (spatialDamping κ N) f ≤
          Real.exp (-(κ * Real.sqrt N)) / 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  filter_upwards [eventually_spatialClock_covers_capacity hκ,
    eventually_ge_atTop (1 : ℕ)] with N hclock hN f hf hfR
  have hr := spatialDamping_spec (le_of_lt (lt_trans (by norm_num) hκ)) N
  have hc : cumulativeCapacity (lagRange (Real.log N / 2)) ≤
      arithmeticClock (spatialDamping κ N) := by
    rwa [lagRange_half_log (lt_of_lt_of_le Nat.zero_lt_one hN)]
  simpa only [hr.2.2] using coupledGreenEnergy_error_bounds f hf hfR hr.1 hr.2.1 hc

/-- Uniform recovery permits both expanding support and exponentially growing derivative energy. -/
theorem growingWindow_Green_uniform {κ η : ℝ} (hκ : 4 < κ) (hη : η < κ)
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : C_c(ℝ, ℝ),
      ContDiff ℝ 2 (f : ℝ → ℝ) → SupportedIn (Real.log N / 2) f →
      (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) ≤ M * Real.exp (η * Real.sqrt N) →
      |weilQuad f - coupledGreenEnergy (spatialDamping κ N) f| < ε := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun N : ℕ => Real.exp (-((κ - η) * Real.sqrt N))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (sub_pos.mpr hη) hsqrt))
  have ht : Tendsto (fun N : ℕ => M / 2 * Real.exp (-((κ - η) * Real.sqrt N)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hdecay.const_mul (M / 2)
  filter_upwards [eventually_growingWindow_Green_error hκ, ht.eventually (gt_mem_nhds hε)]
    with N hb hs f hf hfR hM
  have h := hb f hf hfR
  rw [abs_of_nonneg h.1]
  have hm := mul_le_mul_of_nonneg_left hM
    (div_nonneg (Real.exp_pos (-(κ * Real.sqrt N))).le (by norm_num : (0 : ℝ) ≤ 2))
  have he : Real.exp (-(κ * Real.sqrt N)) / 2 * (M * Real.exp (η * Real.sqrt N)) =
      M / 2 * Real.exp (-((κ - η) * Real.sqrt N)) := by
    calc
      _ = M / 2 * (Real.exp (-(κ * Real.sqrt N)) * Real.exp (η * Real.sqrt N)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [he] at hm
  exact (h.2.trans hm).trans_lt hs

#print axioms tendsto_spatialClock_div_sqrt
#print axioms eventually_spatialDamping_has_unfilled_prime
#print axioms eventually_growingWindow_Green_error
#print axioms growingWindow_Green_uniform

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
