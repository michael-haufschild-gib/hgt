import GaloisForLFunctions.RHTower.XiMassTypeZeroDefect

/-!
# The timelike identity wall

On a timelike ray `h = αu` with `0 < α < 1` the mass Fourier profile has a real stationary point
whose dispersion is `a/√(1−α²)`.  As `α` sweeps `(0,1)` this dispersion sweeps the whole interval
`(a,∞)`.

An isolated complex caustic saddle therefore admits arbitrary finite source-safe vanishing jets,
while the timelike core is a continuum of real saddles: any fixed analytic multiplier annihilating
the leading saddle on every timelike ray vanishes on a real interval and hence identically.  Such
a multiplier annihilates the spectral receiver as well, so no fixed-rank multiplier route can act
on the timelike velocity continuum.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The timelike stationary dispersion `ω(x_α) = a/√(1−α²)`. -/
def xiMassTimelikeSaddleDispersion (a alpha : ℝ) : ℝ :=
  a / Real.sqrt (1 - alpha ^ 2)

theorem xiMassTimelikeSaddleDispersion_gt {a alpha : ℝ} (ha : 0 < a) (h0 : 0 < alpha)
    (h1 : alpha < 1) : a < xiMassTimelikeSaddleDispersion a alpha := by
  have hlt : (0 : ℝ) < 1 - alpha ^ 2 := by nlinarith
  have hle : 1 - alpha ^ 2 < 1 := by nlinarith
  have hs : Real.sqrt (1 - alpha ^ 2) < 1 := by
    have := Real.sqrt_lt_sqrt hlt.le hle
    rwa [Real.sqrt_one] at this
  have hspos : (0 : ℝ) < Real.sqrt (1 - alpha ^ 2) := Real.sqrt_pos.2 hlt
  rw [xiMassTimelikeSaddleDispersion, lt_div_iff₀ hspos]
  nlinarith

/-- **(22.12) The timelike saddle dispersion sweeps the whole exterior interval.** -/
theorem xiMassTimelikeSaddleDispersion_surjOn {a : ℝ} (ha : 0 < a) :
    Set.SurjOn (xiMassTimelikeSaddleDispersion a) (Set.Ioo 0 1) (Set.Ioi a) := by
  intro w hw
  rw [Set.mem_Ioi] at hw
  have hwpos : (0 : ℝ) < w := lt_trans ha hw
  have hratio : (0 : ℝ) < 1 - a ^ 2 / w ^ 2 := by
    have hlt : a ^ 2 / w ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    linarith
  refine ⟨Real.sqrt (1 - a ^ 2 / w ^ 2), ⟨Real.sqrt_pos.2 hratio, ?_⟩, ?_⟩
  · have hlt : 1 - a ^ 2 / w ^ 2 < 1 := by
      have : (0 : ℝ) < a ^ 2 / w ^ 2 := by positivity
      linarith
    have := Real.sqrt_lt_sqrt hratio.le hlt
    rwa [Real.sqrt_one] at this
  · have hsq : Real.sqrt (1 - a ^ 2 / w ^ 2) ^ 2 = 1 - a ^ 2 / w ^ 2 :=
      Real.sq_sqrt hratio.le
    have hval : 1 - Real.sqrt (1 - a ^ 2 / w ^ 2) ^ 2 = a ^ 2 / w ^ 2 := by
      rw [hsq]
      ring
    have hroot : Real.sqrt (1 - Real.sqrt (1 - a ^ 2 / w ^ 2) ^ 2) = a / w := by
      rw [hval, Real.sqrt_div (by positivity : (0 : ℝ) ≤ a ^ 2), Real.sqrt_sq ha.le,
        Real.sqrt_sq hwpos.le]
    rw [xiMassTimelikeSaddleDispersion, hroot]
    field_simp

/-! ## The identity wall -/

/-- **(C42-U) The timelike identity wall.**  A fixed entire multiplier annihilating the leading
timelike saddle on every ray vanishes on the interval `(a,∞)` and hence identically; in particular
it annihilates every spectral point. -/
theorem eq_zero_of_vanishes_on_timelikeSaddles {a : ℝ} (ha : 0 < a) {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P Set.univ)
    (hzero : ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
      P ((xiMassTimelikeSaddleDispersion a alpha : ℝ) : ℂ) = 0) :
    ∀ z : ℂ, P z = 0 := by
  have hreal : ∀ w : ℝ, a < w → P ((w : ℝ) : ℂ) = 0 := by
    intro w hw
    obtain ⟨alpha, halpha, hval⟩ := xiMassTimelikeSaddleDispersion_surjOn ha (Set.mem_Ioi.2 hw)
    rw [← hval]
    exact hzero alpha halpha.1 halpha.2
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = ((a + 1 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hseq : Tendsto (fun n : ℕ => (((a + 1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (nhds z₀) := by
    rw [hz₀]
    have hbase : Tendsto (fun n : ℕ => (a + 1 + 1 / ((n : ℝ) + 1))) atTop (nhds (a + 1)) := by
      have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hconst : Tendsto (fun _ : ℕ => (a + 1 : ℝ)) atTop (nhds (a + 1)) := tendsto_const_nhds
      have hstep := hconst.add hinv
      simpa using hstep
    exact (Complex.continuous_ofReal.tendsto (a + 1)).comp hbase
  have hne : ∀ n : ℕ, (((a + 1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) ∈ ({z₀}ᶜ : Set ℂ) := by
    intro n
    rw [hz₀]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    have hreal := Complex.ofReal_inj.1 hcon
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hwithin : Tendsto (fun n : ℕ => (((a + 1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop
      (nhdsWithin z₀ {z₀}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq
      (Filter.Eventually.of_forall hne)
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin z₀ {z₀}ᶜ, P z = 0 := by
    refine hwithin.frequently (Filter.Frequently.of_forall fun n => ?_)
    refine hreal _ ?_
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hEq := hP.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_univ) (Set.mem_univ z₀) hfreq
  intro z
  simpa using hEq (Set.mem_univ z)

/-! ## The exterior saddle dispersion -/

/-- The exterior stationary dispersion modulus `|ω(x_κ)| = a/√(κ²−1)`. -/
def xiMassSpacelikeSaddleDispersion (a kappa : ℝ) : ℝ := a / Real.sqrt (kappa ^ 2 - 1)

theorem xiMassSpacelikeSaddleDispersion_pos {a kappa : ℝ} (ha : 0 < a) (hkappa : 1 < kappa) :
    0 < xiMassSpacelikeSaddleDispersion a kappa := by
  have hk2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  rw [xiMassSpacelikeSaddleDispersion]
  exact div_pos ha (Real.sqrt_pos.2 hk2)

/-- **(22.1) at the caustic.**  The caustic saddle dispersion is the finite nonzero number
`2a²/κ_B`, so an ordinary inverse-dispersion damping factor changes only a constant and cannot
improve the transport power. -/
theorem xiMassSpacelikeSaddleDispersion_sharpSlope {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSaddleDispersion a (xiMassSpacelikeSharpSlope a)
      = 2 * a ^ 2 / xiMassSpacelikeSharpSlope a := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkB : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hval := sharpSlope_eq_two_mul_sqrt ha
  have hroot : Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1)
      = xiMassSpacelikeSharpSlope a / (2 * a) := by
    rw [eq_div_iff (by positivity : (2 : ℝ) * a ≠ 0)]
    linarith [hval]
  rw [xiMassSpacelikeSaddleDispersion, hroot]
  field_simp

end

end RHTower
