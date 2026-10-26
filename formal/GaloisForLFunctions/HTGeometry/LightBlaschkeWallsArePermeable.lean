import GaloisForLFunctions.HTGeometry.InfiniteBlaschkeMultiplier
import GaloisForLFunctions.HTGeometry.LaurentAnnulus
import GaloisForLFunctions.HTGeometry.SchwarzPickEstimate

/-!
# Light Blaschke walls are permeable

A discrete Cauchy transform `G(u) = Σ_n ν_n/(u − a_n)` whose poles `a_n` lie in the unit disc and
accumulate only at the unit circle can agree outside the circle with a function holomorphic across
it while its masses do not vanish: the circle is then a wall (Wolff). This file proves that the wall
is permeable when the poles form a Blaschke sequence, `Σ (1 − |a_n|) < ∞`, and the masses are
light, `Σ |ν_n|/(1 − |a_n|) < ∞`: then agreement outside forces every `ν_n = 0`.

* **Shadows** (`radialShadow`, `ae_eventually_notMem_radialShadow`). The ray through `e^{iθ}` passes
  within `1 − |a|` of `a` only for `θ` in an arc of length `O(1 − |a|)`. By Borel–Cantelli almost
  every ray meets only finitely many shadows.
* **Radial limits** (`tendsto_cauchy_radial`). Along such a ray the masses dominate the series
  uniformly, so `G` has a radial limit at almost every point of the circle; from outside it is
  continuous up to the circle (`continuousOn_cauchy_outside`).
* **Cancelling one pole** (`poleQuotient`). With `B` the Blaschke product of the poles,
  `B(z)/(z − a_n)` is holomorphic across `a_n`, nonzero there, and bounded by `1/(ρ(1 − |a_n|))`.
* **Zero radial limits on an annulus** (`eqOn_zero_of_radial_tendsto_zero`). A holomorphic function
  on `ρ < |z| < 1`, bounded near the circle, with radial limits `0` almost everywhere, vanishes:
  its circle integrals against the Cauchy kernel and against `z^k` do not depend on the radius and
  tend to `0`, so both parts of its Laurent decomposition vanish.
* **Permeability** (`masses_eq_zero_of_cauchy_eq_outside`). `Σ ν_n B/(z − a_n) − B·E` is
  holomorphic and bounded inside the circle, with zero radial limits; it vanishes, and its value
  `ν_n · B(z)/(z − a_n)|_{a_n}` at each pole is the mass.
-/

open Complex Filter Topology Set Metric MeasureTheory
open scoped Real ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### 1. Shadows -/

/-- The **shadow** of a disc point `a`: the directions `θ` with `|(|a| e^{iθ}) − a| < 2(1 − |a|)`. -/
def radialShadow (a : ℂ) : Set ℝ := {θ | ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖ < 2 * (1 - ‖a‖)}

/-- Off its shadow, the ray through `e^{iθ}` stays at distance `≥ 1 − |a|` from `a`. -/
theorem one_sub_norm_le_of_notMem_radialShadow {a : ℂ} {θ : ℝ} (hθ : θ ∉ radialShadow a) {r : ℝ}
    (hr : 0 ≤ r) : 1 - ‖a‖ ≤ ‖(r : ℂ) * cexp (θ * I) - a‖ := by
  by_contra hlt
  push Not at hlt
  apply hθ
  show ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖ < 2 * (1 - ‖a‖)
  have h1 : |r - ‖a‖| ≤ ‖(r : ℂ) * cexp (θ * I) - a‖ := by
    have := abs_norm_sub_norm_le ((r : ℂ) * cexp (θ * I)) a
    rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr] at this
  have h2 : ‖(‖a‖ : ℂ) * cexp (θ * I) - (r : ℂ) * cexp (θ * I)‖ = |r - ‖a‖| := by
    rw [← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  calc ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖
      ≤ ‖(‖a‖ : ℂ) * cexp (θ * I) - (r : ℂ) * cexp (θ * I)‖ + ‖(r : ℂ) * cexp (θ * I) - a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 * (1 - ‖a‖) := by rw [h2]; linarith

/-- **Jordan's inequality on the circle**: `|e^{ix} − 1| ≥ 2|x|/π` for `|x| ≤ π`. -/
theorem two_div_pi_mul_abs_le_norm_exp_sub_one {x : ℝ} (hx : |x| ≤ π) :
    2 / π * |x| ≤ ‖cexp (x * I) - 1‖ := by
  rw [mul_comm (x : ℂ) I, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_two,
    Real.norm_eq_abs]
  have hy : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin (by positivity : (0 : ℝ) ≤ |x| / 2) hy
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    have h0 : 0 ≤ Real.sin (|x| / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    rcases abs_cases x with ⟨hxa, -⟩ | ⟨hxa, -⟩
    · rw [hxa] at h0 ⊢
      exact abs_of_nonneg h0
    · rw [hxa, neg_div, Real.sin_neg] at h0 ⊢
      exact abs_of_nonpos (by linarith)
  rw [habs]
  have : 2 / π * |x| = 2 * (2 / π * (|x| / 2)) := by ring
  rw [this]
  linarith

/-- The shadow of `a ≠ 0` meets `(0, 2π]` in measure at most `4π (1 − |a|)/|a|`. -/
theorem volume_radialShadow_inter_le {a : ℂ} (ha0 : a ≠ 0) (ha1 : ‖a‖ ≤ 1) :
    volume (radialShadow a ∩ Ioc 0 (2 * π)) ≤ ENNReal.ofReal (4 * π * ((1 - ‖a‖) / ‖a‖)) := by
  set α := a.arg
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set c : ℝ := π * ((1 - ‖a‖) / ‖a‖) with hc
  have hc0 : 0 ≤ c := mul_nonneg Real.pi_pos.le (div_nonneg (by linarith) hna.le)
  have haexp : a = (‖a‖ : ℂ) * cexp (α * I) := (Complex.norm_mul_exp_arg_mul_I a).symm
  -- a shadow direction lies within `c` of `α` or of `α + 2π`
  have hsub : radialShadow a ∩ Ioc 0 (2 * π) ⊆
      Ioo (α - c) (α + c) ∪ Ioo (α + 2 * π - c) (α + 2 * π + c) := by
    rintro θ ⟨hθ, hθ0, hθ2⟩
    have hexp : cexp (α * I) * cexp ((θ - α : ℝ) * I) = cexp (θ * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e : (‖a‖ : ℂ) * cexp (θ * I) - a =
        (‖a‖ : ℂ) * cexp (α * I) * (cexp ((θ - α : ℝ) * I) - 1) := by
      rw [mul_sub, mul_one, mul_assoc, hexp, ← haexp]
    have hθ' : ‖a‖ * ‖cexp ((θ - α : ℝ) * I) - 1‖ < 2 * (1 - ‖a‖) := by
      have := hθ
      simp only [radialShadow, mem_setOf_eq] at this
      rwa [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        Complex.norm_exp_ofReal_mul_I, mul_one] at this
    have hlt : ‖cexp ((θ - α : ℝ) * I) - 1‖ < 2 * ((1 - ‖a‖) / ‖a‖) := by
      rw [mul_div_assoc', lt_div_iff₀ hna]
      linarith
    have hαI := Complex.neg_pi_lt_arg a
    have hαS := Complex.arg_le_pi a
    have hpi := Real.pi_pos
    by_cases hx : θ - α ≤ π
    · left
      have h := two_div_pi_mul_abs_le_norm_exp_sub_one (abs_le.mpr ⟨by linarith, hx⟩)
      have h' : 2 / π * |θ - α| < 2 * ((1 - ‖a‖) / ‖a‖) := lt_of_le_of_lt h hlt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h'
      have : |θ - α| < c := by rw [hc]; linarith
      exact ⟨by linarith [neg_abs_le (θ - α)], by linarith [le_abs_self (θ - α)]⟩
    · right
      push Not at hx
      have h := two_div_pi_mul_abs_le_norm_exp_sub_one
        (abs_le.mpr ⟨by linarith, by linarith⟩ : |θ - α - 2 * π| ≤ π)
      have hper : cexp ((θ - α - 2 * π : ℝ) * I) = cexp ((θ - α : ℝ) * I) := by
        push_cast
        rw [sub_mul, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
      rw [hper] at h
      have h' : 2 / π * |θ - α - 2 * π| < 2 * ((1 - ‖a‖) / ‖a‖) := lt_of_le_of_lt h hlt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h'
      have : |θ - α - 2 * π| < c := by rw [hc]; linarith
      exact ⟨by linarith [neg_abs_le (θ - α - 2 * π)], by linarith [le_abs_self (θ - α - 2 * π)]⟩
  calc volume (radialShadow a ∩ Ioc 0 (2 * π))
      ≤ volume (Ioo (α - c) (α + c) ∪ Ioo (α + 2 * π - c) (α + 2 * π + c)) := measure_mono hsub
    _ ≤ volume (Ioo (α - c) (α + c)) + volume (Ioo (α + 2 * π - c) (α + 2 * π + c)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (2 * c) + ENNReal.ofReal (2 * c) := by
        rw [Real.volume_Ioo, Real.volume_Ioo]
        congr 2 <;> ring
    _ = ENNReal.ofReal (4 * π * ((1 - ‖a‖) / ‖a‖)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hc]
        ring

/-- **Almost every ray meets only finitely many shadows** of a Blaschke sequence in `ρ < |a_n|`. -/
theorem ae_eventually_notMem_radialShadow {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ < 1)
    (hbl : Summable fun n => 1 - ‖a n‖) {ρ : ℝ} (hρ : 0 < ρ) (hρa : ∀ n, ρ < ‖a n‖) :
    ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), ∀ᶠ n in atTop, θ ∉ radialShadow (a n) := by
  refine ae_eventually_notMem ?_
  have hnn : ∀ n, 0 ≤ 4 * π / ρ * (1 - ‖a n‖) := fun n =>
    mul_nonneg (by positivity) (by linarith [ha n])
  refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (4 * π / ρ * (1 - ‖a n‖))) ?_
    (ENNReal.tsum_le_tsum fun n => ?_)
  · rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hbl.mul_left _)]
    exact ENNReal.ofReal_ne_top
  · rw [Measure.restrict_apply' measurableSet_Ioc]
    have ha0 : a n ≠ 0 := fun h => by
      have := hρa n
      rw [h, norm_zero] at this
      linarith
    refine (volume_radialShadow_inter_le ha0 (ha n).le).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (1 - ‖a n‖) / ‖a n‖ ≤ (1 - ‖a n‖) / ρ :=
      div_le_div_of_nonneg_left (by linarith [ha n]) hρ (hρa n).le
    calc 4 * π * ((1 - ‖a n‖) / ‖a n‖) ≤ 4 * π * ((1 - ‖a n‖) / ρ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * π / ρ * (1 - ‖a n‖) := by ring

/-! ### 2. The transform on the circle -/

section Transform

variable {a ν : ℕ → ℂ}

/-- Outside the open disc the poles keep distance `1 − |a_n|`. -/
theorem one_sub_norm_le_norm_sub {b u : ℂ} (hu : 1 ≤ ‖u‖) : 1 - ‖b‖ ≤ ‖u - b‖ := by
  have := norm_sub_norm_le u b
  linarith

/-- **Up to the circle from outside.** For light masses the series converges uniformly on
`|u| ≥ 1`. -/
theorem continuousOn_cauchy_outside (ha : ∀ n, ‖a n‖ < 1)
    (hlight : Summable fun n => ‖ν n‖ / (1 - ‖a n‖)) :
    ContinuousOn (fun u => ∑' n, ν n / (u - a n)) {u | 1 ≤ ‖u‖} := by
  refine continuousOn_tsum (fun n => ?_) hlight fun n u hu => ?_
  · refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun u hu h0 => ?_
    have := one_sub_norm_le_norm_sub (b := a n) hu
    rw [h0, norm_zero] at this
    linarith [ha n]
  · rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [ha n])
      (one_sub_norm_le_norm_sub hu)

/-- Along a ray meeting finitely many shadows, the points near the circle keep distance
`(1 − |a_n|)/2` from every pole. -/
theorem eventually_radial_far (ha : ∀ n, ‖a n‖ < 1) {θ : ℝ}
    (hθ : ∀ᶠ n in atTop, θ ∉ radialShadow (a n)) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ ∀ n, (1 - ‖a n‖) / 2 ≤ ‖(r : ℂ) * cexp (θ * I) - a n‖ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hθ
  have hd : ∀ n, 0 < 1 - ‖a n‖ := fun n => by linarith [ha n]
  -- the finitely many poles before `N` are passed once `r > 1 − (1 − |a_n|)/2`
  have hnear : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ ∀ n ∈ Finset.range N, 1 - (1 - ‖a n‖) / 2 ≤ r := by
    refine (eventually_nhdsWithin_of_eventually_nhds (Ici_mem_nhds (by norm_num))).and ?_
    refine (eventually_all_finset _).mpr fun n _ => eventually_nhdsWithin_of_eventually_nhds ?_
    exact Ici_mem_nhds (by linarith [hd n])
  filter_upwards [hnear] with r ⟨hr0, hr⟩
  refine ⟨hr0, fun n => ?_⟩
  by_cases hn : n < N
  · have h1 := hr n (Finset.mem_range.mpr hn)
    have h2 := norm_sub_norm_le ((r : ℂ) * cexp (θ * I)) (a n)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0] at h2
    linarith
  · have := one_sub_norm_le_of_notMem_radialShadow (hN n (not_lt.mp hn)) hr0
    linarith [hd n]

/-- **Radial limits.** If the ray through `e^{iθ}` meets only finitely many shadows, the transform
tends along it to the series at `e^{iθ}`. -/
theorem tendsto_cauchy_radial (ha : ∀ n, ‖a n‖ < 1)
    (hlight : Summable fun n => ‖ν n‖ / (1 - ‖a n‖)) {θ : ℝ}
    (hθ : ∀ᶠ n in atTop, θ ∉ radialShadow (a n)) :
    Tendsto (fun r : ℝ => ∑' n, ν n / ((r : ℂ) * cexp (θ * I) - a n)) (𝓝[<] 1)
      (𝓝 (∑' n, ν n / (cexp (θ * I) - a n))) := by
  have hd : ∀ n, 0 < 1 - ‖a n‖ := fun n => by linarith [ha n]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => 2 * (‖ν n‖ / (1 - ‖a n‖)))
    (hlight.mul_left 2) (fun n => ?_) ?_
  · have hcont : ContinuousAt (fun r : ℝ => ν n / ((r : ℂ) * cexp (θ * I) - a n)) 1 := by
      refine continuousAt_const.div (by fun_prop) ?_
      intro h0
      have := one_sub_norm_le_norm_sub (b := a n) (u := cexp (θ * I))
        (by rw [Complex.norm_exp_ofReal_mul_I])
      rw [show ((1 : ℝ) : ℂ) * cexp (θ * I) - a n = cexp (θ * I) - a n by push_cast; ring] at h0
      rw [h0, norm_zero] at this
      linarith [hd n]
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_radial_far ha hθ] with r ⟨-, hfar⟩ n
    rw [norm_div]
    calc ‖ν n‖ / ‖(r : ℂ) * cexp (θ * I) - a n‖ ≤ ‖ν n‖ / ((1 - ‖a n‖) / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [hd n]) (hfar n)
      _ = 2 * (‖ν n‖ / (1 - ‖a n‖)) := by field_simp

end Transform

/-! ### 3. Cancelling one pole -/

section Pole

variable {a : ℕ → ℂ}

/-- `|1 − \bar b z| ≥ 1 − |b|` on the closed disc. -/
theorem one_sub_norm_le_norm_one_sub_conj_mul {b z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - ‖b‖ ≤ ‖1 - (starRingEnd ℂ) b * z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) b * z)
  rw [norm_one, norm_mul, Complex.norm_conj] at h
  have : ‖b‖ * ‖z‖ ≤ ‖b‖ := mul_le_of_le_one_right (norm_nonneg _) hz
  linarith

theorem normalizedBlaschkeFactor_zero_left (z : ℂ) : normalizedBlaschkeFactor 0 z = z :=
  if_pos rfl

/-- A normalized Blaschke factor vanishes only at its zero. -/
theorem normalizedBlaschkeFactor_ne_zero {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) (hbz : z ≠ b) :
    normalizedBlaschkeFactor b z ≠ 0 := by
  by_cases hb0 : b = 0
  · rw [hb0, normalizedBlaschkeFactor_zero_left]
    rwa [hb0] at hbz
  rw [normalizedBlaschkeFactor, if_neg hb0, blaschkeFactor]
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb0)) hb0))
    (div_ne_zero (sub_ne_zero.mpr hbz) (one_sub_conj_mul_ne_zero hb hz.le))

theorem norm_update_zero_lt_one (ha : ∀ n, ‖a n‖ < 1) (n m : ℕ) :
    ‖Function.update a n 0 m‖ < 1 := by
  rcases eq_or_ne m n with rfl | hmn
  · simp
  · rw [Function.update_of_ne hmn]
    exact ha m

theorem summable_update_zero (hbl : Summable fun n => 1 - ‖a n‖) (n : ℕ) :
    Summable fun m => 1 - ‖Function.update a n 0 m‖ := by
  have : (fun m => 1 - ‖Function.update a n 0 m‖) = Function.update (fun m => 1 - ‖a m‖) n 1 := by
    funext m
    rcases eq_or_ne m n with rfl | hmn
    · simp
    · rw [Function.update_of_ne hmn, Function.update_of_ne hmn]
  rw [this]
  exact hbl.update n 1

theorem multipliable_blaschke (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖) {z : ℂ}
    (hz : ‖z‖ < 1) : Multipliable fun m => normalizedBlaschkeFactor (a m) z :=
  ((infiniteBlaschkeProduct_hasProdLocallyUniformlyOn a ha hbl).hasProd
    (mem_ball_zero_iff.mpr hz)).multipliable

/-- The Blaschke product with the zero `a_n` moved to the origin. -/
def blaschkeDeleted (a : ℕ → ℂ) (n : ℕ) : ℂ → ℂ := infiniteBlaschkeProduct (Function.update a n 0)

/-- Moving one zero: `z · B(z) = b_{a_n}(z) · B_n(z)`. -/
theorem mul_infiniteBlaschkeProduct_eq (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖)
    {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    z * infiniteBlaschkeProduct a z = normalizedBlaschkeFactor (a n) z * blaschkeDeleted a n z := by
  have h1 := (multipliable_blaschke ha hbl hz).tprod_eq_mul_tprod_ite n
  have h2 := (multipliable_blaschke (norm_update_zero_lt_one ha n) (summable_update_zero hbl n)
    hz).tprod_eq_mul_tprod_ite n
  have hrest : (∏' m, if m = n then 1 else normalizedBlaschkeFactor (Function.update a n 0 m) z) =
      ∏' m, if m = n then 1 else normalizedBlaschkeFactor (a m) z := by
    refine tprod_congr fun m => ?_
    split_ifs with hmn
    · rfl
    · rw [Function.update_of_ne hmn]
  unfold blaschkeDeleted infiniteBlaschkeProduct
  rw [h1, h2, hrest, Function.update_self, normalizedBlaschkeFactor_zero_left]
  ring

/-- The **pole quotient** `B(z)/(z − a_n)`, written so that it is holomorphic across `a_n`. -/
def poleQuotient (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  -((‖a n‖ : ℂ) / a n) * blaschkeDeleted a n z / (z * (1 - (starRingEnd ℂ) (a n) * z))

theorem sub_mul_poleQuotient (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) {n : ℕ} (han : a n ≠ 0) :
    (z - a n) * poleQuotient a n z = infiniteBlaschkeProduct a z := by
  have hden := one_sub_conj_mul_ne_zero (ha n) hz.le
  have h := mul_infiniteBlaschkeProduct_eq ha hbl hz n
  rw [normalizedBlaschkeFactor, if_neg han, blaschkeFactor] at h
  rw [poleQuotient]
  apply mul_left_cancel₀ hz0
  rw [h]
  field_simp
  ring

theorem norm_poleQuotient_le (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖) {ρ : ℝ}
    (hρ : 0 < ρ) {z : ℂ} (hzρ : ρ ≤ ‖z‖) (hz : ‖z‖ < 1) (n : ℕ) :
    ‖poleQuotient a n z‖ ≤ 1 / (ρ * (1 - ‖a n‖)) := by
  have hd : 0 < 1 - ‖a n‖ := sub_pos.mpr (ha n)
  have hB : ‖blaschkeDeleted a n z‖ ≤ 1 :=
    norm_infiniteBlaschkeProduct_le_one _ (norm_update_zero_lt_one ha n)
      (summable_update_zero hbl n) hz
  have hc : ‖-((‖a n‖ : ℂ) / a n)‖ ≤ 1 := by
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hden : ρ * (1 - ‖a n‖) ≤ ‖z * (1 - (starRingEnd ℂ) (a n) * z)‖ := by
    rw [norm_mul]
    exact mul_le_mul hzρ (one_sub_norm_le_norm_one_sub_conj_mul hz.le) hd.le (norm_nonneg _)
  rw [poleQuotient, norm_div, norm_mul]
  exact div_le_div₀ zero_le_one (mul_le_one₀ hc (norm_nonneg _) hB) (by positivity) hden

theorem differentiableOn_poleQuotient (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖)
    (n : ℕ) : DifferentiableOn ℂ (poleQuotient a n) (ball (0 : ℂ) 1 \ {0}) := by
  have hB := differentiableOn_infiniteBlaschkeProduct _ (norm_update_zero_lt_one ha n)
    (summable_update_zero hbl n)
  have hQ : poleQuotient a n = fun z => -((‖a n‖ : ℂ) / a n) *
      infiniteBlaschkeProduct (Function.update a n 0) z / (z * (1 - (starRingEnd ℂ) (a n) * z)) :=
    rfl
  rw [hQ]
  refine ((hB.const_mul _).mono diff_subset).div (by fun_prop) fun z hz => ?_
  exact mul_ne_zero hz.2 (one_sub_conj_mul_ne_zero (ha n) (mem_ball_zero_iff.mp hz.1).le)

/-- The deleted product does not vanish at the deleted zero. -/
theorem blaschkeDeleted_self_ne_zero (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖)
    (hinj : Function.Injective a) {n : ℕ} (han : a n ≠ 0) : blaschkeDeleted a n (a n) ≠ 0 := by
  have hsum : Summable fun m => ‖normalizedBlaschkeFactor (Function.update a n 0 m) (a n) - 1‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => norm_normalizedBlaschkeFactor_sub_one_le (norm_update_zero_lt_one ha n m)
        (norm_nonneg _) (ha n) le_rfl)
      ((summable_update_zero hbl n).mul_left _)
  have e : ∀ x : ℂ, 1 + (x - 1) = x := fun x => by ring
  have hne : ∀ m, 1 + (normalizedBlaschkeFactor (Function.update a n 0 m) (a n) - 1) ≠ 0 := by
    intro m
    rw [e]
    rcases eq_or_ne m n with rfl | hmn
    · rw [Function.update_self, normalizedBlaschkeFactor_zero_left]
      exact han
    · rw [Function.update_of_ne hmn]
      exact normalizedBlaschkeFactor_ne_zero (ha m) (ha n) (hinj.ne hmn.symm)
  have h := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [e] at h
  exact h

theorem poleQuotient_self_ne_zero (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖)
    (hinj : Function.Injective a) {n : ℕ} (han : a n ≠ 0) : poleQuotient a n (a n) ≠ 0 := by
  rw [poleQuotient]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr han)) han))
    (blaschkeDeleted_self_ne_zero ha hbl hinj han))
    (mul_ne_zero han (one_sub_conj_mul_ne_zero (ha n) (ha n).le))

theorem infiniteBlaschkeProduct_self_eq_zero (ha : ∀ n, ‖a n‖ < 1)
    (hbl : Summable fun n => 1 - ‖a n‖) {n : ℕ} (han : a n ≠ 0) :
    infiniteBlaschkeProduct a (a n) = 0 := by
  rw [← sub_mul_poleQuotient ha hbl han (ha n) han, sub_self, zero_mul]

/-- The pole quotient of `a_m` vanishes at every other pole. -/
theorem poleQuotient_eq_zero_of_ne (ha : ∀ n, ‖a n‖ < 1) (hbl : Summable fun n => 1 - ‖a n‖)
    (hinj : Function.Injective a) (ha0 : ∀ n, a n ≠ 0) {m n : ℕ} (hmn : m ≠ n) :
    poleQuotient a m (a n) = 0 := by
  have h := sub_mul_poleQuotient ha hbl (ha0 n) (ha n) (ha0 m)
  rw [infiniteBlaschkeProduct_self_eq_zero ha hbl (ha0 n)] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hinj.ne hmn.symm))

end Pole

/-! ### 4. Zero radial limits on an annulus -/

theorem circleIntegral_zero_eq_intervalIntegral (f : ℂ → ℂ) (s : ℝ) :
    (∮ z in C(0, s), f z) =
      ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 s θ * I) * f (circleMap 0 s θ) := by
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]

/-- **Circle integrals inherit zero radial limits.** If `f` and the weight `w` are continuous and
bounded on `s₀ < |z| < 1` and `f(r e^{iθ}) → 0` as `r → 1⁻` for almost every `θ`, then
`∮_{|z|=s} w f → 0` as `s → 1⁻`. -/
theorem tendsto_circleIntegral_of_radial {f w : ℂ → ℂ} {s₀ M W : ℝ} (hs₀ : 0 ≤ s₀)
    (hs₀1 : s₀ < 1) (hf : ContinuousOn f (annulusAt 0 s₀ 1))
    (hw : ContinuousOn w (annulusAt 0 s₀ 1)) (hfM : ∀ z ∈ annulusAt 0 s₀ 1, ‖f z‖ ≤ M)
    (hwW : ∀ z ∈ annulusAt 0 s₀ 1, ‖w z‖ ≤ W)
    (hrad : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))),
      Tendsto (fun r : ℝ => f ((r : ℂ) * cexp (θ * I))) (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun s : ℝ => ∮ z in C(0, s), w z * f z) (𝓝[<] 1) (𝓝 0) := by
  have hcm : ∀ s θ : ℝ, circleMap 0 s θ = (s : ℂ) * cexp (θ * I) := fun s θ => by
    simp [circleMap]
  have hnorm : ∀ s θ : ℝ, 0 ≤ s → ‖circleMap 0 s θ‖ = s := fun s θ hs => by
    rw [hcm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hs]
  have hmem : ∀ s θ : ℝ, s₀ < s → s < 1 → circleMap 0 s θ ∈ annulusAt 0 s₀ 1 :=
    fun s θ h0 h1 => by
      rw [mem_annulusAt, sub_zero, hnorm s θ (hs₀.trans h0.le)]
      exact ⟨h0, h1⟩
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), s₀ < s ∧ s < 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hs₀1)).and self_mem_nhdsWithin
  have hrw : (fun s : ℝ => ∮ z in C(0, s), w z * f z) = fun s => ∫ θ in (0 : ℝ)..2 * π,
      (circleMap 0 s θ * I) * (w (circleMap 0 s θ) * f (circleMap 0 s θ)) :=
    funext fun s => circleIntegral_zero_eq_intervalIntegral _ s
  have key : Tendsto (fun s => ∫ θ in (0 : ℝ)..2 * π,
      (circleMap 0 s θ * I) * (w (circleMap 0 s θ) * f (circleMap 0 s θ))) (𝓝[<] 1)
      (𝓝 (∫ _ in (0 : ℝ)..2 * π, (0 : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => W * M) ?_
      ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with s ⟨hs0, hs1⟩
      exact (((continuous_circleMap 0 s).mul continuous_const).mul
        ((hw.comp_continuous (continuous_circleMap 0 s) fun θ => hmem s θ hs0 hs1).mul
          (hf.comp_continuous (continuous_circleMap 0 s) fun θ => hmem s θ hs0 hs1))).aestronglyMeasurable
    · filter_upwards [hev] with s ⟨hs0, hs1⟩
      refine Eventually.of_forall fun θ _ => ?_
      have hθ := hmem s θ hs0 hs1
      have hwf : ‖w (circleMap 0 s θ)‖ * ‖f (circleMap 0 s θ)‖ ≤ W * M :=
        mul_le_mul (hwW _ hθ) (hfM _ hθ) (norm_nonneg _) ((norm_nonneg _).trans (hwW _ hθ))
      rw [norm_mul, norm_mul, norm_mul, hnorm s θ (hs₀.trans hs0.le), Complex.norm_I, mul_one]
      calc s * (‖w (circleMap 0 s θ)‖ * ‖f (circleMap 0 s θ)‖)
          ≤ 1 * (‖w (circleMap 0 s θ)‖ * ‖f (circleMap 0 s θ)‖) :=
            mul_le_mul_of_nonneg_right hs1.le (by positivity)
        _ ≤ W * M := by rw [one_mul]; exact hwf
    · rw [ae_restrict_iff' measurableSet_Ioc] at hrad
      filter_upwards [hrad] with θ hθ hmemθ
      rw [uIoc_of_le (by positivity)] at hmemθ
      have hbd : ∀ᶠ s in 𝓝[<] (1 : ℝ),
          ‖(circleMap 0 s θ * I) * (w (circleMap 0 s θ) * f (circleMap 0 s θ))‖ ≤
            W * ‖f ((s : ℂ) * cexp (θ * I))‖ := by
        filter_upwards [hev] with s ⟨hs0, hs1⟩
        have hθ' := hmem s θ hs0 hs1
        have hW0 : 0 ≤ W := (norm_nonneg _).trans (hwW _ hθ')
        rw [norm_mul, norm_mul, norm_mul, hnorm s θ (hs₀.trans hs0.le), Complex.norm_I, mul_one,
          ← hcm]
        calc s * (‖w (circleMap 0 s θ)‖ * ‖f (circleMap 0 s θ)‖)
            ≤ 1 * (W * ‖f (circleMap 0 s θ)‖) :=
              mul_le_mul hs1.le (mul_le_mul_of_nonneg_right (hwW _ hθ') (norm_nonneg _))
                (by positivity) zero_le_one
          _ = W * ‖f (circleMap 0 s θ)‖ := one_mul _
      have hlim : Tendsto (fun s : ℝ => W * ‖f ((s : ℂ) * cexp (θ * I))‖) (𝓝[<] 1) (𝓝 0) := by
        simpa using (hθ hmemθ).norm.const_mul W
      exact squeeze_zero_norm' hbd hlim
  rw [intervalIntegral.integral_zero] at key
  rw [hrw]
  exact key

/-- A circle integral of a function holomorphic on `t₀ < |z| < 1` that tends to `0` as the radius
tends to `1` vanishes on every circle of the annulus: it does not depend on the radius. -/
theorem circleIntegral_eq_zero_of_tendsto {f : ℂ → ℂ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hf : DifferentiableOn ℂ f (annulusAt 0 t₀ 1))
    (hlim : Tendsto (fun s : ℝ => ∮ z in C(0, s), f z) (𝓝[<] 1) (𝓝 0)) {s : ℝ} (hs0 : t₀ < s)
    (hs1 : s < 1) : (∮ z in C(0, s), f z) = 0 := by
  have hconst : ∀ᶠ s' in 𝓝[<] (1 : ℝ), (∮ z in C(0, s'), f z) = ∮ z in C(0, s), f z := by
    filter_upwards [(eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hs1)).and
      self_mem_nhdsWithin] with s' ⟨hs', hs'1⟩
    have hsub : closedBall (0 : ℂ) s' \ ball 0 s ⊆ annulusAt 0 t₀ 1 :=
      closedAnnulus_subset hs0 hs'1
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (ht₀.trans_lt hs0)
      (le_of_lt hs') countable_empty (hf.continuousOn.mono hsub) fun z hz => ?_
    exact hf.differentiableAt ((isOpen_annulusAt 0 t₀ 1).mem_nhds
      (hsub ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩))
  exact (tendsto_nhds_unique hlim
    ((tendsto_const_nhds (x := ∮ z in C(0, s), f z)).congr' (hconst.mono fun _ h => h.symm))).symm

/-- Weighted circle integrals of a function with zero radial limits vanish, for weights holomorphic
on `t₀ < |z| < 1` and bounded near the circle. -/
theorem circleIntegral_mul_eq_zero_of_radial {Φ w : ℂ → ℂ} {ρ s₀ t₀ t₁ M W : ℝ} (hρ : 0 < ρ)
    (hs₀ : ρ ≤ s₀) (hs₀1 : s₀ < 1) (hΦ : DifferentiableOn ℂ Φ (annulusAt 0 ρ 1))
    (hM : ∀ z ∈ annulusAt 0 s₀ 1, ‖Φ z‖ ≤ M)
    (hrad : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))),
      Tendsto (fun r : ℝ => Φ ((r : ℂ) * cexp (θ * I))) (𝓝[<] 1) (𝓝 0))
    (ht₀ : ρ ≤ t₀) (ht₁ : t₀ ≤ t₁) (ht₁1 : t₁ < 1) (hw : DifferentiableOn ℂ w (annulusAt 0 t₀ 1))
    (hW : ∀ z ∈ annulusAt 0 t₁ 1, ‖w z‖ ≤ W) {s : ℝ} (hs0 : t₀ < s) (hs1 : s < 1) :
    (∮ z in C(0, s), w z * Φ z) = 0 := by
  have hmono : ∀ {b c : ℝ}, b ≤ c → annulusAt (0 : ℂ) c 1 ⊆ annulusAt 0 b 1 :=
    fun hbc _ hz => ⟨hbc.trans_lt hz.1, hz.2⟩
  have hdiff : DifferentiableOn ℂ (fun z => w z * Φ z) (annulusAt 0 t₀ 1) :=
    hw.mul (hΦ.mono (hmono ht₀))
  refine circleIntegral_eq_zero_of_tendsto (hρ.le.trans ht₀) hdiff ?_ hs0 hs1
  have h1 : s₀ ≤ max s₀ t₁ := le_max_left _ _
  have h2 : t₁ ≤ max s₀ t₁ := le_max_right _ _
  exact tendsto_circleIntegral_of_radial (hρ.le.trans (hs₀.trans h1)) (max_lt hs₀1 ht₁1)
    (hΦ.continuousOn.mono (hmono (hs₀.trans h1))) (hw.continuousOn.mono (hmono (ht₁.trans h2)))
    (fun z hz => hM z (hmono h1 hz)) (fun z hz => hW z (hmono h2 hz)) hrad

/-- **Zero radial limits force zero on an annulus.** A function holomorphic on `ρ < |z| < 1`,
bounded on `s₀ < |z| < 1`, whose radial limits vanish at almost every point of the unit circle,
vanishes identically. The outer Cauchy integral and every Laurent coefficient of the inner part are
radius-independent circle integrals tending to `0`. -/
theorem eqOn_zero_of_radial_tendsto_zero {Φ : ℂ → ℂ} {ρ s₀ M : ℝ} (hρ : 0 < ρ) (hs₀ : ρ ≤ s₀)
    (hs₀1 : s₀ < 1) (hΦ : DifferentiableOn ℂ Φ (annulusAt 0 ρ 1))
    (hM : ∀ z ∈ annulusAt 0 s₀ 1, ‖Φ z‖ ≤ M)
    (hrad : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))),
      Tendsto (fun r : ℝ => Φ ((r : ℂ) * cexp (θ * I))) (𝓝[<] 1) (𝓝 0)) :
    EqOn Φ 0 (annulusAt 0 ρ 1) := by
  intro z hz
  have hz' := hz
  rw [mem_annulusAt, sub_zero] at hz'
  obtain ⟨hz0, hz1⟩ := hz'
  set r := (ρ + ‖z‖) / 2
  set R := (‖z‖ + 1) / 2
  have hρr : ρ < r := by linarith
  have hrz : r < ‖z - 0‖ := by rw [sub_zero]; linarith
  have hzR : ‖z - 0‖ < R := by rw [sub_zero]; linarith
  have hR1 : R < 1 := by linarith
  have hcf := annulusCauchyFormula hρ hρr (by linarith : r < R) hR1 hΦ hrz hzR
  -- the outer Cauchy integral vanishes
  have hout : (∮ ζ in C(0, R), (ζ - z)⁻¹ • Φ ζ) = 0 := by
    simp only [smul_eq_mul]
    refine circleIntegral_mul_eq_zero_of_radial (w := fun ζ => (ζ - z)⁻¹) (t₀ := ‖z‖) (t₁ := R)
      (W := 2 / (1 - ‖z‖)) hρ hs₀ hs₀1 hΦ hM hrad hz0.le (by linarith) hR1 ?_ ?_ (by linarith) hR1
    · refine DifferentiableOn.inv (by fun_prop) fun ζ hζ h => ?_
      rw [mem_annulusAt, sub_zero] at hζ
      rw [sub_eq_zero] at h
      rw [h] at hζ
      exact lt_irrefl _ hζ.1
    · intro ζ hζ
      rw [mem_annulusAt, sub_zero] at hζ
      have hpos : 0 < (1 - ‖z‖) / 2 := by linarith
      have hdist : (1 - ‖z‖) / 2 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le ζ z
        linarith [hζ.1]
      rw [norm_inv, ← inv_div]
      exact inv_anti₀ hpos hdist
  -- the inner Cauchy integral vanishes: every Laurent coefficient is zero
  have hin : (∮ ζ in C(0, r), (ζ - z)⁻¹ • Φ ζ) = 0 := by
    have hr0 : 0 < r := by linarith
    have hsph : sphere (0 : ℂ) r ⊆ annulusAt 0 ρ 1 := fun ζ hζ => by
      rw [mem_sphere, dist_zero_right] at hζ
      rw [mem_annulusAt, sub_zero, hζ]
      exact ⟨hρr, by linarith⟩
    obtain ⟨K, hK⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
      (hΦ.continuousOn.mono hsph)
    have hsum := hasSum_laurentInner hr0 (le_max_right K 0) (hΦ.continuousOn.mono hsph)
      (fun ζ hζ => (hK ζ hζ).trans (le_max_left _ _)) hrz
    have hcoeff : ∀ k, annulusLaurentCoeff Φ 0 r k = 0 := fun k => by
      have h : (∮ ζ in C(0, r), ((ζ - 0) ^ k) • Φ ζ) = 0 := by
        simp only [smul_eq_mul]
        refine circleIntegral_mul_eq_zero_of_radial (w := fun ζ => (ζ - 0) ^ k) (t₀ := ρ)
          (t₁ := ρ) (W := 1) hρ hs₀ hs₀1 hΦ hM hrad le_rfl le_rfl (by linarith) (by fun_prop)
          (fun ζ hζ => ?_) hρr (by linarith)
        rw [mem_annulusAt] at hζ
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hζ.2.le
      rw [annulusLaurentCoeff, h, smul_zero]
    have hzero : laurentInner Φ 0 r z = 0 := by
      refine hsum.unique ?_
      simp only [hcoeff, smul_zero]
      exact hasSum_zero
    rw [laurentInner, neg_eq_zero, smul_eq_zero] at hzero
    exact hzero.resolve_left (inv_ne_zero annulusTwoPiI_ne_zero)
  rw [hout, hin, sub_zero] at hcf
  exact (smul_eq_zero.mp hcf.symm).resolve_left annulusTwoPiI_ne_zero

/-! ### 5. Permeability -/

/-- **Light Blaschke walls are permeable.** Let the poles `a_n` be distinct, with
`ρ < |a_n| < 1` and `Σ (1 − |a_n|) < ∞`, and the masses light, `Σ |ν_n|/(1 − |a_n|) < ∞`. If
`Σ ν_n/(u − a_n)` agrees on `1 < |u| < R` with a function holomorphic on `ρ < |u| < R`, then every
mass vanishes. -/
theorem masses_eq_zero_of_cauchy_eq_outside {a ν : ℕ → ℂ} {E : ℂ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ)
    (hρa : ∀ n, ρ < ‖a n‖) (ha : ∀ n, ‖a n‖ < 1) (hinj : Function.Injective a)
    (hbl : Summable fun n => 1 - ‖a n‖) (hlight : Summable fun n => ‖ν n‖ / (1 - ‖a n‖))
    (hR : 1 < R) (hE : DifferentiableOn ℂ E (annulusAt 0 ρ R))
    (heq : ∀ u : ℂ, 1 < ‖u‖ → ‖u‖ < R → ∑' m, ν m / (u - a m) = E u) (n : ℕ) : ν n = 0 := by
  have ha0 : ∀ m, a m ≠ 0 := fun m h => by
    have := hρa m
    rw [h, norm_zero] at this
    linarith
  have hρ1 : ρ < 1 := (hρa 0).trans (ha 0)
  have hEcont : ∀ ζ : ℂ, ‖ζ‖ = 1 → ContinuousAt E ζ := fun ζ hζ =>
    (hE.differentiableAt ((isOpen_annulusAt 0 ρ R).mem_nhds
      (by rw [mem_annulusAt, sub_zero, hζ]; exact ⟨hρ1, hR⟩))).continuousAt
  -- the transform agrees with `E` on the circle
  have hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∑' m, ν m / (ζ - a m) = E ζ := by
    intro ζ hζ
    have hpath : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ) * ζ) (𝓝[>] 0) (𝓝 ζ) := by
      have h := ((by fun_prop : Continuous fun t : ℝ => ((1 + t : ℝ) : ℂ) * ζ).tendsto 0).mono_left
        nhdsWithin_le_nhds
      simpa using h
    have hin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        1 < ‖((1 + t : ℝ) : ℂ) * ζ‖ ∧ ‖((1 + t : ℝ) : ℂ) * ζ‖ < R := by
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (by linarith : (0 : ℝ) < R - 1))] with t (ht : 0 < t) (htR : t < R - 1)
      rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      constructor <;> linarith
    have hG := ((continuousOn_cauchy_outside ha hlight) ζ (by rw [mem_setOf_eq, hζ])).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hpath, hin.mono fun t ht => ht.1.le⟩)
    exact tendsto_nhds_unique hG
      (((hEcont ζ hζ).tendsto.comp hpath).congr' (hin.mono fun t ht => (heq _ ht.1 ht.2).symm))
  set B := infiniteBlaschkeProduct a
  set Q := poleQuotient a
  set Φ : ℂ → ℂ := fun z => ∑' m, ν m * Q m z - B z * E z with hΦdef
  have hsub1 : annulusAt (0 : ℂ) ρ 1 ⊆ ball 0 1 \ {0} := fun z hz => by
    rw [mem_annulusAt, sub_zero] at hz
    refine ⟨mem_ball_zero_iff.mpr hz.2, fun h => ?_⟩
    rw [mem_singleton_iff] at h
    rw [h, norm_zero] at hz
    linarith [hz.1]
  have hQb : ∀ m, ∀ z ∈ annulusAt (0 : ℂ) ρ 1, ‖ν m * Q m z‖ ≤ ‖ν m‖ / (1 - ‖a m‖) / ρ := by
    intro m z hz
    rw [mem_annulusAt, sub_zero] at hz
    have hd : 0 < 1 - ‖a m‖ := sub_pos.mpr (ha m)
    rw [norm_mul]
    calc ‖ν m‖ * ‖Q m z‖ ≤ ‖ν m‖ * (1 / (ρ * (1 - ‖a m‖))) :=
          mul_le_mul_of_nonneg_left (norm_poleQuotient_le ha hbl hρ hz.1.le hz.2 m) (norm_nonneg _)
      _ = ‖ν m‖ / (1 - ‖a m‖) / ρ := by field_simp
  have hΦd : DifferentiableOn ℂ Φ (annulusAt 0 ρ 1) := by
    refine (differentiableOn_tsum_of_summable_norm (hlight.div_const ρ)
      (fun m => ((differentiableOn_poleQuotient ha hbl m).mono hsub1).const_mul (ν m))
      (isOpen_annulusAt 0 ρ 1) hQb).sub
      (((differentiableOn_infiniteBlaschkeProduct a ha hbl).mono
        (hsub1.trans diff_subset)).mul (hE.mono fun z hz => ⟨hz.1, hz.2.trans hR⟩))
  -- boundedness near the circle
  set s₀ := (ρ + 1) / 2
  have hcpt : closedBall (0 : ℂ) 1 \ ball 0 s₀ ⊆ annulusAt 0 ρ R :=
    closedAnnulus_subset (by linarith) hR
  obtain ⟨ME, hME⟩ := ((isCompact_closedBall 0 1).diff isOpen_ball).exists_bound_of_continuousOn
    (hE.continuousOn.mono hcpt)
  have hΦM : ∀ z ∈ annulusAt 0 s₀ 1, ‖Φ z‖ ≤ (∑' m, ‖ν m‖ / (1 - ‖a m‖) / ρ) + ME := by
    intro z hz
    have hz' := hz
    rw [mem_annulusAt, sub_zero] at hz'
    have hzA : z ∈ annulusAt (0 : ℂ) ρ 1 := ⟨by rw [sub_zero]; linarith [hz'.1], hz.2⟩
    have hzK : z ∈ closedBall (0 : ℂ) 1 \ ball 0 s₀ :=
      ⟨mem_closedBall_zero_iff.mpr hz'.2.le, fun h => by
        rw [mem_ball_zero_iff] at h
        linarith [hz'.1]⟩
    have h1 : ‖∑' m, ν m * Q m z‖ ≤ ∑' m, ‖ν m‖ / (1 - ‖a m‖) / ρ :=
      tsum_of_norm_bounded (hlight.div_const ρ).hasSum fun m => hQb m z hzA
    have h2 : ‖B z * E z‖ ≤ ME := by
      rw [norm_mul]
      exact mul_le_of_le_one_of_le' (norm_infiniteBlaschkeProduct_le_one a ha hbl hz'.2)
        (hME z hzK) (norm_nonneg _) ((norm_nonneg _).trans (hME z hzK))
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  -- zero radial limits
  have hrad : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))),
      Tendsto (fun r : ℝ => Φ ((r : ℂ) * cexp (θ * I))) (𝓝[<] 1) (𝓝 0) := by
    filter_upwards [ae_eventually_notMem_radialShadow ha hbl hρ hρa] with θ hθ
    have he : ‖cexp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have hpath : Tendsto (fun r : ℝ => (r : ℂ) * cexp (θ * I)) (𝓝[<] 1) (𝓝 (cexp (θ * I))) := by
      have h := ((by fun_prop : Continuous fun r : ℝ => (r : ℂ) * cexp (θ * I)).tendsto
        1).mono_left nhdsWithin_le_nhds
      simpa using h
    have hdiff : Tendsto (fun r : ℝ => ∑' m, ν m / ((r : ℂ) * cexp (θ * I) - a m) -
        E ((r : ℂ) * cexp (θ * I))) (𝓝[<] 1) (𝓝 0) := by
      have h := (tendsto_cauchy_radial ha hlight hθ).sub ((hEcont _ he).tendsto.comp hpath)
      rwa [hbd _ he, sub_self] at h
    refine squeeze_zero_norm' ?_ (by simpa using hdiff.norm)
    filter_upwards [eventually_radial_far ha hθ, eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds hρ1), self_mem_nhdsWithin] with r ⟨hr0, hfar⟩ (hrρ : ρ < r) (hr1 : r < 1)
    set z := (r : ℂ) * cexp (θ * I)
    have hz : ‖z‖ = r := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]
    have hz0 : z ≠ 0 := fun h => by
      rw [h, norm_zero] at hz
      linarith
    have hne : ∀ m, z - a m ≠ 0 := fun m h => by
      have := hfar m
      rw [h, norm_zero] at this
      linarith [ha m]
    have hQz : ∀ m, Q m z = B z / (z - a m) := fun m =>
      (eq_div_iff (hne m)).mpr (by
        rw [mul_comm]
        exact sub_mul_poleQuotient ha hbl hz0 (by rw [hz]; exact hr1) (ha0 m))
    have hΦz : Φ z = B z * (∑' m, ν m / (z - a m) - E z) := by
      simp only [hΦdef, hQz]
      rw [mul_sub, ← tsum_mul_left]
      congr 2
      funext m
      ring
    rw [hΦz, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (norm_infiniteBlaschkeProduct_le_one a ha hbl (by rw [hz]; exact hr1))
  -- `Φ` vanishes, and its value at `a_n` is `ν_n` times a nonzero number
  have hzero := eqOn_zero_of_radial_tendsto_zero hρ (s₀ := s₀) (by linarith) (by linarith) hΦd hΦM
    hrad
  have han : a n ∈ annulusAt (0 : ℂ) ρ 1 := by
    rw [mem_annulusAt, sub_zero]
    exact ⟨hρa n, ha n⟩
  have hΦn : Φ (a n) = ν n * Q n (a n) := by
    simp only [hΦdef]
    rw [infiniteBlaschkeProduct_self_eq_zero ha hbl (ha0 n), zero_mul, sub_zero,
      tsum_eq_single n fun m hm => by
        rw [poleQuotient_eq_zero_of_ne ha hbl hinj ha0 hm, mul_zero]]
  have h := hzero han
  rw [hΦn, Pi.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_right (poleQuotient_self_ne_zero ha hbl hinj (ha0 n))

end

end GaloisForLFunctions.HTGeometry
