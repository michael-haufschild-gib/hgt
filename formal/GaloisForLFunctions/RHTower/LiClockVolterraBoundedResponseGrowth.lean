import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert

/-!
# Upper-bounded Volterra responses force square-root exponential kernel ceilings

For continuous real functions `F` and `B`, assume `B` is nonnegative on the
half-line and `F ⋆ B = t B'`. An eventual upper bound on `F` globalizes by
compactness. The signed differential comparison for
`V(u) = (∫ s in 0..u², B s) + 2u B(u²)` then bounds `B(t)` by
`K exp(R sqrt(t))` for every `t ≥ 1`.

Consequently, faster-than-every-square-root-exponential growth of `B` forces
arbitrarily high positive values of `F` on every tail. No monotonicity of `B`
or continuity of its derivative is required.
-/

open Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- A continuous function with an eventual upper bound has a positive global
upper bound on the half-line. -/
theorem liClock_exists_global_upperBound_of_eventually_bddAbove {F : ℝ → ℝ}
    (hF : Continuous F) (hupper : ∃ m : ℝ, ∀ᶠ t : ℝ in atTop, F t ≤ m) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → F t ≤ M := by
  obtain ⟨m, hm⟩ := hupper
  obtain ⟨T, hT⟩ := eventually_atTop.mp hm
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max T 0))).bddAbove_image
    hF.continuousOn
  refine ⟨max 1 (max m C), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  by_cases htt : t ≤ max T 0
  · exact (hC ⟨t, ⟨ht, htt⟩, rfl⟩).trans
      ((le_max_right m C).trans (le_max_right _ _))
  · exact (hT t ((le_max_left T 0).trans (le_of_not_ge htt))).trans
      ((le_max_left m C).trans (le_max_right _ _))

/-- Global upper response bounds pass through a nonnegative Volterra kernel. -/
theorem liClockVolterra_convolution_le_mul_integral_of_upperBound {F B : ℝ → ℝ}
    (hF : Continuous F) (hB : Continuous B)
    (hB0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ B t) (M : ℝ)
    (hFM : ∀ t : ℝ, 0 ≤ t → F t ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, F s * B (t - s)) ≤ M * ∫ s in (0 : ℝ)..t, B s := by
  have hc : Continuous (fun s : ℝ => B (t - s)) :=
    hB.comp (continuous_const.sub continuous_id)
  have hle := intervalIntegral.integral_mono_on (μ := volume) ht
    ((hF.mul hc).intervalIntegrable 0 t)
    ((continuous_const.mul hc).intervalIntegrable 0 t)
    (fun s hs => mul_le_mul_of_nonneg_right (hFM s hs.1)
      (hB0 (t - s) (by linarith [hs.2])))
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, M * B (t - s) := hle
    _ = M * ∫ s in (0 : ℝ)..t, B (t - s) := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [intervalIntegral.integral_comp_sub_left]; simp

private theorem growthCeiling_of_differentialBound {B : ℝ → ℝ}
    (hB : Continuous B) (hdB : Differentiable ℝ B)
    (hB0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ B t) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → t * deriv B t ≤ M * ∫ s in (0 : ℝ)..t, B s) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧
      ∀ t : ℝ, 1 ≤ t → B t ≤ K * Real.exp (R * Real.sqrt t) := by
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, B s
  have hH (t : ℝ) : HasDerivAt H (B t) t :=
    intervalIntegral.integral_hasDerivAt_right (hB.intervalIntegrable (μ := volume) 0 t)
      hB.stronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt
  have hH0 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ H t :=
    intervalIntegral.integral_nonneg ht (fun s hs => hB0 s hs.1)
  let V : ℝ → ℝ := fun u => H (u ^ 2) + 2 * u * B (u ^ 2)
  let V' : ℝ → ℝ := fun u =>
    2 * u * B (u ^ 2) + 2 * B (u ^ 2) + 4 * u ^ 2 * deriv B (u ^ 2)
  have hdV (u : ℝ) : HasDerivAt V (V' u) u := by
    have hY := (hH (u ^ 2)).comp u ((hasDerivAt_id u).pow 2)
    have hZ := ((hasDerivAt_id u).const_mul 2).mul
      ((hdB (u ^ 2)).hasDerivAt.comp u ((hasDerivAt_id u).pow 2))
    have hraw := (hY.add hZ).congr_deriv (g' := V' u) (by
      dsimp only [V', Function.comp_def, id_eq]
      norm_num
      ring)
    simpa only [V, Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      using! hraw
  have hVcont : Continuous V := continuous_iff_continuousAt.mpr fun u => (hdV u).continuousAt
  have hV0 (u : ℝ) (hu : 0 ≤ u) : 0 ≤ V u := by
    dsimp [V]
    exact add_nonneg (hH0 _ (sq_nonneg _))
      (mul_nonneg (by positivity) (hB0 _ (sq_nonneg _)))
  let R : ℝ := max 2 (4 * M)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hVbound (u : ℝ) (hu : 1 ≤ u) : V' u ≤ R * V u := by
    have hb := hbound (u ^ 2) (sq_nonneg u)
    have hnonneg := hB0 (u ^ 2) (sq_nonneg u)
    have hprim := hH0 (u ^ 2) (sq_nonneg u)
    have hR2 : 2 ≤ R := le_max_left _ _
    have hRM : 4 * M ≤ R := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_right hR2
      (show 0 ≤ 2 * u * B (u ^ 2) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hRM hprim
    have h3 := mul_nonneg (show 0 ≤ u - 1 by linarith) hnonneg
    dsimp [V, V', H] at *
    nlinarith
  have hVupper (u : ℝ) (hu : 1 ≤ u) : V u ≤ V 1 * Real.exp (R * (u - 1)) := by
    have hg := le_gronwallBound_of_liminf_deriv_right_le
      (f := V) (f' := V') (δ := V 1) (K := R) (ε := 0) (a := 1) (b := u)
      hVcont.continuousOn
      (fun x _hx r hr => by
        have hs := ((hdV x).hasDerivWithinAt (s := Ici x)).liminf_right_slope_le hr
        simpa [slope, smul_eq_mul] using hs)
      le_rfl (fun x hx => by simpa using hVbound x hx.1)
    simpa only [gronwallBound_ε0] using hg u ⟨hu, le_rfl⟩
  let K : ℝ := V 1 + 1
  have hV1 : 0 ≤ V 1 := hV0 1 (by norm_num)
  refine ⟨K, R, by dsimp [K]; linarith, hR, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  have hu : 1 ≤ Real.sqrt t := by
    simpa using Real.sqrt_le_sqrt ht
  have hlower : B ((Real.sqrt t) ^ 2) ≤ V (Real.sqrt t) := by
    have hb := hB0 ((Real.sqrt t) ^ 2) (sq_nonneg _)
    have hh := hH0 ((Real.sqrt t) ^ 2) (sq_nonneg _)
    have hm := mul_nonneg (show 0 ≤ 2 * Real.sqrt t - 1 by linarith) hb
    dsimp [V]
    nlinarith
  have he : Real.exp (R * (Real.sqrt t - 1)) ≤ Real.exp (R * Real.sqrt t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    B t = B ((Real.sqrt t) ^ 2) := by rw [Real.sq_sqrt ht0]
    _ ≤ V (Real.sqrt t) := hlower
    _ ≤ V 1 * Real.exp (R * (Real.sqrt t - 1)) := hVupper _ hu
    _ ≤ V 1 * Real.exp (R * Real.sqrt t) := mul_le_mul_of_nonneg_left he hV1
    _ ≤ K * Real.exp (R * Real.sqrt t) :=
      mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (Real.exp_pos _).le

/-- An eventually upper-bounded continuous response forces a square-root
exponential kernel ceiling for every `t ≥ 1`. -/
theorem liClockVolterra_growthCeiling_of_eventually_bddAbove {F B : ℝ → ℝ}
    (hF : Continuous F) (hB : Continuous B) (hdB : Differentiable ℝ B)
    (hB0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ B t)
    (hconv : ∀ t : ℝ, 0 ≤ t →
      (∫ s in (0 : ℝ)..t, F s * B (t - s)) = t * deriv B t)
    (hupper : ∃ M : ℝ, ∀ᶠ t : ℝ in atTop, F t ≤ M) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧
      ∀ t : ℝ, 1 ≤ t → B t ≤ K * Real.exp (R * Real.sqrt t) := by
  obtain ⟨M, _hM, hFM⟩ := liClock_exists_global_upperBound_of_eventually_bddAbove hF hupper
  apply growthCeiling_of_differentialBound hB hdB hB0 (M := M)
  intro t ht
  rw [← hconv t ht]
  exact liClockVolterra_convolution_le_mul_integral_of_upperBound hF hB hB0 M hFM ht

/-- Faster-than-every-square-root-exponential kernel growth forces arbitrarily
high positive response values on every tail. -/
theorem liClockVolterra_response_unboundedAbove_cofinally_of_fastGrowth {F B : ℝ → ℝ}
    (hF : Continuous F) (hB : Continuous B) (hdB : Differentiable ℝ B)
    (hB0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ B t)
    (hconv : ∀ t : ℝ, 0 ≤ t →
      (∫ s in (0 : ℝ)..t, F s * B (t - s)) = t * deriv B t)
    (hgrowth : ∀ R : ℝ, Tendsto (fun t : ℝ => B t / Real.exp (R * Real.sqrt t)) atTop atTop) :
    ∀ M T₀ : ℝ, ∃ t > T₀, M < F t := by
  intro M T₀
  by_contra h
  have hupper : ∃ m : ℝ, ∀ᶠ t : ℝ in atTop, F t ≤ m := by
    refine ⟨M, ?_⟩
    filter_upwards [eventually_gt_atTop T₀] with t ht
    by_contra hn
    exact h ⟨t, ht, lt_of_not_ge hn⟩
  obtain ⟨K, R, _hK, _hR, hceil⟩ :=
    liClockVolterra_growthCeiling_of_eventually_bddAbove hF hB hdB hB0 hconv hupper
  have hlarge : ∀ᶠ t : ℝ in atTop, K < B t / Real.exp (R * Real.sqrt t) :=
    (hgrowth R).eventually_gt_atTop K
  obtain ⟨t, ht, hlt⟩ := (hlarge.and (eventually_ge_atTop (1 : ℝ))).exists
  have hc := hceil t hlt
  have hgt := (lt_div_iff₀ (Real.exp_pos _)).mp ht
  linarith

end
end RHTower
