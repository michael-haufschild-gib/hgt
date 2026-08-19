import Mathlib

/-!
# Analyticity of a Mellin transform on a half plane

A function on `(1, ∞)` that is interval integrable from `1` and bounded by `x^ρ log x` past a
threshold has a Mellin transform `∫_1^∞ f(x) x^{-w} dx` which converges and is holomorphic on the
half plane `Re w > ρ + 1`.  Both statements are read off from mathlib's Mellin calculus after
extending `f` by zero to `(0, 1]`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics

namespace GaloisForLFunctions.HTGeometry

/-- The Mellin transform of a function supported on `(1, ∞)`. -/
def halfPlaneMellin (f : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x in Set.Ioi (1:ℝ), f x * (x : ℂ) ^ (-w)

theorem halfPlaneMellin_eq_mellin (f : ℝ → ℂ) (w : ℂ) :
    halfPlaneMellin f w = mellin (Set.indicator (Set.Ioi (1:ℝ)) f) (1 - w) := by
  rw [halfPlaneMellin, mellin]
  have hfun : (fun t : ℝ => (t : ℂ) ^ ((1 - w) - 1) • Set.indicator (Set.Ioi (1:ℝ)) f t)
      = Set.indicator (Set.Ioi (1:ℝ)) (fun t : ℝ => f t * (t : ℂ) ^ (-w)) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
      have hexp : (1 - w) - 1 = -w := by ring
      rw [hexp, mul_comm]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [hfun, setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioi (0:ℝ) ∩ Set.Ioi (1:ℝ) = Set.Ioi (1:ℝ) := by
    rw [Set.Ioi_inter_Ioi]
    norm_num
  rw [hset]

/-- The zero extension of an interval integrable function is locally integrable. -/
theorem locallyIntegrableOn_indicator_of_intervalIntegrable {f : ℝ → ℂ}
    (hf : ∀ y : ℝ, 1 ≤ y → IntervalIntegrable f volume 1 y) :
    LocallyIntegrableOn (Set.indicator (Set.Ioi (1:ℝ)) f) (Set.Ioi 0) volume := by
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  refine ⟨Set.Ioo (t / 2) (t + 1), ?_, ?_⟩
  · refine mem_nhdsWithin_of_mem_nhds ?_
    exact Ioo_mem_nhds (by linarith) (by linarith)
  · rw [integrableOn_indicator_iff measurableSet_Ioi]
    have hsub : Set.Ioi (1:ℝ) ∩ Set.Ioo (t / 2) (t + 1) ⊆ Set.Ioc 1 (t + 1) := by
      intro x hx
      exact ⟨hx.1, le_of_lt hx.2.2⟩
    refine IntegrableOn.mono_set ?_ hsub
    rcases le_or_gt (1:ℝ) (t + 1) with hle | hlt
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 (hf (t + 1) hle)
    · have : Set.Ioc (1:ℝ) (t + 1) = ∅ := Set.Ioc_eq_empty (by linarith)
      rw [this]
      exact integrableOn_empty

/-- A polynomially bounded tail dominates every larger power. -/
theorem isBigO_atTop_indicator_of_polyLog {f : ℝ → ℂ} {ρ X : ℝ} (hX : 1 ≤ X)
    (hb : ∀ x : ℝ, X ≤ x → ‖f x‖ ≤ x ^ ρ * Real.log x) {ε : ℝ} (hε : 0 < ε) :
    (Set.indicator (Set.Ioi (1:ℝ)) f) =O[atTop] fun x : ℝ => x ^ (ρ + ε) := by
  refine IsBigO.of_bound (1 / ε) ?_
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hxpos : (0:ℝ) < x := by linarith
  have hmem : x ∈ Set.Ioi (1:ℝ) ∨ x ∉ Set.Ioi (1:ℝ) := em _
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div (le_of_lt hxpos) hε
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hρ : (0:ℝ) < x ^ ρ := Real.rpow_pos_of_pos hxpos ρ
  have hsplit : x ^ (ρ + ε) = x ^ ρ * x ^ ε := Real.rpow_add hxpos ρ ε
  have hkey : ‖f x‖ ≤ 1 / ε * ‖x ^ (ρ + ε)‖ := by
    have h1 : x ^ ρ * Real.log x ≤ x ^ ρ * (x ^ ε / ε) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hρ)
    have h2 : ‖x ^ (ρ + ε)‖ = x ^ (ρ + ε) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hxpos) _)]
    rw [h2, hsplit]
    have h3 : x ^ ρ * (x ^ ε / ε) = 1 / ε * (x ^ ρ * x ^ ε) := by
      field_simp
    calc ‖f x‖ ≤ x ^ ρ * Real.log x := hb x hx
      _ ≤ x ^ ρ * (x ^ ε / ε) := h1
      _ = 1 / ε * (x ^ ρ * x ^ ε) := h3
  rcases hmem with hx' | hx'
  · rw [Set.indicator_of_mem hx']
    exact hkey
  · rw [Set.indicator_of_notMem hx', norm_zero]
    have : (0:ℝ) ≤ 1 / ε * ‖x ^ (ρ + ε)‖ := by positivity
    exact this

/-- Near the origin the zero extension is trivially dominated. -/
theorem isBigO_zero_indicator (f : ℝ → ℂ) (b : ℝ) :
    (Set.indicator (Set.Ioi (1:ℝ)) f) =O[nhdsWithin 0 (Set.Ioi (0:ℝ))]
      fun x : ℝ => x ^ b := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
  have hnot : x ∉ Set.Ioi (1:ℝ) := by
    simp only [Set.mem_Ioi, not_lt]
    exact le_of_lt hx.2
  rw [Set.indicator_of_notMem hnot, norm_zero]
  positivity

/-- **Convergence.**  The transform converges on `Re w > ρ + 1`. -/
theorem integrableOn_halfPlaneMellin {f : ℝ → ℂ} {ρ X : ℝ} (hX : 1 ≤ X)
    (hf : ∀ y : ℝ, 1 ≤ y → IntervalIntegrable f volume 1 y)
    (hb : ∀ x : ℝ, X ≤ x → ‖f x‖ ≤ x ^ ρ * Real.log x) {w : ℂ} (hw : ρ + 1 < w.re) :
    IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-w)) (Set.Ioi (1:ℝ)) := by
  set ε : ℝ := (w.re - ρ - 1) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    linarith
  have hconv : MellinConvergent (Set.indicator (Set.Ioi (1:ℝ)) f) (1 - w) := by
    refine mellinConvergent_of_isBigO_rpow (a := -(ρ + ε)) (b := -w.re)
      (locallyIntegrableOn_indicator_of_intervalIntegrable hf) ?_ ?_ ?_ ?_
    · have := isBigO_atTop_indicator_of_polyLog hX hb hε
      simpa using this
    · rw [Complex.sub_re, Complex.one_re]
      rw [hεdef]
      linarith
    · simpa using isBigO_zero_indicator f (-(-w.re))
    · rw [Complex.sub_re, Complex.one_re]
      linarith
  rw [MellinConvergent] at hconv
  have hfun : (fun t : ℝ => (t : ℂ) ^ ((1 - w) - 1) • Set.indicator (Set.Ioi (1:ℝ)) f t)
      = Set.indicator (Set.Ioi (1:ℝ)) (fun t : ℝ => f t * (t : ℂ) ^ (-w)) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
      have hexp : (1 - w) - 1 = -w := by ring
      rw [hexp, mul_comm]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [hfun, integrableOn_indicator_iff measurableSet_Ioi] at hconv
  refine IntegrableOn.mono_set hconv ?_
  intro x hx
  exact ⟨hx, Set.mem_Ioi.2 (lt_trans zero_lt_one (Set.mem_Ioi.1 hx))⟩


/-- **Analyticity.**  The transform is holomorphic on `Re w > ρ + 1`. -/
theorem differentiableAt_halfPlaneMellin {f : ℝ → ℂ} {ρ X : ℝ} (hX : 1 ≤ X)
    (hf : ∀ y : ℝ, 1 ≤ y → IntervalIntegrable f volume 1 y)
    (hb : ∀ x : ℝ, X ≤ x → ‖f x‖ ≤ x ^ ρ * Real.log x) {w : ℂ} (hw : ρ + 1 < w.re) :
    DifferentiableAt ℂ (halfPlaneMellin f) w := by
  set ε : ℝ := (w.re - ρ - 1) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    linarith
  have hmel : DifferentiableAt ℂ (mellin (Set.indicator (Set.Ioi (1:ℝ)) f)) (1 - w) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -(ρ + ε)) (b := -w.re)
      (locallyIntegrableOn_indicator_of_intervalIntegrable hf) ?_ ?_ ?_ ?_
    · have := isBigO_atTop_indicator_of_polyLog hX hb hε
      simpa using this
    · rw [Complex.sub_re, Complex.one_re]
      rw [hεdef]
      linarith
    · simpa using isBigO_zero_indicator f (-(-w.re))
    · rw [Complex.sub_re, Complex.one_re]
      linarith
  have haff : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) w :=
    (differentiableAt_const _).sub differentiableAt_id
  have hcomp := hmel.comp w haff
  have hfun : (mellin (Set.indicator (Set.Ioi (1:ℝ)) f)) ∘ (fun z : ℂ => (1 : ℂ) - z)
      = halfPlaneMellin f := by
    funext z
    rw [Function.comp_apply, halfPlaneMellin_eq_mellin]
  rwa [hfun] at hcomp

end GaloisForLFunctions.HTGeometry

end
