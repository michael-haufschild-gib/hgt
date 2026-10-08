import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutoff support and Mellin convergence

Bounded functions vanishing near zero have a holomorphic Mellin transform
on the left half-plane. Functions vanishing near both ends have an entire
Mellin transform. Smooth upper cutoffs and all their positive derivatives
supply these conditions without an analytic assumption on the cubic datum.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

private lemma isBigO_rpow_zero_near_origin {f : ℝ → ℂ}
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, f x = 0) (b : ℝ) :
    f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  obtain ⟨a, ha, hf⟩ := h0
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT ha] with x hx
  simp [hf x hx.2]

private lemma isBigO_rpow_zero_near_infinity {f : ℝ → ℂ}
    (htop : ∃ b : ℝ, ∀ x > b, f x = 0) (a : ℝ) :
    f =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  obtain ⟨b, hf⟩ := htop
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop b] with x hx
  simp [hf x hx]

/-- Boundedness and an origin buffer pay convergence and holomorphy for `re s < 0`. -/
theorem mellin_bounded_zero_near_origin {f : ℝ → ℂ} (hf : Continuous f)
    (hB : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, f x = 0)
    {s : ℂ} (hs : s.re < 0) :
    MellinConvergent f s ∧ DifferentiableAt ℂ (mellin f) s := by
  obtain ⟨C, hC⟩ := hB
  have ht : f =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound C (Eventually.of_forall fun x => ?_)
    simpa using hC x
  have hb := isBigO_rpow_zero_near_origin h0 (s.re - 1)
  have hl : LocallyIntegrableOn f (Ioi 0) :=
    hf.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact ⟨mellinConvergent_of_isBigO_rpow hl ht hs hb (by linarith),
    mellin_differentiableAt_of_isBigO_rpow hl ht hs hb (by linarith)⟩

/-- A continuous function with buffers at both ends has an entire Mellin transform. -/
theorem mellin_zero_near_endpoints {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, f x = 0)
    (htop : ∃ b : ℝ, ∀ x > b, f x = 0) (s : ℂ) :
    MellinConvergent f s ∧ DifferentiableAt ℂ (mellin f) s := by
  have ht := isBigO_rpow_zero_near_infinity htop (s.re + 1)
  have hb := isBigO_rpow_zero_near_origin h0 (s.re - 1)
  have hl : LocallyIntegrableOn f (Ioi 0) :=
    hf.continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact ⟨mellinConvergent_of_isBigO_rpow hl ht (by linarith) hb (by linarith),
    mellin_differentiableAt_of_isBigO_rpow hl ht (by linarith) hb (by linarith)⟩

/-- Ordinary smooth upper-cutoff geometry, independent of the arithmetic datum. -/
structure IsMellinTailCutoff (ψ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  zero_near_origin : ∃ a : ℝ, 0 < a ∧ ∀ x < a, ψ x = 0
  one_near_infinity : ∃ b : ℝ, ∀ x > b, ψ x = 1

theorem IsMellinTailCutoff.bounded {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) :
    ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C := by
  obtain ⟨a, _, ha⟩ := hψ.zero_near_origin
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hψ.smooth.continuous.continuousOn (s := Icc a b))
  refine ⟨max 1 C, fun x => ?_⟩
  by_cases hxa : x < a
  · rw [ha x hxa, norm_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_cases hxb : b < x
  · rw [hb x hxb, norm_one]
    exact le_max_left _ _
  exact (hC x ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩).trans (le_max_right _ _)

theorem IsMellinTailCutoff.iteratedDeriv_zero_near_origin {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (n : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∀ x < a, iteratedDeriv n ψ x = 0 := by
  obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
  refine ⟨a, ha, fun x hx => ?_⟩
  have he : ψ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact h0 y hy
  simpa using he.iteratedDeriv_eq n

theorem IsMellinTailCutoff.iteratedDeriv_zero_near_infinity {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {n : ℕ} (hn : n ≠ 0) :
    ∃ b : ℝ, ∀ x > b, iteratedDeriv n ψ x = 0 := by
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  refine ⟨b, fun x hx => ?_⟩
  have he : ψ =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hb y hy
  simpa [iteratedDeriv_const, hn] using he.iteratedDeriv_eq n

/-- The positive cutoff derivatives give entire Mellin factors even after a continuous multiplier. -/
theorem IsMellinTailCutoff.mellin_mul_iteratedDeriv {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    MellinConvergent (fun x => F x * iteratedDeriv n ψ x) s ∧
      DifferentiableAt ℂ (mellin (fun x => F x * iteratedDeriv n ψ x)) s := by
  obtain ⟨a, ha, h0⟩ := hψ.iteratedDeriv_zero_near_origin n
  obtain ⟨b, htop⟩ := hψ.iteratedDeriv_zero_near_infinity hn
  exact mellin_zero_near_endpoints (f := fun x => F x * iteratedDeriv n ψ x)
    (hF.mul (hψ.smooth.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞)))))
    ⟨a, ha, fun x hx => by rw [h0 x hx, mul_zero]⟩
    ⟨b, fun x hx => by rw [htop x hx, mul_zero]⟩ s

/-- The noncompact primitive factor needs only its already proved global bound. -/
theorem IsMellinTailCutoff.mellin_mul {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) {s : ℂ} (hs : s.re < 0) :
    MellinConvergent (fun x => F x * ψ x) s ∧
      DifferentiableAt ℂ (mellin (fun x => F x * ψ x)) s := by
  obtain ⟨C, hC⟩ := hB
  obtain ⟨D, hD⟩ := hψ.bounded
  obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
  apply mellin_bounded_zero_near_origin (f := fun x => F x * ψ x)
    (hF.mul hψ.smooth.continuous) _
    ⟨a, ha, fun x hx => by rw [h0 x hx, mul_zero]⟩ hs
  refine ⟨C * D, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

/-- A fixed smooth cutoff: zero below one, one above two. -/
def mellinTailCutoff (x : ℝ) : ℂ := Real.smoothTransition (x - 1)

theorem isMellinTailCutoff_mellinTailCutoff : IsMellinTailCutoff mellinTailCutoff := by
  refine ⟨?_, ⟨1, zero_lt_one, ?_⟩, ⟨2, ?_⟩⟩
  · unfold mellinTailCutoff
    exact Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
  · intro x hx
    simp [mellinTailCutoff, Real.smoothTransition.zero_of_nonpos (by linarith : x - 1 ≤ 0)]
  · intro x hx
    simp [mellinTailCutoff, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - 1)]

end RHTower.WeilHigherDenominator
