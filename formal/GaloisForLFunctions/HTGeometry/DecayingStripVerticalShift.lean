import GaloisForLFunctions.HTGeometry.StripContourShift
import Mathlib.Analysis.MellinInversion

/-!
# The vertical contour shift under uniform quadratic decay

A function holomorphic on a closed vertical strip `c₁ ≤ Re s ≤ c₂` (in either order) with a
uniform bound `|Φ(s)| ≤ C/(1 + (Im s)²)` has the same integral along the two boundary lines. This
is the horizontal strip shift applied to `z ↦ Φ(iz)`, with the horizontal segments at height `±R`
bounded by `C/(1+R²) · |c₂ - c₁| → 0`.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Vertical contour shift.** A function holomorphic on a closed vertical strip with uniform
`C/(1+t²)` decay has equal integrals along the two boundary lines. -/
theorem integral_vertical_line_shift_of_decay {Φ : ℂ → ℂ} {c₁ c₂ C : ℝ}
    (hd : ∀ s : ℂ, s.re ∈ uIcc c₁ c₂ → DifferentiableAt ℂ Φ s)
    (hb : ∀ s : ℂ, s.re ∈ uIcc c₁ c₂ → ‖Φ s‖ ≤ C / (1 + s.im ^ 2)) :
    ∫ t : ℝ, Φ ((c₁ : ℂ) + t * I) = ∫ t : ℝ, Φ ((c₂ : ℂ) + t * I) := by
  set G : ℂ → ℂ := fun z => Φ (I * z) with hG
  have hGline : ∀ c : ℝ, (fun x : ℝ => G ((x : ℂ) + ((-c : ℝ) : ℂ) * I))
      = fun t : ℝ => Φ ((c : ℂ) + t * I) := by
    intro c
    funext t
    simp only [hG]
    congr 1
    push_cast
    ring_nf
    simp [I_sq]
  have hlineInt : ∀ c : ℝ, c ∈ uIcc c₁ c₂ → Integrable (fun t : ℝ => Φ ((c : ℂ) + t * I)) := by
    intro c hc
    have hcont : Continuous (fun t : ℝ => Φ ((c : ℂ) + t * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (hd _ (by simpa using hc)).continuousAt.comp (by fun_prop)
    have hdom : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul C
    refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have := hb ((c : ℂ) + t * I) (by simpa using hc)
    simpa [div_eq_mul_inv] using this
  have hdiff : ∀ z : ℂ, z.im ∈ uIcc (-c₁) (-c₂) → DifferentiableAt ℂ G z := by
    intro z hz
    have hre : (I * z).re ∈ uIcc c₁ c₂ := by
      have : (I * z).re = -z.im := by simp
      rw [this]
      rw [Set.mem_uIcc] at hz ⊢
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    exact (hd _ hre).comp z (differentiableAt_id.const_mul I)
  have hA : Integrable (fun x : ℝ => G ((x : ℂ) + ((-c₁ : ℝ) : ℂ) * I)) := by
    rw [hGline]; exact hlineInt c₁ left_mem_uIcc
  have hB : Integrable (fun x : ℝ => G ((x : ℂ) + ((-c₂ : ℝ) : ℂ) * I)) := by
    rw [hGline]; exact hlineInt c₂ right_mem_uIcc
  have hseg : Tendsto (fun R : ℝ => ‖∫ y in (-c₁)..(-c₂), G ((R : ℂ) + (y : ℂ) * I)‖
      + ‖∫ y in (-c₁)..(-c₂), G (-(R : ℂ) + (y : ℂ) * I)‖) atTop (𝓝 0) := by
    have hmem : ∀ y : ℝ, y ∈ Set.uIoc (-c₁) (-c₂) → (-y) ∈ uIcc c₁ c₂ := by
      intro y hy
      have hy' := Set.uIoc_subset_uIcc hy
      rw [Set.mem_uIcc] at hy' ⊢
      rcases hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    have hbound : ∀ (R : ℝ) (ε : ℝ), (ε = 1 ∨ ε = -1) →
        ‖∫ y in (-c₁)..(-c₂), G ((ε * R : ℝ) + (y : ℂ) * I)‖ ≤ C / (1 + R ^ 2) * |(-c₂) - (-c₁)| := by
      intro R ε hε
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      simp only [hG]
      have hs : I * (((ε * R : ℝ) : ℂ) + (y : ℂ) * I) = ((-y : ℝ) : ℂ) + ((ε * R : ℝ) : ℂ) * I := by
        push_cast; ring_nf; simp [I_sq]; ring
      rw [hs]
      have h := hb (((-y : ℝ) : ℂ) + ((ε * R : ℝ) : ℂ) * I) (by simpa using hmem y hy)
      have him : ((((-y : ℝ) : ℂ) + ((ε * R : ℝ) : ℂ) * I)).im ^ 2 = R ^ 2 := by
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add]
        rcases hε with h | h <;> rw [h] <;> ring
      rw [him] at h
      exact h
    have hlim : Tendsto (fun R : ℝ => 2 * (C / (1 + R ^ 2) * |(-c₂) - (-c₁)|)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
      have h2 := (tendsto_const_nhds (x := C)).div_atTop h1
      simpa using ((h2.mul_const |(-c₂) - (-c₁)|).const_mul 2)
    refine squeeze_zero (fun R => by positivity) (fun R => ?_) hlim
    have e1 := hbound R 1 (Or.inl rfl)
    have e2 := hbound R (-1) (Or.inr rfl)
    simp only [one_mul, neg_one_mul, ofReal_neg] at e1 e2
    linarith
  have h := integral_line_shift hdiff hA hB hseg
  have e1 := congrArg (fun F : ℝ → ℂ => ∫ t, F t) (hGline c₁)
  have e2 := congrArg (fun F : ℝ → ℂ => ∫ t, F t) (hGline c₂)
  rw [← e1, ← e2]
  exact h

end GaloisForLFunctions.HTGeometry
