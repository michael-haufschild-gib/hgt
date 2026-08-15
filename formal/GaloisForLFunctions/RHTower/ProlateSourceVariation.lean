import GaloisForLFunctions.RHTower.ProlateSourcePolarPrimitive
import GaloisForLFunctions.HTGeometry.BoundedVariationRiemannSum

/-!
# Bounded variation of the prolate cut-off source

On the positive half-line the cut-off source is the smooth mode profile times a decreasing step:
one on the open aperture, one half at the endpoint, zero beyond.  The profile is Lipschitz on every
compact interval and the step is monotone, so the product has bounded variation.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- The real part is one-Lipschitz. -/
theorem lipschitzWith_complex_re : LipschitzWith 1 (Complex.re) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.dist_eq, Complex.dist_eq]
  have h : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  simp only [Complex.sub_re] at h
  simpa using h

/-- Real bounded variation follows from complex bounded variation of the complexification. -/
theorem boundedVariationOn_of_ofReal {F : ℝ → ℝ} {s : Set ℝ}
    (h : BoundedVariationOn (fun x => ((F x : ℝ) : ℂ)) s) : BoundedVariationOn F s := by
  have hcomp := lipschitzWith_complex_re.comp_boundedVariationOn h
  exact hcomp

/-- The symmetric half-endpoint step on the positive half-line. -/
def halfStep (A : ℝ) (y : ℝ) : ℝ := if y < A then 1 else if y = A then 1 / 2 else 0

theorem antitoneOn_halfStep (A : ℝ) (s : Set ℝ) : AntitoneOn (halfStep A) s := by
  intro x _ y _ hxy
  unfold halfStep
  by_cases hy : y < A
  · rw [if_pos hy, if_pos (lt_of_le_of_lt hxy hy)]
  · rw [if_neg hy]
    by_cases hyA : y = A
    · rw [if_pos hyA]
      by_cases hx : x < A
      · rw [if_pos hx]
        norm_num
      · rw [if_neg hx, if_pos (le_antisymm (by rw [← hyA]; exact hxy) (not_lt.mp hx) : x = A)]
    · rw [if_neg hyA]
      by_cases hx : x < A
      · rw [if_pos hx]
        norm_num
      · rw [if_neg hx]
        by_cases hxA : x = A
        · rw [if_pos hxA]
          norm_num
        · rw [if_neg hxA]

theorem abs_halfStep_le (A y : ℝ) : |halfStep A y| ≤ 1 := by
  unfold halfStep
  by_cases hy : y < A
  · rw [if_pos hy]
    norm_num
  · rw [if_neg hy]
    by_cases hyA : y = A
    · rw [if_pos hyA]
      norm_num
    · rw [if_neg hyA]
      norm_num

theorem lipschitzWith_neg_real : LipschitzWith 1 (fun x : ℝ => -x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, show (-x) - -y = -(x - y) by ring, abs_neg]
  simp

theorem boundedVariationOn_halfStep (A : ℝ) {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (halfStep A) (Icc a b) := by
  have hmono : MonotoneOn (fun y => -halfStep A y) (Icc a b) := fun x hx y hy hxy =>
    neg_le_neg (antitoneOn_halfStep A (Icc a b) hx hy hxy)
  have hloc := hmono.locallyBoundedVariationOn
  have hbv : BoundedVariationOn (fun y => -halfStep A y) (Icc a b) := by
    have h := hloc a b (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rwa [Set.inter_self] at h
  have hcomp := lipschitzWith_neg_real.comp_boundedVariationOn hbv
  simpa [Function.comp_def] using hcomp

/-- On the positive half-line the cut-off source factors through the step. -/
theorem prolateModeSource_eq_mul_halfStep {A : ℝ} (hA : 0 < A) {Φ : ℝ → ℝ} {y : ℝ}
    (hy : 0 ≤ y) : prolateModeSource A Φ y = Φ (y / A) * halfStep A y := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff halfStep
  by_cases h1 : y < A
  · rw [if_pos ⟨by linarith, h1⟩, if_pos h1, mul_one]
  · have hnotIoo : y ∉ Ioo (-A) A := fun h => h1 h.2
    rw [if_neg hnotIoo, if_neg h1]
    by_cases h2 : y = A
    · rw [if_pos (Or.inr h2), if_pos h2]
      show Φ (y / A) / 2 = Φ (y / A) * (1 / 2)
      ring
    · have hne : ¬(y = -A ∨ y = A) := by
        rintro (h | h)
        · linarith
        · exact h2 h
      rw [if_neg hne, if_neg h2, mul_zero]

/-- **Bounded variation of the cut-off source on a half-line window.** -/
theorem boundedVariationOn_prolateModeSource {A : ℝ} (hA : 0 < A) {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) {L : ℝ} (hL : 0 ≤ L) :
    BoundedVariationOn (prolateModeSource A Φ) (Icc 0 L) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hdc : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
  have hgd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Φ (z / A)) (deriv Φ (y / A) / A) y := by
    intro y
    have hin : HasDerivAt (fun z : ℝ => z / A) (1 / A) y := by
      simpa using (hasDerivAt_id y).div_const A
    have h := (hd1 (y / A)).hasDerivAt.comp y hin
    simpa [Function.comp_def, div_eq_mul_inv] using h
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L / A)).exists_bound_of_continuousOn
    hdc.continuousOn
  have hD0 : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, by positivity⟩)
  have hlipg : LipschitzOnWith ⟨D / A, by positivity⟩ (fun z : ℝ => Φ (z / A)) (Icc 0 L) := by
    refine (convex_Icc (0 : ℝ) L).lipschitzOnWith_of_nnnorm_deriv_le
      (fun y _ => (hgd y).differentiableAt) ?_
    intro y hy
    rw [(hgd y).deriv]
    have hmem : y / A ∈ Icc (0 : ℝ) (L / A) := by
      refine ⟨div_nonneg hy.1 hA.le, ?_⟩
      rw [div_le_div_iff₀ hA hA]
      nlinarith [hy.2, hA]
    have hb : |deriv Φ (y / A)| ≤ D := by
      simpa [Real.norm_eq_abs] using hD (y / A) hmem
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_div, abs_of_pos hA]
    show |deriv Φ (y / A)| / A ≤ D / A
    rw [div_le_div_iff₀ hA hA]
    nlinarith [hb, hA, abs_nonneg (deriv Φ (y / A))]
  have hstepC : BoundedVariationOn (fun y : ℝ => ((halfStep A y : ℝ) : ℂ)) (Icc 0 L) := by
    have h := (RCLike.lipschitzWith_ofReal (K := ℂ)).comp_boundedVariationOn
      (boundedVariationOn_halfStep A hL)
    simpa [Function.comp_def] using h
  have hlipC : LipschitzOnWith ⟨D / A, by positivity⟩
      (fun y : ℝ => ((Φ (y / A) : ℝ) : ℂ)) (Icc 0 L) := by
    have h := (RCLike.lipschitzWith_ofReal (K := ℂ)).comp_lipschitzOnWith hlipg
    simpa [Function.comp_def] using h
  obtain ⟨Mg, hMg⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    ((hd1.continuous.comp (continuous_id.div_const A)).continuousOn)
  have hMg0 : (0 : ℝ) ≤ Mg := le_trans (norm_nonneg _) (hMg 0 ⟨le_refl 0, hL⟩)
  have hprod := HTGeometry.BoundedVariationOn.mul_of_norm_le_of_lipschitzOn
    (f := fun y : ℝ => ((halfStep A y : ℝ) : ℂ))
    (h := fun y : ℝ => ((Φ (y / A) : ℝ) : ℂ))
    hL hstepC (by norm_num : (0 : ℝ) ≤ 1) hMg0
    (fun x _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_halfStep_le A x)
    (fun x hx => by
      rw [Complex.norm_real]
      exact hMg x hx) hlipC
  refine boundedVariationOn_of_ofReal ?_
  have hEq : EqOn (fun y : ℝ => ((halfStep A y : ℝ) : ℂ) * ((Φ (y / A) : ℝ) : ℂ))
      (fun y : ℝ => ((prolateModeSource A Φ y : ℝ) : ℂ)) (Icc 0 L) := by
    intro x hx
    show ((halfStep A x : ℝ) : ℂ) * ((Φ (x / A) : ℝ) : ℂ)
      = ((prolateModeSource A Φ x : ℝ) : ℂ)
    rw [prolateModeSource_eq_mul_halfStep hA hx.1]
    push_cast
    ring
  unfold BoundedVariationOn at hprod ⊢
  rwa [eVariationOn.congr hEq] at hprod

/-- Variation is subadditive in the profile. -/
theorem eVariationOn_sub_le {f g : ℝ → ℝ} {s : Set ℝ} :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  have hbound : ∀ i : ℕ,
      edist ((fun x => f x - g x) (p.2.1 (i + 1))) ((fun x => f x - g x) (p.2.1 i))
        ≤ edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) + edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) := by
    intro i
    have h : |(f (p.2.1 (i + 1)) - g (p.2.1 (i + 1))) - (f (p.2.1 i) - g (p.2.1 i))|
        ≤ |f (p.2.1 (i + 1)) - f (p.2.1 i)| + |g (p.2.1 (i + 1)) - g (p.2.1 i)| := by
      have := abs_add_le (f (p.2.1 (i + 1)) - f (p.2.1 i)) (-(g (p.2.1 (i + 1)) - g (p.2.1 i)))
      rw [abs_neg] at this
      calc |(f (p.2.1 (i + 1)) - g (p.2.1 (i + 1))) - (f (p.2.1 i) - g (p.2.1 i))|
          = |(f (p.2.1 (i + 1)) - f (p.2.1 i)) + -(g (p.2.1 (i + 1)) - g (p.2.1 i))| := by
            congr 1
            ring
        _ ≤ _ := this
    have h' : |f (p.2.1 (i + 1)) - g (p.2.1 (i + 1)) + g (p.2.1 i) - f (p.2.1 i)|
        ≤ |f (p.2.1 (i + 1)) - f (p.2.1 i)| + |g (p.2.1 (i + 1)) - g (p.2.1 i)| := by
      rw [show f (p.2.1 (i + 1)) - g (p.2.1 (i + 1)) + g (p.2.1 i) - f (p.2.1 i)
          = (f (p.2.1 (i + 1)) - g (p.2.1 (i + 1))) - (f (p.2.1 i) - g (p.2.1 i)) by ring]
      exact h
    simpa [edist_dist, Real.dist_eq, ← ENNReal.ofReal_add, abs_nonneg] using
      ENNReal.ofReal_le_ofReal h'
  calc (∑ i ∈ Finset.range p.1,
        edist ((fun x => f x - g x) (p.2.1 (i + 1))) ((fun x => f x - g x) (p.2.1 i)))
      ≤ ∑ i ∈ Finset.range p.1, (edist (f (p.2.1 (i + 1))) (f (p.2.1 i))
          + edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)))
          + ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le p.2.2.1 p.2.2.2) (eVariationOn.sum_le p.2.2.1 p.2.2.2)

theorem boundedVariationOn_sub {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x - g x) s := by
  refine ne_top_of_le_ne_top ?_ eVariationOn_sub_le
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

theorem boundedVariationOn_const_mul {f : ℝ → ℝ} {s : Set ℝ} (r : ℝ)
    (hf : BoundedVariationOn f s) : BoundedVariationOn (fun x => r * f x) s := by
  have hlip : LipschitzWith ⟨|r|, abs_nonneg r⟩ (fun x : ℝ => r * x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, show r * x - r * y = r * (x - y) by ring, abs_mul]
    exact le_of_eq rfl
  have h := hlip.comp_boundedVariationOn hf
  simpa [Function.comp_def] using h

/-- **Bounded variation of the mean-zero source.** -/
theorem boundedVariationOn_prolateMeanZeroSource {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    {Φ : ℝ → ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) {L : ℝ} (hL : 0 ≤ L) :
    BoundedVariationOn (prolateMeanZeroSource A lam Φ) (Icc 0 L) := by
  have h1 := boundedVariationOn_prolateModeSource hA hsm hL (Φ := Φ)
  have h2 := boundedVariationOn_prolateModeSource
    (by positivity : (0 : ℝ) < lam * A) hsm hL (Φ := Φ)
  exact boundedVariationOn_sub h1 (boundedVariationOn_const_mul lam⁻¹ h2)

end RHTower
