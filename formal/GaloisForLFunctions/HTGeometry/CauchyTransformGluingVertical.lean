import GaloisForLFunctions.HTGeometry.CauchyTransformGluing

/-!
# Gluing two Cauchy transforms across a vertical strip

The mirror of the horizontal gluing: two functionals carried by compact sets separated by a
vertical strip have Cauchy transforms holomorphic on complementary half-planes overlapping in that
strip.  If the transforms are opposite on the strip they glue to an entire function, both decay at
infinity, and Liouville forces the glued function — hence each transform — to vanish; the identity
theorem then propagates the vanishing over the whole preconnected complement of the carrier.

* `GaloisForLFunctions.HTGeometry.differentiable_glueVert`;
* `GaloisForLFunctions.HTGeometry.cauchyTransform_eq_zero_of_glue_re`.
-/

noncomputable section

open Complex Set Filter

namespace GaloisForLFunctions.HTGeometry

/-- Gluing two functions along the line `Re = c₂`. -/
def glueVert (f g : ℂ → ℂ) (c₂ : ℝ) : ℂ → ℂ := fun v => if v.re < c₂ then f v else g v

theorem glueVert_of_lt {f g : ℂ → ℂ} {c₂ : ℝ} {v : ℂ} (h : v.re < c₂) :
    glueVert f g c₂ v = f v := by
  rw [glueVert, if_pos h]

theorem glueVert_eqOn_right {f g : ℂ → ℂ} {c₁ c₂ : ℝ}
    (hagree : ∀ v : ℂ, c₁ < v.re → v.re < c₂ → f v = g v) :
    EqOn (glueVert f g c₂) g {v : ℂ | c₁ < v.re} := by
  intro v hv
  rw [glueVert]
  by_cases h : v.re < c₂
  · rw [if_pos h]
    exact hagree v hv h
  · rw [if_neg h]

/-- **Two functions agreeing on the overlap of two half-planes glue to an entire function.** -/
theorem differentiable_glueVert {f g : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hf : DifferentiableOn ℂ f {v : ℂ | v.re < c₂})
    (hg : DifferentiableOn ℂ g {v : ℂ | c₁ < v.re})
    (hagree : ∀ v : ℂ, c₁ < v.re → v.re < c₂ → f v = g v) :
    Differentiable ℂ (glueVert f g c₂) := by
  have hopenL : IsOpen {v : ℂ | v.re < c₂} := isOpen_lt Complex.continuous_re continuous_const
  have hopenU : IsOpen {v : ℂ | c₁ < v.re} := isOpen_lt continuous_const Complex.continuous_re
  intro v
  by_cases hv : v.re < c₂
  · have hmem : v ∈ {v : ℂ | v.re < c₂} := hv
    have hev : glueVert f g c₂ =ᶠ[nhds v] f := by
      filter_upwards [hopenL.mem_nhds hmem] with w hw using glueVert_of_lt hw
    exact (hf.differentiableAt (hopenL.mem_nhds hmem)).congr_of_eventuallyEq hev
  · have hvu : c₁ < v.re := by
      have := not_lt.mp hv
      linarith
    have hmem : v ∈ {v : ℂ | c₁ < v.re} := hvu
    have hev : glueVert f g c₂ =ᶠ[nhds v] g := by
      filter_upwards [hopenU.mem_nhds hmem] with w hw using glueVert_eqOn_right hagree hw
    exact (hg.differentiableAt (hopenU.mem_nhds hmem)).congr_of_eventuallyEq hev

variable {Kc Kc' : Set ℂ} [CompactSpace Kc] [CompactSpace Kc']

/-- **Two Cauchy transforms opposite on the separating vertical strip vanish on the left
half-plane.** -/
theorem cauchyTransform_eq_zero_of_glue_re_lt
    {c₁ c₂ R : ℝ} (hc : c₁ < c₂)
    (hKcRe : ∀ z ∈ Kc, c₂ ≤ z.re) (hKc'Re : ∀ z ∈ Kc', z.re ≤ c₁)
    (hKcR : ∀ z ∈ Kc, ‖z‖ ≤ R) (hKc'R : ∀ z ∈ Kc', ‖z‖ ≤ R)
    (L : C(Kc, ℂ) →L[ℂ] ℂ) (L' : C(Kc', ℂ) →L[ℂ] ℂ)
    (hagree : ∀ v : ℂ, c₁ < v.re → v.re < c₂ →
      functionalCauchyTransform L v + functionalCauchyTransform L' v = 0) :
    ∀ v : ℂ, v.re < c₂ → functionalCauchyTransform L v = 0 := by
  classical
  set f : ℂ → ℂ := functionalCauchyTransform L with hf
  set g : ℂ → ℂ := fun v => -functionalCauchyTransform L' v with hg
  have hagree' : ∀ v : ℂ, c₁ < v.re → v.re < c₂ → f v = g v := by
    intro v h1 h2
    have := hagree v h1 h2
    rw [hf, hg]
    linear_combination this
  have hfd : DifferentiableOn ℂ f {v : ℂ | v.re < c₂} := by
    refine (differentiableOn_cauchyTransform L).mono ?_
    intro v hv hcon
    exact absurd (hKcRe v hcon) (not_le.mpr hv)
  have hgd : DifferentiableOn ℂ g {v : ℂ | c₁ < v.re} := by
    refine ((differentiableOn_cauchyTransform L').mono ?_).neg
    intro v hv hcon
    exact absurd (hKc'Re v hcon) (not_le.mpr hv)
  have hglue : Differentiable ℂ (glueVert f g c₂) := differentiable_glueVert hc hfd hgd hagree'
  have hsmall : ∀ v : ℂ, R < ‖v‖ →
      ‖glueVert f g c₂ v‖ ≤ (max ‖L‖ ‖L'‖) * (‖v‖ - R)⁻¹ := by
    intro v hv
    rw [glueVert]
    by_cases h : v.re < c₂
    · rw [if_pos h]
      refine le_trans (norm_cauchyTransform_le_of_far L hKcR hv) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [if_neg h]
      rw [hg, norm_neg]
      refine le_trans (norm_cauchyTransform_le_of_far L' hKc'R hv) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hbdd : Bornology.IsBounded (Set.range (glueVert f g c₂)) := by
    have hcont : Continuous (glueVert f g c₂) := hglue.continuous
    have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (R + 1)) := isCompact_closedBall _ _
    obtain ⟨M, hM⟩ := (hcompact.image hcont).isBounded.subset_closedBall 0
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max M (max ‖L‖ ‖L'‖), ?_⟩
    rintro _ ⟨v, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_cases hv : ‖v‖ ≤ R + 1
    · have hmem : glueVert f g c₂ v ∈ Metric.closedBall (0 : ℂ) M := by
        apply hM
        exact ⟨v, by simpa [Metric.mem_closedBall, dist_zero_right] using hv, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans hmem (le_max_left _ _)
    · have hvR : R < ‖v‖ := by
        have := not_le.mp hv
        linarith
      refine le_trans (hsmall v hvR) (le_trans ?_ (le_max_right _ _))
      have h1 : (1 : ℝ) ≤ ‖v‖ - R := by
        have := not_le.mp hv
        linarith
      have h2 : (‖v‖ - R)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact h1
      calc (max ‖L‖ ‖L'‖) * (‖v‖ - R)⁻¹ ≤ (max ‖L‖ ‖L'‖) * 1 :=
            mul_le_mul_of_nonneg_left h2 (le_trans (norm_nonneg L) (le_max_left _ _))
        _ = max ‖L‖ ‖L'‖ := mul_one _
  have hconst : ∀ v w : ℂ, glueVert f g c₂ v = glueVert f g c₂ w :=
    Differentiable.apply_eq_apply_of_bounded hglue hbdd
  have hzero : ∀ v : ℂ, glueVert f g c₂ v = 0 := by
    intro v
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add ?_)
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (R + 1 + (max ‖L‖ ‖L'‖) / ε)
    set w : ℂ := ((n : ℝ) : ℂ) with hw
    have hwn : ‖w‖ = (n : ℝ) := by
      rw [hw, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hR' : R < ‖w‖ := by
      rw [hwn]
      have : (0:ℝ) ≤ (max ‖L‖ ‖L'‖) / ε := by positivity
      linarith
    have hden : (max ‖L‖ ‖L'‖) / ε < ‖w‖ - R := by
      rw [hwn]
      linarith
    have hbound := hsmall w hR'
    rw [hconst v w]
    have hpos : 0 < ‖w‖ - R := by linarith
    have hfinal : (max ‖L‖ ‖L'‖) * (‖w‖ - R)⁻¹ ≤ ε := by
      rw [mul_inv_le_iff₀ hpos]
      have h := (div_lt_iff₀ hε).mp hden
      linarith [h, mul_comm (‖w‖ - R) ε]
    rw [zero_add]
    exact le_trans hbound hfinal
  intro v hv
  have hval := hzero v
  rwa [glueVert_of_lt hv] at hval

/-- **Two Cauchy transforms opposite on the separating vertical strip both vanish.** -/
theorem cauchyTransform_eq_zero_of_glue_re
    (hKc : IsCompact Kc)
    {c₁ c₂ R : ℝ} (hc : c₁ < c₂)
    (hKcRe : ∀ z ∈ Kc, c₂ ≤ z.re) (hKc'Re : ∀ z ∈ Kc', z.re ≤ c₁)
    (hKcR : ∀ z ∈ Kc, ‖z‖ ≤ R) (hKc'R : ∀ z ∈ Kc', ‖z‖ ≤ R)
    (L : C(Kc, ℂ) →L[ℂ] ℂ) (L' : C(Kc', ℂ) →L[ℂ] ℂ)
    (hagree : ∀ v : ℂ, c₁ < v.re → v.re < c₂ →
      functionalCauchyTransform L v + functionalCauchyTransform L' v = 0)
    (hpre : IsPreconnected (Kcᶜ)) :
    ∀ v ∉ Kc, functionalCauchyTransform L v = 0 := by
  classical
  have hlow : ∀ v : ℂ, v.re < c₂ → functionalCauchyTransform L v = 0 :=
    cauchyTransform_eq_zero_of_glue_re_lt (Kc' := Kc') hc hKcRe hKc'Re hKcR hKc'R L L' hagree
  have hanalytic : AnalyticOnNhd ℂ (functionalCauchyTransform L) Kcᶜ :=
    analyticOnNhd_functionalCauchyTransform hKc L
  have hopenL : IsOpen {v : ℂ | v.re < c₂} := isOpen_lt Complex.continuous_re continuous_const
  have hlowsub : {v : ℂ | v.re < c₂} ⊆ Kcᶜ := by
    intro w hw hcon
    exact absurd (hKcRe w hcon) (not_le.mpr hw)
  set v₀ : ℂ := ((c₂ - 1 : ℝ) : ℂ) with hv₀def
  have hv₀re : v₀.re = c₂ - 1 := by
    rw [hv₀def]
    simp
  have hv₀low : v₀.re < c₂ := by
    rw [hv₀re]
    linarith
  have hv₀mem : v₀ ∈ Kcᶜ := hlowsub hv₀low
  have hev : functionalCauchyTransform L =ᶠ[nhds v₀] 0 := by
    filter_upwards [hopenL.mem_nhds hv₀low] with w hw
    exact hlow w hw
  exact fun v hv => hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hv₀mem hev hv

end GaloisForLFunctions.HTGeometry
