import GaloisForLFunctions.HTGeometry.ReflectedCarrierFunctional
import Mathlib.Analysis.Complex.Liouville

/-!
# Gluing two Cauchy transforms across a strip

Two functionals carried by compact sets separated by a horizontal strip have Cauchy transforms
holomorphic on complementary half-planes overlapping in that strip.  If the transforms are opposite
on the strip they glue to an entire function, and both decay at infinity, so Liouville forces the
glued function — hence each transform on its own half-plane — to vanish.  Since the complement of
either carrier is preconnected, the vanishing propagates to the whole complement.

* `GaloisForLFunctions.HTGeometry.differentiable_glueStrip`;
* `GaloisForLFunctions.HTGeometry.cauchyTransform_eq_zero_of_glue`.
-/

noncomputable section

open Complex Set Filter

namespace GaloisForLFunctions.HTGeometry

/-- Gluing two functions along the line `Im = c`. -/
def glueStrip (f g : ℂ → ℂ) (c : ℝ) : ℂ → ℂ := fun v => if v.im < c then f v else g v

theorem glueStrip_of_lt {f g : ℂ → ℂ} {c : ℝ} {v : ℂ} (h : v.im < c) :
    glueStrip f g c v = f v := by
  rw [glueStrip, if_pos h]

theorem glueStrip_eqOn_upper {f g : ℂ → ℂ} {c : ℝ}
    (hagree : ∀ v : ℂ, -c < v.im → v.im < c → f v = g v) :
    EqOn (glueStrip f g c) g {v : ℂ | -c < v.im} := by
  intro v hv
  rw [glueStrip]
  by_cases h : v.im < c
  · rw [if_pos h]
    exact hagree v hv h
  · rw [if_neg h]

/-- **Two functions agreeing on the overlap of two half-planes glue to an entire function.** -/
theorem differentiable_glueStrip {f g : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hf : DifferentiableOn ℂ f {v : ℂ | v.im < c})
    (hg : DifferentiableOn ℂ g {v : ℂ | -c < v.im})
    (hagree : ∀ v : ℂ, -c < v.im → v.im < c → f v = g v) :
    Differentiable ℂ (glueStrip f g c) := by
  have hopenL : IsOpen {v : ℂ | v.im < c} := isOpen_lt Complex.continuous_im continuous_const
  have hopenU : IsOpen {v : ℂ | -c < v.im} := isOpen_lt continuous_const Complex.continuous_im
  intro v
  by_cases hv : v.im < c
  · have hmem : v ∈ {v : ℂ | v.im < c} := hv
    have hev : glueStrip f g c =ᶠ[nhds v] f := by
      filter_upwards [hopenL.mem_nhds hmem] with w hw using glueStrip_of_lt hw
    exact (hf.differentiableAt (hopenL.mem_nhds hmem)).congr_of_eventuallyEq hev
  · have hvu : -c < v.im := by
      have := not_lt.mp hv
      linarith
    have hmem : v ∈ {v : ℂ | -c < v.im} := hvu
    have hev : glueStrip f g c =ᶠ[nhds v] g := by
      filter_upwards [hopenU.mem_nhds hmem] with w hw using glueStrip_eqOn_upper hagree hw
    exact (hg.differentiableAt (hopenU.mem_nhds hmem)).congr_of_eventuallyEq hev

variable {Kc Kc' : Set ℂ} [CompactSpace Kc] [CompactSpace Kc']

theorem norm_cauchyTransform_le_of_far (L : C(Kc, ℂ) →L[ℂ] ℂ) {R : ℝ}
    (hKcR : ∀ z ∈ Kc, ‖z‖ ≤ R) {v : ℂ} (hv : R < ‖v‖) :
    ‖cauchyTransform L v‖ ≤ ‖L‖ * (‖v‖ - R)⁻¹ := by
  have hvK : v ∉ Kc := fun hc => absurd (hKcR v hc) (not_le.mpr hv)
  refine norm_cauchyTransform_le L hvK (by linarith) ?_
  intro z hz
  have h1 : ‖v‖ - ‖z‖ ≤ ‖v - z‖ := norm_sub_norm_le v z
  have h2 : ‖z‖ ≤ R := hKcR z hz
  linarith

/-- **Two Cauchy transforms opposite on the separating strip both vanish.** -/
theorem cauchyTransform_eq_zero_of_glue
    (hKc : IsCompact Kc)
    {c R : ℝ} (hc : 0 < c)
    (hKcIm : ∀ z ∈ Kc, c ≤ z.im) (hKc'Im : ∀ z ∈ Kc', z.im ≤ -c)
    (hKcR : ∀ z ∈ Kc, ‖z‖ ≤ R) (hKc'R : ∀ z ∈ Kc', ‖z‖ ≤ R)
    (L : C(Kc, ℂ) →L[ℂ] ℂ) (L' : C(Kc', ℂ) →L[ℂ] ℂ)
    (hagree : ∀ v : ℂ, -c < v.im → v.im < c →
      cauchyTransform L v + cauchyTransform L' v = 0)
    (hpre : IsPreconnected (Kcᶜ)) :
    ∀ v ∉ Kc, cauchyTransform L v = 0 := by
  classical
  set f : ℂ → ℂ := cauchyTransform L with hf
  set g : ℂ → ℂ := fun v => -cauchyTransform L' v with hg
  have hagree' : ∀ v : ℂ, -c < v.im → v.im < c → f v = g v := by
    intro v h1 h2
    have := hagree v h1 h2
    rw [hf, hg]
    linear_combination this
  have hfd : DifferentiableOn ℂ f {v : ℂ | v.im < c} := by
    refine (differentiableOn_cauchyTransform L).mono ?_
    intro v hv hcon
    exact absurd (hKcIm v hcon) (not_le.mpr hv)
  have hgd : DifferentiableOn ℂ g {v : ℂ | -c < v.im} := by
    refine ((differentiableOn_cauchyTransform L').mono ?_).neg
    intro v hv hcon
    exact absurd (hKc'Im v hcon) (not_le.mpr hv)
  have hglue : Differentiable ℂ (glueStrip f g c) := differentiable_glueStrip hc hfd hgd hagree'
  -- the glued function is small far away
  have hsmall : ∀ v : ℂ, R < ‖v‖ →
      ‖glueStrip f g c v‖ ≤ (max ‖L‖ ‖L'‖) * (‖v‖ - R)⁻¹ := by
    intro v hv
    rw [glueStrip]
    by_cases h : v.im < c
    · rw [if_pos h]
      refine le_trans (norm_cauchyTransform_le_of_far L hKcR hv) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [if_neg h]
      rw [hg, norm_neg]
      refine le_trans (norm_cauchyTransform_le_of_far L' hKc'R hv) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  -- boundedness of the glued function
  have hbdd : Bornology.IsBounded (Set.range (glueStrip f g c)) := by
    have hcont : Continuous (glueStrip f g c) := hglue.continuous
    have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (R + 1)) := isCompact_closedBall _ _
    obtain ⟨M, hM⟩ := (hcompact.image hcont).isBounded.subset_closedBall 0
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max M (max ‖L‖ ‖L'‖), ?_⟩
    rintro _ ⟨v, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_cases hv : ‖v‖ ≤ R + 1
    · have hmem : glueStrip f g c v ∈ Metric.closedBall (0 : ℂ) M := by
        apply hM
        exact ⟨v, by simpa [Metric.mem_closedBall, dist_zero_right] using hv, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans hmem (le_max_left _ _)
    · have hvR : R < ‖v‖ := by
        have := not_le.mp hv
        linarith
      refine le_trans (hsmall v hvR) (le_trans ?_ (le_max_right _ _))
      have h1 : (1 : ℝ) ≤ ‖v‖ - R := by linarith
      have h2 : (‖v‖ - R)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact h1
      calc (max ‖L‖ ‖L'‖) * (‖v‖ - R)⁻¹ ≤ (max ‖L‖ ‖L'‖) * 1 :=
            mul_le_mul_of_nonneg_left h2 (le_trans (norm_nonneg L) (le_max_left _ _))
        _ = max ‖L‖ ‖L'‖ := mul_one _
  -- Liouville
  have hconst : ∀ v w : ℂ, glueStrip f g c v = glueStrip f g c w :=
    Differentiable.apply_eq_apply_of_bounded hglue hbdd
  have hzero : ∀ v : ℂ, glueStrip f g c v = 0 := by
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
    have hML : (0:ℝ) ≤ max ‖L‖ ‖L'‖ := le_trans (norm_nonneg L) (le_max_left _ _)
    have hpos : 0 < ‖w‖ - R := by linarith
    have hfinal : (max ‖L‖ ‖L'‖) * (‖w‖ - R)⁻¹ ≤ ε := by
      rw [mul_inv_le_iff₀ hpos]
      have h := (div_lt_iff₀ hε).mp hden
      linarith [h, mul_comm (‖w‖ - R) ε]
    rw [zero_add]
    exact le_trans hbound hfinal
  -- propagate to the whole complement of the carrier
  have hlow : ∀ v : ℂ, v.im < c → cauchyTransform L v = 0 := by
    intro v hv
    have := hzero v
    rwa [glueStrip_of_lt hv] at this
  have hanalytic : AnalyticOnNhd ℂ (cauchyTransform L) Kcᶜ :=
    analyticOnNhd_cauchyTransform hKc L
  have hopenL : IsOpen {v : ℂ | v.im < c} := isOpen_lt Complex.continuous_im continuous_const
  have hlowsub : {v : ℂ | v.im < c} ⊆ Kcᶜ := by
    intro w hw hcon
    exact absurd (hKcIm w hcon) (not_le.mpr hw)
  set v₀ : ℂ := ((-(c + 1) : ℝ) : ℂ) * Complex.I with hv₀def
  have hv₀im : v₀.im = -(c + 1) := by
    rw [hv₀def]
    simp
  have hv₀low : v₀.im < c := by
    rw [hv₀im]
    linarith
  have hv₀mem : v₀ ∈ Kcᶜ := hlowsub hv₀low
  have hev : cauchyTransform L =ᶠ[nhds v₀] 0 := by
    filter_upwards [hopenL.mem_nhds hv₀low] with w hw
    exact hlow w hw
  exact fun v hv => hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hv₀mem hev hv

end GaloisForLFunctions.HTGeometry
