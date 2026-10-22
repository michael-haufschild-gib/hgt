import GaloisForLFunctions.RHTower.Suzuki.SuzukiHalfInnerLocalFactor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

/-!
# `A/E` on the real axis, unconditionally

The half `A/E = (1+Θ)/2` is holomorphic on a neighbourhood of every real point, with no appeal to
the Riemann hypothesis.  Indeed `A` and `A'` are real on the real axis, so `E = A + iA'` can vanish
at a real point only where `A` itself vanishes, and there the local factorisation of
`SuzukiHalfInnerLocalFactor` already supplies holomorphy.

Consequently the divided slope `dslope (A/E) c` at any zero `c` of `A` — real or not — is
continuous along the real axis, and it lies in `L²(ℝ)`: near `c.re` it is bounded by compactness,
and away from `c.re` it is bounded by `1/‖x - c‖` because `|A/E| ≤ 1` on the real axis.

This is the unconditional replacement for the Hermite--Biehler route of `SuzukiFGammaOrthonormal`,
which produced the same conclusions only above the axis and only under RH.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower

/-- On the real axis `E = A + iA'` vanishes only where `A` does: both `A` and `A'` are real
there. -/
theorem XiC_eq_zero_of_xiHedenmalmDeBrangesE_eq_zero_ofReal {x : ℝ}
    (hE : xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) = 0) : XiC ((x : ℝ) : ℂ) = 0 := by
  have hAc : (starRingEnd ℂ) (XiC ((x : ℝ) : ℂ)) = XiC ((x : ℝ) : ℂ) := by
    rw [← XiC_conj]
    simp
  have hA'c : (starRingEnd ℂ) (deriv XiC ((x : ℝ) : ℂ)) = deriv XiC ((x : ℝ) : ℂ) := by
    rw [← deriv_XiC_conj]
    simp
  have hE' := congrArg (starRingEnd ℂ) hE
  rw [xiHedenmalmDeBrangesE, map_add, map_mul, Complex.conj_I, hAc, hA'c, map_zero] at hE'
  rw [xiHedenmalmDeBrangesE] at hE
  linear_combination (hE + hE') / 2

/-- `A/E` is holomorphic on a whole neighbourhood of every real point. -/
theorem eventually_differentiableAt_suzukiHalfInner_ofReal (x : ℝ) :
    ∀ᶠ z in 𝓝 ((x : ℝ) : ℂ), DifferentiableAt ℂ suzukiHalfInner z := by
  by_cases hE : xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) = 0
  · exact eventually_differentiableAt_suzukiHalfInner
      (XiC_eq_zero_of_xiHedenmalmDeBrangesE_eq_zero_ofReal hE)
  · have hne : ∀ᶠ z in 𝓝 ((x : ℝ) : ℂ), xiHedenmalmDeBrangesE z ≠ 0 :=
      (differentiable_xiHedenmalmDeBrangesE _).continuousAt.eventually_ne hE
    filter_upwards [hne] with z hz
    exact (XiC_differentiable z).div (differentiable_xiHedenmalmDeBrangesE z) hz

theorem differentiableAt_suzukiHalfInner_ofReal (x : ℝ) :
    DifferentiableAt ℂ suzukiHalfInner ((x : ℝ) : ℂ) :=
  (eventually_differentiableAt_suzukiHalfInner_ofReal x).self_of_nhds

variable {c : ℂ}

/-- The divided slope of `A/E` at a zero of `A` is holomorphic at every real point. -/
theorem differentiableAt_dslope_suzukiHalfInner_ofReal (hc : XiC c = 0) (x : ℝ) :
    DifferentiableAt ℂ (dslope suzukiHalfInner c) ((x : ℝ) : ℂ) := by
  rcases eq_or_ne ((x : ℝ) : ℂ) c with h | hne
  · obtain ⟨g, hg, hfac, _⟩ := exists_localFactor_suzukiHalfInner_of_XiC_zero hc
    rw [h]
    exact GaloisForLFunctions.HTGeometry.differentiableAt_dslope_of_localFactor hg hfac
  · exact (differentiableAt_dslope_of_ne hne).mpr (differentiableAt_suzukiHalfInner_ofReal x)

theorem continuous_dslope_suzukiHalfInner_ofReal (hc : XiC c = 0) :
    Continuous fun x : ℝ => dslope suzukiHalfInner c ((x : ℝ) : ℂ) :=
  continuous_iff_continuousAt.mpr fun x =>
    ((differentiableAt_dslope_suzukiHalfInner_ofReal hc x).continuousAt).comp
      Complex.continuous_ofReal.continuousAt

/-- Off the centre the divided slope is bounded by the Cauchy kernel, because `|A/E| ≤ 1` on the
real axis. -/
theorem norm_dslope_suzukiHalfInner_ofReal_le (hc : XiC c = 0) {x : ℝ}
    (hx : ((x : ℝ) : ℂ) ≠ c) :
    ‖dslope suzukiHalfInner c ((x : ℝ) : ℂ)‖ ≤ 1 / ‖((x : ℝ) : ℂ) - c‖ := by
  have hden : ‖((x : ℝ) : ℂ) - c‖ ≠ 0 := by
    simpa [sub_eq_zero] using hx
  rw [dslope_suzukiHalfInner_apply hc hx, norm_div, div_le_div_iff_of_pos_right
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hden))]
  exact norm_suzukiHalfInner_ofReal_le_one x

theorem norm_sq_ofReal_sub_center (w : ℂ) (x : ℝ) :
    ‖((x : ℝ) : ℂ) - w‖ ^ (2 : ℕ) = (x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  simp
  ring

/-- A single Cauchy-kernel majorant for the squared modulus of the divided slope along the real
axis: bounded near the centre by compactness, and by `1/(x-c.re)^(2 : ℕ)` far away. -/
theorem exists_bound_norm_sq_dslope_suzukiHalfInner (hc : XiC c = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
      ‖dslope suzukiHalfInner c ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ D / (1 + (x - c.re) ^ (2 : ℕ)) := by
  set f : ℝ → ℂ := fun x => dslope suzukiHalfInner c ((x : ℝ) : ℂ) with hf
  have hcont : Continuous f := continuous_dslope_suzukiHalfInner_ofReal hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c.re - 1) (b := c.re + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (f c.re)) (hC c.re (by constructor <;> linarith))
  refine ⟨2 * C ^ (2 : ℕ) + 2, by positivity, fun x => ?_⟩
  have hpos : (0 : ℝ) < 1 + (x - c.re) ^ (2 : ℕ) := by positivity
  rw [le_div_iff₀ hpos]
  by_cases hx : x ∈ Set.Icc (c.re - 1) (c.re + 1)
  · have h1 : ‖f x‖ ≤ C := hC x hx
    have h2 : (x - c.re) ^ (2 : ℕ) ≤ 1 := by
      obtain ⟨hl, hr⟩ := hx
      nlinarith
    nlinarith [norm_nonneg (f x), sq_nonneg (x - c.re)]
  · have hfar : 1 < (x - c.re) ^ (2 : ℕ) := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h <;> nlinarith
    have hne : ((x : ℝ) : ℂ) ≠ c := by
      intro h
      have hxc : x = c.re := by rw [← h]; simp
      rw [hxc] at hfar
      simp at hfar
      linarith
    have hden : (0 : ℝ) < ‖((x : ℝ) : ℂ) - c‖ := by
      simpa [sub_eq_zero] using hne
    have h1 : ‖f x‖ ≤ 1 / ‖((x : ℝ) : ℂ) - c‖ := norm_dslope_suzukiHalfInner_ofReal_le hc hne
    have h2 : ‖f x‖ ^ (2 : ℕ) ≤ 1 / ‖((x : ℝ) : ℂ) - c‖ ^ (2 : ℕ) := by
      have hsq := mul_self_le_mul_self (norm_nonneg (f x)) h1
      rw [← pow_two] at hsq
      calc ‖f x‖ ^ (2 : ℕ)
          ≤ (1 / ‖((x : ℝ) : ℂ) - c‖) * (1 / ‖((x : ℝ) : ℂ) - c‖) := hsq
        _ = 1 / ‖((x : ℝ) : ℂ) - c‖ ^ (2 : ℕ) := by field_simp
    rw [norm_sq_ofReal_sub_center] at h2
    have h3 : (0 : ℝ) < (x - c.re) ^ (2 : ℕ) + c.im ^ (2 : ℕ) := by nlinarith [sq_nonneg c.im]
    have h4 : ‖f x‖ ^ (2 : ℕ) * ((x - c.re) ^ (2 : ℕ) + c.im ^ (2 : ℕ)) ≤ 1 := by
      rw [← le_div_iff₀ h3]
      simpa using h2
    nlinarith [sq_nonneg c.im, norm_nonneg (f x), sq_nonneg (‖f x‖)]

theorem integrable_norm_sq_dslope_suzukiHalfInner (hc : XiC c = 0) :
    Integrable (fun x : ℝ => ‖dslope suzukiHalfInner c ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)) := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_norm_sq_dslope_suzukiHalfInner hc
  have hg : Integrable (fun x : ℝ => D * (1 + (x - c.re) ^ (2 : ℕ))⁻¹) :=
    (integrable_inv_one_add_sq.comp_sub_right c.re).const_mul D
  refine Integrable.mono' hg
    (((continuous_dslope_suzukiHalfInner_ofReal hc).norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hD x
  rwa [div_eq_mul_inv] at h

/-- **The divided slope of `A/E` at any zero of `A` is square-integrable on the line.**
Unconditional: no Hermite--Biehler input, no half-plane. -/
theorem memLp_dslope_suzukiHalfInner (hc : XiC c = 0) :
    MemLp (fun x : ℝ => dslope suzukiHalfInner c ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_dslope_suzukiHalfInner_ofReal hc).aestronglyMeasurable).mpr
    (integrable_norm_sq_dslope_suzukiHalfInner hc)

end RHTower
