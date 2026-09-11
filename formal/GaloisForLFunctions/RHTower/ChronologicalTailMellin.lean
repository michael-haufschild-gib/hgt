import GaloisForLFunctions.RHTower.ChronologicalTailTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Mellin transform of a Bose transform

For a measurable profile `g` on `(0,1)` with `∫₀¹ ‖g(x)‖ x^(-s) dx < ∞` and real `0 < s < 1`,

  `∫₀^∞ u^(s-1) (∫₀¹ g(x) h(xu) dx) du = (∫₀^∞ h(y) y^(s-1) dy) · ∫₀¹ g(x) x^(-s) dx`.

This is the multiplicative-convolution law for the Bose kernel: Fubini in `(u,x)` and the scaling
`∫₀^∞ u^(s-1) h(xu) du = x^(-s) ∫₀^∞ h(y) y^(s-1) dy`. The bracket is the strictly positive factor
`boseBracket s` that gets cancelled in the fixed-tail separation argument.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- The Mellin bracket of the Bose kernel. -/
def boseBracket (s : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), fusionBoseDefect y * y ^ (s - 1)

theorem boseBracket_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < boseBracket s :=
  boseMellinBracket_pos h0 h1

theorem measurable_fusionBoseDefect : Measurable fusionBoseDefect := by
  have h : fusionBoseDefect
      = fun t : ℝ => if 0 < t then 1 / t - 1 / (Real.exp t - 1) else 0 := rfl
  rw [h]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  exact (measurable_const.div measurable_id).sub
    (measurable_const.div (Real.measurable_exp.sub measurable_const))

/-! ### The scaling law for the bracket -/

theorem integrableOn_bracketScaled {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => (y / x) ^ (s - 1) * fusionBoseDefect y) (Ioi 0) := by
  have hbase := (integrableOn_boseDefect_rpow hs0 hs1).const_mul ((x ^ (s - 1))⁻¹)
  refine hbase.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : (0 : ℝ) < y := hy
  rw [Real.div_rpow hy0.le hx.le]
  have hxne : x ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  field_simp

theorem integrableOn_scaledBoseDefect {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => u ^ (s - 1) * fusionBoseDefect (x * u)) (Ioi 0) := by
  have hbase : IntegrableOn (fun y : ℝ => (y / x) ^ (s - 1) * fusionBoseDefect y)
      (Ioi (x * 0)) := by
    rw [mul_zero]
    exact integrableOn_bracketScaled hs0 hs1 hx
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => (y / x) ^ (s - 1) * fusionBoseDefect y) 0 hx).mpr hbase
  refine h.congr ?_
  filter_upwards with u
  show ((x * u) / x) ^ (s - 1) * fusionBoseDefect (x * u)
      = u ^ (s - 1) * fusionBoseDefect (x * u)
  rw [mul_div_cancel_left₀ _ (ne_of_gt hx)]

theorem integral_scaledBoseDefect {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fusionBoseDefect (x * u) = x ^ (-s) * boseBracket s := by
  have hcomp := integral_comp_mul_left_Ioi
    (fun y : ℝ => (y / x) ^ (s - 1) * fusionBoseDefect y) 0 hx
  rw [mul_zero] at hcomp
  have hleft : ∫ u in Ioi (0 : ℝ), (fun y : ℝ => (y / x) ^ (s - 1) * fusionBoseDefect y) (x * u)
      = ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fusionBoseDefect (x * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only
    rw [mul_div_cancel_left₀ _ (ne_of_gt hx)]
  have hright : ∫ y in Ioi (0 : ℝ), (y / x) ^ (s - 1) * fusionBoseDefect y
      = (x ^ (s - 1))⁻¹ * boseBracket s := by
    rw [boseBracket, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    have hxne : x ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
    rw [Real.div_rpow hy0.le hx.le]
    field_simp
  have hxe : x⁻¹ * ((x ^ (s - 1))⁻¹) = x ^ (-s) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  rw [← hleft, hcomp, hright, smul_eq_mul, ← mul_assoc, hxe]

/-! ### The transform on the positive axis -/

theorem boseTransform_ofReal (g : ℝ → ℂ) {u : ℝ} (hu : 0 < u) :
    boseTransform g (u : ℂ)
      = ∫ x in Ioo (0 : ℝ) 1, g x * ((fusionBoseDefect (x * u) : ℝ) : ℂ) := by
  rw [boseTransform]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  have hxu : (0 : ℝ) < x * u := mul_pos hx.1 hu
  rw [show ((x : ℂ) * (u : ℂ)) = (((x * u : ℝ)) : ℂ) from by push_cast; ring,
    boseKernelE_ofReal hxu]

/-! ### The Fubini identity -/

theorem mellin_boseTransform {g : ℝ → ℂ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hgm : Measurable g)
    (hint : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1)) :
    ∫ u in Ioi (0 : ℝ), ((u ^ (s - 1) : ℝ) : ℂ) * boseTransform g (u : ℂ)
      = ((boseBracket s : ℝ) : ℂ) * ∫ x in Ioo (0 : ℝ) 1, g x * ((x ^ (-s) : ℝ) : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hν
  set F : ℝ → ℝ → ℂ := fun u x =>
    ((u ^ (s - 1) : ℝ) : ℂ) * (g x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) with hFdef
  have hmeasF : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun p : ℝ × ℝ => ((p.1 ^ (s - 1) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((measurable_fst).pow_const _)
    have h2 : Measurable fun p : ℝ × ℝ => g p.2 := hgm.comp measurable_snd
    have h3 : Measurable fun p : ℝ × ℝ => ((fusionBoseDefect (p.2 * p.1) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (measurable_fusionBoseDefect.comp (measurable_snd.mul measurable_fst))
    exact h1.mul (h2.mul h3)
  have hnormF : ∀ u : ℝ, 0 < u → ∀ x : ℝ, 0 < x →
      ‖F u x‖ = u ^ (s - 1) * ‖g x‖ * fusionBoseDefect (x * u) := by
    intro u hu x hx
    rw [hFdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg hu.le _),
      abs_of_nonneg (fusionBoseDefect_bounds (x * u)).1]
    ring
  have hinner : ∀ x : ℝ, 0 < x → Integrable (fun u : ℝ => F u x) μ := by
    intro x hx
    have hbase := (integrableOn_scaledBoseDefect hs0 hs1 hx).const_mul ‖g x‖
    refine Integrable.mono' (g := fun u : ℝ => ‖g x‖ * (u ^ (s - 1) * fusionBoseDefect (x * u)))
      hbase ?_ ?_
    · refine ((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (measurable_fusionBoseDefect.comp (measurable_const.mul measurable_id))))
        ).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [hnormF u hu x hx]
      ring_nf
      exact le_rfl
  have houter : Integrable (fun x : ℝ => ∫ u : ℝ, ‖Function.uncurry F (u, x)‖ ∂μ) ν := by
    have heq : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
        (∫ u : ℝ, ‖Function.uncurry F (u, x)‖ ∂μ) = boseBracket s * (‖g x‖ * x ^ (-s)) := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hstep : (∫ u : ℝ, ‖Function.uncurry F (u, x)‖ ∂μ)
          = ∫ u in Ioi (0 : ℝ), ‖g x‖ * (u ^ (s - 1) * fusionBoseDefect (x * u)) := by
        rw [hμ]
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        have hu0 : (0 : ℝ) < u := hu
        rw [Function.uncurry_apply_pair, hnormF u hu0 x hx0]
        ring
      rw [hstep, integral_const_mul, integral_scaledBoseDefect hs0 hs1 hx0]
      ring
    refine (hint.const_mul (boseBracket s)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (heq x hx).symm
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine (integrable_prod_iff' hmeasF.aestronglyMeasurable).mpr ⟨?_, houter⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hinner x hx.1
  have hswap := integral_integral_swap hprod
  have hlhs : ∫ u in Ioi (0 : ℝ), ((u ^ (s - 1) : ℝ) : ℂ) * boseTransform g (u : ℂ)
      = ∫ u : ℝ, ∫ x : ℝ, F u x ∂ν ∂μ := by
    rw [hμ]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [boseTransform_ofReal g hu0, hν, ← integral_const_mul]
  have hrhs : ∫ x : ℝ, ∫ u : ℝ, F u x ∂μ ∂ν
      = ((boseBracket s : ℝ) : ℂ) * ∫ x in Ioo (0 : ℝ) 1, g x * ((x ^ (-s) : ℝ) : ℂ) := by
    rw [← integral_const_mul, hν]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx.1
    have hcast : ∫ u : ℝ, F u x ∂μ
        = (Complex.ofRealCLM (∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fusionBoseDefect (x * u))) *
          g x := by
      have hstep : ∫ u : ℝ, F u x ∂μ
          = ∫ u : ℝ, Complex.ofRealCLM (u ^ (s - 1) * fusionBoseDefect (x * u)) * g x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
        rw [hFdef]
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
        ring
      rw [hstep, integral_mul_const,
        ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM
          (integrableOn_scaledBoseDefect hs0 hs1 hx0)]
    rw [hcast, integral_scaledBoseDefect hs0 hs1 hx0]
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
    ring
  rw [hlhs, hswap, hrhs]

end RHTower
