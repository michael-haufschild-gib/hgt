import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma41
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Suzuki's canonical Hankel unitary: physical kernel formula

The logarithmic kernel identity in `SuzukiCanonicalHankelLemma41` is converted back to Suzuki's
literal physical carrier.  For every compactly supported smooth logarithmic half-density `g`, the
canonical spectral unitary agrees almost everywhere on `(0,∞)` with

`x ↦ ∫ y in (0,∞), h_omega (x*y) f(y) dy`.

This is the physical-coordinate part of Suzuki (2012), Lemma 4.1 needed to identify finite
compressions with the already constructed literal Hilbert--Schmidt kernel operator.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Exact logarithmic-to-positive coordinate formula -/

theorem logEvenUnitary_symm_eq_invLogEvenEven (q : SoninL2) :
    logEvenUnitary.symm q = invLogEvenEven q := by
  apply logEvenUnitary.injective
  rw [logEvenUnitary.apply_symm_apply]
  exact (logEvenIsometry_invLogEvenEven q).symm

/-- The exact positive-ray representative of a logarithmic half-density. -/
theorem suzukiPositiveHalfLineUnitary_logEven_symm_ae (q : SoninL2) :
    (suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x => (Real.exp (-(Real.log x) / 2) : ℂ) *
          l2MeasurableRep q (Real.log x) := by
  rw [logEvenUnitary_symm_eq_invLogEvenEven]
  filter_upwards [suzukiPositiveRestriction_ae (invLogEvenEven q),
    ae_restrict_of_ae (invLogEvenAux_ae q), ae_restrict_mem measurableSet_Ioi] with
      x hpos hinv hx
  change suzukiPositiveRestriction (invLogEvenEven q) x = _
  rw [hpos]
  change ((Real.sqrt 2 : ℝ) : ℂ) * invLogEvenAux q x = _
  rw [hinv]
  simp only [invLogEvenFun, invLogEvenWeight]
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [if_neg hx0, abs_of_pos hx]
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) *
      ((((Real.sqrt 2)⁻¹ * Real.exp (-(Real.log x) / 2) : ℝ) : ℂ) *
        l2MeasurableRep q (Real.log x)) =
      (((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
        (Real.exp (-(Real.log x) / 2) : ℂ) *
          l2MeasurableRep q (Real.log x) by push_cast; ring]
  rw [hsqrt, one_mul]

/-! ## Exponential substitution for Bochner integrals -/

/-- Exact Bochner-integral substitution `y = exp t` on the positive ray. -/
theorem integral_Ioi_eq_integral_exp_smul (F : ℝ → ℂ) :
    (∫ y : ℝ in Ioi (0 : ℝ), F y) =
      ∫ t : ℝ, Real.exp t • F (Real.exp t) := by
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := (Set.univ : Set ℝ)) MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn F
  rw [Set.image_univ, Real.range_exp, setIntegral_univ] at hcov
  simpa only [abs_of_pos (Real.exp_pos _)] using hcov

/-- `log : (0,∞) → ℝ` preserves null sets in the pullback direction.  This is the missing
measure-class fact needed to move almost-everywhere logarithmic identities to the physical ray. -/
theorem realLog_restrict_Ioi_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.log
      (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, ?_⟩
  intro s hs
  let t := MeasureTheory.toMeasurable volume s
  have htm : MeasurableSet t := MeasureTheory.measurableSet_toMeasurable _ _
  have ht0 : volume t = 0 := by
    simpa only [t, MeasureTheory.measure_toMeasurable] using hs
  have himage : volume (Real.exp '' t) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := volume) (f := Real.exp) Real.differentiable_exp.differentiableOn ht0
  have hpre : (volume.restrict (Ioi (0 : ℝ))) (Real.log ⁻¹' t) = 0 := by
    rw [Measure.restrict_apply (htm.preimage Real.measurable_log)]
    apply le_antisymm _ bot_le
    apply le_trans (measure_mono ?_) (le_of_eq himage)
    rintro x ⟨hxt, hx⟩
    refine ⟨Real.log x, hxt, ?_⟩
    exact Real.exp_log hx
  apply le_antisymm _ bot_le
  calc
    (volume.restrict (Ioi (0 : ℝ))).map Real.log s ≤
        (volume.restrict (Ioi (0 : ℝ))).map Real.log t :=
      measure_mono (MeasureTheory.subset_toMeasurable volume s)
    _ = (volume.restrict (Ioi (0 : ℝ))) (Real.log ⁻¹' t) :=
      Measure.map_apply_of_aemeasurable Real.measurable_log.aemeasurable htm
    _ = 0 := hpre

/-! ## Literal input and output representatives -/

theorem suzukiCompactSmoothPositiveL2_ae
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    (suzukiCompactSmoothPositiveL2 g hsmooth hcompact : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun y => (Real.exp (-(Real.log y) / 2) : ℂ) * g (Real.log y) := by
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae
    (suzukiCompactSmoothLogL2 g hsmooth hcompact)
  have hrepBase : l2MeasurableRep (suzukiCompactSmoothLogL2 g hsmooth hcompact) =ᵐ[volume] g :=
    (l2MeasurableRep_ae _).trans (suzukiStrongLogL2_ae
      (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact)
  have hrep := hrepBase.comp_tendsto
      realLog_restrict_Ioi_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcoord, hrep] with y hcoord hrep
  change (suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm (suzukiCompactSmoothLogL2 g hsmooth hcompact)) : ℝ → ℂ) y = _
  rw [hcoord]
  change l2MeasurableRep (suzukiCompactSmoothLogL2 g hsmooth hcompact) (Real.log y) =
    g (Real.log y) at hrep
  rw [hrep]

theorem suzukiCompactSmoothLiteralPositiveHankelL2_ae
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    (suzukiCompactSmoothLiteralPositiveHankelL2 omega c homega hc hinner
        g hsmooth hcompact : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x => (Real.exp (-(Real.log x) / 2) : ℂ) *
          suzukiLiteralLogHankel omega
            (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) (Real.log x) := by
  let G := suzukiCompactSmoothStrongLogTarget g hsmooth hcompact
  let q := suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
    g hsmooth hcompact
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  have hrepBase : l2MeasurableRep q =ᵐ[volume] suzukiLiteralLogHankel omega G :=
    (l2MeasurableRep_ae q).trans
      (memLp_two_suzukiLiteralLogHankel homega hc hinner G hcompact).coeFn_toLp
  have hrepLog := hrepBase.comp_tendsto
    realLog_restrict_Ioi_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcoord, hrepLog] with x hcoord hrep
  change (suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) : ℝ → ℂ) x = _
  rw [hcoord]
  change l2MeasurableRep q (Real.log x) =
      suzukiLiteralLogHankel omega G (Real.log x) at hrep
  rw [hrep]

/-! ## Physical kernel identity -/

/-- **Suzuki (2012), Lemma 4.1, literal physical a.e. kernel formula.** -/
theorem suzuki2012_lemma_four_one_positive_half_line_ae_kernel
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    (suzukiCanonicalPositiveHankelUnitary omega hinner
        (suzukiCompactSmoothPositiveL2 g hsmooth hcompact) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x => ∫ y : ℝ in Ioi (0 : ℝ),
          suzukiSourceHFinite omega (x * y) *
            suzukiCompactSmoothPositiveL2 g hsmooth hcompact y := by
  rw [suzuki2012_lemma_four_one_positive_half_line_literal_kernel
    homega hc hinner g hsmooth hcompact]
  let G := suzukiCompactSmoothStrongLogTarget g hsmooth hcompact
  have hout := suzukiCompactSmoothLiteralPositiveHankelL2_ae
    homega hc hinner g hsmooth hcompact
  have hin := suzukiCompactSmoothPositiveL2_ae g hsmooth hcompact
  have hinWhole := (ae_restrict_iff' measurableSet_Ioi).mp hin
  have hinExp := realExp_quasiMeasurePreserving.ae hinWhole
  filter_upwards [hout, ae_restrict_mem measurableSet_Ioi] with x hxout hxpos
  rw [hxout]
  rw [integral_Ioi_eq_integral_exp_smul]
  have hrhs :
      (∫ t : ℝ, Real.exp t •
        (suzukiSourceHFinite omega (x * Real.exp t) *
          suzukiCompactSmoothPositiveL2 g hsmooth hcompact (Real.exp t))) =
      ∫ t : ℝ, (Real.exp (t / 2) : ℂ) *
        suzukiSourceHFinite omega (x * Real.exp t) * g t := by
    apply integral_congr_ae
    filter_upwards [hinExp] with t hin
    have hin' := hin (Real.exp_pos t)
    rw [hin']
    simp only [Real.log_exp]
    change (Real.exp t : ℂ) *
        (suzukiSourceHFinite omega (x * Real.exp t) *
          ((Real.exp (-t / 2) : ℂ) * g t)) = _
    have hcoef : (Real.exp t : ℂ) * (Real.exp (-t / 2) : ℂ) =
        (Real.exp (t / 2) : ℂ) := by
      norm_cast
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show (Real.exp t : ℂ) *
        (suzukiSourceHFinite omega (x * Real.exp t) *
          ((Real.exp (-t / 2) : ℂ) * g t)) =
        ((Real.exp t : ℂ) * (Real.exp (-t / 2) : ℂ)) *
          suzukiSourceHFinite omega (x * Real.exp t) * g t by ring,
      hcoef]
  rw [hrhs]
  rw [suzukiLiteralLogHankel]
  change (Real.exp (-(Real.log x) / 2) : ℂ) *
      (∫ s : ℝ, (Real.exp ((Real.log x + s) / 2) : ℂ) *
        suzukiSourceHFinite omega (Real.exp (Real.log x + s)) *
          (G : ℝ → ℂ) s) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [G, suzukiCompactSmoothStrongLogTarget]
  have hkernelArg : Real.exp (Real.log x + t) = x * Real.exp t := by
    rw [Real.exp_add, Real.exp_log hxpos]
  rw [hkernelArg]
  have hcoef : (Real.exp (-(Real.log x) / 2) : ℂ) *
      (Real.exp ((Real.log x + t) / 2) : ℂ) =
      (Real.exp (t / 2) : ℂ) := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (Real.exp (-(Real.log x) / 2) : ℂ) *
      ((Real.exp ((Real.log x + t) / 2) : ℂ) *
        suzukiSourceHFinite omega (x * Real.exp t) * g t) =
      ((Real.exp (-(Real.log x) / 2) : ℂ) *
        (Real.exp ((Real.log x + t) / 2) : ℂ)) *
          suzukiSourceHFinite omega (x * Real.exp t) * g t by ring,
    hcoef]

end RHTower
