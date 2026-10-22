import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinResolventExponentialWidth

/-!
# A one-sided bound on the integrated Chebyshev deficit bounds the zero width

Let `D(T) = ∫_0^T (e^t − ψ(e^t)) dt`. The corpus proves that `−B(1+T)e^{T/2} ≤ D(T)` forces RH
(`RHTower.riemannHypothesis_of_logChebyshevDeficitPrimitive_ge_mul`). This file proves the
quantitative version at every width.

**Theorem** (`xiZeroHalfPlaneBound_of_deficitPrimitive_ge`). Let `0 ≤ α < ½`. If
`−B(1+T) e^{(1/2+α)T} ≤ D(T)` for all `T ≥ 0`, then every zero of `ξ` has `Re ρ ≤ ½ + α`. The same
holds for the reverse bound (`xiZeroHalfPlaneBound_of_deficitPrimitive_le`).

**Mechanism.** Landau's theorem at width `α`.
* `g(T) = B(1+T) ± e^{−(1/2+α)T} D(T)` is a nonnegative density; its Laplace transform equals
  `(B+1)/z + B/z² ± (ζ_u'/ζ_u(z+½+α) + 1)/(z+½+α)²` for real `z > ½ − α`, which is analytic at every
  real `z > 0`. Landau moves the abscissa to `0`.
* The transform then continues the regularized critical-Mellin defect to `Re u > α − ½`
  (`xiZeroHalfPlaneBound_of_regularizedCriticalMellinDefect_extensionAbove`), and rotating into Xi
  coordinates excludes every zero right of `½ + α`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions
open _root_.RHTower GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. A continuation of the defect above `α − ½` bounds the zero width -/

/-- **Extension above `α − ½`.** If an analytic function on `Re u > α − ½` agrees with the
regularized critical-Mellin defect on `Re u > 0`, then every Xi zero has `Re ρ ≤ ½ + α`. -/
theorem xiZeroHalfPlaneBound_of_regularizedCriticalMellinDefect_extensionAbove {α : ℝ}
    (hα : 0 ≤ α) (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A {s : ℂ | α - 1 / 2 < s.re})
    (hagree : ∀ s : ℂ, 0 < s.re → A s = regularizedCriticalMellinDefect s) :
    XiZeroHalfPlaneBound α := by
  let B : ℂ → ℂ := fun w =>
    -I * (A (-1 / 2 - I * w) + gammaRealLogConnection (1 / 2 - I * w))
  have hB : AnalyticOnNhd ℂ B (GaloisForLFunctions.RHTower.ccmXiUpperHalfPlaneAbove α) := by
    intro w hw
    change α < w.im at hw
    have hs : -1 / 2 - I * w ∈ {s : ℂ | α - 1 / 2 < s.re} := by
      change α - 1 / 2 < (-1 / 2 - I * w).re
      simp [mul_re]
      linarith
    have hinner : AnalyticAt ℂ (fun z : ℂ => -1 / 2 - I * z) w := by fun_prop
    have hAcomp : AnalyticAt ℂ (fun z : ℂ => A (-1 / 2 - I * z)) w :=
      AnalyticAt.comp (f := fun z : ℂ => -1 / 2 - I * z) (hA _ hs) hinner
    have hgammaArg : 0 < ((1 / 2 - I * w) / 2).re := by
      norm_num [Complex.div_re, mul_re]
      linarith
    have hgammaBase : AnalyticAt ℂ Complex.digamma ((1 / 2 - I * w) / 2) :=
      digamma_analyticOnNhd_re_pos _ hgammaArg
    have hgammaInner : AnalyticAt ℂ (fun z : ℂ => (1 / 2 - I * z) / 2) w := by fun_prop
    have hgammaComp : AnalyticAt ℂ (fun z : ℂ => Complex.digamma ((1 / 2 - I * z) / 2)) w :=
      AnalyticAt.comp (f := fun z : ℂ => (1 / 2 - I * z) / 2) hgammaBase hgammaInner
    have hconn : AnalyticAt ℂ (fun z : ℂ => gammaRealLogConnection (1 / 2 - I * z)) w := by
      unfold gammaRealLogConnection
      fun_prop
    exact analyticAt_const.mul (hAcomp.add hconn)
  have hBagree : ∀ w : ℂ, 1 / 2 < w.im → B w = logDeriv XiC w := by
    intro w hw
    let z : ℂ := -w
    let s : ℂ := 1 / 2 + z * I
    have hsre : 1 < s.re := by
      dsimp only [s, z]
      simp [mul_re]
      linarith
    have hspos : 0 < s.re := lt_trans zero_lt_one hsre
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.zero_re] at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.one_re] at hre
      linarith
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hsre
    have htrace : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
      rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hspos hs1 hzeta]
      exact (logDeriv_XiC_eq_relativeResolventTrace
        (by
          change xi s ≠ 0
          rw [xi_eq_archFactor_mul_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)]
          exact mul_ne_zero
            (archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)) hzeta)).symm
    have hsource := continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma hspos hs0 hs1
    have hcoord : xiCriticalMellinCoordinate z = -1 / 2 - I * w := by
      dsimp only [xiCriticalMellinCoordinate, z]
      ring
    have hgammaCoord : 1 / 2 + z * I = 1 / 2 - I * w := by
      dsimp only [z]
      ring
    have hdefRe : 0 < (-1 / 2 - I * w).re := by
      simp [mul_re]
      linarith
    have hdef := hagree (-1 / 2 - I * w) hdefRe
    have hreg := regularizedCriticalMellinDefect_eq_continued hdefRe
    dsimp only [B]
    rw [hdef]
    have hsource' : continuedPrimeArchSourceRelativeTrace z =
        I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
          gammaRealLogConnection (1 / 2 - I * w)) := by
      rw [hsource, continuedMellinGammaSourceTrace, hcoord, hgammaCoord]
      rw [← hreg]
    rw [hsource'] at htrace
    rw [show logDeriv XiC z = -logDeriv XiC w by
      dsimp only [z]
      rw [logDeriv_XiC_neg]] at htrace
    calc
      -I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
          gammaRealLogConnection (1 / 2 - I * w)) =
          -(I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
            gammaRealLogConnection (1 / 2 - I * w))) := by ring
      _ = -(-logDeriv XiC w) := by rw [htrace]
      _ = logDeriv XiC w := neg_neg _
  exact GaloisForLFunctions.RHTower.xiZeroHalfPlaneBound_of_upper_logDeriv_extensionAbove B hB hBagree

/-! ### 2. The one-sided Landau measure at width `α` -/

/-- The clipped density `max(B(1+T) + ε e^{−(1/2+α)T} D(T), 0)`. -/
def widthDeficitDensity (α ε B : ℝ) (T : ℝ) : NNReal :=
  Real.toNNReal (B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T))

theorem measurable_widthDeficitDensity (α ε B : ℝ) : Measurable (widthDeficitDensity α ε B) := by
  unfold widthDeficitDensity
  exact ((measurable_const.mul (measurable_const.add measurable_id)).add (measurable_const.mul
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_deficitPrimitive).measurable)).real_toNNReal

/-- `(B(1+T) + ε e^{−(1/2+α)T} D(T)) dT` on `(0,∞)` plus Lebesgue measure. -/
def widthDeficitMeasure (α ε B : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun T => (widthDeficitDensity α ε B T : ENNReal)) +
    volume

theorem widthDeficitDensity_le {α ε B : ℝ} (hε : |ε| ≤ 1) {T : ℝ} (hT : 0 < T) :
    ((widthDeficitDensity α ε B T : ℝ)) ≤
      |B| * (1 + T) + chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T) := by
  unfold widthDeficitDensity
  rw [Real.coe_toNNReal']
  have hD := abs_deficitPrimitive_le hT.le
  have he : Real.exp (-(1 / 2 + α) * T) * Real.exp T = Real.exp ((1 / 2 - α) * T) := by
    rw [← Real.exp_add]; congr 1; ring
  have hprod : |Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T| ≤
      chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(1 / 2 + α) * T) * |ccmLogChebyshevDeficitPrimitive T|
        ≤ Real.exp (-(1 / 2 + α) * T) * (chebyshevDeficitConst * Real.exp T) :=
          mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le
      _ = chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T) := by rw [← he]; ring
  have hε' : |ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T)| ≤
      chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T) := by
    rw [abs_mul]
    calc |ε| * |Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T|
        ≤ 1 * (chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T)) :=
          mul_le_mul hε hprod (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h1 : B * (1 + T) ≤ |B| * (1 + T) :=
    mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
  have h2 := le_abs_self (ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T))
  have h3 : 0 ≤ |B| * (1 + T) + chebyshevDeficitConst * Real.exp ((1 / 2 - α) * T) := by
    have := chebyshevDeficitConst_pos; positivity
  rcases le_or_gt (B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) *
    ccmLogChebyshevDeficitPrimitive T)) 0 with h | h
  · rw [max_eq_right h]; exact h3
  · rw [max_eq_left h.le]; linarith

theorem integrableOn_widthDeficitMajorant {α σ B : ℝ} (hσ : 1 / 2 - α < σ) (hσ0 : 0 < σ) :
    IntegrableOn (fun T : ℝ => (|B| * (1 + T) + chebyshevDeficitConst *
      Real.exp ((1 / 2 - α) * T)) * Real.exp (-σ * T)) (Ioi 0) := by
  have h1 : IntegrableOn (fun T : ℝ => |B| * (Real.exp (-σ * T) + T * Real.exp (-σ * T))) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 hσ0).add (integrableOn_id_mul_real_exp_neg_mul hσ0)).const_mul _
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - (1 / 2 - α))).const_mul
    chebyshevDeficitConst
  refine IntegrableOn.congr_fun (h1.add h2) (fun T _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [show Real.exp (-(σ - (1 / 2 - α)) * T) = Real.exp ((1 / 2 - α) * T) * Real.exp (-σ * T) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_widthDeficitDensity_ne_top {α ε B σ : ℝ} (hε : |ε| ≤ 1)
    (hσ : 1 / 2 - α < σ) (hσ0 : 0 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun T => (widthDeficitDensity α ε B T : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun T : ℝ => ENNReal.ofReal (Real.exp (-σ * T))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_widthDeficitDensity α ε B).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top (integrableOn_widthDeficitMajorant (B := B) hσ hσ0).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (widthDeficitDensity_le hε hT) (Real.exp_pos _).le

theorem laplaceMass_widthDeficitMeasure_eq (α ε B σ : ℝ) :
    laplaceMass (widthDeficitMeasure α ε B) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (widthDeficitDensity α ε B T : ENNReal))) σ + laplaceMass volume σ := by
  unfold laplaceMass widthDeficitMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

theorem isAbscissa_widthDeficitMeasure {α ε B : ℝ} (hα : 0 ≤ α) (hε : |ε| ≤ 1) :
    IsAbscissa (widthDeficitMeasure α ε B)
        (sInf {σ : ℝ | laplaceMass (widthDeficitMeasure α ε B) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (widthDeficitMeasure α ε B) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (widthDeficitMeasure α ε B) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_widthDeficitMeasure_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (widthDeficitMeasure α ε B) 1 ≠ ⊤
    rw [laplaceMass_widthDeficitMeasure_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_widthDeficitDensity_ne_top hε (by linarith) one_pos,
      laplaceMass_volume_ne_top one_pos⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ### 3. The real Laplace transform -/

/-- The candidate continuation `(B+1)/z + B/z² + ε (ζ_u'/ζ_u(z+½+α) + 1)/(z+½+α)²`. -/
def widthDeficitContinuation (α ε B : ℝ) (z : ℂ) : ℂ :=
  (B + 1) / z + B / z ^ 2 +
    ε * ((logDeriv zetaResidueUnit (z + 1 / 2 + α) + 1) / (z + 1 / 2 + α) ^ 2)

theorem analyticAt_widthDeficitContinuation (α ε B : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z + 1 / 2 + α ≠ 0) (hζ : zetaResidueUnit (z + 1 / 2 + α) ≠ 0) :
    AnalyticAt ℂ (widthDeficitContinuation α ε B) z := by
  unfold widthDeficitContinuation
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2 + α) z := by fun_prop
  have hζan : AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2 + α)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2 + α) (analyticAt_zetaResidueUnit _) hshift
  have hdζ : AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2 + α)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2 + α) (analyticAt_zetaResidueUnit _).deriv hshift
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2 + α)) z := by
    simp only [logDeriv_apply]
    exact hdζ.div hζan hζ
  refine ((analyticAt_const.div analyticAt_id hz0).add
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hz0))).add (analyticAt_const.mul ?_)
  exact (hlog.add analyticAt_const).div (hshift.pow 2) (pow_ne_zero 2 hz1)

theorem widthDeficitDensity_eq {α ε B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T →
      0 ≤ B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T))
    {T : ℝ} (hT : 0 ≤ T) :
    ((widthDeficitDensity α ε B T : ℝ)) =
      B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T) := by
  unfold widthDeficitDensity
  exact Real.coe_toNNReal _ (hB T hT)

/-- On real `σ > ½ − α` the Laplace transform of the width measure is the continuation. -/
theorem laplaceReal_widthDeficitMeasure_eq {α ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T →
      0 ≤ B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T))
    {σ : ℝ} (hσ : 1 / 2 - α < σ) (hσ0 : 0 < σ) :
    ((laplaceReal (widthDeficitMeasure α ε B) σ : ℝ) : ℂ) =
      widthDeficitContinuation α ε B (σ : ℂ) := by
  have hexpInt : IntegrableOn (fun T : ℝ => Real.exp (-σ * T)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hσ0
  have hdensInt : Integrable (fun T : ℝ => Real.exp (-σ * T))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (widthDeficitDensity α ε B T : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_widthDeficitDensity α ε B)]
    refine (integrableOn_widthDeficitMajorant (B := B) hσ hσ0).mono' ?_ ?_
    · exact ((measurable_widthDeficitDensity α ε B).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (widthDeficitDensity_le hε hT) (Real.exp_pos _).le
  have hsplit : laplaceReal (widthDeficitMeasure α ε B) σ =
      (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (widthDeficitDensity α ε B T : ENNReal)))) + 1 / σ := by
    unfold laplaceReal widthDeficitMeasure
    rw [Measure.restrict_add, integral_add_measure hdensInt hexpInt,
      integral_exp_neg_mul_Ioi_real hσ0]
  have hdens : (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (widthDeficitDensity α ε B T : ENNReal)))) =
      B / σ + B / σ ^ 2 + ε * ∫ T in Ioi (0:ℝ),
        Real.exp (-(σ + 1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_widthDeficitDensity α ε B)]
    have hpt : ∀ T ∈ Ioi (0:ℝ), widthDeficitDensity α ε B T • Real.exp (-σ * T) =
        (B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T))) +
          ε * (Real.exp (-(σ + 1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T) := by
      intro T hT
      rw [NNReal.smul_def, smul_eq_mul, widthDeficitDensity_eq hB (le_of_lt hT)]
      have he : Real.exp (-(1 / 2 + α) * T) * Real.exp (-σ * T) =
          Real.exp (-(σ + 1 / 2 + α) * T) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [← he]; ring
    have hf : Integrable (fun T : ℝ => B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T)))
        (volume.restrict (Ioi 0)) :=
      (hexpInt.const_mul B).add ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add hf
        ((integrableOn_exp_mul_deficitPrimitive (by linarith : 1 < σ + 1 / 2 + α)).const_mul ε),
      integral_add (hexpInt.const_mul B) ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_exp_neg_mul_Ioi_real hσ0,
      integral_id_mul_real_exp_neg_mul hσ0]
    ring
  rw [hsplit, hdens, integral_exp_mul_deficitPrimitive (by linarith : 1 < σ + 1 / 2 + α)]
  have hL := integral_exp_mul_chebyshevLogDeficit_eq_laplace (σ + α)
  rw [show σ + α + 1 / 2 = σ + 1 / 2 + α by ring] at hL
  have hlog := criticalNormalizedChebyshevErrorLaplace_eq_logDeriv (z := ((σ + α : ℝ) : ℂ))
    (by simp; linarith)
  unfold widthDeficitContinuation
  push_cast
  push_cast at hL hlog
  rw [hL, hlog]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hσh : (σ : ℂ) + 1 / 2 + α ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simp at hre; linarith
  have hσh' : (σ : ℂ) + α + 1 / 2 ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simp at hre; linarith
  rw [show (σ : ℂ) + α + 1 / 2 = (σ : ℂ) + 1 / 2 + α by ring]
  field_simp
  ring

/-! ### 4. Landau: the abscissa is zero -/

theorem abscissa_widthDeficitMeasure_eq_zero {α ε B : ℝ} (hα : 0 ≤ α) (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T →
      0 ≤ B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T)) :
    IsAbscissa (widthDeficitMeasure α ε B) 0 := by
  obtain ⟨hc, hc0⟩ := isAbscissa_widthDeficitMeasure (B := B) hα hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (widthDeficitMeasure α ε B) σ ≠ ⊤} with hcdef
  rcases hc0.lt_or_eq with hpos | hzero
  · exfalso
    have hζc : zetaResidueUnit ((c : ℂ) + 1 / 2 + α) ≠ 0 := by
      have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := c + 1 / 2 + α) (by linarith)
      simpa using h
    have hopen : IsOpen {z : ℂ | zetaResidueUnit (z + 1 / 2 + α) ≠ 0} :=
      isOpen_ne_fun ((analyticOnNhd_univ_iff_differentiable.mp
        (fun z _ => analyticAt_zetaResidueUnit z)).continuous.comp
          ((continuous_id.add continuous_const).add continuous_const)) continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hζc
    set δ : ℝ := min c d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min hpos hd)
    have hδc : δ ≤ c / 2 := by rw [hδdef]; linarith [min_le_left c d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right c d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := widthDeficitContinuation α ε B) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : c / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hz1 : z + 1 / 2 + α ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hzζ : zetaResidueUnit (z + 1 / 2 + α) ≠ 0 := by
        have hmem := hball (show z ∈ Metric.ball (c : ℂ) d from by
          rw [Metric.mem_ball, Complex.dist_eq]; linarith)
        exact hmem
      exact analyticAt_widthDeficitContinuation α ε B hz0 hz1 hzζ
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (widthDeficitMeasure α ε B))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (widthDeficitMeasure α ε B) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (widthDeficitMeasure α ε B)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => widthDeficitContinuation α ε B (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (widthDeficitContinuation α ε B) (t : ℂ) := by
          refine analyticAt_widthDeficitContinuation α ε B (by exact_mod_cast ht0.ne') ?_ ?_
          · intro h; have hre := congrArg Complex.re h; simp at hre; linarith
          · have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := t + 1 / 2 + α) (by linarith)
            simpa using h
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by
        show c < 1
        have hc34 : c ≤ 3 / 4 := by
          refine csInf_le ⟨0, fun σ' hσ' => ?_⟩ ?_
          · by_contra hlt
            apply hσ'
            rw [laplaceMass_widthDeficitMeasure_eq, laplaceMass_volume_eq_top (not_le.mp hlt),
              add_top]
          · show laplaceMass (widthDeficitMeasure α ε B) (3 / 4) ≠ ⊤
            rw [laplaceMass_widthDeficitMeasure_eq]
            exact ENNReal.add_ne_top.mpr ⟨laplaceMass_widthDeficitDensity_ne_top hε
              (by linarith) (by norm_num), laplaceMass_volume_ne_top (by norm_num)⟩
        linarith
      have hfg : (fun t : ℝ => complexLaplace (widthDeficitMeasure α ε B) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => widthDeficitContinuation α ε B (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        rw [_root_.RHTower.complexLaplace_ofReal]
        exact laplaceReal_widthDeficitMeasure_eq hε hB (by linarith [ht.1]) (by linarith [ht.1])
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ' : complexLaplace (widthDeficitMeasure α ε B) (σ : ℂ) =
          widthDeficitContinuation α ε B (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ', _root_.RHTower.complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ### 5. The width criterion -/

/-- The extension of the regularized critical-Mellin defect manufactured from the width measure. -/
def widthDeficitDefectExtension (α ε B : ℝ) (u : ℂ) : ℂ :=
  1 / (u + 1) + ε * ((u + 1) ^ 2 *
    (complexLaplace (widthDeficitMeasure α ε B) (u + 1 / 2 - α) - (B + 1) / (u + 1 / 2 - α) -
      B / (u + 1 / 2 - α) ^ 2)) - 1

theorem widthDeficitDefectExtension_eq_regularized {α ε B : ℝ} (hεsq : (ε : ℂ) * ε = 1) {u : ℂ}
    (hu : complexLaplace (widthDeficitMeasure α ε B) (u + 1 / 2 - α) =
      widthDeficitContinuation α ε B (u + 1 / 2 - α))
    (hu1 : u + 1 ≠ 0) :
    widthDeficitDefectExtension α ε B u = regularizedCriticalMellinDefect u := by
  unfold widthDeficitDefectExtension regularizedCriticalMellinDefect
  rw [hu]
  unfold widthDeficitContinuation
  have hsum : u + 1 / 2 - α + 1 / 2 + α = u + 1 := by ring
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hsum, hreg]
  have hcancel : (u + 1) ^ 2 * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2) =
      logDeriv zetaResidueUnit (u + 1) + 1 := by
    field_simp
  calc 1 / (u + 1) + (ε : ℂ) * ((u + 1) ^ 2 * (((B:ℂ) + 1) / (u + 1 / 2 - α) +
          (B:ℂ) / (u + 1 / 2 - α) ^ 2 +
          (ε : ℂ) * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2) -
          ((B:ℂ) + 1) / (u + 1 / 2 - α) - (B:ℂ) / (u + 1 / 2 - α) ^ 2)) - 1
      = 1 / (u + 1) + ((ε : ℂ) * ε) *
          ((u + 1) ^ 2 * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2)) - 1 := by ring
    _ = 1 / (u + 1) + logDeriv zetaResidueUnit (u + 1) := by rw [hcancel, hεsq]; ring

/-- **The width criterion.** For `0 ≤ α < ½` and `ε = ±1`: if
`0 ≤ B(1+T) + ε e^{−(1/2+α)T} D(T)` for every `T ≥ 0`, then every Xi zero has `Re ρ ≤ ½ + α`. -/
theorem xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided {α ε B : ℝ} (hα : 0 ≤ α)
    (hα' : α < 1 / 2) (hε : ε = 1 ∨ ε = -1)
    (hB : ∀ T : ℝ, 0 ≤ T →
      0 ≤ B * (1 + T) + ε * (Real.exp (-(1 / 2 + α) * T) * ccmLogChebyshevDeficitPrimitive T)) :
    XiZeroHalfPlaneBound α := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hc := abscissa_widthDeficitMeasure_eq_zero hα hε1 hB
  have hA : AnalyticOnNhd ℂ (widthDeficitDefectExtension α ε B) {s : ℂ | α - 1 / 2 < s.re} := by
    intro u hu
    change α - 1 / 2 < u.re at hu
    have hz : 0 < (u + 1 / 2 - α).re := by simp; linarith
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2 - α) u := by fun_prop
    have hL : AnalyticAt ℂ
        (fun w : ℂ => complexLaplace (widthDeficitMeasure α ε B) (w + 1 / 2 - α)) u := by
      have hdiff : DifferentiableOn ℂ (complexLaplace (widthDeficitMeasure α ε B))
          {z : ℂ | 0 < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2 - α) (hdiff.analyticAt (hopen.mem_nhds hz))
        hshift
    have hu1 : u + 1 ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    have hu12 : u + 1 / 2 - α ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    unfold widthDeficitDefectExtension
    refine ((analyticAt_const.div (analyticAt_id.add analyticAt_const) hu1).add
      (analyticAt_const.mul (((analyticAt_id.add analyticAt_const).pow 2).mul
        ((hL.sub (analyticAt_const.div hshift hu12)).sub
          (analyticAt_const.div (hshift.pow 2) (pow_ne_zero 2 hu12)))))).sub analyticAt_const
  refine xiZeroHalfPlaneBound_of_regularizedCriticalMellinDefect_extensionAbove hα _ hA ?_
  -- agreement on the right half-plane, from agreement on the positive reals
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAU : AnalyticOnNhd ℂ (widthDeficitDefectExtension α ε B) U :=
    hA.mono (fun u hu => by change 0 < u.re at hu; change α - 1 / 2 < u.re; linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have hreal : ∀ r : ℝ, 0 < r →
      widthDeficitDefectExtension α ε B (r : ℂ) = regularizedCriticalMellinDefect (r : ℂ) := by
    intro r hr
    have hlap := laplaceReal_widthDeficitMeasure_eq hε1 hB (σ := r + 1 / 2 - α) (by linarith)
      (by linarith)
    rw [← _root_.RHTower.complexLaplace_ofReal] at hlap
    have hcast : (((r + 1 / 2 - α : ℝ)) : ℂ) = (r : ℂ) + 1 / 2 - α := by push_cast; ring
    rw [hcast] at hlap
    have hr1 : (r : ℂ) + 1 ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    exact widthDeficitDefectExtension_eq_regularized hεsq hlap hr1
  have htwo : (2 : ℂ) ∈ U := by change 0 < (2 : ℂ).re; norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      widthDeficitDefectExtension α ε B z = regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r (lt_trans (by norm_num) hr)
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have heq := hAU.eqOn_of_preconnected_of_frequently_eq hR hUpre htwo hfreq
  intro s hs
  exact heq (show s ∈ U from hs)

/-- **A one-sided lower bound bounds the width.** If `−B(1+T)e^{(1/2+α)T} ≤ D(T)` for all `T ≥ 0`,
with `0 ≤ α`, then every Xi zero has `Re ρ ≤ ½ + α`. -/
theorem xiZeroHalfPlaneBound_of_deficitPrimitive_ge {α B : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hB : ∀ T : ℝ, 0 ≤ T →
      -(B * (1 + T) * Real.exp ((1 / 2 + α) * T)) ≤ ccmLogChebyshevDeficitPrimitive T) :
    XiZeroHalfPlaneBound α := by
  refine xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided (ε := 1) (B := B) hα hα' (Or.inl rfl) ?_
  intro T hT
  have h := hB T hT
  have he : Real.exp (-(1 / 2 + α) * T) * Real.exp ((1 / 2 + α) * T) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1 / 2 + α) * T)).le
  have h2 : Real.exp (-(1 / 2 + α) * T) * -(B * (1 + T) * Real.exp ((1 / 2 + α) * T)) =
      -(B * (1 + T)) := by
    rw [show Real.exp (-(1 / 2 + α) * T) * -(B * (1 + T) * Real.exp ((1 / 2 + α) * T)) =
      -(B * (1 + T)) * (Real.exp (-(1 / 2 + α) * T) * Real.exp ((1 / 2 + α) * T)) by ring, he,
      mul_one]
  rw [h2] at this
  linarith

/-- **A one-sided upper bound bounds the width.** -/
theorem xiZeroHalfPlaneBound_of_deficitPrimitive_le {α B : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hB : ∀ T : ℝ, 0 ≤ T →
      ccmLogChebyshevDeficitPrimitive T ≤ B * (1 + T) * Real.exp ((1 / 2 + α) * T)) :
    XiZeroHalfPlaneBound α := by
  refine xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided (ε := -1) (B := B) hα hα' (Or.inr rfl) ?_
  intro T hT
  have h := hB T hT
  have he : Real.exp (-(1 / 2 + α) * T) * Real.exp ((1 / 2 + α) * T) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1 / 2 + α) * T)).le
  have h2 : Real.exp (-(1 / 2 + α) * T) * (B * (1 + T) * Real.exp ((1 / 2 + α) * T)) =
      B * (1 + T) := by
    rw [show Real.exp (-(1 / 2 + α) * T) * (B * (1 + T) * Real.exp ((1 / 2 + α) * T)) =
      B * (1 + T) * (Real.exp (-(1 / 2 + α) * T) * Real.exp ((1 / 2 + α) * T)) by ring, he,
      mul_one]
  rw [h2] at this
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
