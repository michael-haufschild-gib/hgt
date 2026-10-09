import GaloisForLFunctions.RHTower.RoutePCompletedErrorOneSidedLandau
import GaloisForLFunctions.RHTower.CCMSharpRectangularSewing

/-!
# A one-sided linear bound on the primitive of the completed critical-Mellin error forces RH

Let `E(h) = 4 sinh(h/2) − Σ_{k ≤ e^h} Λ(k) k^{−1/2}` be the completed critical-Mellin error and
`P(T) = ∫_0^T E` its primitive.  An eventual one-sided linear bound on `P`, from either side,
implies the Riemann hypothesis (`riemannHypothesis_of_completedErrorPrimitive_eventually_ge`,
`riemannHypothesis_of_completedErrorPrimitive_eventually_le`).

The mechanism is Landau's theorem, as for the pointwise bound on `E`.
* Integration by parts gives `∫_0^∞ e^{−σT} P(T) dT = σ⁻¹ ∫_0^∞ e^{−σT} E(T) dT` for `σ > ½`.  The
  transform of `E` is `D(σ − ½)/σ`, with `D` the regularized critical-Mellin defect.
* For `B(1+T) ± P(T) ≥ 0` the measure `(B(1+T) ± P(T)) dT + dT` has transform
  `(B+1)/z + B/z² ± D(z − ½)/z²` to the right of `½`.  This is analytic at every real `z > 0`,
  because `(s−1)ζ(s)` has no positive real zero.
* Landau's theorem moves the abscissa to `0`, and the resulting continuation of `D` to `Re u > −½`
  gives RH.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The primitive -/

/-- The primitive `P(T) = ∫_0^T E` of the completed critical-Mellin error. -/
def completedErrorPrimitive (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, criticalMellinCompletedError t

theorem intervalIntegrable_criticalMellinCompletedError_any (a b : ℝ) :
    IntervalIntegrable criticalMellinCompletedError volume a b := by
  have h : criticalMellinCompletedError =
      fun s => 4 * Real.sinh (s / 2) - criticalMellinPrimeMass s :=
    funext criticalMellinCompletedError_eq_polar_sub_primeMass
  rw [h]
  exact ((continuous_const.mul (Real.continuous_sinh.comp
    (continuous_id.div_const 2))).intervalIntegrable a b).sub
      criticalMellinPrimeMass_mono.intervalIntegrable

theorem continuous_completedErrorPrimitive : Continuous completedErrorPrimitive :=
  intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_criticalMellinCompletedError_any a b) 0

theorem measurable_completedErrorPrimitive : Measurable completedErrorPrimitive :=
  continuous_completedErrorPrimitive.measurable

theorem integral_exp_half (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.exp (t / 2) = 2 * (Real.exp (T / 2) - 1) := by
  rw [intervalIntegral.integral_comp_div (fun x => Real.exp x) (two_ne_zero), integral_exp]
  simp

theorem abs_completedErrorPrimitive_le {T : ℝ} (hT : 0 ≤ T) :
    |completedErrorPrimitive T| ≤ 46 * Real.exp (T / 2) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := criticalMellinCompletedError) (g := fun t => 23 * Real.exp (t / 2)) hT
    (Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]
      exact abs_criticalMellinCompletedError_le_sqrt ht.1.le)
    ((by fun_prop : Continuous fun t : ℝ => 23 * Real.exp (t / 2)).intervalIntegrable 0 T)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_exp_half] at hb
  unfold completedErrorPrimitive
  have := Real.exp_pos (T / 2)
  linarith

/-! ## Laplace transform of the primitive -/

theorem integrableOn_exp_mul_completedErrorPrimitive {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun T => Real.exp (-σ * T) * completedErrorPrimitive T) (Ioi 0) := by
  have hmaj := (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ - 1 / 2)).const_mul 46
  refine hmaj.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_completedErrorPrimitive).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-σ * T) * |completedErrorPrimitive T|
      ≤ Real.exp (-σ * T) * (46 * Real.exp (T / 2)) :=
        mul_le_mul_of_nonneg_left (abs_completedErrorPrimitive_le (le_of_lt hT))
          (Real.exp_pos _).le
    _ = 46 * Real.exp (-(σ - 1 / 2) * T) := by
        rw [show -(σ - 1 / 2) * T = -σ * T + T / 2 by ring, Real.exp_add]; ring

/-- Finite-interval integration by parts for the primitive against `e^{−σT}`. -/
theorem integral_exp_mul_completedErrorPrimitive_interval {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
    ∫ T in (0 : ℝ)..R, Real.exp (-σ * T) * completedErrorPrimitive T =
      -(Real.exp (-σ * R) / σ) * completedErrorPrimitive R +
        (1 / σ) * ∫ T in (0 : ℝ)..R, Real.exp (-σ * T) * criticalMellinCompletedError T := by
  let G : ℝ → ℝ := fun T => -(Real.exp (-σ * T) / σ)
  let P : ℝ → ℝ := completedErrorPrimitive
  have hi : IntervalIntegrable criticalMellinCompletedError volume 0 R :=
    intervalIntegrable_criticalMellinCompletedError_any 0 R
  have hPac : AbsolutelyContinuousOnInterval P 0 R :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (show (0 : ℝ) ∈ uIcc 0 R by simp [hR])
  have hGcd : ContDiff ℝ 1 G := by dsimp [G]; fun_prop
  have hGac : AbsolutelyContinuousOnInterval G 0 R := hGcd.contDiffOn.absolutelyContinuousOnInterval
  have hparts := hGac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in (0 : ℝ)..R, G t * deriv P t) =
      ∫ t in (0 : ℝ)..R, G t * criticalMellinCompletedError t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (criticalMellinCompletedError t) t :=
      ht (uIoc_subset_uIcc hmem) 0 (by simp [hR])
    rw [hd.deriv]
  have hderivG : ∀ t, deriv G t = Real.exp (-σ * t) := by
    intro t
    have h1 : HasDerivAt (fun T : ℝ => -σ * T) (-σ) t := by
      simpa using (hasDerivAt_id t).const_mul (-σ)
    have h2 : HasDerivAt (fun T : ℝ => Real.exp (-σ * T)) (Real.exp (-σ * t) * -σ) t := h1.exp
    have h3 : HasDerivAt G (-(Real.exp (-σ * t) * -σ / σ)) t := (h2.div_const σ).neg
    have hval : -(Real.exp (-σ * t) * -σ / σ) = Real.exp (-σ * t) := by
      rw [mul_neg, neg_div, neg_neg, mul_div_assoc, div_self hσ.ne', mul_one]
    rw [hval] at h3
    exact h3.deriv
  have hright : (∫ t in (0 : ℝ)..R, deriv G t * P t) =
      ∫ t in (0 : ℝ)..R, Real.exp (-σ * t) * completedErrorPrimitive t := by
    apply intervalIntegral.integral_congr
    intro t _
    show deriv G t * P t = Real.exp (-σ * t) * completedErrorPrimitive t
    rw [hderivG]
  have hP0 : P 0 = 0 := by simp [P, completedErrorPrimitive]
  rw [hleft, hright, hP0, mul_zero, sub_zero] at hparts
  have hGf : (∫ t in (0 : ℝ)..R, G t * criticalMellinCompletedError t) =
      -(1 / σ) * ∫ t in (0 : ℝ)..R, Real.exp (-σ * t) * criticalMellinCompletedError t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [G]
    ring
  rw [hGf] at hparts
  dsimp only [G, P] at hparts
  linarith

/-- **Laplace transform of the primitive.**  For `σ > ½`,
`∫_0^∞ e^{−σT} P(T) dT = σ⁻¹ ∫_0^∞ e^{−σT} E(T) dT`. -/
theorem integral_exp_mul_completedErrorPrimitive {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * completedErrorPrimitive T =
      (1 / σ) * ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * criticalMellinCompletedError T := by
  have hσ0 : 0 < σ := by linarith
  have hL := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_exp_mul_completedErrorPrimitive hσ) tendsto_id
  have hR := (intervalIntegral_tendsto_integral_Ioi 0
    (routeP_integrable_exp_completedError hσ) tendsto_id).const_mul (1 / σ)
  have hB : Tendsto (fun R : ℝ => -(Real.exp (-σ * R) / σ) * completedErrorPrimitive R)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => Real.exp (-((σ - 1 / 2) * R))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < σ - 1 / 2))
    have hdecay : Tendsto (fun R : ℝ => 46 / σ * Real.exp (-((σ - 1 / 2) * R)))
        atTop (𝓝 0) := by
      simpa using h0.const_mul (46 / σ)
    refine squeeze_zero_norm' ?_ hdecay
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hσ0]
    calc Real.exp (-σ * R) / σ * |completedErrorPrimitive R|
        ≤ Real.exp (-σ * R) / σ * (46 * Real.exp (R / 2)) :=
          mul_le_mul_of_nonneg_left (abs_completedErrorPrimitive_le hR) (by positivity)
      _ = 46 / σ * Real.exp (-((σ - 1 / 2) * R)) := by
          rw [show -((σ - 1 / 2) * R) = -σ * R + R / 2 by ring, Real.exp_add]; ring
  have hsum := hB.add hR
  rw [zero_add] at hsum
  have heq : (fun R : ℝ => ∫ T in (0 : ℝ)..id R, Real.exp (-σ * T) * completedErrorPrimitive T)
      =ᶠ[atTop] fun R => -(Real.exp (-σ * R) / σ) * completedErrorPrimitive R +
        (1 / σ) * ∫ T in (0 : ℝ)..id R, Real.exp (-σ * T) * criticalMellinCompletedError T := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact integral_exp_mul_completedErrorPrimitive_interval hσ0 hR
  exact tendsto_nhds_unique (hL.congr' heq) hsum

/-! ## The one-sided comparison measure -/

/-- The clipped density `max(B(1+T) + ε P(T), 0)`. -/
def primitiveOneSidedDensity (ε B : ℝ) (T : ℝ) : NNReal :=
  Real.toNNReal (B * (1 + T) + ε * completedErrorPrimitive T)

theorem measurable_primitiveOneSidedDensity (ε B : ℝ) :
    Measurable (primitiveOneSidedDensity ε B) := by
  unfold primitiveOneSidedDensity
  exact ((measurable_const.mul (measurable_const.add measurable_id)).add
    (measurable_const.mul measurable_completedErrorPrimitive)).real_toNNReal

/-- `(B(1+T) + ε P(T)) dT` on `(0,∞)` plus Lebesgue measure. -/
def primitiveOneSidedMeasure (ε B : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun T => (primitiveOneSidedDensity ε B T : ENNReal)) + volume

theorem primitiveOneSidedDensity_le {ε B : ℝ} (hε : |ε| ≤ 1) {T : ℝ} (hT : 0 < T) :
    ((primitiveOneSidedDensity ε B T : ℝ)) ≤ (2 * |B| + 46) * Real.exp (T / 2) := by
  unfold primitiveOneSidedDensity
  rw [Real.coe_toNNReal']
  have hprod := abs_completedErrorPrimitive_le hT.le
  have hε' : |ε * completedErrorPrimitive T| ≤ 46 * Real.exp (T / 2) := by
    rw [abs_mul]
    calc |ε| * |completedErrorPrimitive T| ≤ 1 * (46 * Real.exp (T / 2)) :=
          mul_le_mul hε hprod (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h1T : 1 + T ≤ 2 * Real.exp (T / 2) := by
    have := Real.add_one_le_exp (T / 2); linarith
  have h1 : B * (1 + T) ≤ 2 * |B| * Real.exp (T / 2) := by
    calc B * (1 + T) ≤ |B| * (1 + T) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
      _ ≤ |B| * (2 * Real.exp (T / 2)) := mul_le_mul_of_nonneg_left h1T (abs_nonneg B)
      _ = 2 * |B| * Real.exp (T / 2) := by ring
  have h2 := le_abs_self (ε * completedErrorPrimitive T)
  have h3 : 0 ≤ (2 * |B| + 46) * Real.exp (T / 2) := by positivity
  rcases le_or_gt (B * (1 + T) + ε * completedErrorPrimitive T) 0 with h | h
  · rw [max_eq_right h]; exact h3
  · rw [max_eq_left h.le]; nlinarith

theorem integrableOn_primitiveMajorant {σ B : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun T : ℝ => (2 * |B| + 46) * Real.exp (T / 2) * Real.exp (-σ * T))
      (Ioi 0) := by
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ - 1 / 2)).const_mul
    (2 * |B| + 46)
  refine IntegrableOn.congr_fun h2 (fun T _ => ?_) measurableSet_Ioi
  rw [show Real.exp (-(σ - 1 / 2) * T) = Real.exp (T / 2) * Real.exp (-σ * T) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_primitiveDensity_ne_top {ε B σ : ℝ} (hε : |ε| ≤ 1) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun T => (primitiveOneSidedDensity ε B T : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun T : ℝ => ENNReal.ofReal (Real.exp (-σ * T))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_primitiveOneSidedDensity ε B).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top (integrableOn_primitiveMajorant (B := B) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (primitiveOneSidedDensity_le hε hT) (Real.exp_pos _).le

theorem laplaceMass_primitiveOneSided_eq (ε B σ : ℝ) :
    laplaceMass (primitiveOneSidedMeasure ε B) σ =
      laplaceMass ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun T => (primitiveOneSidedDensity ε B T : ENNReal))) σ + laplaceMass volume σ := by
  unfold laplaceMass primitiveOneSidedMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

/-- The convergence set lies in `(0,∞)` and contains `1`; its infimum is the abscissa. -/
theorem isAbscissa_primitiveOneSided {ε B : ℝ} (hε : |ε| ≤ 1) :
    IsAbscissa (primitiveOneSidedMeasure ε B)
        (sInf {σ : ℝ | laplaceMass (primitiveOneSidedMeasure ε B) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (primitiveOneSidedMeasure ε B) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (primitiveOneSidedMeasure ε B) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_primitiveOneSided_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1 : ℝ) ∈ S := by
    show laplaceMass (primitiveOneSidedMeasure ε B) 1 ≠ ⊤
    rw [laplaceMass_primitiveOneSided_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_primitiveDensity_ne_top hε (by norm_num),
      laplaceMass_volume_ne_top one_pos⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The continuation -/

/-- The candidate continuation `(B+1)/z + B/z² + ε (1/(z+½) + ζ_u'/ζ_u(z+½))/z²`. -/
def primitiveOneSidedContinuation (ε B : ℝ) (z : ℂ) : ℂ :=
  (B + 1) / z + B / z ^ 2 + ε *
    ((1 / (z + 1 / 2) + logDeriv zetaResidueUnit (z + 1 / 2)) / z ^ 2)

theorem analyticAt_primitiveOneSidedContinuation (ε B : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z + 1 / 2 ≠ 0) (hζ : zetaResidueUnit (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (primitiveOneSidedContinuation ε B) z := by
  unfold primitiveOneSidedContinuation
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hζan : AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)) hshift
  have hdζ : AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)).deriv
      hshift
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2)) z := by
    simp only [logDeriv_apply]
    exact hdζ.div hζan hζ
  refine ((analyticAt_const.div analyticAt_id hz0).add
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hz0))).add (analyticAt_const.mul ?_)
  exact ((analyticAt_const.div hshift hz1).add hlog).div (analyticAt_id.pow 2) (pow_ne_zero 2 hz0)

theorem primitiveOneSidedDensity_eq {ε B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * completedErrorPrimitive T)
    {T : ℝ} (hT : 0 ≤ T) :
    ((primitiveOneSidedDensity ε B T : ℝ)) = B * (1 + T) + ε * completedErrorPrimitive T := by
  unfold primitiveOneSidedDensity
  exact Real.coe_toNNReal _ (hB T hT)

/-- On real `σ > ½` the transform of the comparison measure is the continuation. -/
theorem laplaceReal_primitiveOneSided_eq {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * completedErrorPrimitive T)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((laplaceReal (primitiveOneSidedMeasure ε B) σ : ℝ) : ℂ) =
      primitiveOneSidedContinuation ε B (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hexpInt : IntegrableOn (fun T : ℝ => Real.exp (-σ * T)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hσ0
  have hdensInt : Integrable (fun T : ℝ => Real.exp (-σ * T))
      (((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun T => (primitiveOneSidedDensity ε B T : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul
        (measurable_primitiveOneSidedDensity ε B)]
    refine (integrableOn_primitiveMajorant (B := B) hσ).mono' ?_ ?_
    · exact ((measurable_primitiveOneSidedDensity ε B).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (primitiveOneSidedDensity_le hε hT) (Real.exp_pos _).le
  have hsplit : laplaceReal (primitiveOneSidedMeasure ε B) σ =
      (∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun T => (primitiveOneSidedDensity ε B T : ENNReal)))) + 1 / σ := by
    unfold laplaceReal primitiveOneSidedMeasure
    rw [Measure.restrict_add, integral_add_measure hdensInt hexpInt,
      integral_exp_neg_mul_Ioi_real hσ0]
  have hdens : (∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun T => (primitiveOneSidedDensity ε B T : ENNReal)))) =
      B / σ + B / σ ^ 2 + ε * ∫ T in Ioi (0 : ℝ),
        Real.exp (-σ * T) * completedErrorPrimitive T := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_primitiveOneSidedDensity ε B)]
    have hpt : ∀ T ∈ Ioi (0 : ℝ), primitiveOneSidedDensity ε B T • Real.exp (-σ * T) =
        (B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T))) +
          ε * (Real.exp (-σ * T) * completedErrorPrimitive T) := by
      intro T hT
      rw [NNReal.smul_def, smul_eq_mul, primitiveOneSidedDensity_eq hB (le_of_lt hT)]
      ring
    have hf : Integrable (fun T : ℝ => B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T)))
        (volume.restrict (Ioi 0)) :=
      (hexpInt.const_mul B).add ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add hf ((integrableOn_exp_mul_completedErrorPrimitive hσ).const_mul ε),
      integral_add (hexpInt.const_mul B) ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_exp_neg_mul_Ioi_real hσ0,
      integral_id_mul_real_exp_neg_mul hσ0]
    ring
  rw [hsplit, hdens, integral_exp_mul_completedErrorPrimitive hσ]
  push_cast
  rw [routeP_completedError_real_laplace hσ]
  unfold primitiveOneSidedContinuation regularizedCriticalMellinDefect
  rw [show (σ : ℂ) - 1 / 2 + 1 = σ + 1 / 2 by ring]
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hreg]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  field_simp
  ring

/-! ## Landau: the abscissa is zero -/

theorem abscissa_primitiveOneSided_eq_zero {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * completedErrorPrimitive T) :
    IsAbscissa (primitiveOneSidedMeasure ε B) 0 := by
  obtain ⟨hc, hc0⟩ := isAbscissa_primitiveOneSided (B := B) hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (primitiveOneSidedMeasure ε B) σ ≠ ⊤} with hcdef
  rcases hc0.lt_or_eq with hpos | hzero
  · exfalso
    have hζc : zetaResidueUnit ((c : ℂ) + 1 / 2) ≠ 0 := by
      have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := c + 1 / 2) (by linarith)
      simpa using h
    have hopen : IsOpen {z : ℂ | zetaResidueUnit (z + 1 / 2) ≠ 0} :=
      isOpen_ne_fun ((analyticOnNhd_univ_iff_differentiable.mp
        (fun z _ => analyticAt_zetaResidueUnit z)).continuous.comp
          (continuous_id.add continuous_const)) continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hζc
    set δ : ℝ := min c d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min hpos hd)
    have hδc : δ ≤ c / 2 := by rw [hδdef]; linarith [min_le_left c d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right c d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := primitiveOneSidedContinuation ε B) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : c / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hz1 : z + 1 / 2 ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hzζ : zetaResidueUnit (z + 1 / 2) ≠ 0 := by
        have hmem := hball (show z ∈ Metric.ball (c : ℂ) d from by
          rw [Metric.mem_ball, Complex.dist_eq]; linarith)
        exact hmem
      exact analyticAt_primitiveOneSidedContinuation ε B hz0 hz1 hzζ
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (primitiveOneSidedMeasure ε B))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ
          (fun t : ℝ => complexLaplace (primitiveOneSidedMeasure ε B) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (primitiveOneSidedMeasure ε B)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => primitiveOneSidedContinuation ε B (t : ℂ))
          (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (primitiveOneSidedContinuation ε B) (t : ℂ) := by
          refine analyticAt_primitiveOneSidedContinuation ε B (by exact_mod_cast ht0.ne') ?_ ?_
          · intro h; have hre := congrArg Complex.re h; simp at hre; linarith
          · have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := t + 1 / 2) (by linarith)
            simpa using h
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by
        show c < 1
        have hc34 : c ≤ 3 / 4 := by
          refine csInf_le ⟨0, fun σ' hσ' => ?_⟩ ?_
          · by_contra hlt
            apply hσ'
            rw [laplaceMass_primitiveOneSided_eq, laplaceMass_volume_eq_top (not_le.mp hlt),
              add_top]
          · show laplaceMass (primitiveOneSidedMeasure ε B) (3 / 4) ≠ ⊤
            rw [laplaceMass_primitiveOneSided_eq]
            exact ENNReal.add_ne_top.mpr ⟨laplaceMass_primitiveDensity_ne_top hε (by norm_num),
              laplaceMass_volume_ne_top (by norm_num)⟩
        linarith
      have hfg : (fun t : ℝ => complexLaplace (primitiveOneSidedMeasure ε B) (t : ℂ))
          =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => primitiveOneSidedContinuation ε B (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
            fun t ht => ?_
        rw [complexLaplace_ofReal]
        exact laplaceReal_primitiveOneSided_eq hε hB ht.1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ' : complexLaplace (primitiveOneSidedMeasure ε B) (σ : ℂ) =
          primitiveOneSidedContinuation ε B (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ', complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The regularized defect continues across `Re u > −½` -/

/-- The regularized defect recovered from the comparison measure. -/
def primitiveOneSidedDefectExtension (ε B : ℝ) (u : ℂ) : ℂ :=
  ε * ((u + 1 / 2) ^ 2 *
    (complexLaplace (primitiveOneSidedMeasure ε B) (u + 1 / 2) - (B + 1) / (u + 1 / 2) -
      B / (u + 1 / 2) ^ 2))

theorem primitiveOneSidedDefectExtension_eq_regularized {ε B : ℝ}
    (hεsq : (ε : ℂ) * ε = 1) {u : ℂ}
    (hu : complexLaplace (primitiveOneSidedMeasure ε B) (u + 1 / 2) =
      primitiveOneSidedContinuation ε B (u + 1 / 2))
    (hu12 : u + 1 / 2 ≠ 0) :
    primitiveOneSidedDefectExtension ε B u = regularizedCriticalMellinDefect u := by
  unfold primitiveOneSidedDefectExtension regularizedCriticalMellinDefect
  rw [hu]
  unfold primitiveOneSidedContinuation
  rw [show u + 1 / 2 + 1 / 2 = u + 1 by ring]
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hreg]
  have hsq : (u + 1 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hu12
  calc
    (ε : ℂ) * ((u + 1 / 2) ^ 2 *
        (((B : ℂ) + 1) / (u + 1 / 2) + (B : ℂ) / (u + 1 / 2) ^ 2 +
        (ε : ℂ) * ((1 / (u + 1) + logDeriv zetaResidueUnit (u + 1)) / (u + 1 / 2) ^ 2) -
        ((B : ℂ) + 1) / (u + 1 / 2) - (B : ℂ) / (u + 1 / 2) ^ 2)) =
      ((ε : ℂ) * ε) * ((u + 1 / 2) ^ 2 *
        ((1 / (u + 1) + logDeriv zetaResidueUnit (u + 1)) / (u + 1 / 2) ^ 2)) := by ring
    _ = _ := by rw [hεsq, one_mul, mul_div_cancel₀ _ hsq]

/-- **Either one-sided linear bound on the primitive of the completed error forces RH.** -/
theorem riemannHypothesis_of_completedErrorPrimitive_oneSided_linear {ε B : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * completedErrorPrimitive T) :
    RiemannHypothesis := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hc := abscissa_primitiveOneSided_eq_zero hε1 hB
  have hA : AnalyticOnNhd ℂ (primitiveOneSidedDefectExtension ε B)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
    intro u hu
    change -1 / 2 < u.re at hu
    have hz : 0 < (u + 1 / 2).re := by simp; linarith
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) u := by fun_prop
    have hL : AnalyticAt ℂ
        (fun w : ℂ => complexLaplace (primitiveOneSidedMeasure ε B) (w + 1 / 2)) u := by
      have hdiff : DifferentiableOn ℂ (complexLaplace (primitiveOneSidedMeasure ε B))
          {z : ℂ | 0 < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (hdiff.analyticAt (hopen.mem_nhds hz))
        hshift
    have hu12 : u + 1 / 2 ≠ 0 := ne_zero_of_re_pos hz
    unfold primitiveOneSidedDefectExtension
    exact analyticAt_const.mul ((hshift.pow 2).mul
      ((hL.sub (analyticAt_const.div hshift hu12)).sub
        (analyticAt_const.div (hshift.pow 2) (pow_ne_zero 2 hu12))))
  refine riemannHypothesis_of_regularizedCriticalMellinDefect_extension _ hA ?_
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAU : AnalyticOnNhd ℂ (primitiveOneSidedDefectExtension ε B) U :=
    hA.mono (fun u hu => by change 0 < u.re at hu; change -1 / 2 < u.re; linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have hreal : ∀ r : ℝ, 0 < r →
      primitiveOneSidedDefectExtension ε B (r : ℂ) = regularizedCriticalMellinDefect (r : ℂ) := by
    intro r hr
    have hlap := laplaceReal_primitiveOneSided_eq hε1 hB (σ := r + 1 / 2) (by linarith)
    rw [← complexLaplace_ofReal] at hlap
    have hcast : (((r + 1 / 2 : ℝ)) : ℂ) = (r : ℂ) + 1 / 2 := by push_cast; ring
    rw [hcast] at hlap
    have hr12 : (r : ℂ) + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
    exact primitiveOneSidedDefectExtension_eq_regularized hεsq hlap hr12
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
      primitiveOneSidedDefectExtension ε B z = regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r (lt_trans (by norm_num) hr)
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have heq := hAU.eqOn_of_preconnected_of_frequently_eq hR hUpre htwo hfreq
  intro s hs
  exact heq (show s ∈ U from hs)

/-- **A late linear lower bound on the primitive forces RH.** -/
theorem riemannHypothesis_of_completedErrorPrimitive_eventually_ge {C L : ℝ}
    (hC : ∀ T : ℝ, L ≤ T → -(C * (1 + T)) ≤ completedErrorPrimitive T) :
    RiemannHypothesis := by
  let B : ℝ := |C| + 46 * Real.exp (L / 2)
  refine riemannHypothesis_of_completedErrorPrimitive_oneSided_linear (ε := 1) (B := B)
    (Or.inl rfl) ?_
  intro T hT
  have hB1 : |C| ≤ B := by dsimp [B]; have := Real.exp_pos (L / 2); linarith
  rw [one_mul]
  by_cases hLT : L ≤ T
  · have h := hC T hLT
    have : C * (1 + T) ≤ B * (1 + T) :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans hB1) (by linarith)
    linarith
  · have hP := (abs_le.mp (abs_completedErrorPrimitive_le hT)).1
    have he := Real.exp_le_exp.mpr (show T / 2 ≤ L / 2 by linarith)
    have hB2 : 46 * Real.exp (L / 2) ≤ B := by dsimp [B]; have := abs_nonneg C; linarith
    nlinarith

/-- **A late linear upper bound on the primitive forces RH.** -/
theorem riemannHypothesis_of_completedErrorPrimitive_eventually_le {C L : ℝ}
    (hC : ∀ T : ℝ, L ≤ T → completedErrorPrimitive T ≤ C * (1 + T)) :
    RiemannHypothesis := by
  let B : ℝ := |C| + 46 * Real.exp (L / 2)
  refine riemannHypothesis_of_completedErrorPrimitive_oneSided_linear (ε := -1) (B := B)
    (Or.inr rfl) ?_
  intro T hT
  have hB1 : |C| ≤ B := by dsimp [B]; have := Real.exp_pos (L / 2); linarith
  by_cases hLT : L ≤ T
  · have h := hC T hLT
    have : C * (1 + T) ≤ B * (1 + T) :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans hB1) (by linarith)
    linarith
  · have hP := (abs_le.mp (abs_completedErrorPrimitive_le hT)).2
    have he := Real.exp_le_exp.mpr (show T / 2 ≤ L / 2 by linarith)
    have hB2 : 46 * Real.exp (L / 2) ≤ B := by dsimp [B]; have := abs_nonneg C; linarith
    nlinarith

end

end RHTower
