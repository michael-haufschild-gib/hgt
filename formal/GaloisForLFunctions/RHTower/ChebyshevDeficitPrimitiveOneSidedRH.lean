import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAbelCompleteness
import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet

/-!
# A one-sided square-root bound on the integrated Chebyshev deficit forces RH

Let `D(T) = ∫_0^T (e^t − ψ(e^t)) dt` be the logarithmic primitive of the Chebyshev deficit.
A two-sided bound `|D(T)| ≤ B e^{T/2}` is equivalent to RH
(`riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound`). One side already suffices.

**Theorem** (`riemannHypothesis_of_logChebyshevDeficitPrimitive_ge`). If `−B e^{T/2} ≤ D(T)` for
every `T ≥ 0`, then RH holds. The same holds for the reverse bound
(`riemannHypothesis_of_logChebyshevDeficitPrimitive_le`).

The mechanism is Landau's theorem.
* `g(T) = B ± e^{−T/2}D(T)` is a nonnegative density on `(0,∞)`.
* Integration by parts gives `∫_0^∞ e^{−aT} D(T) dT = a⁻¹ ∫_0^∞ e^{−aT}(e^T − ψ(e^T)) dT` for
  `a > 1`. Hence the Laplace transform of `g dT + dT` equals
  `(B+1)/z ∓ (ζ_u'/ζ_u(z+½) + 1)/(z+½)²` to the right of `½`, where `ζ_u(s) = (s−1)ζ(s)`.
* That function is analytic at every real `z > 0`, because `ζ_u` has no positive real zero.
* Landau moves the abscissa to `0`. The transform then continues the regularized critical-Mellin
  defect across `Re u > −½`, and the extension criterion gives RH.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The deficit and its primitive -/

/-- The Chebyshev deficit `e^t − ψ(e^t)` in the logarithmic variable. -/
def chebyshevLogDeficit (t : ℝ) : ℝ := Real.exp t - Chebyshev.psi (Real.exp t)

theorem measurable_chebyshevLogDeficit : Measurable chebyshevLogDeficit :=
  Real.measurable_exp.sub (Chebyshev.psi_mono.comp Real.exp_monotone).measurable

theorem intervalIntegrable_chebyshevLogDeficit (a b : ℝ) :
    IntervalIntegrable chebyshevLogDeficit volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)

/-- The constant `log 4 + 5` in the Chebyshev bound for the deficit. -/
def chebyshevDeficitConst : ℝ := Real.log 4 + 5

theorem chebyshevDeficitConst_pos : 0 < chebyshevDeficitConst := by
  unfold chebyshevDeficitConst
  have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
  linarith

theorem abs_chebyshevLogDeficit_le (t : ℝ) :
    |chebyshevLogDeficit t| ≤ chebyshevDeficitConst * Real.exp t := by
  unfold chebyshevLogDeficit chebyshevDeficitConst
  have hp := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
  have h0 := Chebyshev.psi_nonneg (Real.exp t)
  have he := Real.exp_pos t
  have hl := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem deficitPrimitive_eq (T : ℝ) :
    ccmLogChebyshevDeficitPrimitive T = ∫ t in (0:ℝ)..T, chebyshevLogDeficit t := rfl

theorem continuous_deficitPrimitive : Continuous ccmLogChebyshevDeficitPrimitive := by
  have h : ccmLogChebyshevDeficitPrimitive = fun T => ∫ t in (0:ℝ)..T, chebyshevLogDeficit t := rfl
  rw [h]
  exact intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_chebyshevLogDeficit a b) 0

theorem abs_deficitPrimitive_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T| ≤ chebyshevDeficitConst * Real.exp T := by
  rw [deficitPrimitive_eq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := chebyshevLogDeficit)
    (g := fun t => chebyshevDeficitConst * Real.exp t) hT
    (Filter.Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs]; exact abs_chebyshevLogDeficit_le t)
    ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero] at hb
  have hc := chebyshevDeficitConst_pos
  nlinarith

/-! ## Laplace transform of the primitive -/

theorem integrableOn_exp_mul_chebyshevLogDeficit {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t => Real.exp (-a * t) * chebyshevLogDeficit t) (Ioi 0) := by
  have hmaj := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < a - 1)).const_mul
    chebyshevDeficitConst
  refine hmaj.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
    measurable_chebyshevLogDeficit).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-a * t) * |chebyshevLogDeficit t|
      ≤ Real.exp (-a * t) * (chebyshevDeficitConst * Real.exp t) :=
        mul_le_mul_of_nonneg_left (abs_chebyshevLogDeficit_le t) (Real.exp_pos _).le
    _ = chebyshevDeficitConst * Real.exp (-(a - 1) * t) := by
        rw [show -(a - 1) * t = -a * t + t by ring, Real.exp_add]; ring

theorem integrableOn_exp_mul_deficitPrimitive {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun T => Real.exp (-a * T) * ccmLogChebyshevDeficitPrimitive T) (Ioi 0) := by
  have hmaj := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < a - 1)).const_mul
    chebyshevDeficitConst
  refine hmaj.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_deficitPrimitive).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-a * T) * |ccmLogChebyshevDeficitPrimitive T|
      ≤ Real.exp (-a * T) * (chebyshevDeficitConst * Real.exp T) :=
        mul_le_mul_of_nonneg_left (abs_deficitPrimitive_le (le_of_lt hT)) (Real.exp_pos _).le
    _ = chebyshevDeficitConst * Real.exp (-(a - 1) * T) := by
        rw [show -(a - 1) * T = -a * T + T by ring, Real.exp_add]; ring

/-- Finite-interval integration by parts for the primitive against `e^{−aT}`. -/
theorem integral_exp_mul_deficitPrimitive_interval {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    ∫ T in (0:ℝ)..R, Real.exp (-a * T) * ccmLogChebyshevDeficitPrimitive T =
      -(Real.exp (-a * R) / a) * ccmLogChebyshevDeficitPrimitive R +
        (1 / a) * ∫ T in (0:ℝ)..R, Real.exp (-a * T) * chebyshevLogDeficit T := by
  let E : ℝ → ℝ := fun T => -(Real.exp (-a * T) / a)
  let P : ℝ → ℝ := ccmLogChebyshevDeficitPrimitive
  have hi : IntervalIntegrable chebyshevLogDeficit volume 0 R :=
    intervalIntegrable_chebyshevLogDeficit 0 R
  have hPac : AbsolutelyContinuousOnInterval P 0 R :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (show (0:ℝ) ∈ uIcc 0 R by simp [hR])
  have hEcd : ContDiff ℝ 1 E := by dsimp [E]; fun_prop
  have hEac : AbsolutelyContinuousOnInterval E 0 R := hEcd.contDiffOn.absolutelyContinuousOnInterval
  have hparts := hEac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in (0:ℝ)..R, E t * deriv P t) = ∫ t in (0:ℝ)..R, E t * chebyshevLogDeficit t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (chebyshevLogDeficit t) t := ht (uIoc_subset_uIcc hmem) 0 (by simp [hR])
    rw [hd.deriv]
  have hderivE : ∀ t, deriv E t = Real.exp (-a * t) := by
    intro t
    have h1 : HasDerivAt (fun T : ℝ => -a * T) (-a) t := by
      simpa using (hasDerivAt_id t).const_mul (-a)
    have h2 : HasDerivAt (fun T : ℝ => Real.exp (-a * T)) (Real.exp (-a * t) * -a) t := h1.exp
    have h3 : HasDerivAt E (-(Real.exp (-a * t) * -a / a)) t := (h2.div_const a).neg
    have hval : -(Real.exp (-a * t) * -a / a) = Real.exp (-a * t) := by
      rw [mul_neg, neg_div, neg_neg, mul_div_assoc, div_self ha.ne', mul_one]
    rw [hval] at h3
    exact h3.deriv
  have hright : (∫ t in (0:ℝ)..R, deriv E t * P t) =
      ∫ t in (0:ℝ)..R, Real.exp (-a * t) * ccmLogChebyshevDeficitPrimitive t := by
    apply intervalIntegral.integral_congr
    intro t _
    show deriv E t * P t = Real.exp (-a * t) * ccmLogChebyshevDeficitPrimitive t
    rw [hderivE]
  have hP0 : P 0 = 0 := by simp [P, ccmLogChebyshevDeficitPrimitive]
  rw [hleft, hright, hP0, mul_zero, sub_zero] at hparts
  have hEf : (∫ t in (0:ℝ)..R, E t * chebyshevLogDeficit t) =
      -(1 / a) * ∫ t in (0:ℝ)..R, Real.exp (-a * t) * chebyshevLogDeficit t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [E]
    ring
  rw [hEf] at hparts
  dsimp only [E, P] at hparts
  linarith

/-- **Laplace transform of the primitive.** For `a > 1`,
`∫_0^∞ e^{−aT} D(T) dT = a⁻¹ ∫_0^∞ e^{−aT} (e^T − ψ(e^T)) dT`. -/
theorem integral_exp_mul_deficitPrimitive {a : ℝ} (ha : 1 < a) :
    ∫ T in Ioi (0:ℝ), Real.exp (-a * T) * ccmLogChebyshevDeficitPrimitive T =
      (1 / a) * ∫ T in Ioi (0:ℝ), Real.exp (-a * T) * chebyshevLogDeficit T := by
  have ha0 : 0 < a := by linarith
  have hL := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_deficitPrimitive ha)
    tendsto_id
  have hR := (intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_exp_mul_chebyshevLogDeficit ha) tendsto_id).const_mul (1 / a)
  have hB : Tendsto (fun R : ℝ => -(Real.exp (-a * R) / a) * ccmLogChebyshevDeficitPrimitive R)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => Real.exp (-((a - 1) * R))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by linarith : (0:ℝ) < a - 1))
    have hdecay : Tendsto (fun R : ℝ => chebyshevDeficitConst / a * Real.exp (-((a - 1) * R)))
        atTop (𝓝 0) := by
      simpa using h0.const_mul (chebyshevDeficitConst / a)
    refine squeeze_zero_norm' ?_ hdecay
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos ha0]
    calc Real.exp (-a * R) / a * |ccmLogChebyshevDeficitPrimitive R|
        ≤ Real.exp (-a * R) / a * (chebyshevDeficitConst * Real.exp R) :=
          mul_le_mul_of_nonneg_left (abs_deficitPrimitive_le hR) (by positivity)
      _ = chebyshevDeficitConst / a * Real.exp (-((a - 1) * R)) := by
          rw [show -((a - 1) * R) = -a * R + R by ring, Real.exp_add]; ring
  have hsum := hB.add hR
  rw [zero_add] at hsum
  have heq : (fun R : ℝ => ∫ T in (0:ℝ)..id R, Real.exp (-a * T) * ccmLogChebyshevDeficitPrimitive T)
      =ᶠ[atTop] fun R => -(Real.exp (-a * R) / a) * ccmLogChebyshevDeficitPrimitive R +
        (1 / a) * ∫ T in (0:ℝ)..id R, Real.exp (-a * T) * chebyshevLogDeficit T := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    exact integral_exp_mul_deficitPrimitive_interval ha0 hR
  exact tendsto_nhds_unique (hL.congr' heq) hsum

/-- The deficit is `−e^{t/2}` times the critically normalized Chebyshev error. -/
theorem chebyshevLogDeficit_eq (t : ℝ) :
    chebyshevLogDeficit t = -(Real.exp (t / 2) * criticalMellinNormalizedChebyshevError t) := by
  rw [criticalMellinNormalizedChebyshevError_eq_apertureError, criticalMellinChebyshevError_eq_exp]
  unfold chebyshevLogDeficit
  have he : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
  linear_combination (Chebyshev.psi (Real.exp t) - Real.exp t) * he

/-- The Laplace transform of the deficit at `σ + ½` is minus the critical Mellin transform of the
normalized Chebyshev error at `σ` (as integrals; both converge for `σ > ½`). -/
theorem integral_exp_mul_chebyshevLogDeficit_eq_laplace (σ : ℝ) :
    ((∫ T in Ioi (0:ℝ), Real.exp (-(σ + 1 / 2) * T) * chebyshevLogDeficit T : ℝ) : ℂ) =
      -criticalNormalizedChebyshevErrorLaplace (σ : ℂ) := by
  unfold criticalNormalizedChebyshevErrorLaplace
  rw [← integral_neg, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun T => ?_)
  beta_reduce
  have he : Real.exp (-(σ + 1 / 2) * T) * Real.exp (T / 2) = Real.exp (-σ * T) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc : Complex.exp (-((σ : ℂ) * (T : ℂ))) = ((Real.exp (-σ * T) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hreal : Real.exp (-(σ + 1 / 2) * T) * chebyshevLogDeficit T =
      -(Real.exp (-σ * T) * criticalMellinNormalizedChebyshevError T) := by
    rw [chebyshevLogDeficit_eq, ← he]; ring
  rw [hc, hreal, Complex.ofReal_neg, Complex.ofReal_mul]

/-! ## The one-sided Landau measure -/

/-- The clipped density `max(B + ε e^{−T/2} D(T), 0)`, `ε = ±1`. -/
def deficitOneSidedDensity (ε B : ℝ) (T : ℝ) : NNReal :=
  Real.toNNReal (B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T))

theorem measurable_deficitOneSidedDensity (ε B : ℝ) : Measurable (deficitOneSidedDensity ε B) := by
  unfold deficitOneSidedDensity
  exact (measurable_const.add (measurable_const.mul
    ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      continuous_deficitPrimitive).measurable)).real_toNNReal

/-- `(B + ε e^{−T/2} D(T)) dT` on `(0,∞)` plus Lebesgue measure. -/
def deficitOneSidedMeasure (ε B : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun T => (deficitOneSidedDensity ε B T : ENNReal)) +
    volume

theorem deficitOneSidedDensity_le {ε B : ℝ} (hε : |ε| ≤ 1) {T : ℝ} (hT : 0 < T) :
    ((deficitOneSidedDensity ε B T : ℝ)) ≤ |B| + chebyshevDeficitConst * Real.exp (T / 2) := by
  unfold deficitOneSidedDensity
  rw [Real.coe_toNNReal']
  have hD := abs_deficitPrimitive_le hT.le
  have he : Real.exp (-T / 2) * Real.exp T = Real.exp (T / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hprod : |Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T| ≤
      chebyshevDeficitConst * Real.exp (T / 2) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-T / 2) * |ccmLogChebyshevDeficitPrimitive T|
        ≤ Real.exp (-T / 2) * (chebyshevDeficitConst * Real.exp T) :=
          mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le
      _ = chebyshevDeficitConst * Real.exp (T / 2) := by rw [← he]; ring
  have hε' : |ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T)| ≤
      chebyshevDeficitConst * Real.exp (T / 2) := by
    rw [abs_mul]
    calc |ε| * |Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T|
        ≤ 1 * (chebyshevDeficitConst * Real.exp (T / 2)) :=
          mul_le_mul hε hprod (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h1 := le_abs_self B
  have h2 := le_abs_self (ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T))
  have h3 : 0 ≤ |B| + chebyshevDeficitConst * Real.exp (T / 2) := by
    have := chebyshevDeficitConst_pos; positivity
  rcases le_or_gt (B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T)) 0 with h | h
  · rw [max_eq_right h]; exact h3
  · rw [max_eq_left h.le]; linarith

theorem integrableOn_deficitMajorant {σ B : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun T : ℝ => (|B| + chebyshevDeficitConst * Real.exp (T / 2)) * Real.exp (-σ * T))
      (Ioi 0) := by
  have h1 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ)).const_mul |B|
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1 / 2)).const_mul
    chebyshevDeficitConst
  refine IntegrableOn.congr_fun (h1.add h2) (fun T _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [show Real.exp (-(σ - 1 / 2) * T) = Real.exp (T / 2) * Real.exp (-σ * T) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_deficitDensity_ne_top {ε B σ : ℝ} (hε : |ε| ≤ 1) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun T => (deficitOneSidedDensity ε B T : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun T : ℝ => ENNReal.ofReal (Real.exp (-σ * T))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_deficitOneSidedDensity ε B).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top (integrableOn_deficitMajorant (B := B) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (deficitOneSidedDensity_le hε hT) (Real.exp_pos _).le

theorem laplaceMass_deficitOneSided_eq (ε B σ : ℝ) :
    laplaceMass (deficitOneSidedMeasure ε B) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (deficitOneSidedDensity ε B T : ENNReal))) σ + laplaceMass volume σ := by
  unfold laplaceMass deficitOneSidedMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

/-- The convergence set lies in `(0,∞)`, contains `1`, and is an up-set; its infimum is the
abscissa. -/
theorem isAbscissa_deficitOneSided {ε B : ℝ} (hε : |ε| ≤ 1) :
    IsAbscissa (deficitOneSidedMeasure ε B)
        (sInf {σ : ℝ | laplaceMass (deficitOneSidedMeasure ε B) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (deficitOneSidedMeasure ε B) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (deficitOneSidedMeasure ε B) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_deficitOneSided_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (deficitOneSidedMeasure ε B) 1 ≠ ⊤
    rw [laplaceMass_deficitOneSided_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_deficitDensity_ne_top hε (by norm_num),
      laplaceMass_volume_ne_top one_pos⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The real Laplace transform -/

/-- The candidate continuation `(B+1)/z + ε (ζ_u'/ζ_u(z+½) + 1)/(z+½)²`. -/
def deficitOneSidedContinuation (ε B : ℝ) (z : ℂ) : ℂ :=
  (B + 1) / z + ε * ((logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2) ^ 2)

theorem analyticAt_deficitOneSidedContinuation (ε B : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z + 1 / 2 ≠ 0) (hζ : zetaResidueUnit (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (deficitOneSidedContinuation ε B) z := by
  unfold deficitOneSidedContinuation
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hζan : AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)) hshift
  have hdζ : AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)).deriv
      hshift
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2)) z := by
    simp only [logDeriv_apply]
    exact hdζ.div hζan hζ
  refine (analyticAt_const.div analyticAt_id hz0).add (analyticAt_const.mul ?_)
  exact (hlog.add analyticAt_const).div (hshift.pow 2) (pow_ne_zero 2 hz1)

theorem deficitOneSidedDensity_eq {ε B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T))
    {T : ℝ} (hT : 0 ≤ T) :
    ((deficitOneSidedDensity ε B T : ℝ)) =
      B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T) := by
  unfold deficitOneSidedDensity
  exact Real.coe_toNNReal _ (hB T hT)

/-- On real `σ > ½` the Laplace transform of the one-sided measure is the continuation. -/
theorem laplaceReal_deficitOneSided_eq {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T))
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((laplaceReal (deficitOneSidedMeasure ε B) σ : ℝ) : ℂ) =
      deficitOneSidedContinuation ε B (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hexpInt : IntegrableOn (fun T : ℝ => Real.exp (-σ * T)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hσ0
  have hdensInt : Integrable (fun T : ℝ => Real.exp (-σ * T))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (deficitOneSidedDensity ε B T : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_deficitOneSidedDensity ε B)]
    refine (integrableOn_deficitMajorant (B := B) hσ).mono' ?_ ?_
    · exact ((measurable_deficitOneSidedDensity ε B).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (deficitOneSidedDensity_le hε hT) (Real.exp_pos _).le
  have hsplit : laplaceReal (deficitOneSidedMeasure ε B) σ =
      (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (deficitOneSidedDensity ε B T : ENNReal)))) + 1 / σ := by
    unfold laplaceReal deficitOneSidedMeasure
    rw [Measure.restrict_add, integral_add_measure hdensInt hexpInt,
      integral_exp_neg_mul_Ioi_real hσ0]
  have hdens : (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (deficitOneSidedDensity ε B T : ENNReal)))) =
      B / σ + ε * ∫ T in Ioi (0:ℝ),
        Real.exp (-(σ + 1 / 2) * T) * ccmLogChebyshevDeficitPrimitive T := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_deficitOneSidedDensity ε B)]
    have hpt : ∀ T ∈ Ioi (0:ℝ), deficitOneSidedDensity ε B T • Real.exp (-σ * T) =
        B * Real.exp (-σ * T) +
          ε * (Real.exp (-(σ + 1 / 2) * T) * ccmLogChebyshevDeficitPrimitive T) := by
      intro T hT
      rw [NNReal.smul_def, smul_eq_mul, deficitOneSidedDensity_eq hB (le_of_lt hT)]
      have he : Real.exp (-T / 2) * Real.exp (-σ * T) = Real.exp (-(σ + 1 / 2) * T) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [← he]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add (hexpInt.const_mul B)
        ((integrableOn_exp_mul_deficitPrimitive (by linarith : 1 < σ + 1 / 2)).const_mul ε),
      integral_const_mul, integral_const_mul, integral_exp_neg_mul_Ioi_real hσ0]
    ring
  rw [hsplit, hdens, integral_exp_mul_deficitPrimitive (by linarith : 1 < σ + 1 / 2)]
  have hL := integral_exp_mul_chebyshevLogDeficit_eq_laplace σ
  have hlog := criticalNormalizedChebyshevErrorLaplace_eq_logDeriv (z := (σ : ℂ))
    (by simpa using hσ)
  unfold deficitOneSidedContinuation
  push_cast
  rw [hL, hlog]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hσh : (σ : ℂ) + 1 / 2 ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simp at hre; linarith
  field_simp
  ring

/-! ## Landau: the abscissa is zero -/

theorem abscissa_deficitOneSided_eq_zero {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T)) :
    IsAbscissa (deficitOneSidedMeasure ε B) 0 := by
  obtain ⟨hc, hc0⟩ := isAbscissa_deficitOneSided (B := B) hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (deficitOneSidedMeasure ε B) σ ≠ ⊤} with hcdef
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
    refine false_of_analyticAt_abscissa hc hδ (Φ := deficitOneSidedContinuation ε B) ?_ ?_
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
      exact analyticAt_deficitOneSidedContinuation ε B hz0 hz1 hzζ
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (deficitOneSidedMeasure ε B))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (deficitOneSidedMeasure ε B) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (deficitOneSidedMeasure ε B)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => deficitOneSidedContinuation ε B (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (deficitOneSidedContinuation ε B) (t : ℂ) := by
          refine analyticAt_deficitOneSidedContinuation ε B (by exact_mod_cast ht0.ne') ?_ ?_
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
            rw [laplaceMass_deficitOneSided_eq, laplaceMass_volume_eq_top (not_le.mp hlt), add_top]
          · show laplaceMass (deficitOneSidedMeasure ε B) (3 / 4) ≠ ⊤
            rw [laplaceMass_deficitOneSided_eq]
            exact ENNReal.add_ne_top.mpr ⟨laplaceMass_deficitDensity_ne_top hε (by norm_num),
              laplaceMass_volume_ne_top (by norm_num)⟩
        linarith
      have hfg : (fun t : ℝ => complexLaplace (deficitOneSidedMeasure ε B) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => deficitOneSidedContinuation ε B (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        rw [complexLaplace_ofReal]
        exact laplaceReal_deficitOneSided_eq hε hB ht.1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ' : complexLaplace (deficitOneSidedMeasure ε B) (σ : ℂ) =
          deficitOneSidedContinuation ε B (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ', complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The criterion -/

/-- The extension of the regularized critical-Mellin defect manufactured from the one-sided
Landau measure. -/
def deficitOneSidedDefectExtension (ε B : ℝ) (u : ℂ) : ℂ :=
  1 / (u + 1) + ε * ((u + 1) ^ 2 *
    (complexLaplace (deficitOneSidedMeasure ε B) (u + 1 / 2) - (B + 1) / (u + 1 / 2))) - 1

/-- Where the Laplace transform equals the continuation, the manufactured extension is the
regularized critical-Mellin defect. -/
theorem deficitOneSidedDefectExtension_eq_regularized {ε B : ℝ} (hεsq : (ε : ℂ) * ε = 1) {u : ℂ}
    (hu : complexLaplace (deficitOneSidedMeasure ε B) (u + 1 / 2) =
      deficitOneSidedContinuation ε B (u + 1 / 2))
    (hu1 : u + 1 ≠ 0) :
    deficitOneSidedDefectExtension ε B u = regularizedCriticalMellinDefect u := by
  unfold deficitOneSidedDefectExtension regularizedCriticalMellinDefect
  rw [hu]
  unfold deficitOneSidedContinuation
  have hsum : u + 1 / 2 + 1 / 2 = u + 1 := by ring
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hsum, hreg]
  have hcancel : (u + 1) ^ 2 * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2) =
      logDeriv zetaResidueUnit (u + 1) + 1 := by
    field_simp
  calc 1 / (u + 1) + (ε : ℂ) * ((u + 1) ^ 2 * (((B:ℂ) + 1) / (u + 1 / 2) +
          (ε : ℂ) * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2) -
          ((B:ℂ) + 1) / (u + 1 / 2))) - 1
      = 1 / (u + 1) + ((ε : ℂ) * ε) *
          ((u + 1) ^ 2 * ((logDeriv zetaResidueUnit (u + 1) + 1) / (u + 1) ^ 2)) - 1 := by ring
    _ = 1 / (u + 1) + logDeriv zetaResidueUnit (u + 1) := by rw [hcancel, hεsq]; ring

theorem riemannHypothesis_of_logChebyshevDeficitPrimitive_oneSided {ε B : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B + ε * (Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T)) :
    RiemannHypothesis := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hc := abscissa_deficitOneSided_eq_zero hε1 hB
  have hA : AnalyticOnNhd ℂ (deficitOneSidedDefectExtension ε B)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
    intro u hu
    change -1 / 2 < u.re at hu
    have hz : 0 < (u + 1 / 2).re := by simp; linarith
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) u := by fun_prop
    have hL : AnalyticAt ℂ (fun w : ℂ => complexLaplace (deficitOneSidedMeasure ε B) (w + 1 / 2)) u := by
      have hdiff : DifferentiableOn ℂ (complexLaplace (deficitOneSidedMeasure ε B)) {z : ℂ | 0 < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (hdiff.analyticAt (hopen.mem_nhds hz))
        hshift
    have hu1 : u + 1 ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    have hu12 : u + 1 / 2 ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    unfold deficitOneSidedDefectExtension
    refine ((analyticAt_const.div (analyticAt_id.add analyticAt_const) hu1).add
      (analyticAt_const.mul (((analyticAt_id.add analyticAt_const).pow 2).mul
        (hL.sub (analyticAt_const.div hshift hu12))))).sub analyticAt_const
  refine riemannHypothesis_of_regularizedCriticalMellinDefect_extension _ hA ?_
  -- agreement on the right half-plane, from agreement on the positive reals
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAU : AnalyticOnNhd ℂ (deficitOneSidedDefectExtension ε B) U :=
    hA.mono (fun u hu => by change 0 < u.re at hu; change -1 / 2 < u.re; linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have hreal : ∀ r : ℝ, 0 < r →
      deficitOneSidedDefectExtension ε B (r : ℂ) = regularizedCriticalMellinDefect (r : ℂ) := by
    intro r hr
    have hlap := laplaceReal_deficitOneSided_eq hε1 hB (σ := r + 1 / 2) (by linarith)
    rw [← complexLaplace_ofReal] at hlap
    have hcast : (((r + 1 / 2 : ℝ)) : ℂ) = (r : ℂ) + 1 / 2 := by push_cast; ring
    rw [hcast] at hlap
    have hr1 : (r : ℂ) + 1 ≠ 0 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; linarith
    exact deficitOneSidedDefectExtension_eq_regularized hεsq hlap hr1
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
      deficitOneSidedDefectExtension ε B z = regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r (lt_trans (by norm_num) hr)
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have heq := hAU.eqOn_of_preconnected_of_frequently_eq hR hUpre htwo hfreq
  intro s hs
  exact heq (show s ∈ U from hs)

/-- **A one-sided lower bound suffices.** If `−B e^{T/2} ≤ ∫_0^T (e^t − ψ(e^t)) dt` for all
`T ≥ 0`, then RH holds. -/
theorem riemannHypothesis_of_logChebyshevDeficitPrimitive_ge {B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T → -(B * Real.exp (T / 2)) ≤ ccmLogChebyshevDeficitPrimitive T) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_oneSided (ε := 1) (B := B) (Or.inl rfl) ?_
  intro T hT
  have h := hB T hT
  have he : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  have hpos := Real.exp_pos (-T / 2)
  have hmul := mul_le_mul_of_nonneg_left h hpos.le
  have hB' : Real.exp (-T / 2) * -(B * Real.exp (T / 2)) = -B := by
    rw [show Real.exp (-T / 2) * -(B * Real.exp (T / 2)) =
      -B * (Real.exp (-T / 2) * Real.exp (T / 2)) by ring, he, mul_one]
  linarith

/-- **A one-sided upper bound suffices.** If `∫_0^T (e^t − ψ(e^t)) dt ≤ B e^{T/2}` for all
`T ≥ 0`, then RH holds. -/
theorem riemannHypothesis_of_logChebyshevDeficitPrimitive_le {B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T → ccmLogChebyshevDeficitPrimitive T ≤ B * Real.exp (T / 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_oneSided (ε := -1) (B := B)
    (Or.inr rfl) ?_
  intro T hT
  have h := hB T hT
  have he : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  have hpos := Real.exp_pos (-T / 2)
  have hmul := mul_le_mul_of_nonneg_left h hpos.le
  have hB' : Real.exp (-T / 2) * (B * Real.exp (T / 2)) = B := by
    rw [show Real.exp (-T / 2) * (B * Real.exp (T / 2)) =
      B * (Real.exp (-T / 2) * Real.exp (T / 2)) by ring, he, mul_one]
  linarith

end

end RHTower
