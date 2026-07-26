import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments
import GaloisForLFunctions.RHTower.MobiusIncidenceKMSEntropyProduction
import GaloisForLFunctions.HTGeometry.FiniteProbabilityGiniLayerCake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Four-unit Mobius incidence-clock energy

This module proves the exact finite layer-cake/Gini identity for divisor packets, upgrades weak
critical-clock convergence to convergence of the unbounded absolute gap moment, and derives the
four-unit incidence and projective-Fisher limits.  It also proves the finite-window profile
`4 * (1 - exp (-u))^2`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

/-- Strict lower-cut mass for a finite divisor-incidence packet. -/
def finiteIncidenceLowerCutMass
    {alpha : Type*} [Fintype alpha]
    (sigma : ℝ) (d : alpha → ℕ) (t : ℝ) : ℝ :=
  _root_.HTGeometry.finiteStrictLowerCutMass
    (finiteIncidenceProbability sigma d) (fun i => Real.log (d i)) t

/-- Clock-relative rank-one incidence energy of a finite divisor packet. -/
def finiteIncidenceRelativeClockEnergy
    {alpha : Type*} [Fintype alpha]
    (sigma epsilon : ℝ) (d : alpha → ℕ) : ℝ :=
  8 * epsilon * ∫ t : ℝ in Ioi 0,
    finiteIncidenceLowerCutMass sigma d t *
      (1 - finiteIncidenceLowerCutMass sigma d t)

/-- The finite relative clock energy is exactly the finite incidence Gini energy. -/
theorem finiteIncidenceRelativeClockEnergy_eq_gini
    {alpha : Type*} [Fintype alpha] [Nonempty alpha]
    {sigma epsilon : ℝ} {d : alpha → ℕ} (hd : ∀ i, 0 < d i) :
    finiteIncidenceRelativeClockEnergy sigma epsilon d =
      finiteIncidenceGiniEnergy sigma epsilon d := by
  rw [finiteIncidenceRelativeClockEnergy]
  unfold finiteIncidenceLowerCutMass
  rw [_root_.HTGeometry.integral_Ioi_finiteStrictLowerCutMass_mul_one_sub
    (sum_finiteIncidenceProbability hd)
    (fun i => Real.log_natCast_nonneg (d i))]
  unfold finiteIncidenceGiniEnergy
  ring

private theorem pmf_toMeasure_eq_sum_smul_dirac
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    (p : PMF X) :
    p.toMeasure = Measure.sum (fun x => (p x) • Measure.dirac x) := by
  ext s hs
  rw [p.toMeasure_apply hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ s <;> simp [Measure.smul_apply, hs, hx]

private theorem integrable_squarefreeMobiusCriticalClock_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun y : ℝ => y ^ 2)
      (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) := by
  let p := squarefreeMobiusCriticalPMF sigma
  let clock := squarefreeMobiusCriticalClock sigma
  have hsum : Summable (fun n : ℕ =>
      (p n).toReal * ‖clock n ^ 2‖) := by
    have h := (summable_squarefreeMobiusLogMoment 2 hsigma).mul_left
      ((sigma - 1) ^ 2)
    apply h.congr
    intro n
    simp only [p, squarefreeMobiusCriticalPMF_toReal hsigma,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    unfold clock squarefreeMobiusCriticalClock
    ring
  have hsource : Integrable (fun n : ℕ => clock n ^ 2) p.toMeasure := by
    rw [pmf_toMeasure_eq_sum_smul_dirac]
    exact integrable_sum_dirac (fun n => p.apply_ne_top n) hsum
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  exact (integrable_map_measure
    (continuous_pow 2).aestronglyMeasurable
    (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)).2 hsource

private theorem integral_squarefreeMobiusCriticalClock_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ y : ℝ, y ^ 2
      ∂(squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)) =
      (sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma := by
  let p := squarefreeMobiusCriticalPMF sigma
  let clock := squarefreeMobiusCriticalClock sigma
  have hsource : Integrable (fun n : ℕ => clock n ^ 2) p.toMeasure := by
    have hmap := integrable_squarefreeMobiusCriticalClock_sq hsigma
    rw [squarefreeMobiusCriticalClockProbabilityMeasure] at hmap
    exact (integrable_map_measure
      (continuous_pow 2).aestronglyMeasurable
      (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)).1 hmap
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map
    (Measurable.of_discrete.aemeasurable : AEMeasurable clock p.toMeasure)
    (continuous_pow 2).aestronglyMeasurable]
  rw [PMF.integral_eq_tsum p _ hsource]
  simp only [smul_eq_mul]
  simp only [p]
  simp_rw [squarefreeMobiusCriticalPMF_toReal hsigma]
  unfold clock squarefreeMobiusCriticalClock squarefreeMobiusLogMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

private theorem integrable_squarefreeMobiusCriticalGap_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun y : ℝ => y ^ 2)
      (squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ) := by
  let μ := (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
  have hsquare : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_squarefreeMobiusCriticalClock_sq hsigma
  have hfst : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2) (μ.prod μ) :=
    (hsquare.comp_fst μ).const_mul 2
  have hsnd : Integrable (fun p : ℝ × ℝ => 2 * p.2 ^ 2) (μ.prod μ) :=
    (hsquare.comp_snd μ).const_mul 2
  have hdom : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.2 ^ 2) (μ.prod μ) :=
    hfst.add hsnd
  have hsource : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (p.1 + p.2)]
  unfold squarefreeMobiusCriticalGapProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (continuous_fst.sub continuous_snd).aemeasurable).2 hsource

private theorem integral_squarefreeMobiusCriticalGap_sq_le
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ y : ℝ, y ^ 2
      ∂(squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ)) ≤
      4 * ((sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma) := by
  let μ := (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)
  have hsquare : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_squarefreeMobiusCriticalClock_sq hsigma
  have hfst : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2) (μ.prod μ) :=
    (hsquare.comp_fst μ).const_mul 2
  have hsnd : Integrable (fun p : ℝ × ℝ => 2 * p.2 ^ 2) (μ.prod μ) :=
    (hsquare.comp_snd μ).const_mul 2
  have hdom : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.2 ^ 2) (μ.prod μ) :=
    hfst.add hsnd
  have hsource : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (p.1 + p.2)]
  have hmono : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ)) ≤
      ∫ p : ℝ × ℝ, (2 * p.1 ^ 2 + 2 * p.2 ^ 2) ∂(μ.prod μ) := by
    exact integral_mono hsource hdom (fun p => by
      nlinarith [sq_nonneg (p.1 + p.2)])
  have hmap : (∫ y : ℝ, y ^ 2
      ∂(squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ)) =
      ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ) := by
    unfold squarefreeMobiusCriticalGapProbabilityMeasure ProbabilityMeasure.map
    simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
    exact integral_map (continuous_fst.sub continuous_snd).aemeasurable
      (continuous_pow 2).aestronglyMeasurable
  rw [hmap]
  calc
    _ ≤ ∫ p : ℝ × ℝ, (2 * p.1 ^ 2 + 2 * p.2 ^ 2) ∂(μ.prod μ) := hmono
    _ = 4 * ∫ x : ℝ, x ^ 2 ∂μ := by
      have hifst : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂(μ.prod μ)) =
          ∫ x : ℝ, x ^ 2 ∂μ := by
        simpa [μ] using
          (integral_fun_fst (μ := μ) (ν := μ) (fun x : ℝ => x ^ 2))
      have hisnd : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂(μ.prod μ)) =
          ∫ x : ℝ, x ^ 2 ∂μ := by
        simpa [μ] using
          (integral_fun_snd (μ := μ) (ν := μ) (fun x : ℝ => x ^ 2))
      rw [integral_add hfst hsnd, integral_const_mul, integral_const_mul,
        hifst, hisnd]
      ring
    _ = 4 * ((sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma) := by
      rw [integral_squarefreeMobiusCriticalClock_sq hsigma]

private theorem integral_abs_mul_mobiusCriticalLaplaceGapDensity :
    (∫ x : ℝ, |x| * mobiusCriticalLaplaceGapDensity x) = 1 := by
  rw [show (fun x : ℝ => |x| * mobiusCriticalLaplaceGapDensity x) =
      fun x : ℝ => (1 / 2 : ℝ) * (|x| * Real.exp (-|x|)) by
    funext x
    unfold mobiusCriticalLaplaceGapDensity
    ring]
  rw [integral_const_mul,
    integral_comp_abs (f := fun x : ℝ => x * Real.exp (-x))]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  have hhalf : (∫ x : ℝ in Ioi 0, x * Real.exp (-x)) = 1 := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          x ^ ((2 : ℝ) - 1) * Real.exp (-(1 * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        norm_num
      _ = (1 / (1 : ℝ)) ^ (2 : ℝ) * Real.Gamma 2 := hgamma
      _ = 1 := by norm_num [Real.Gamma_nat_eq_factorial]
  rw [hhalf]
  norm_num

private theorem integrableOn_sq_mul_exp_neg :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num)
  exact h.congr_fun (fun x hx => by norm_num; ring) measurableSet_Ioi

private theorem integrable_sq_mul_exp_neg_abs :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-|x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-|x|)) (Ioi 0) :=
    integrableOn_sq_mul_exp_neg.congr_fun (fun x hx => by
      rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-|x|)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
  rw [← integrableOn_univ]
  simpa only [Ioi_union_Iic] using hpos.union hneg

private theorem integrable_sq_mul_mobiusCriticalLaplaceGapDensity :
    Integrable (fun x : ℝ => x ^ 2 * mobiusCriticalLaplaceGapDensity x) := by
  rw [show (fun x : ℝ => x ^ 2 * mobiusCriticalLaplaceGapDensity x) =
      fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2 * Real.exp (-|x|)) by
    funext x
    unfold mobiusCriticalLaplaceGapDensity
    ring]
  exact integrable_sq_mul_exp_neg_abs.const_mul (1 / 2 : ℝ)

private theorem integral_sq_mul_mobiusCriticalLaplaceGapDensity :
    (∫ x : ℝ, x ^ 2 * mobiusCriticalLaplaceGapDensity x) = 2 := by
  rw [show (fun x : ℝ => x ^ 2 * mobiusCriticalLaplaceGapDensity x) =
      fun x : ℝ => (1 / 2 : ℝ) * (|x| ^ 2 * Real.exp (-|x|)) by
    funext x
    unfold mobiusCriticalLaplaceGapDensity
    rw [sq_abs]
    ring]
  rw [integral_const_mul,
    integral_comp_abs (f := fun x : ℝ => x ^ 2 * Real.exp (-x))]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  have hhalf : (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-x)) = 2 := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          x ^ ((3 : ℝ) - 1) * Real.exp (-(1 * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        norm_num
      _ = (1 / (1 : ℝ)) ^ (3 : ℝ) * Real.Gamma 3 := hgamma
      _ = 2 := by norm_num [Real.Gamma_nat_eq_factorial]
  rw [hhalf]
  norm_num

/-- The universal Laplace gap law has absolute first moment one. -/
theorem integral_abs_mobiusCriticalExponentialGapProbabilityMeasure :
    (∫ x : ℝ, |x|
      ∂(mobiusCriticalExponentialGapProbabilityMeasure : Measure ℝ)) = 1 := by
  rw [mobiusCriticalExponentialGapProbabilityMeasure_eq_laplace]
  unfold mobiusCriticalLaplaceGapProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [mobiusCriticalLaplaceGapMeasure,
    integral_withDensity_eq_integral_smul
      continuous_mobiusCriticalLaplaceGapDensityNNReal.measurable]
  rw [show (fun x : ℝ => mobiusCriticalLaplaceGapDensityNNReal x • |x|) =
      fun x : ℝ => |x| * mobiusCriticalLaplaceGapDensity x by
    funext x
    change mobiusCriticalLaplaceGapDensity x * |x| = _
    ring]
  exact integral_abs_mul_mobiusCriticalLaplaceGapDensity

/-- The universal Laplace gap law has an integrable square. -/
theorem integrable_sq_mobiusCriticalExponentialGapProbabilityMeasure :
    Integrable (fun x : ℝ => x ^ 2)
      (mobiusCriticalExponentialGapProbabilityMeasure : Measure ℝ) := by
  rw [mobiusCriticalExponentialGapProbabilityMeasure_eq_laplace]
  unfold mobiusCriticalLaplaceGapProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [mobiusCriticalLaplaceGapMeasure,
    integrable_withDensity_iff_integrable_coe_smul
      continuous_mobiusCriticalLaplaceGapDensityNNReal.measurable]
  change Integrable (fun x : ℝ => mobiusCriticalLaplaceGapDensity x * x ^ 2)
  simpa [mul_comm] using integrable_sq_mul_mobiusCriticalLaplaceGapDensity

/-- The universal Laplace gap law has second moment two. -/
theorem integral_sq_mobiusCriticalExponentialGapProbabilityMeasure :
    (∫ x : ℝ, x ^ 2
      ∂(mobiusCriticalExponentialGapProbabilityMeasure : Measure ℝ)) = 2 := by
  rw [mobiusCriticalExponentialGapProbabilityMeasure_eq_laplace]
  unfold mobiusCriticalLaplaceGapProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [mobiusCriticalLaplaceGapMeasure,
    integral_withDensity_eq_integral_smul
      continuous_mobiusCriticalLaplaceGapDensityNNReal.measurable]
  rw [show (fun x : ℝ => mobiusCriticalLaplaceGapDensityNNReal x • x ^ 2) =
      fun x : ℝ => x ^ 2 * mobiusCriticalLaplaceGapDensity x by
    funext x
    change mobiusCriticalLaplaceGapDensity x * x ^ 2 = _
    ring]
  exact integral_sq_mul_mobiusCriticalLaplaceGapDensity

private def clippedAbsBCF (R : ℝ) (hR : 0 ≤ R) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : ℝ => min |x| R, continuous_abs.min continuous_const⟩
    (2 * R)
    (fun x y => by
      rw [Real.dist_eq]
      have hx0 : 0 ≤ min |x| R := le_min (abs_nonneg x) hR
      have hy0 : 0 ≤ min |y| R := le_min (abs_nonneg y) hR
      have hxR : min |x| R ≤ R := min_le_right _ _
      have hyR : min |y| R ≤ R := min_le_right _ _
      calc
        |min |x| R - min |y| R| ≤ |min |x| R| + |min |y| R| := abs_sub _ _
        _ = min |x| R + min |y| R := by rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
        _ ≤ 2 * R := by linarith)

private theorem integrable_abs_of_integrable_sq
    (μ : ProbabilityMeasure ℝ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
  have hdom : Integrable (fun x : ℝ => 1 + x ^ 2) (μ : Measure ℝ) :=
    (integrable_const 1).add hsq
  refine hdom.mono' continuous_abs.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_abs]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsqabs : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - 1 / 2)]

private theorem abs_sub_min_abs_le_sq_div
    {R x : ℝ} (hR : 0 < R) :
    |x| - min |x| R ≤ x ^ 2 / R := by
  by_cases hxR : |x| ≤ R
  · rw [min_eq_left hxR]
    simpa using div_nonneg (sq_nonneg x) hR.le
  · have hRabs : R < |x| := lt_of_not_ge hxR
    rw [min_eq_right hRabs.le]
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hdiv : |x| ≤ x ^ 2 / R := by
      rw [le_div_iff₀ hR]
      nlinarith [sq_abs x]
    linarith

private theorem integral_abs_sub_clippedAbs_le
    (μ : ProbabilityMeasure ℝ) {R C : ℝ} (hR : 0 < R)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ))
    (hbound : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) ≤ C) :
    (∫ x : ℝ, (|x| - min |x| R) ∂(μ : Measure ℝ)) ≤ C / R := by
  have habs := integrable_abs_of_integrable_sq μ hsq
  have hclip : Integrable (fun x : ℝ => min |x| R) (μ : Measure ℝ) := by
    exact BoundedContinuousFunction.integrable (μ : Measure ℝ) (clippedAbsBCF R hR.le)
  have htail : Integrable (fun x : ℝ => |x| - min |x| R) (μ : Measure ℝ) :=
    habs.sub hclip
  have hscaled : Integrable (fun x : ℝ => x ^ 2 / R) (μ : Measure ℝ) :=
    hsq.div_const R
  calc
    _ ≤ ∫ x : ℝ, x ^ 2 / R ∂(μ : Measure ℝ) :=
      integral_mono htail hscaled (fun x => abs_sub_min_abs_le_sq_div hR)
    _ = (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) / R := by
      rw [integral_div]
    _ ≤ C / R := (div_le_div_iff_of_pos_right hR).mpr hbound

/-- **Weak convergence plus a uniform second moment gives convergence of the absolute first
moment.**  Clipping `|x|` at a height `R` gives a bounded continuous test function; the clipping
error is controlled uniformly by `C/R`.  No property of the measures beyond the uniform square
bound is used. -/
theorem tendsto_integral_abs_of_weak_of_uniform_sq
    {I : Type*} {F : Filter I} [NeBot F]
    {mus : I → ProbabilityMeasure ℝ} {mu : ProbabilityMeasure ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hweak : Tendsto mus F (nhds mu))
    (hsq : ∀ᶠ i in F,
      Integrable (fun x : ℝ => x ^ 2) (mus i : Measure ℝ) ∧
        (∫ x : ℝ, x ^ 2 ∂(mus i : Measure ℝ)) ≤ C)
    (hsqLimit : Integrable (fun x : ℝ => x ^ 2) (mu : Measure ℝ))
    (hboundLimit : (∫ x : ℝ, x ^ 2 ∂(mu : Measure ℝ)) ≤ C) :
    Tendsto (fun i => ∫ x : ℝ, |x| ∂(mus i : Measure ℝ)) F
      (nhds (∫ x : ℝ, |x| ∂(mu : Measure ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (3 * C / epsilon)
  have hnpos : 0 < (n : ℝ) := by
    have hnonneg : 0 ≤ 3 * C / epsilon := by positivity
    exact_mod_cast hnonneg.trans_lt hn
  have htailSmall : C / (n : ℝ) < epsilon / 3 := by
    have hmul : 3 * C < (n : ℝ) * epsilon := by
      exact (div_lt_iff₀ hepsilon).mp (by simpa [div_eq_mul_inv] using hn)
    rw [div_lt_iff₀ hnpos]
    nlinarith
  have hclipTendsto :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
      (clippedAbsBCF n hnpos.le)
  have hclipEventually : ∀ᶠ i in F,
      dist (∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ))
        (∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ)) < epsilon / 3 :=
    (Metric.tendsto_nhds.mp hclipTendsto) (epsilon / 3) (by positivity)
  filter_upwards [hsq, hclipEventually] with i hsqI hclipI
  have habsI := integrable_abs_of_integrable_sq (mus i) hsqI.1
  have habsLimit := integrable_abs_of_integrable_sq mu hsqLimit
  have hclipIInt : Integrable (fun x : ℝ => min |x| (n : ℝ))
      (mus i : Measure ℝ) :=
    BoundedContinuousFunction.integrable (mus i : Measure ℝ)
      (clippedAbsBCF n hnpos.le)
  have hclipLimitInt : Integrable (fun x : ℝ => min |x| (n : ℝ))
      (mu : Measure ℝ) :=
    BoundedContinuousFunction.integrable (mu : Measure ℝ)
      (clippedAbsBCF n hnpos.le)
  let tailI := ∫ x : ℝ, (|x| - min |x| (n : ℝ)) ∂(mus i : Measure ℝ)
  let tailLimit := ∫ x : ℝ, (|x| - min |x| (n : ℝ)) ∂(mu : Measure ℝ)
  have htailI0 : 0 ≤ tailI := integral_nonneg (fun x => sub_nonneg.mpr (min_le_left _ _))
  have htailLimit0 : 0 ≤ tailLimit :=
    integral_nonneg (fun x => sub_nonneg.mpr (min_le_left _ _))
  have htailI : tailI < epsilon / 3 :=
    (integral_abs_sub_clippedAbs_le (mus i) hnpos hsqI.1 hsqI.2).trans_lt htailSmall
  have htailLimit : tailLimit < epsilon / 3 :=
    (integral_abs_sub_clippedAbs_le mu hnpos hsqLimit hboundLimit).trans_lt htailSmall
  have hsplitI : (∫ x : ℝ, |x| ∂(mus i : Measure ℝ)) =
      (∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) + tailI := by
    dsimp [tailI]
    calc
      _ = ∫ x : ℝ, min |x| (n : ℝ) +
          (|x| - min |x| (n : ℝ)) ∂(mus i : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := integral_add hclipIInt (habsI.sub hclipIInt)
  have hsplitLimit : (∫ x : ℝ, |x| ∂(mu : Measure ℝ)) =
      (∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ)) + tailLimit := by
    dsimp [tailLimit]
    calc
      _ = ∫ x : ℝ, min |x| (n : ℝ) +
          (|x| - min |x| (n : ℝ)) ∂(mu : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := integral_add hclipLimitInt (habsLimit.sub hclipLimitInt)
  rw [Real.dist_eq] at hclipI ⊢
  rw [hsplitI, hsplitLimit]
  have htriangle := abs_add_three
    ((∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) -
      (∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ)))
    tailI (-tailLimit)
  rw [abs_of_nonneg htailI0, abs_neg, abs_of_nonneg htailLimit0] at htriangle
  calc
    |((∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) + tailI) -
        ((∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ)) + tailLimit)| ≤
        |(∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) -
          (∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ))| +
          tailI + tailLimit := by
      rw [show
        ((∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) + tailI) -
            ((∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ)) + tailLimit) =
          ((∫ x : ℝ, min |x| (n : ℝ) ∂(mus i : Measure ℝ)) -
            (∫ x : ℝ, min |x| (n : ℝ) ∂(mu : Measure ℝ))) +
            tailI + (-tailLimit) by ring]
      exact htriangle
    _ < epsilon := by linarith

/-- The critical squarefree clock gap has Gini mean difference tending to one. -/
theorem tendsto_integral_abs_squarefreeMobiusCriticalGapProbabilityMeasure :
    Tendsto (fun sigma : ℝ =>
      ∫ x : ℝ, |x|
        ∂(squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have hmomentEventually : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      (sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma ≤ 3 := by
    have hlt := (tendsto_order.1 tendsto_squarefreeMobiusLogMoment_two_critical).2
      3 (by norm_num)
    exact hlt.mono fun sigma hsigma => hsigma.le
  have hsqEventually : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      Integrable (fun x : ℝ => x ^ 2)
          (squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ) ∧
        (∫ x : ℝ, x ^ 2
          ∂(squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ)) ≤ 12 := by
    filter_upwards [self_mem_nhdsWithin, hmomentEventually] with sigma hsigma hmoment
    refine ⟨integrable_squarefreeMobiusCriticalGap_sq hsigma, ?_⟩
    exact (integral_squarefreeMobiusCriticalGap_sq_le hsigma).trans (by nlinarith)
  have htendsto := tendsto_integral_abs_of_weak_of_uniform_sq
    (C := (12 : ℝ)) (by norm_num)
    tendsto_squarefreeMobiusCriticalGapProbabilityMeasure
    hsqEventually
    integrable_sq_mobiusCriticalExponentialGapProbabilityMeasure
    (by rw [integral_sq_mobiusCriticalExponentialGapProbabilityMeasure]; norm_num)
  rwa [integral_abs_mobiusCriticalExponentialGapProbabilityMeasure] at htendsto

/-- Critical rank-one incidence energy after the intrinsic clock rescaling. -/
def squarefreeMobiusCriticalRelativeClockEnergy (sigma : ℝ) : ℝ :=
  4 * ∫ x : ℝ, |x|
    ∂(squarefreeMobiusCriticalGapProbabilityMeasure sigma : Measure ℝ)

/-- The squarefree divisor-incidence clock carries exactly four asymptotic energy units. -/
theorem tendsto_squarefreeMobiusCriticalRelativeClockEnergy :
    Tendsto squarefreeMobiusCriticalRelativeClockEnergy
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  simpa [squarefreeMobiusCriticalRelativeClockEnergy] using
    tendsto_const_nhds.mul
      tendsto_integral_abs_squarefreeMobiusCriticalGapProbabilityMeasure

/-- Variance of the rescaled squarefree logarithmic clock. -/
def squarefreeMobiusCriticalClockVariance (sigma : ℝ) : ℝ :=
  (sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma -
    ((sigma - 1) * squarefreeMobiusLogMoment 1 sigma) ^ 2

/-- The rescaled squarefree logarithmic clock has asymptotic variance one. -/
theorem tendsto_squarefreeMobiusCriticalClockVariance :
    Tendsto squarefreeMobiusCriticalClockVariance
    (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have h := tendsto_squarefreeMobiusLogMoment_two_critical.sub
    (tendsto_squarefreeMobiusLogMoment_one_critical.pow 2)
  have hvalue : (2 : ℝ) - 1 ^ 2 = 1 := by norm_num
  rw [hvalue] at h
  simpa [squarefreeMobiusCriticalClockVariance] using h

/-- Projective Fisher energy of the squarefree critical source. -/
def squarefreeMobiusCriticalProjectiveFisherEnergy (sigma : ℝ) : ℝ :=
  4 * squarefreeMobiusCriticalClockVariance sigma

/-- The projective Fisher tangent carries the same four-unit critical budget. -/
theorem tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy :
    Tendsto squarefreeMobiusCriticalProjectiveFisherEnergy
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  simpa [squarefreeMobiusCriticalProjectiveFisherEnergy] using
    tendsto_const_nhds.mul tendsto_squarefreeMobiusCriticalClockVariance

/-- Fisher and incidence curvature energies collide at the critical clock law. -/
theorem tendsto_squarefreeMobiusCriticalFisher_sub_incidenceEnergy :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusCriticalProjectiveFisherEnergy sigma -
        squarefreeMobiusCriticalRelativeClockEnergy sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  simpa using tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy.sub
    tendsto_squarefreeMobiusCriticalRelativeClockEnergy

/-- CDF of the rescaled squarefree logarithmic clock. -/
def squarefreeMobiusCriticalClockCDF (sigma y : ℝ) : ℝ :=
  ProbabilityTheory.cdf
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) y

/-- Pointwise convergence of the squarefree critical-clock CDF to the unit exponential CDF. -/
theorem tendsto_squarefreeMobiusCriticalClockCDF (y : ℝ) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusCriticalClockCDF sigma y)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if 0 ≤ y then 1 - Real.exp (-y) else 0)) := by
  have hnull : mobiusCriticalExponentialProbabilityMeasure (frontier (Iic y)) = 0 := by
    rw [frontier_Iic]
    ext
    simp [mobiusCriticalExponentialProbabilityMeasure,
      ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  have hmeasure :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      tendsto_squarefreeMobiusCriticalClockProbabilityMeasure hnull
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp hmeasure
  have hreal' : Tendsto (fun sigma : ℝ =>
      ProbabilityTheory.cdf
        (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) y)
      (nhdsWithin 1 (Ioi 1))
      (nhds (ProbabilityTheory.cdf
        (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) y)) := by
    simpa [Function.comp_apply, ProbabilityTheory.cdf_eq_real, Measure.real,
      ProbabilityMeasure.coe_mk] using hreal
  have hlimit := ProbabilityTheory.cdf_expMeasure_eq (r := (1 : ℝ))
    (by norm_num) y
  simpa [squarefreeMobiusCriticalClockCDF,
    mobiusCriticalExponentialProbabilityMeasure, hlimit] using hreal'

/-- Scaled finite-window incidence energy in critical clock coordinates. -/
def squarefreeMobiusCriticalIncidenceWindowEnergy (sigma u : ℝ) : ℝ :=
  8 * ∫ y : ℝ in Ioc 0 u,
    squarefreeMobiusCriticalClockCDF sigma y *
      (1 - squarefreeMobiusCriticalClockCDF sigma y)

private theorem integral_Ioc_exponentialCDF_mul_one_sub
    {u : ℝ} (hu : 0 ≤ u) :
    (∫ y : ℝ in Ioc 0 u,
      (1 - Real.exp (-y)) * Real.exp (-y)) =
      (1 / 2 : ℝ) * (1 - Real.exp (-u)) ^ 2 := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * (1 - Real.exp (-y)) ^ 2)
      ((1 - Real.exp (-x)) * Real.exp (-x)) x := by
    intro x
    have hq := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).neg.exp)
    have hp := (hq.pow 2).const_mul (1 / 2 : ℝ)
    convert hp using 1
    simp only [Pi.sub_apply, Pi.neg_apply, Function.id_def]
    ring
  have hint : IntervalIntegrable
      (fun y : ℝ => (1 - Real.exp (-y)) * Real.exp (-y)) volume 0 u :=
    (by fun_prop : Continuous (fun y : ℝ =>
      (1 - Real.exp (-y)) * Real.exp (-y))).intervalIntegrable 0 u
  rw [← intervalIntegral.integral_of_le hu]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x) hint]
  norm_num

/-- The finite critical incidence window has profile `4(1-exp(-u))^2`. -/
theorem tendsto_squarefreeMobiusCriticalIncidenceWindowEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      squarefreeMobiusCriticalIncidenceWindowEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (4 * (1 - Real.exp (-u)) ^ 2)) := by
  let F : ℝ → ℝ → ℝ := fun sigma y =>
    squarefreeMobiusCriticalClockCDF sigma y *
      (1 - squarefreeMobiusCriticalClockCDF sigma y)
  let f : ℝ → ℝ := fun y =>
    (1 - Real.exp (-y)) * Real.exp (-y)
  have hmeas : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      AEStronglyMeasurable (F sigma) (volume.restrict (Ioc 0 u)) := by
    filter_upwards [] with sigma
    have hcdf : Measurable (squarefreeMobiusCriticalClockCDF sigma) := by
      exact (ProbabilityTheory.monotone_cdf
        (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ)).measurable
    exact (hcdf.mul (measurable_const.sub hcdf)).aestronglyMeasurable
  have hbound : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      ∀ᵐ y ∂(volume.restrict (Ioc 0 u)), ‖F sigma y‖ ≤ (1 : ℝ) := by
    filter_upwards [] with sigma
    filter_upwards [] with y
    have h0 := ProbabilityTheory.cdf_nonneg
      (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) y
    have h1 := ProbabilityTheory.cdf_le_one
      (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) y
    dsimp [F]
    unfold squarefreeMobiusCriticalClockCDF
    rw [abs_of_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1))]
    nlinarith
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioc 0 u)) := by
    rw [← IntegrableOn]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hpointwise : ∀ᵐ y ∂(volume.restrict (Ioc 0 u)),
      Tendsto (fun sigma : ℝ => F sigma y)
        (nhdsWithin 1 (Ioi 1)) (nhds (f y)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    have hy0 : 0 ≤ y := hy.1.le
    have hcdf := tendsto_squarefreeMobiusCriticalClockCDF y
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
    have hprod := hcdf.mul (hone.sub hcdf)
    simpa [F, f, if_pos hy0] using hprod
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 u)) (F := F) (f := f)
    (fun _ : ℝ => (1 : ℝ)) hmeas hbound hconst hpointwise
  have hscaled : Tendsto (fun sigma : ℝ =>
      8 * ∫ y : ℝ in Ioc 0 u, F sigma y)
      (nhdsWithin 1 (Ioi 1))
      (nhds (8 * ∫ y : ℝ in Ioc 0 u, f y)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (8 : ℝ))
      (nhdsWithin 1 (Ioi 1)) (nhds 8)).mul hdct
  rw [show (∫ y : ℝ, f y ∂(volume.restrict (Ioc 0 u))) =
      (1 / 2 : ℝ) * (1 - Real.exp (-u)) ^ 2 by
    simpa [f] using integral_Ioc_exponentialCDF_mul_one_sub hu] at hscaled
  have hvalue : 8 * ((1 / 2 : ℝ) * (1 - Real.exp (-u)) ^ 2) =
      4 * (1 - Real.exp (-u)) ^ 2 := by ring
  rw [hvalue] at hscaled
  simpa [squarefreeMobiusCriticalIncidenceWindowEnergy, F] using hscaled

end RHTower
