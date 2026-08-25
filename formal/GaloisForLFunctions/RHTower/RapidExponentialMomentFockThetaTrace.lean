import GaloisForLFunctions.RHTower.PolynomialMomentFockThetaTrace
import GaloisForLFunctions.RHTower.RapidExponentialMomentFockKernelBound

/-!
# Completed theta trace on the rapid exponential moment Fock carrier

For `0 < a < 1/2`, theta's double-exponential decay dominates the point-evaluation growth of the
literal rapid moment carrier.  This file constructs the resulting entire trace, proves continuous
dependence on the Hilbert vector on every fixed strip, and identifies the distinguished constant
vector with the completed critical-line zeta trace.
-/

open Filter Topology Set MeasureTheory Complex Real
open scoped Real

namespace RHTower

noncomputable section

theorem tendsto_rapidExponentialFockPotential_shift_div_exp_zero
    {a : ℝ} (_ha : 0 < a) (haHalf : a < 1 / 2) :
    Tendsto (fun u : ℝ =>
      rapidExponentialFockPotential a (u + 2) / Real.exp u)
      atTop (nhds 0) := by
  have hgap : 0 < 1 - 2 * a := by linarith
  have hdecay :=
    GaloisForLFunctions.HTGeometry.tendsto_exp_neg_mul_atTop_nhds_zero hgap
  have hscaled : Tendsto (fun u : ℝ =>
      Real.exp (4 * a) * Real.exp (-((1 - 2 * a) * u))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hdecay : Tendsto (fun u : ℝ =>
        Real.exp (4 * a) * Real.exp (-((1 - 2 * a) * u))) atTop
          (nhds (Real.exp (4 * a) * 0)))
  apply hscaled.congr'
  filter_upwards with u
  unfold rapidExponentialFockPotential
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem tendsto_id_div_exp_zero :
    Tendsto (fun u : ℝ => u / Real.exp u) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.rpow_one, div_eq_mul_inv, ← Real.exp_neg]
  ring

theorem eventually_rapidExponentialFockTheta_exponent_le
    {a : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (A : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      2 * rapidExponentialFockPotential a (u + 2) + (A + 9 / 4) * u ≤
        (Real.pi / 2) * Real.exp u := by
  have hratio : Tendsto (fun u : ℝ =>
      (2 * rapidExponentialFockPotential a (u + 2) + (A + 9 / 4) * u) /
        Real.exp u) atTop (nhds 0) := by
    have hp :=
      (tendsto_rapidExponentialFockPotential_shift_div_exp_zero ha haHalf).const_mul 2
    have hl := tendsto_id_div_exp_zero.const_mul (A + 9 / 4)
    have hs := hp.add hl
    convert hs using 1
    · funext u
      field_simp [Real.exp_ne_zero u]
    · ring
  have hevent := hratio.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 2))
  filter_upwards [hevent] with u hu
  rw [div_lt_iff₀ (Real.exp_pos u)] at hu
  exact hu.le

theorem rapidExponentialMomentFockEvaluationMajorant_real_le
    {a u : ℝ} (hu : 0 ≤ u) :
    rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) ≤
      2 * Real.exp (2 * rapidExponentialFockPotential a (u + 2)) * (u + 1) ^ 2 := by
  let φ : ℝ := rapidExponentialFockPotential a (u + 2)
  have hφ : 0 ≤ φ := by
    dsimp [φ, rapidExponentialFockPotential]
    exact (Real.exp_pos _).le
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hcoeff :
      (2 * Real.pi * Real.exp (-2 * φ))⁻¹ ≤ Real.exp (2 * φ) := by
    rw [mul_inv_rev, ← Real.exp_neg]
    have hinv : (2 * Real.pi)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).2 hpi
    have harg : -(-2 * φ) = 2 * φ := by ring
    rw [harg]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hinv (Real.exp_pos (2 * φ)).le)
  have hsq : 1 ≤ (u + 1) ^ 2 := by nlinarith
  have hexp : 1 ≤ Real.exp (2 * φ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hone : 1 ≤ Real.exp (2 * φ) * (u + 1) ^ 2 := by nlinarith
  unfold rapidExponentialMomentFockEvaluationMajorant
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hterm :
      (2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (u + 2)))⁻¹ *
          (u + 1) ^ 2 ≤
        Real.exp (2 * rapidExponentialFockPotential a (u + 2)) * (u + 1) ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by simpa [φ] using hcoeff) (sq_nonneg _)
  nlinarith

/-- Scalar theta envelope on the positive ray. -/
def rapidExponentialMomentFockThetaWeightMajorant (a A u : ℝ) : ℝ :=
  rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) *
    ‖xiThetaLogSource u‖ * Real.exp (A * u)

theorem eventually_rapidExponentialMomentFockThetaWeightMajorant_le
    {a : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (A : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      rapidExponentialMomentFockThetaWeightMajorant a A u ≤
        6 * Real.exp (-(Real.pi / 2 * u)) := by
  have hevent := eventually_rapidExponentialFockTheta_exponent_le ha haHalf A
  filter_upwards [hevent, eventually_ge_atTop (0 : ℝ)] with u hexponent hu
  have hmajorant := rapidExponentialMomentFockEvaluationMajorant_real_le (a := a) hu
  have htheta := norm_xiThetaLogSource_le_doubleExp u
  rw [abs_of_nonneg hu] at htheta
  have hsq := sq_one_add_le_exp_two_mul hu
  have hmajorant' :
      rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) ≤
        2 * Real.exp (2 * rapidExponentialFockPotential a (u + 2)) * Real.exp (2 * u) :=
    hmajorant.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hfirst :
      rapidExponentialMomentFockThetaWeightMajorant a A u ≤
        (2 * Real.exp (2 * rapidExponentialFockPotential a (u + 2)) * Real.exp (2 * u)) *
          (3 * Real.exp (u / 4) * Real.exp (-Real.pi * Real.exp u)) *
            Real.exp (A * u) := by
    unfold rapidExponentialMomentFockThetaWeightMajorant
    gcongr
  have hexpIdentity :
      Real.exp (2 * rapidExponentialFockPotential a (u + 2)) *
          Real.exp (2 * u) * Real.exp (u / 4) *
            Real.exp (-Real.pi * Real.exp u) * Real.exp (A * u) =
        Real.exp
          (2 * rapidExponentialFockPotential a (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hcombined :
      (2 * Real.exp (2 * rapidExponentialFockPotential a (u + 2)) * Real.exp (2 * u)) *
          (3 * Real.exp (u / 4) * Real.exp (-Real.pi * Real.exp u)) *
            Real.exp (A * u) =
        6 * Real.exp
          (2 * rapidExponentialFockPotential a (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := by
    rw [← hexpIdentity]
    ring
  rw [hcombined] at hfirst
  have hexponent' :
      2 * rapidExponentialFockPotential a (u + 2) +
          (A + 9 / 4) * u - Real.pi * Real.exp u ≤
        -(Real.pi / 2) * Real.exp u := by
    linarith
  have hu_exp : u ≤ Real.exp u := by
    linarith [Real.add_one_le_exp u]
  calc
    rapidExponentialMomentFockThetaWeightMajorant a A u ≤
        6 * Real.exp
          (2 * rapidExponentialFockPotential a (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := hfirst
    _ ≤ 6 * Real.exp (-(Real.pi / 2) * Real.exp u) := by gcongr
    _ ≤ 6 * Real.exp (-(Real.pi / 2 * u)) := by
      have hneg : -(Real.pi / 2) * Real.exp u ≤ -(Real.pi / 2) * u :=
        mul_le_mul_of_nonpos_left hu_exp (by nlinarith [Real.pi_pos])
      have harg : -(Real.pi / 2) * u = -(Real.pi / 2 * u) := by ring
      rw [← harg]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by norm_num)

theorem continuous_rapidExponentialMomentFockEvaluationMajorant_real (a : ℝ) :
    Continuous (fun u : ℝ =>
      rapidExponentialMomentFockEvaluationMajorant a (u : ℂ)) := by
  unfold rapidExponentialMomentFockEvaluationMajorant
  have hnorm : Continuous (fun u : ℝ => ‖(u : ℂ)‖) := by fun_prop
  have hpotential : Continuous (fun u : ℝ =>
      rapidExponentialFockPotential a (‖(u : ℂ)‖ + 2)) :=
    (continuous_rapidExponentialFockPotential a).comp
      (hnorm.add continuous_const)
  have hden : Continuous (fun u : ℝ =>
      2 * Real.pi * Real.exp
        (-2 * rapidExponentialFockPotential a (‖(u : ℂ)‖ + 2))) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hpotential))
  have hden0 : ∀ u : ℝ,
      2 * Real.pi * Real.exp
        (-2 * rapidExponentialFockPotential a (‖(u : ℂ)‖ + 2)) ≠ 0 := by
    intro u
    positivity
  exact continuous_const.add
    ((hden.inv₀ hden0).mul ((hnorm.add continuous_const).pow 2))

/-- Seam-free positive-half representative of the rapid theta envelope. -/
def rapidExponentialMomentFockThetaPositiveWeightMajorant (a A u : ℝ) : ℝ :=
  rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) *
    ‖xiThetaPositiveFormula u‖ * Real.exp (A * u)

theorem continuous_rapidExponentialMomentFockThetaPositiveWeightMajorant (a A : ℝ) :
    Continuous (rapidExponentialMomentFockThetaPositiveWeightMajorant a A) := by
  unfold rapidExponentialMomentFockThetaPositiveWeightMajorant
  exact ((continuous_rapidExponentialMomentFockEvaluationMajorant_real a).mul
    continuous_xiThetaPositiveFormula.norm).mul (by fun_prop)

theorem rapidExponentialMomentFockThetaPositiveWeightMajorant_nonneg
    (a A u : ℝ) :
    0 ≤ rapidExponentialMomentFockThetaPositiveWeightMajorant a A u := by
  unfold rapidExponentialMomentFockThetaPositiveWeightMajorant
  unfold rapidExponentialMomentFockEvaluationMajorant
  positivity

theorem rapidExponentialMomentFockThetaWeightMajorant_nonneg (a A u : ℝ) :
    0 ≤ rapidExponentialMomentFockThetaWeightMajorant a A u := by
  unfold rapidExponentialMomentFockThetaWeightMajorant
  unfold rapidExponentialMomentFockEvaluationMajorant
  positivity

theorem rapidExponentialMomentFockThetaPositiveWeightMajorant_eq
    {a A u : ℝ} (hu : 0 < u) :
    rapidExponentialMomentFockThetaPositiveWeightMajorant a A u =
      rapidExponentialMomentFockThetaWeightMajorant a A u := by
  unfold rapidExponentialMomentFockThetaPositiveWeightMajorant
  unfold rapidExponentialMomentFockThetaWeightMajorant
  rw [xiThetaLogSource_eq_positiveFormula hu]

theorem integrableOn_rapidExponentialMomentFockThetaWeightMajorant_Ioi
    {a : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (A : ℝ) :
    IntegrableOn (rapidExponentialMomentFockThetaWeightMajorant a A) (Ioi 0) := by
  have hevent := eventually_rapidExponentialMomentFockThetaWeightMajorant_le ha haHalf A
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨T, hT⟩
  let B : ℝ := max T 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have htailBase :
      IntegrableOn (fun u : ℝ => 6 * Real.exp (-(Real.pi / 2 * u))) (Ioi B) :=
    (GaloisForLFunctions.HTGeometry.integrableOn_exp_neg_mul_Ioi
      (b := Real.pi / 2) (by positivity) B).const_mul 6
  have htail :
      IntegrableOn (rapidExponentialMomentFockThetaPositiveWeightMajorant a A) (Ioi B) := by
    apply htailBase.mono'
    · exact
        (continuous_rapidExponentialMomentFockThetaPositiveWeightMajorant a A).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hu0 : 0 < u := lt_of_le_of_lt hB0 hu
      have hbound := hT u ((le_max_left T 0).trans hu.le)
      rw [rapidExponentialMomentFockThetaPositiveWeightMajorant_eq hu0]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (rapidExponentialMomentFockThetaWeightMajorant_nonneg a A u)]
      exact hbound
  have hcompact :
      IntegrableOn (rapidExponentialMomentFockThetaPositiveWeightMajorant a A) (Ioc 0 B) :=
    ((continuous_rapidExponentialMomentFockThetaPositiveWeightMajorant a A).integrableOn_Icc).mono_set
      (by intro u hu; exact ⟨hu.1.le, hu.2⟩)
  have hpositive :
      IntegrableOn (rapidExponentialMomentFockThetaPositiveWeightMajorant a A) (Ioi 0) := by
    have hset : Ioi (0 : ℝ) = Ioc 0 B ∪ Ioi B := by
      ext u
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hu
        by_cases hub : u ≤ B
        · exact Or.inl ⟨hu, hub⟩
        · exact Or.inr (lt_of_not_ge hub)
      · rintro (hu | hu)
        · exact hu.1
        · exact lt_of_le_of_lt hB0 hu
    rw [hset]
    exact hcompact.union htail
  refine hpositive.congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact rapidExponentialMomentFockThetaPositiveWeightMajorant_eq hu

/-- Two-sided scalar envelope for every exponential Fourier weight. -/
def rapidExponentialMomentFockThetaAbsWeightMajorant (a A u : ℝ) : ℝ :=
  rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) *
    ‖xiThetaLogSource u‖ * Real.exp (A * |u|)

theorem rapidExponentialMomentFockThetaAbsWeightMajorant_neg (a A u : ℝ) :
    rapidExponentialMomentFockThetaAbsWeightMajorant a A (-u) =
      rapidExponentialMomentFockThetaAbsWeightMajorant a A u := by
  unfold rapidExponentialMomentFockThetaAbsWeightMajorant
  have hmajorant :
      rapidExponentialMomentFockEvaluationMajorant a ((-u : ℝ) : ℂ) =
        rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) := by
    unfold rapidExponentialMomentFockEvaluationMajorant
    rw [show ((-u : ℝ) : ℂ) = -(u : ℂ) by norm_num, norm_neg]
  rw [hmajorant, xiThetaLogSource_neg]
  simp only [abs_neg]

theorem rapidExponentialMomentFockThetaAbsWeightMajorant_nonneg (a A u : ℝ) :
    0 ≤ rapidExponentialMomentFockThetaAbsWeightMajorant a A u := by
  unfold rapidExponentialMomentFockThetaAbsWeightMajorant
  unfold rapidExponentialMomentFockEvaluationMajorant
  positivity

theorem integrable_rapidExponentialMomentFockThetaAbsWeightMajorant
    {a : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (A : ℝ) :
    Integrable (rapidExponentialMomentFockThetaAbsWeightMajorant a A) := by
  have hposWeight :=
    integrableOn_rapidExponentialMomentFockThetaWeightMajorant_Ioi ha haHalf A
  have hpos :
      IntegrableOn (rapidExponentialMomentFockThetaAbsWeightMajorant a A) (Ioi 0) := by
    refine hposWeight.congr_fun ?_ measurableSet_Ioi
    intro u hu
    unfold rapidExponentialMomentFockThetaAbsWeightMajorant
    unfold rapidExponentialMomentFockThetaWeightMajorant
    rw [abs_of_pos hu]
  have hneg :
      IntegrableOn (rapidExponentialMomentFockThetaAbsWeightMajorant a A) (Iio 0) := by
    simpa using GaloisForLFunctions.RHTower.connes_integrableOn_Iio_neg_of_even
      (rapidExponentialMomentFockThetaAbsWeightMajorant_neg a A) hpos
  have hzero :
      IntegrableOn (rapidExponentialMomentFockThetaAbsWeightMajorant a A) ({0} : Set ℝ) :=
    integrableOn_singleton
      (f := rapidExponentialMomentFockThetaAbsWeightMajorant a A)
      (hfx := by finiteness) (hx := by simp)
  have hnonneg :
      IntegrableOn (rapidExponentialMomentFockThetaAbsWeightMajorant a A) (Ici 0) := by
    have h := hzero.union hpos
    have hset : ({0} : Set ℝ) ∪ Ioi 0 = Ici 0 := by ext u; simp
    simpa only [hset] using h
  have hall := hneg.union hnonneg
  rw [Iio_union_Ici] at hall
  simpa only [IntegrableOn, Measure.restrict_univ] using hall

/-- Literal theta source obtained by evaluating a rapid moment-Fock vector on the real axis. -/
def rapidExponentialMomentFockThetaSource
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (u : ℝ) : ℂ :=
  rapidExponentialMomentFockFunction a ha f (u : ℂ) * xiThetaLogSource u

theorem aestronglyMeasurable_rapidExponentialMomentFockThetaSource
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    AEStronglyMeasurable (rapidExponentialMomentFockThetaSource a ha f) volume := by
  have hreal : Continuous (fun u : ℝ => (u : ℂ)) := by fun_prop
  have hcarrier : Continuous (fun u : ℝ =>
      rapidExponentialMomentFockFunction a ha f (u : ℂ)) :=
    (differentiable_rapidExponentialMomentFockFunction a ha f).continuous.comp hreal
  unfold rapidExponentialMomentFockThetaSource
  exact hcarrier.aestronglyMeasurable.mul
    xiThetaLogSource_integrable.aestronglyMeasurable

theorem allExpWeightIntegrable_rapidExponentialMomentFockThetaSource
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) :
    AllExpWeightIntegrable (rapidExponentialMomentFockThetaSource a ha f) := by
  intro A
  have hmajorant :=
    (integrable_rapidExponentialMomentFockThetaAbsWeightMajorant ha haHalf A).const_mul ‖f‖
  apply hmajorant.mono'
  · exact (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha f).norm.mul
      (by fun_prop)
  · filter_upwards with u
    have hcarrier := norm_rapidExponentialMomentFockFunction_le_majorant ha f (u : ℂ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold rapidExponentialMomentFockThetaSource
    rw [norm_mul]
    calc
      ‖rapidExponentialMomentFockFunction a ha f (u : ℂ)‖ *
            ‖xiThetaLogSource u‖ * Real.exp (A * |u|) ≤
          (rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) * ‖f‖) *
            ‖xiThetaLogSource u‖ * Real.exp (A * |u|) := by
        gcongr
      _ = ‖f‖ * rapidExponentialMomentFockThetaAbsWeightMajorant a A u := by
        unfold rapidExponentialMomentFockThetaAbsWeightMajorant
        ring

/-- Entire theta trace of a rapid exponential moment-Fock vector. -/
def rapidExponentialMomentFockThetaTrace
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (z : ℂ) : ℂ :=
  expFourier (rapidExponentialMomentFockThetaSource a ha f) (2 * Real.pi * z)

theorem differentiable_rapidExponentialMomentFockThetaTrace
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) :
    Differentiable ℂ (rapidExponentialMomentFockThetaTrace a ha f) := by
  have houter := differentiable_expFourier_of_allExpWeightIntegrable
    (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha f)
    (allExpWeightIntegrable_rapidExponentialMomentFockThetaSource a ha haHalf f)
  unfold rapidExponentialMomentFockThetaTrace
  fun_prop

theorem rapidExponentialMomentFockThetaSource_one
    (a : ℝ) (ha : 0 < a) (u : ℝ) :
    rapidExponentialMomentFockThetaSource a ha
        (rapidExponentialMomentFockOne a ha) u = xiThetaLogSource u := by
  unfold rapidExponentialMomentFockThetaSource
  rw [rapidExponentialMomentFockFunction_one]
  simp

theorem rapidExponentialMomentFockThetaTrace_one
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    rapidExponentialMomentFockThetaTrace a ha
        (rapidExponentialMomentFockOne a ha) z =
      expFourier xiThetaLogSource (2 * Real.pi * z) := by
  unfold rapidExponentialMomentFockThetaTrace
  congr 2
  funext u
  exact rapidExponentialMomentFockThetaSource_one a ha u

theorem rapidExponentialMomentFockThetaTrace_one_real_eq_fourier
    (a : ℝ) (ha : 0 < a) (w : ℝ) :
    rapidExponentialMomentFockThetaTrace a ha
        (rapidExponentialMomentFockOne a ha) (w : ℂ) =
      FourierTransform.fourier xiThetaLogSource w := by
  rw [rapidExponentialMomentFockThetaTrace_one,
    fourier_eq_expFourier_two_pi]
  congr 2
  push_cast
  ring

theorem completedRiemannZeta₀_critical_eq_rapidExponentialMomentFockThetaTrace_one
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) =
      rapidExponentialMomentFockThetaTrace a ha
        (rapidExponentialMomentFockOne a ha)
        ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  rw [completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource,
    rapidExponentialMomentFockThetaTrace_one_real_eq_fourier]

/-- Weighted-L¹ bound controlling rapid theta traces in a fixed imaginary strip. -/
def rapidExponentialMomentFockThetaTraceWeightBound (a A : ℝ) : ℝ :=
  ∫ u : ℝ, rapidExponentialMomentFockThetaAbsWeightMajorant a A u

theorem rapidExponentialMomentFockThetaTraceWeightBound_nonneg (a A : ℝ) :
    0 ≤ rapidExponentialMomentFockThetaTraceWeightBound a A := by
  unfold rapidExponentialMomentFockThetaTraceWeightBound
  exact integral_nonneg
    (fun u => rapidExponentialMomentFockThetaAbsWeightMajorant_nonneg a A u)

theorem norm_rapidExponentialMomentFockThetaTrace_le_weightBound
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) (z : ℂ) {A : ℝ}
    (hA : |(2 * (Real.pi : ℂ) * z).im| ≤ A) :
    ‖rapidExponentialMomentFockThetaTrace a ha f z‖ ≤
      rapidExponentialMomentFockThetaTraceWeightBound a A * ‖f‖ := by
  let w : ℂ := 2 * (Real.pi : ℂ) * z
  have hkernel : Integrable (fun u : ℝ =>
      rapidExponentialMomentFockThetaSource a ha f u * Complex.exp (-(I * w * u))) :=
    integrable_expFourier_kernel'
      (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha f)
      ((allExpWeightIntegrable_rapidExponentialMomentFockThetaSource a ha haHalf f).expWeightIntegrable
        (|w.im| + 1)) (by linarith)
  have hright : Integrable (fun u : ℝ =>
      ‖f‖ * rapidExponentialMomentFockThetaAbsWeightMajorant a A u) :=
    (integrable_rapidExponentialMomentFockThetaAbsWeightMajorant ha haHalf A).const_mul ‖f‖
  unfold rapidExponentialMomentFockThetaTrace expFourier
  change ‖∫ u : ℝ,
      rapidExponentialMomentFockThetaSource a ha f u * Complex.exp (-(I * w * u))‖ ≤ _
  calc
    ‖∫ u : ℝ,
        rapidExponentialMomentFockThetaSource a ha f u * Complex.exp (-(I * w * u))‖ ≤
        ∫ u : ℝ, ‖rapidExponentialMomentFockThetaSource a ha f u *
          Complex.exp (-(I * w * u))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ,
        ‖f‖ * rapidExponentialMomentFockThetaAbsWeightMajorant a A u := by
      apply integral_mono hkernel.norm hright
      intro u
      have hcarrier := norm_rapidExponentialMomentFockFunction_le_majorant ha f (u : ℂ)
      have him : w.im * u ≤ A * |u| := by
        calc
          w.im * u ≤ |w.im * u| := le_abs_self _
          _ = |w.im| * |u| := abs_mul _ _
          _ ≤ A * |u| := mul_le_mul_of_nonneg_right (by simpa [w] using hA) (abs_nonneg u)
      change ‖rapidExponentialMomentFockThetaSource a ha f u *
        Complex.exp (-(I * w * u))‖ ≤ _
      rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
      unfold rapidExponentialMomentFockThetaSource
      rw [norm_mul]
      have hmajorant0 :
          0 ≤ rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) := by
        unfold rapidExponentialMomentFockEvaluationMajorant
        positivity
      calc
        (‖rapidExponentialMomentFockFunction a ha f (u : ℂ)‖ * ‖xiThetaLogSource u‖) *
              Real.exp (w.im * u) ≤
            ((rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) * ‖f‖) *
              ‖xiThetaLogSource u‖) * Real.exp (w.im * u) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcarrier (norm_nonneg _)) (Real.exp_nonneg _)
        _ ≤ ((rapidExponentialMomentFockEvaluationMajorant a (u : ℂ) * ‖f‖) *
              ‖xiThetaLogSource u‖) * Real.exp (A * |u|) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him)
            (mul_nonneg (mul_nonneg hmajorant0 (norm_nonneg f)) (norm_nonneg _))
        _ = ‖f‖ * rapidExponentialMomentFockThetaAbsWeightMajorant a A u := by
          unfold rapidExponentialMomentFockThetaAbsWeightMajorant
          ring
    _ = rapidExponentialMomentFockThetaTraceWeightBound a A * ‖f‖ := by
      rw [integral_const_mul]
      unfold rapidExponentialMomentFockThetaTraceWeightBound
      ring

theorem rapidExponentialMomentFockThetaSource_add
    (a : ℝ) (ha : 0 < a) (f g : MomentFock) (u : ℝ) :
    rapidExponentialMomentFockThetaSource a ha (f + g) u =
      rapidExponentialMomentFockThetaSource a ha f u +
        rapidExponentialMomentFockThetaSource a ha g u := by
  simp only [rapidExponentialMomentFockThetaSource,
    rapidExponentialMomentFockFunction_eq_evaluation, map_add]
  ring

theorem rapidExponentialMomentFockThetaSource_smul
    (a : ℝ) (ha : 0 < a) (c : ℂ) (f : MomentFock) (u : ℝ) :
    rapidExponentialMomentFockThetaSource a ha (c • f) u =
      c • rapidExponentialMomentFockThetaSource a ha f u := by
  simp only [rapidExponentialMomentFockThetaSource,
    rapidExponentialMomentFockFunction_eq_evaluation, map_smul, smul_eq_mul]
  ring

theorem rapidExponentialMomentFockThetaTrace_add
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2)
    (f g : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockThetaTrace a ha (f + g) z =
      rapidExponentialMomentFockThetaTrace a ha f z +
        rapidExponentialMomentFockThetaTrace a ha g z := by
  unfold rapidExponentialMomentFockThetaTrace expFourier
  have hf := integrable_expFourier_kernel'
    (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha f)
    ((allExpWeightIntegrable_rapidExponentialMomentFockThetaSource a ha haHalf f).expWeightIntegrable
      (|(2 * (Real.pi : ℂ) * z).im| + 1)) (by linarith)
  have hg := integrable_expFourier_kernel'
    (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha g)
    ((allExpWeightIntegrable_rapidExponentialMomentFockThetaSource a ha haHalf g).expWeightIntegrable
      (|(2 * (Real.pi : ℂ) * z).im| + 1)) (by linarith)
  calc
    (∫ u : ℝ, rapidExponentialMomentFockThetaSource a ha (f + g) u *
        Complex.exp (-(I * (2 * Real.pi * z) * u))) =
      ∫ u : ℝ,
        rapidExponentialMomentFockThetaSource a ha f u *
            Complex.exp (-(I * (2 * Real.pi * z) * u)) +
          rapidExponentialMomentFockThetaSource a ha g u *
            Complex.exp (-(I * (2 * Real.pi * z) * u)) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [rapidExponentialMomentFockThetaSource_add]
        ring
    _ = (∫ u : ℝ, rapidExponentialMomentFockThetaSource a ha f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u))) +
        ∫ u : ℝ, rapidExponentialMomentFockThetaSource a ha g u *
          Complex.exp (-(I * (2 * Real.pi * z) * u)) := integral_add hf hg

theorem rapidExponentialMomentFockThetaTrace_smul
    (a : ℝ) (ha : 0 < a) (c : ℂ) (f : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockThetaTrace a ha (c • f) z =
      c • rapidExponentialMomentFockThetaTrace a ha f z := by
  unfold rapidExponentialMomentFockThetaTrace expFourier
  calc
    (∫ u : ℝ, rapidExponentialMomentFockThetaSource a ha (c • f) u *
        Complex.exp (-(I * (2 * Real.pi * z) * u))) =
      ∫ u : ℝ, c •
        (rapidExponentialMomentFockThetaSource a ha f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u))) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [rapidExponentialMomentFockThetaSource_smul]
        simp only [smul_eq_mul]
        ring
    _ = c • ∫ u : ℝ, rapidExponentialMomentFockThetaSource a ha f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u)) := integral_smul c _

/-- Trace evaluation at a fixed complex point as a bounded functional on the rapid carrier. -/
def rapidExponentialMomentFockThetaTraceLinearMap
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (z : ℂ) :
    MomentFock →ₗ[ℂ] ℂ where
  toFun f := rapidExponentialMomentFockThetaTrace a ha f z
  map_add' f g := rapidExponentialMomentFockThetaTrace_add a ha haHalf f g z
  map_smul' c f := rapidExponentialMomentFockThetaTrace_smul a ha c f z

def rapidExponentialMomentFockThetaTraceFunctional
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (z : ℂ) :
    MomentFock →L[ℂ] ℂ :=
  (rapidExponentialMomentFockThetaTraceLinearMap a ha haHalf z).mkContinuous
    (rapidExponentialMomentFockThetaTraceWeightBound a
      |(2 * (Real.pi : ℂ) * z).im|)
    (fun f => norm_rapidExponentialMomentFockThetaTrace_le_weightBound
      a ha haHalf f z le_rfl)

theorem rapidExponentialMomentFockThetaTraceFunctional_apply
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (z : ℂ) (f : MomentFock) :
    rapidExponentialMomentFockThetaTraceFunctional a ha haHalf z f =
      rapidExponentialMomentFockThetaTrace a ha f z := rfl

theorem norm_rapidExponentialMomentFockThetaTrace_le_verticalStrip
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) {R : ℝ}
    {z : ℂ} (hz : |z.im| ≤ R) :
    ‖rapidExponentialMomentFockThetaTrace a ha f z‖ ≤
      rapidExponentialMomentFockThetaTraceWeightBound a (2 * Real.pi * R) * ‖f‖ := by
  apply norm_rapidExponentialMomentFockThetaTrace_le_weightBound a ha haHalf f z
  have him : (2 * (Real.pi : ℂ) * z).im = 2 * Real.pi * z.im := by
    simp [Complex.mul_im, Complex.mul_re]
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * Real.pi)

/-! ## Exact trace moments -/

/-- Source of the `n`th rapid theta-trace derivative. -/
def rapidExponentialMomentFockThetaMomentSource
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) (u : ℝ) : ℂ :=
  (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n *
    rapidExponentialMomentFockThetaSource a ha f u

theorem aestronglyMeasurable_rapidExponentialMomentFockThetaMomentSource
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    AEStronglyMeasurable (rapidExponentialMomentFockThetaMomentSource a ha f n) volume := by
  unfold rapidExponentialMomentFockThetaMomentSource
  exact (by fun_prop : Continuous (fun u : ℝ =>
    (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n)).aestronglyMeasurable.mul
      (aestronglyMeasurable_rapidExponentialMomentFockThetaSource a ha f)

theorem norm_rapidExponentialMomentFockThetaMomentPhase_le (n : ℕ) (u : ℝ) :
    ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ ≤
      (2 * Real.pi) ^ n * (n.factorial : ℝ) * Real.exp |u| := by
  have hpow := pow_abs_le_factorial_mul_exp (a := 2) (by norm_num) n u
  have hnormTwoPi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_pow, norm_neg, norm_mul, norm_mul, hnormTwoPi, norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num at hpow
  rw [mul_pow]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) n))

theorem allExpWeightIntegrable_rapidExponentialMomentFockThetaMomentSource
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) (n : ℕ) :
    AllExpWeightIntegrable (rapidExponentialMomentFockThetaMomentSource a ha f n) := by
  intro A
  let C : ℝ := (2 * Real.pi) ^ n * (n.factorial : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase :=
    (allExpWeightIntegrable_rapidExponentialMomentFockThetaSource a ha haHalf f (A + 1)).const_mul C
  apply hbase.mono'
  · exact (aestronglyMeasurable_rapidExponentialMomentFockThetaMomentSource a ha f n).norm.mul
      (by fun_prop)
  · filter_upwards with u
    have hphase :
        ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ ≤ C * Real.exp |u| := by
      simpa only [C] using norm_rapidExponentialMomentFockThetaMomentPhase_le n u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold rapidExponentialMomentFockThetaMomentSource
    rw [norm_mul]
    calc
      ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ *
            ‖rapidExponentialMomentFockThetaSource a ha f u‖ * Real.exp (A * |u|) ≤
          (C * Real.exp |u|) *
            ‖rapidExponentialMomentFockThetaSource a ha f u‖ * Real.exp (A * |u|) := by
        gcongr
      _ = C * (‖rapidExponentialMomentFockThetaSource a ha f u‖ *
            Real.exp ((A + 1) * |u|)) := by
        rw [show (A + 1) * |u| = |u| + A * |u| by ring, Real.exp_add]
        ring

/-- Holomorphic integral representing the `n`th derivative of the rapid theta trace. -/
def rapidExponentialMomentFockThetaDerivativeIntegral
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) (z : ℂ) : ℂ :=
  expFourier (rapidExponentialMomentFockThetaMomentSource a ha f n) (2 * Real.pi * z)

theorem rapidExponentialMomentFockThetaDerivativeIntegral_zero
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockThetaDerivativeIntegral a ha f 0 z =
      rapidExponentialMomentFockThetaTrace a ha f z := by
  unfold rapidExponentialMomentFockThetaDerivativeIntegral rapidExponentialMomentFockThetaTrace
  congr 2
  funext u
  simp [rapidExponentialMomentFockThetaMomentSource]

theorem hasDerivAt_rapidExponentialMomentFockThetaDerivativeIntegral
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2)
    (f : MomentFock) (n : ℕ) (z : ℂ) :
    HasDerivAt (rapidExponentialMomentFockThetaDerivativeIntegral a ha f n)
      (rapidExponentialMomentFockThetaDerivativeIntegral a ha f (n + 1) z) z := by
  let w : ℂ := 2 * Real.pi * z
  have houter := hasDerivAt_expFourier'
    (aestronglyMeasurable_rapidExponentialMomentFockThetaMomentSource a ha f n)
    ((allExpWeightIntegrable_rapidExponentialMomentFockThetaMomentSource a ha haHalf f n).expWeightIntegrable
      (|w.im| + 1)) (by linarith : |w.im| < |w.im| + 1)
  have hinner : HasDerivAt (fun q : ℂ => 2 * (Real.pi : ℂ) * q)
      (2 * (Real.pi : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ))
  have hcomp := houter.comp z hinner
  have hderiv :
      (∫ u : ℝ,
          rapidExponentialMomentFockThetaMomentSource a ha f n u * (-(I * u)) *
            Complex.exp (-(I * w * u))) * (2 * (Real.pi : ℂ)) =
        rapidExponentialMomentFockThetaDerivativeIntegral a ha f (n + 1) z := by
    rw [← integral_mul_const]
    unfold rapidExponentialMomentFockThetaDerivativeIntegral expFourier
    apply integral_congr_ae
    filter_upwards with u
    unfold rapidExponentialMomentFockThetaMomentSource
    rw [pow_succ]
    dsimp [w]
    ring
  rw [hderiv] at hcomp
  change HasDerivAt (rapidExponentialMomentFockThetaDerivativeIntegral a ha f n)
    (rapidExponentialMomentFockThetaDerivativeIntegral a ha f (n + 1) z) z at hcomp
  exact hcomp

theorem iteratedDeriv_rapidExponentialMomentFockThetaTrace_eq_integral
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2)
    (f : MomentFock) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (rapidExponentialMomentFockThetaTrace a ha f) z =
      rapidExponentialMomentFockThetaDerivativeIntegral a ha f n z := by
  induction n generalizing z with
  | zero =>
      simpa [iteratedDeriv_zero] using
        (rapidExponentialMomentFockThetaDerivativeIntegral_zero a ha f z).symm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (rapidExponentialMomentFockThetaTrace a ha f) =
          rapidExponentialMomentFockThetaDerivativeIntegral a ha f n := by
        funext q
        exact ih q
      rw [hfun]
      simpa [Nat.succ_eq_add_one] using
        (hasDerivAt_rapidExponentialMomentFockThetaDerivativeIntegral
          a ha haHalf f n z).deriv

/-- Every rapid theta-trace moment is the exact derivative at the origin. -/
theorem iteratedDeriv_rapidExponentialMomentFockThetaTrace_zero_eq_moment
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) (n : ℕ) :
    iteratedDeriv n (rapidExponentialMomentFockThetaTrace a ha f) 0 =
      ∫ u : ℝ,
        (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n *
          rapidExponentialMomentFockFunction a ha f (u : ℂ) * xiThetaLogSource u := by
  rw [iteratedDeriv_rapidExponentialMomentFockThetaTrace_eq_integral a ha haHalf]
  unfold rapidExponentialMomentFockThetaDerivativeIntegral expFourier
  apply integral_congr_ae
  filter_upwards with u
  unfold rapidExponentialMomentFockThetaMomentSource rapidExponentialMomentFockThetaSource
  simp
  ring

end

end RHTower
