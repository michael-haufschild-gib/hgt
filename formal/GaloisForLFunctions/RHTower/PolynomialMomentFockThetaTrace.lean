import GaloisForLFunctions.RHTower.PolynomialMomentFockKernelBound
import GaloisForLFunctions.RHTower.XiThetaExplicitBounds
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeEntireTransform
import GaloisForLFunctions.RHTower.ConnesTwoSidedPowerTail
import GaloisForLFunctions.RHTower.ExpFourierNormalization
import GaloisForLFunctions.HTGeometry.ExpRayL2

open Filter Topology Set MeasureTheory Complex Real
open scoped Real

namespace RHTower

noncomputable section

/-- The completed logarithmic theta source has its literal two-sided double-exponential bound. -/
theorem norm_xiThetaLogSource_le_doubleExp (u : ℝ) :
    ‖xiThetaLogSource u‖ ≤
      3 * Real.exp (|u| / 4) * Real.exp (-Real.pi * Real.exp |u|) := by
  have hposbound : ∀ {v : ℝ}, 0 < v →
      ‖xiThetaLogSource v‖ ≤
        3 * Real.exp (v / 4) * Real.exp (-Real.pi * Real.exp v) := by
    intro v hv
    rw [xiThetaLogSource_eq_positiveFormula hv]
    unfold xiThetaPositiveFormula
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (evenKernel_zero_sub_one_pos (Real.exp_pos v)).le]
    have htail := evenKernel_zero_sub_one_le
      (show 1 ≤ Real.exp v by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hv.le)
    calc
      Real.exp (v / 4) * (HurwitzZeta.evenKernel 0 (Real.exp v) - 1) ≤
          Real.exp (v / 4) * (3 * Real.exp (-Real.pi * Real.exp v)) := by
        gcongr
      _ = 3 * Real.exp (v / 4) * Real.exp (-Real.pi * Real.exp v) := by ring
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [← xiThetaLogSource_neg u, abs_of_neg hu]
    exact hposbound (neg_pos.mpr hu)
  · simp only [xiThetaLogSource_zero, norm_zero]
    positivity
  · simpa [abs_of_pos hu] using hposbound hu

theorem polynomialFockPotential_shift_le_rpow
    {m u : ℝ} (hm : 2 ≤ m) (hu : 0 ≤ u) :
    polynomialFockPotential m (u + 2) ≤ (u + 3) ^ m := by
  have hbase : 1 + (u + 2) ^ 2 ≤ (u + 3) ^ 2 := by nlinarith
  have hbase0 : 0 ≤ 1 + (u + 2) ^ 2 := by positivity
  have hpow := Real.rpow_le_rpow hbase0 hbase (by linarith : 0 ≤ m / 2)
  rw [polynomialFockPotential]
  calc
    (1 + (u + 2) ^ 2) ^ (m / 2) ≤ ((u + 3) ^ 2) ^ (m / 2) := hpow
    _ = (u + 3) ^ m := by
      rw [← Real.rpow_two]
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring

theorem tendsto_exp_div_shifted_rpow (m : ℝ) :
    Tendsto (fun u : ℝ => Real.exp u / (u + 3) ^ m) atTop atTop := by
  have hbase := (tendsto_exp_div_rpow_atTop m).comp
    (tendsto_atTop_add_const_right atTop 3 tendsto_id)
  have hmul := hbase.atTop_mul_const (Real.exp_pos (-3))
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (-3 : ℝ)] with u hu
  have hup : 0 < u + 3 := by linarith
  have hpow : 0 < (u + 3) ^ m := Real.rpow_pos_of_pos hup m
  simp only [Function.comp_apply, id_eq]
  field_simp [hpow.ne']
  rw [← Real.exp_add]
  ring_nf

theorem eventually_polynomialFockTheta_exponent_le
    {m : ℝ} (hm : 2 ≤ m) (A : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      2 * polynomialFockPotential m (u + 2) + (A + 9 / 4) * u ≤
        (Real.pi / 2) * Real.exp u := by
  let B : ℝ := |A + 9 / 4|
  let C : ℝ := 2 + B
  have hC : 0 < C := by dsimp [C, B]; positivity
  have hratio := (tendsto_exp_div_shifted_rpow m).eventually_ge_atTop
    (2 * C / Real.pi)
  filter_upwards [hratio, eventually_ge_atTop (0 : ℝ)] with u hratio hu
  have hbase : 1 ≤ u + 3 := by linarith
  have hup : 0 < u + 3 := by linarith
  have hpowpos : 0 < (u + 3) ^ m := Real.rpow_pos_of_pos hup m
  have hpow_ge_u : u ≤ (u + 3) ^ m := by
    calc
      u ≤ u + 3 := by linarith
      _ = (u + 3) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (u + 3) ^ m :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hpot := polynomialFockPotential_shift_le_rpow hm hu
  have hlinear : (A + 9 / 4) * u ≤ B * (u + 3) ^ m := by
    calc
      (A + 9 / 4) * u ≤ B * u := by
        exact mul_le_mul_of_nonneg_right (le_abs_self (A + 9 / 4)) hu
      _ ≤ B * (u + 3) ^ m :=
        mul_le_mul_of_nonneg_left hpow_ge_u (abs_nonneg _)
  have hleft :
      2 * polynomialFockPotential m (u + 2) + (A + 9 / 4) * u ≤
        C * (u + 3) ^ m := by
    dsimp [C]
    nlinarith
  have hdiv : (2 * C / Real.pi) * (u + 3) ^ m ≤ Real.exp u :=
    (le_div_iff₀ hpowpos).mp hratio
  have hscaled := mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
  have hright : C * (u + 3) ^ m ≤ (Real.pi / 2) * Real.exp u := by
    calc
      C * (u + 3) ^ m =
          (Real.pi / 2) * ((2 * C / Real.pi) * (u + 3) ^ m) := by
        field_simp
      _ ≤ (Real.pi / 2) * Real.exp u := by gcongr
  exact hleft.trans hright

theorem polynomialMomentFockEvaluationMajorant_real_le
    {m u : ℝ} (hm : 2 ≤ m) (hu : 0 ≤ u) :
    polynomialMomentFockEvaluationMajorant m (u : ℂ) ≤
      2 * Real.exp (2 * polynomialFockPotential m (u + 2)) * (u + 1) ^ 2 := by
  let φ : ℝ := polynomialFockPotential m (u + 2)
  have hφ : 0 ≤ φ := by
    dsimp [φ]
    exact (sq_nonneg (u + 2)).trans (polynomialFockPotential_ge_sq hm)
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
  unfold polynomialMomentFockEvaluationMajorant
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hterm :
      (2 * Real.pi * Real.exp (-2 * polynomialFockPotential m (u + 2)))⁻¹ *
          (u + 1) ^ 2 ≤
        Real.exp (2 * polynomialFockPotential m (u + 2)) * (u + 1) ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by simpa [φ] using hcoeff) (sq_nonneg _)
  nlinarith

theorem sq_one_add_le_exp_two_mul {u : ℝ} (hu : 0 ≤ u) :
    (u + 1) ^ 2 ≤ Real.exp (2 * u) := by
  have h := Real.add_one_le_exp u
  have hnonneg : 0 ≤ u + 1 := by linarith
  calc
    (u + 1) ^ 2 ≤ (Real.exp u) ^ 2 := by nlinarith [Real.exp_pos u]
    _ = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; norm_num

/-- Scalar envelope for the theta-weighted polynomial Fock carrier on a real ray. -/
def polynomialMomentFockThetaWeightMajorant (m A u : ℝ) : ℝ :=
  polynomialMomentFockEvaluationMajorant m (u : ℂ) *
    ‖xiThetaLogSource u‖ * Real.exp (A * u)

theorem eventually_polynomialMomentFockThetaWeightMajorant_le
    {m : ℝ} (hm : 2 ≤ m) (A : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      polynomialMomentFockThetaWeightMajorant m A u ≤
        6 * Real.exp (-(Real.pi / 2 * u)) := by
  have hevent := eventually_polynomialFockTheta_exponent_le hm A
  filter_upwards [hevent, eventually_ge_atTop (0 : ℝ)] with u hexponent hu
  have hmajorant := polynomialMomentFockEvaluationMajorant_real_le hm hu
  have htheta := norm_xiThetaLogSource_le_doubleExp u
  rw [abs_of_nonneg hu] at htheta
  have hsq := sq_one_add_le_exp_two_mul hu
  have hmajorant' :
      polynomialMomentFockEvaluationMajorant m (u : ℂ) ≤
        2 * Real.exp (2 * polynomialFockPotential m (u + 2)) * Real.exp (2 * u) :=
    hmajorant.trans
      (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hfirst :
      polynomialMomentFockThetaWeightMajorant m A u ≤
        (2 * Real.exp (2 * polynomialFockPotential m (u + 2)) * Real.exp (2 * u)) *
          (3 * Real.exp (u / 4) * Real.exp (-Real.pi * Real.exp u)) *
            Real.exp (A * u) := by
    unfold polynomialMomentFockThetaWeightMajorant
    gcongr
  have hexpIdentity :
      Real.exp (2 * polynomialFockPotential m (u + 2)) *
          Real.exp (2 * u) * Real.exp (u / 4) *
            Real.exp (-Real.pi * Real.exp u) * Real.exp (A * u) =
        Real.exp
          (2 * polynomialFockPotential m (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hcombined :
      (2 * Real.exp (2 * polynomialFockPotential m (u + 2)) * Real.exp (2 * u)) *
          (3 * Real.exp (u / 4) * Real.exp (-Real.pi * Real.exp u)) *
            Real.exp (A * u) =
        6 * Real.exp
          (2 * polynomialFockPotential m (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := by
    rw [← hexpIdentity]
    ring
  rw [hcombined] at hfirst
  have hexponent' :
      2 * polynomialFockPotential m (u + 2) +
          (A + 9 / 4) * u - Real.pi * Real.exp u ≤
        -(Real.pi / 2) * Real.exp u := by
    linarith
  have hu_exp : u ≤ Real.exp u := by
    linarith [Real.add_one_le_exp u]
  calc
    polynomialMomentFockThetaWeightMajorant m A u ≤
        6 * Real.exp
          (2 * polynomialFockPotential m (u + 2) +
            (A + 9 / 4) * u - Real.pi * Real.exp u) := hfirst
    _ ≤ 6 * Real.exp (-(Real.pi / 2) * Real.exp u) := by
      gcongr
    _ ≤ 6 * Real.exp (-(Real.pi / 2 * u)) := by
      have hneg :
          -(Real.pi / 2) * Real.exp u ≤ -(Real.pi / 2) * u :=
        mul_le_mul_of_nonpos_left hu_exp (by nlinarith [Real.pi_pos])
      have harg : -(Real.pi / 2) * u = -(Real.pi / 2 * u) := by ring
      rw [← harg]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by norm_num)

theorem continuous_polynomialMomentFockEvaluationMajorant_real (m : ℝ) :
    Continuous (fun u : ℝ =>
      polynomialMomentFockEvaluationMajorant m (u : ℂ)) := by
  unfold polynomialMomentFockEvaluationMajorant
  have hnorm : Continuous (fun u : ℝ => ‖(u : ℂ)‖) := by fun_prop
  have harg : Continuous (fun u : ℝ => ‖(u : ℂ)‖ + 2) :=
    hnorm.add continuous_const
  have hpotential : Continuous (fun u : ℝ =>
      polynomialFockPotential m (‖(u : ℂ)‖ + 2)) :=
    (continuous_polynomialFockPotential m).comp harg
  have hden : Continuous (fun u : ℝ =>
      2 * Real.pi * Real.exp
        (-2 * polynomialFockPotential m (‖(u : ℂ)‖ + 2))) := by
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hpotential))
  have hden0 : ∀ u : ℝ,
      2 * Real.pi * Real.exp
        (-2 * polynomialFockPotential m (‖(u : ℂ)‖ + 2)) ≠ 0 := by
    intro u
    positivity
  exact continuous_const.add
    ((hden.inv₀ hden0).mul ((hnorm.add continuous_const).pow 2))

/-- Seam-free positive-half representative of the scalar theta/Fock envelope. -/
def polynomialMomentFockThetaPositiveWeightMajorant (m A u : ℝ) : ℝ :=
  polynomialMomentFockEvaluationMajorant m (u : ℂ) *
    ‖xiThetaPositiveFormula u‖ * Real.exp (A * u)

theorem continuous_polynomialMomentFockThetaPositiveWeightMajorant (m A : ℝ) :
    Continuous (polynomialMomentFockThetaPositiveWeightMajorant m A) := by
  unfold polynomialMomentFockThetaPositiveWeightMajorant
  exact ((continuous_polynomialMomentFockEvaluationMajorant_real m).mul
    continuous_xiThetaPositiveFormula.norm).mul (by fun_prop)

theorem polynomialMomentFockThetaPositiveWeightMajorant_nonneg
    (m A u : ℝ) :
    0 ≤ polynomialMomentFockThetaPositiveWeightMajorant m A u := by
  unfold polynomialMomentFockThetaPositiveWeightMajorant
  unfold polynomialMomentFockEvaluationMajorant
  positivity

theorem polynomialMomentFockThetaWeightMajorant_nonneg (m A u : ℝ) :
    0 ≤ polynomialMomentFockThetaWeightMajorant m A u := by
  unfold polynomialMomentFockThetaWeightMajorant
  unfold polynomialMomentFockEvaluationMajorant
  positivity

theorem polynomialMomentFockThetaPositiveWeightMajorant_eq
    {m A u : ℝ} (hu : 0 < u) :
    polynomialMomentFockThetaPositiveWeightMajorant m A u =
      polynomialMomentFockThetaWeightMajorant m A u := by
  unfold polynomialMomentFockThetaPositiveWeightMajorant
  unfold polynomialMomentFockThetaWeightMajorant
  rw [xiThetaLogSource_eq_positiveFormula hu]

theorem integrableOn_polynomialMomentFockThetaWeightMajorant_Ioi
    {m : ℝ} (hm : 2 ≤ m) (A : ℝ) :
    IntegrableOn (polynomialMomentFockThetaWeightMajorant m A) (Ioi 0) := by
  have hevent := eventually_polynomialMomentFockThetaWeightMajorant_le hm A
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨T, hT⟩
  let B : ℝ := max T 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have htailBase :
      IntegrableOn (fun u : ℝ => 6 * Real.exp (-(Real.pi / 2 * u))) (Ioi B) := by
    exact
      (GaloisForLFunctions.HTGeometry.integrableOn_exp_neg_mul_Ioi
        (b := Real.pi / 2) (by positivity) B).const_mul 6
  have htail :
      IntegrableOn (polynomialMomentFockThetaPositiveWeightMajorant m A) (Ioi B) := by
    apply htailBase.mono'
    · exact (continuous_polynomialMomentFockThetaPositiveWeightMajorant m A).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hu0 : 0 < u := lt_of_le_of_lt hB0 hu
      have hbound := hT u ((le_max_left T 0).trans hu.le)
      rw [polynomialMomentFockThetaPositiveWeightMajorant_eq hu0]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (polynomialMomentFockThetaWeightMajorant_nonneg m A u)]
      exact hbound
  have hcompact :
      IntegrableOn (polynomialMomentFockThetaPositiveWeightMajorant m A) (Ioc 0 B) := by
    exact ((continuous_polynomialMomentFockThetaPositiveWeightMajorant m A).integrableOn_Icc).mono_set (by
        intro u hu
        exact ⟨hu.1.le, hu.2⟩)
  have hpositive :
      IntegrableOn (polynomialMomentFockThetaPositiveWeightMajorant m A) (Ioi 0) := by
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
  exact polynomialMomentFockThetaPositiveWeightMajorant_eq hu

/-- Two-sided scalar envelope used for every exponential weight. -/
def polynomialMomentFockThetaAbsWeightMajorant (m A u : ℝ) : ℝ :=
  polynomialMomentFockEvaluationMajorant m (u : ℂ) *
    ‖xiThetaLogSource u‖ * Real.exp (A * |u|)

theorem polynomialMomentFockThetaAbsWeightMajorant_neg (m A u : ℝ) :
    polynomialMomentFockThetaAbsWeightMajorant m A (-u) =
      polynomialMomentFockThetaAbsWeightMajorant m A u := by
  unfold polynomialMomentFockThetaAbsWeightMajorant
  have hmajorant :
      polynomialMomentFockEvaluationMajorant m ((-u : ℝ) : ℂ) =
        polynomialMomentFockEvaluationMajorant m (u : ℂ) := by
    unfold polynomialMomentFockEvaluationMajorant
    rw [show ((-u : ℝ) : ℂ) = -(u : ℂ) by norm_num, norm_neg]
  rw [hmajorant, xiThetaLogSource_neg]
  simp only [abs_neg]

theorem polynomialMomentFockThetaAbsWeightMajorant_nonneg (m A u : ℝ) :
    0 ≤ polynomialMomentFockThetaAbsWeightMajorant m A u := by
  unfold polynomialMomentFockThetaAbsWeightMajorant
  unfold polynomialMomentFockEvaluationMajorant
  positivity

theorem integrable_polynomialMomentFockThetaAbsWeightMajorant
    {m : ℝ} (hm : 2 ≤ m) (A : ℝ) :
    Integrable (polynomialMomentFockThetaAbsWeightMajorant m A) := by
  have hposWeight := integrableOn_polynomialMomentFockThetaWeightMajorant_Ioi hm A
  have hpos :
      IntegrableOn (polynomialMomentFockThetaAbsWeightMajorant m A) (Ioi 0) := by
    refine hposWeight.congr_fun ?_ measurableSet_Ioi
    intro u hu
    unfold polynomialMomentFockThetaAbsWeightMajorant
    unfold polynomialMomentFockThetaWeightMajorant
    rw [abs_of_pos hu]
  have hneg :
      IntegrableOn (polynomialMomentFockThetaAbsWeightMajorant m A) (Iio 0) := by
    simpa using GaloisForLFunctions.RHTower.connes_integrableOn_Iio_neg_of_even
      (polynomialMomentFockThetaAbsWeightMajorant_neg m A) hpos
  have hzero :
      IntegrableOn (polynomialMomentFockThetaAbsWeightMajorant m A) ({0} : Set ℝ) := by
    exact integrableOn_singleton
      (f := polynomialMomentFockThetaAbsWeightMajorant m A)
      (hfx := by finiteness) (hx := by simp)
  have hnonneg :
      IntegrableOn (polynomialMomentFockThetaAbsWeightMajorant m A) (Ici 0) := by
    have h := hzero.union hpos
    have hset : ({0} : Set ℝ) ∪ Ioi 0 = Ici 0 := by
      ext u
      simp
    simpa only [hset] using h
  have hall := hneg.union hnonneg
  rw [Iio_union_Ici] at hall
  simpa only [IntegrableOn, Measure.restrict_univ] using hall

/-- Literal theta source obtained by evaluating a polynomial moment-Fock vector on the real axis. -/
def polynomialMomentFockThetaSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (u : ℝ) : ℂ :=
  polynomialMomentFockFunction m hm f (u : ℂ) * xiThetaLogSource u

theorem aestronglyMeasurable_polynomialMomentFockThetaSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    AEStronglyMeasurable (polynomialMomentFockThetaSource m hm f) volume := by
  have hreal : Continuous (fun u : ℝ => (u : ℂ)) := by fun_prop
  have hcarrier : Continuous (fun u : ℝ =>
      polynomialMomentFockFunction m hm f (u : ℂ)) :=
    (differentiable_polynomialMomentFockFunction m hm f).continuous.comp hreal
  unfold polynomialMomentFockThetaSource
  exact hcarrier.aestronglyMeasurable.mul
    xiThetaLogSource_integrable.aestronglyMeasurable

theorem allExpWeightIntegrable_polynomialMomentFockThetaSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    AllExpWeightIntegrable (polynomialMomentFockThetaSource m hm f) := by
  intro A
  have hmajorant :=
    (integrable_polynomialMomentFockThetaAbsWeightMajorant hm A).const_mul ‖f‖
  apply hmajorant.mono'
  · exact (aestronglyMeasurable_polynomialMomentFockThetaSource m hm f).norm.mul
      (by fun_prop)
  · filter_upwards with u
    have hcarrier := norm_polynomialMomentFockFunction_le_majorant hm f (u : ℂ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold polynomialMomentFockThetaSource
    rw [norm_mul]
    calc
      ‖polynomialMomentFockFunction m hm f (u : ℂ)‖ *
            ‖xiThetaLogSource u‖ * Real.exp (A * |u|) ≤
          (polynomialMomentFockEvaluationMajorant m (u : ℂ) * ‖f‖) *
            ‖xiThetaLogSource u‖ * Real.exp (A * |u|) := by
        gcongr
      _ = ‖f‖ * polynomialMomentFockThetaAbsWeightMajorant m A u := by
        unfold polynomialMomentFockThetaAbsWeightMajorant
        ring

/-- Entire theta trace of a polynomial moment-Fock vector, in the `2π` Fourier normalization. -/
def polynomialMomentFockThetaTrace
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) : ℂ :=
  expFourier (polynomialMomentFockThetaSource m hm f) (2 * Real.pi * z)

theorem differentiable_polynomialMomentFockThetaTrace
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Differentiable ℂ (polynomialMomentFockThetaTrace m hm f) := by
  have houter := differentiable_expFourier_of_allExpWeightIntegrable
    (aestronglyMeasurable_polynomialMomentFockThetaSource m hm f)
    (allExpWeightIntegrable_polynomialMomentFockThetaSource m hm f)
  unfold polynomialMomentFockThetaTrace
  fun_prop

theorem polynomialMomentFockThetaSource_one
    (m : ℝ) (hm : 2 ≤ m) (u : ℝ) :
    polynomialMomentFockThetaSource m hm (polynomialMomentFockOne m hm) u =
      xiThetaLogSource u := by
  unfold polynomialMomentFockThetaSource
  rw [polynomialMomentFockFunction_one]
  simp

theorem polynomialMomentFockThetaTrace_one
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) :
    polynomialMomentFockThetaTrace m hm (polynomialMomentFockOne m hm) z =
      expFourier xiThetaLogSource (2 * Real.pi * z) := by
  unfold polynomialMomentFockThetaTrace
  congr 2
  funext u
  exact polynomialMomentFockThetaSource_one m hm u

theorem polynomialMomentFockThetaTrace_one_real_eq_fourier
    (m : ℝ) (hm : 2 ≤ m) (w : ℝ) :
    polynomialMomentFockThetaTrace m hm (polynomialMomentFockOne m hm) (w : ℂ) =
      FourierTransform.fourier xiThetaLogSource w := by
  rw [polynomialMomentFockThetaTrace_one,
    fourier_eq_expFourier_two_pi]
  congr 2
  push_cast
  ring

theorem completedRiemannZeta₀_critical_eq_polynomialMomentFockThetaTrace_one
    (m : ℝ) (hm : 2 ≤ m) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) =
      polynomialMomentFockThetaTrace m hm (polynomialMomentFockOne m hm)
        ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  rw [completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource,
    polynomialMomentFockThetaTrace_one_real_eq_fourier]

/-- Source of the `n`th trace derivative. -/
def polynomialMomentFockThetaMomentSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (u : ℝ) : ℂ :=
  (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n *
    polynomialMomentFockThetaSource m hm f u

theorem aestronglyMeasurable_polynomialMomentFockThetaMomentSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    AEStronglyMeasurable (polynomialMomentFockThetaMomentSource m hm f n) volume := by
  unfold polynomialMomentFockThetaMomentSource
  exact (by fun_prop : Continuous (fun u : ℝ =>
    (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n)).aestronglyMeasurable.mul
      (aestronglyMeasurable_polynomialMomentFockThetaSource m hm f)

theorem norm_polynomialMomentFockThetaMomentPhase_le (n : ℕ) (u : ℝ) :
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

theorem allExpWeightIntegrable_polynomialMomentFockThetaMomentSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    AllExpWeightIntegrable (polynomialMomentFockThetaMomentSource m hm f n) := by
  intro A
  let C : ℝ := (2 * Real.pi) ^ n * (n.factorial : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase :=
    (allExpWeightIntegrable_polynomialMomentFockThetaSource m hm f (A + 1)).const_mul C
  apply hbase.mono'
  · exact (aestronglyMeasurable_polynomialMomentFockThetaMomentSource m hm f n).norm.mul
      (by fun_prop)
  · filter_upwards with u
    have hphase :
        ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ ≤
          C * Real.exp |u| := by
      simpa only [C] using norm_polynomialMomentFockThetaMomentPhase_le n u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold polynomialMomentFockThetaMomentSource
    rw [norm_mul]
    calc
      ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ *
            ‖polynomialMomentFockThetaSource m hm f u‖ * Real.exp (A * |u|) ≤
          (C * Real.exp |u|) *
            ‖polynomialMomentFockThetaSource m hm f u‖ * Real.exp (A * |u|) := by
        gcongr
      _ = C *
          (‖polynomialMomentFockThetaSource m hm f u‖ *
            Real.exp ((A + 1) * |u|)) := by
        rw [show (A + 1) * |u| = |u| + A * |u| by ring, Real.exp_add]
        ring

/-- Holomorphic integral representing the `n`th derivative of the theta trace. -/
def polynomialMomentFockThetaDerivativeIntegral
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (z : ℂ) : ℂ :=
  expFourier (polynomialMomentFockThetaMomentSource m hm f n) (2 * Real.pi * z)

theorem polynomialMomentFockThetaDerivativeIntegral_zero
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    polynomialMomentFockThetaDerivativeIntegral m hm f 0 z =
      polynomialMomentFockThetaTrace m hm f z := by
  unfold polynomialMomentFockThetaDerivativeIntegral polynomialMomentFockThetaTrace
  congr 2
  funext u
  simp [polynomialMomentFockThetaMomentSource]

theorem hasDerivAt_polynomialMomentFockThetaDerivativeIntegral
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (z : ℂ) :
    HasDerivAt (polynomialMomentFockThetaDerivativeIntegral m hm f n)
      (polynomialMomentFockThetaDerivativeIntegral m hm f (n + 1) z) z := by
  let w : ℂ := 2 * Real.pi * z
  have houter := hasDerivAt_expFourier'
    (aestronglyMeasurable_polynomialMomentFockThetaMomentSource m hm f n)
    ((allExpWeightIntegrable_polynomialMomentFockThetaMomentSource m hm f n).expWeightIntegrable
      (|w.im| + 1)) (by linarith : |w.im| < |w.im| + 1)
  have hinner : HasDerivAt (fun q : ℂ => 2 * (Real.pi : ℂ) * q)
      (2 * (Real.pi : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ))
  have hcomp := houter.comp z hinner
  have hderiv :
      (∫ u : ℝ,
          polynomialMomentFockThetaMomentSource m hm f n u * (-(I * u)) *
            Complex.exp (-(I * w * u))) * (2 * (Real.pi : ℂ)) =
        polynomialMomentFockThetaDerivativeIntegral m hm f (n + 1) z := by
    rw [← integral_mul_const]
    unfold polynomialMomentFockThetaDerivativeIntegral expFourier
    apply integral_congr_ae
    filter_upwards with u
    unfold polynomialMomentFockThetaMomentSource
    rw [pow_succ]
    dsimp [w]
    ring
  rw [hderiv] at hcomp
  change HasDerivAt (polynomialMomentFockThetaDerivativeIntegral m hm f n)
    (polynomialMomentFockThetaDerivativeIntegral m hm f (n + 1) z) z at hcomp
  exact hcomp

theorem iteratedDeriv_polynomialMomentFockThetaTrace_eq_integral
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (polynomialMomentFockThetaTrace m hm f) z =
      polynomialMomentFockThetaDerivativeIntegral m hm f n z := by
  induction n generalizing z with
  | zero =>
      simpa [iteratedDeriv_zero] using
        (polynomialMomentFockThetaDerivativeIntegral_zero m hm f z).symm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (polynomialMomentFockThetaTrace m hm f) =
          polynomialMomentFockThetaDerivativeIntegral m hm f n := by
        funext q
        exact ih q
      rw [hfun]
      simpa [Nat.succ_eq_add_one] using
        (hasDerivAt_polynomialMomentFockThetaDerivativeIntegral m hm f n z).deriv

theorem iteratedDeriv_polynomialMomentFockThetaTrace_zero_eq_moment
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    iteratedDeriv n (polynomialMomentFockThetaTrace m hm f) 0 =
      ∫ u : ℝ,
        (-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n *
          polynomialMomentFockFunction m hm f (u : ℂ) * xiThetaLogSource u := by
  rw [iteratedDeriv_polynomialMomentFockThetaTrace_eq_integral]
  unfold polynomialMomentFockThetaDerivativeIntegral expFourier
  apply integral_congr_ae
  filter_upwards with u
  unfold polynomialMomentFockThetaMomentSource polynomialMomentFockThetaSource
  simp
  ring

theorem norm_polynomialMomentFockThetaMomentSource_le
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (u : ℝ) :
    ‖polynomialMomentFockThetaMomentSource m hm f n u‖ ≤
      ((2 * Real.pi) ^ n * (n.factorial : ℝ)) * ‖f‖ *
        polynomialMomentFockThetaAbsWeightMajorant m 1 u := by
  have hphase := norm_polynomialMomentFockThetaMomentPhase_le n u
  have hcarrier := norm_polynomialMomentFockFunction_le_majorant hm f (u : ℂ)
  unfold polynomialMomentFockThetaMomentSource polynomialMomentFockThetaSource
  rw [norm_mul, norm_mul]
  calc
    ‖(-(2 * (Real.pi : ℂ) * I * (u : ℂ))) ^ n‖ *
          (‖polynomialMomentFockFunction m hm f (u : ℂ)‖ *
            ‖xiThetaLogSource u‖) ≤
        (((2 * Real.pi) ^ n * (n.factorial : ℝ)) * Real.exp |u|) *
          ((polynomialMomentFockEvaluationMajorant m (u : ℂ) * ‖f‖) *
            ‖xiThetaLogSource u‖) := by
      gcongr
    _ = ((2 * Real.pi) ^ n * (n.factorial : ℝ)) * ‖f‖ *
          polynomialMomentFockThetaAbsWeightMajorant m 1 u := by
      unfold polynomialMomentFockThetaAbsWeightMajorant
      simp only [one_mul]
      ring

/-- Explicit norm bound for the `n`th trace-moment functional. -/
def polynomialMomentFockThetaMomentBound (m : ℝ) (n : ℕ) : ℝ :=
  ((2 * Real.pi) ^ n * (n.factorial : ℝ)) *
    ∫ u : ℝ, polynomialMomentFockThetaAbsWeightMajorant m 1 u

theorem polynomialMomentFockThetaMomentBound_nonneg
    (m : ℝ) (n : ℕ) :
    0 ≤ polynomialMomentFockThetaMomentBound m n := by
  unfold polynomialMomentFockThetaMomentBound
  have hintegral : 0 ≤ ∫ u : ℝ,
      polynomialMomentFockThetaAbsWeightMajorant m 1 u :=
    integral_nonneg (fun u => polynomialMomentFockThetaAbsWeightMajorant_nonneg m 1 u)
  positivity

theorem norm_integral_polynomialMomentFockThetaMomentSource_le
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    ‖∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u‖ ≤
      polynomialMomentFockThetaMomentBound m n * ‖f‖ := by
  let C : ℝ := ((2 * Real.pi) ^ n * (n.factorial : ℝ)) * ‖f‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hleft : Integrable (fun u : ℝ =>
      ‖polynomialMomentFockThetaMomentSource m hm f n u‖) := by
    simpa using
      (allExpWeightIntegrable_polynomialMomentFockThetaMomentSource m hm f n 0)
  have hright : Integrable (fun u : ℝ =>
      C * polynomialMomentFockThetaAbsWeightMajorant m 1 u) :=
    (integrable_polynomialMomentFockThetaAbsWeightMajorant hm 1).const_mul C
  calc
    ‖∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u‖ ≤
        ∫ u : ℝ, ‖polynomialMomentFockThetaMomentSource m hm f n u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, C * polynomialMomentFockThetaAbsWeightMajorant m 1 u := by
      apply integral_mono hleft hright
      intro u
      simpa only [C, mul_assoc] using
        norm_polynomialMomentFockThetaMomentSource_le m hm f n u
    _ = polynomialMomentFockThetaMomentBound m n * ‖f‖ := by
      rw [integral_const_mul]
      unfold polynomialMomentFockThetaMomentBound C
      ring

theorem polynomialMomentFockThetaMomentSource_add
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) (n : ℕ) (u : ℝ) :
    polynomialMomentFockThetaMomentSource m hm (f + g) n u =
      polynomialMomentFockThetaMomentSource m hm f n u +
        polynomialMomentFockThetaMomentSource m hm g n u := by
  simp only [polynomialMomentFockThetaMomentSource, polynomialMomentFockThetaSource,
    polynomialMomentFockFunction_eq_evaluation, map_add]
  ring

theorem polynomialMomentFockThetaMomentSource_smul
    (m : ℝ) (hm : 2 ≤ m) (c : ℂ) (f : MomentFock) (n : ℕ) (u : ℝ) :
    polynomialMomentFockThetaMomentSource m hm (c • f) n u =
      c • polynomialMomentFockThetaMomentSource m hm f n u := by
  simp only [polynomialMomentFockThetaMomentSource, polynomialMomentFockThetaSource,
    polynomialMomentFockFunction_eq_evaluation, map_smul, smul_eq_mul]
  ring

theorem integrable_polynomialMomentFockThetaMomentSource
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    Integrable (polynomialMomentFockThetaMomentSource m hm f n) := by
  have h := integrable_expFourier_kernel'
    (aestronglyMeasurable_polynomialMomentFockThetaMomentSource m hm f n)
    ((allExpWeightIntegrable_polynomialMomentFockThetaMomentSource m hm f n).expWeightIntegrable 1)
    (w := 0) (by norm_num)
  simpa using h

/-- Algebraic `n`th moment of the theta trace as a complex-linear functional. -/
def polynomialMomentFockThetaMomentLinearMap
    (m : ℝ) (hm : 2 ≤ m) (n : ℕ) : MomentFock →ₗ[ℂ] ℂ where
  toFun f := ∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u
  map_add' f g := by
    calc
      (∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm (f + g) n u) =
          ∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u +
            polynomialMomentFockThetaMomentSource m hm g n u := by
        apply integral_congr_ae
        filter_upwards with u
        exact polynomialMomentFockThetaMomentSource_add m hm f g n u
      _ = (∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u) +
          ∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm g n u :=
        integral_add
          (integrable_polynomialMomentFockThetaMomentSource m hm f n)
          (integrable_polynomialMomentFockThetaMomentSource m hm g n)
  map_smul' c f := by
    calc
      (∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm (c • f) n u) =
          ∫ u : ℝ, c • polynomialMomentFockThetaMomentSource m hm f n u := by
        apply integral_congr_ae
        filter_upwards with u
        exact polynomialMomentFockThetaMomentSource_smul m hm c f n u
      _ = c • ∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u :=
        integral_smul c _

/-- Every trace moment is a bounded complex-linear functional on the carrier. -/
def polynomialMomentFockThetaMomentFunctional
    (m : ℝ) (hm : 2 ≤ m) (n : ℕ) : MomentFock →L[ℂ] ℂ :=
  (polynomialMomentFockThetaMomentLinearMap m hm n).mkContinuous
    (polynomialMomentFockThetaMomentBound m n)
    (fun f => norm_integral_polynomialMomentFockThetaMomentSource_le m hm f n)

theorem polynomialMomentFockThetaMomentFunctional_apply
    (m : ℝ) (hm : 2 ≤ m) (n : ℕ) (f : MomentFock) :
    polynomialMomentFockThetaMomentFunctional m hm n f =
      iteratedDeriv n (polynomialMomentFockThetaTrace m hm f) 0 := by
  rw [iteratedDeriv_polynomialMomentFockThetaTrace_zero_eq_moment]
  change (∫ u : ℝ, polynomialMomentFockThetaMomentSource m hm f n u) = _
  apply integral_congr_ae
  filter_upwards with u
  unfold polynomialMomentFockThetaMomentSource polynomialMomentFockThetaSource
  ring

/-- Weighted-L¹ bound controlling theta traces in a fixed imaginary strip. -/
def polynomialMomentFockThetaTraceWeightBound (m A : ℝ) : ℝ :=
  ∫ u : ℝ, polynomialMomentFockThetaAbsWeightMajorant m A u

theorem polynomialMomentFockThetaTraceWeightBound_nonneg (m A : ℝ) :
    0 ≤ polynomialMomentFockThetaTraceWeightBound m A := by
  unfold polynomialMomentFockThetaTraceWeightBound
  exact integral_nonneg
    (fun u => polynomialMomentFockThetaAbsWeightMajorant_nonneg m A u)

theorem norm_polynomialMomentFockThetaTrace_le_weightBound
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) {A : ℝ}
    (hA : |(2 * (Real.pi : ℂ) * z).im| ≤ A) :
    ‖polynomialMomentFockThetaTrace m hm f z‖ ≤
      polynomialMomentFockThetaTraceWeightBound m A * ‖f‖ := by
  let w : ℂ := 2 * (Real.pi : ℂ) * z
  have hkernel : Integrable (fun u : ℝ =>
      polynomialMomentFockThetaSource m hm f u * Complex.exp (-(I * w * u))) :=
    integrable_expFourier_kernel'
      (aestronglyMeasurable_polynomialMomentFockThetaSource m hm f)
      ((allExpWeightIntegrable_polynomialMomentFockThetaSource m hm f).expWeightIntegrable
        (|w.im| + 1)) (by linarith)
  have hright : Integrable (fun u : ℝ =>
      ‖f‖ * polynomialMomentFockThetaAbsWeightMajorant m A u) :=
    (integrable_polynomialMomentFockThetaAbsWeightMajorant hm A).const_mul ‖f‖
  unfold polynomialMomentFockThetaTrace expFourier
  change ‖∫ u : ℝ,
      polynomialMomentFockThetaSource m hm f u * Complex.exp (-(I * w * u))‖ ≤ _
  calc
    ‖∫ u : ℝ,
        polynomialMomentFockThetaSource m hm f u * Complex.exp (-(I * w * u))‖ ≤
        ∫ u : ℝ,
          ‖polynomialMomentFockThetaSource m hm f u *
            Complex.exp (-(I * w * u))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ,
        ‖f‖ * polynomialMomentFockThetaAbsWeightMajorant m A u := by
      apply integral_mono hkernel.norm hright
      intro u
      have hcarrier := norm_polynomialMomentFockFunction_le_majorant hm f (u : ℂ)
      have him : w.im * u ≤ A * |u| := by
        calc
          w.im * u ≤ |w.im * u| := le_abs_self _
          _ = |w.im| * |u| := abs_mul _ _
          _ ≤ A * |u| := mul_le_mul_of_nonneg_right (by simpa [w] using hA) (abs_nonneg u)
      change ‖polynomialMomentFockThetaSource m hm f u *
        Complex.exp (-(I * w * u))‖ ≤ _
      rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
      unfold polynomialMomentFockThetaSource
      rw [norm_mul]
      have hmajorant0 :
          0 ≤ polynomialMomentFockEvaluationMajorant m (u : ℂ) := by
        unfold polynomialMomentFockEvaluationMajorant
        positivity
      calc
        (‖polynomialMomentFockFunction m hm f (u : ℂ)‖ * ‖xiThetaLogSource u‖) *
              Real.exp (w.im * u) ≤
            ((polynomialMomentFockEvaluationMajorant m (u : ℂ) * ‖f‖) *
              ‖xiThetaLogSource u‖) * Real.exp (w.im * u) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcarrier (norm_nonneg _)) (Real.exp_nonneg _)
        _ ≤
            ((polynomialMomentFockEvaluationMajorant m (u : ℂ) * ‖f‖) *
              ‖xiThetaLogSource u‖) * Real.exp (A * |u|) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him)
            (mul_nonneg (mul_nonneg hmajorant0 (norm_nonneg f)) (norm_nonneg _))
        _ = ‖f‖ * polynomialMomentFockThetaAbsWeightMajorant m A u := by
          unfold polynomialMomentFockThetaAbsWeightMajorant
          ring
    _ = polynomialMomentFockThetaTraceWeightBound m A * ‖f‖ := by
      rw [integral_const_mul]
      unfold polynomialMomentFockThetaTraceWeightBound
      ring

theorem polynomialMomentFockThetaTrace_add
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) (z : ℂ) :
    polynomialMomentFockThetaTrace m hm (f + g) z =
      polynomialMomentFockThetaTrace m hm f z +
        polynomialMomentFockThetaTrace m hm g z := by
  unfold polynomialMomentFockThetaTrace expFourier
  have hf := integrable_expFourier_kernel'
    (aestronglyMeasurable_polynomialMomentFockThetaSource m hm f)
    ((allExpWeightIntegrable_polynomialMomentFockThetaSource m hm f).expWeightIntegrable
      (|(2 * (Real.pi : ℂ) * z).im| + 1)) (by linarith)
  have hg := integrable_expFourier_kernel'
    (aestronglyMeasurable_polynomialMomentFockThetaSource m hm g)
    ((allExpWeightIntegrable_polynomialMomentFockThetaSource m hm g).expWeightIntegrable
      (|(2 * (Real.pi : ℂ) * z).im| + 1)) (by linarith)
  calc
    (∫ u : ℝ, polynomialMomentFockThetaSource m hm (f + g) u *
        Complex.exp (-(I * (2 * Real.pi * z) * u))) =
      ∫ u : ℝ,
        polynomialMomentFockThetaSource m hm f u *
            Complex.exp (-(I * (2 * Real.pi * z) * u)) +
          polynomialMomentFockThetaSource m hm g u *
            Complex.exp (-(I * (2 * Real.pi * z) * u)) := by
        apply integral_congr_ae
        filter_upwards with u
        have hsource : polynomialMomentFockThetaSource m hm (f + g) u =
            polynomialMomentFockThetaSource m hm f u +
              polynomialMomentFockThetaSource m hm g u := by
          simpa [polynomialMomentFockThetaMomentSource] using
            polynomialMomentFockThetaMomentSource_add m hm f g 0 u
        rw [hsource]
        ring
    _ = (∫ u : ℝ, polynomialMomentFockThetaSource m hm f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u))) +
        ∫ u : ℝ, polynomialMomentFockThetaSource m hm g u *
          Complex.exp (-(I * (2 * Real.pi * z) * u)) := integral_add hf hg

theorem polynomialMomentFockThetaTrace_smul
    (m : ℝ) (hm : 2 ≤ m) (c : ℂ) (f : MomentFock) (z : ℂ) :
    polynomialMomentFockThetaTrace m hm (c • f) z =
      c • polynomialMomentFockThetaTrace m hm f z := by
  unfold polynomialMomentFockThetaTrace expFourier
  calc
    (∫ u : ℝ, polynomialMomentFockThetaSource m hm (c • f) u *
        Complex.exp (-(I * (2 * Real.pi * z) * u))) =
      ∫ u : ℝ, c •
        (polynomialMomentFockThetaSource m hm f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u))) := by
        apply integral_congr_ae
        filter_upwards with u
        have hsource : polynomialMomentFockThetaSource m hm (c • f) u =
            c • polynomialMomentFockThetaSource m hm f u := by
          simpa [polynomialMomentFockThetaMomentSource] using
            polynomialMomentFockThetaMomentSource_smul m hm c f 0 u
        rw [hsource]
        simp only [smul_eq_mul]
        ring
    _ = c • ∫ u : ℝ, polynomialMomentFockThetaSource m hm f u *
          Complex.exp (-(I * (2 * Real.pi * z) * u)) := integral_smul c _

/-- Trace evaluation at a fixed complex point as a bounded functional on the Fock carrier. -/
def polynomialMomentFockThetaTraceLinearMap
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) : MomentFock →ₗ[ℂ] ℂ where
  toFun f := polynomialMomentFockThetaTrace m hm f z
  map_add' f g := polynomialMomentFockThetaTrace_add m hm f g z
  map_smul' c f := polynomialMomentFockThetaTrace_smul m hm c f z

def polynomialMomentFockThetaTraceFunctional
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) : MomentFock →L[ℂ] ℂ :=
  (polynomialMomentFockThetaTraceLinearMap m hm z).mkContinuous
    (polynomialMomentFockThetaTraceWeightBound m |(2 * (Real.pi : ℂ) * z).im|)
    (fun f => norm_polynomialMomentFockThetaTrace_le_weightBound m hm f z le_rfl)

theorem polynomialMomentFockThetaTraceFunctional_apply
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) (f : MomentFock) :
    polynomialMomentFockThetaTraceFunctional m hm z f =
      polynomialMomentFockThetaTrace m hm f z := rfl

theorem norm_polynomialMomentFockThetaTrace_le_verticalStrip
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) {R : ℝ}
    {z : ℂ} (hz : |z.im| ≤ R) :
    ‖polynomialMomentFockThetaTrace m hm f z‖ ≤
      polynomialMomentFockThetaTraceWeightBound m (2 * Real.pi * R) * ‖f‖ := by
  apply norm_polynomialMomentFockThetaTrace_le_weightBound m hm f z
  have him : (2 * (Real.pi : ℂ) * z).im = 2 * Real.pi * z.im := by
    simp [Complex.mul_im, Complex.mul_re]
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * Real.pi)

end

end RHTower
