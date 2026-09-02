import GaloisForLFunctions.RHTower.TCDCompleteStrictReflectedHankelRealRootednessNoGo
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds

open Real Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

def tcdUniformMeasure : Measure ℝ :=
  (centeredUniformClockProbabilityMeasure 1 : Measure ℝ)

instance : IsProbabilityMeasure tcdUniformMeasure := by
  unfold tcdUniformMeasure
  infer_instance

instance : NullSingletonClass tcdUniformMeasure := by
  constructor
  intro x
  rw [tcdUniformMeasure, centeredUniformClockProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : (fun u : ℝ => (1 : ℝ) * (2 * u - 1)) ⁻¹' {x} = {(x + 1) / 2} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, one_mul]
    constructor <;> intro h <;> linarith
  rw [hpre]
  change (volume.restrict (Ioc 0 1)) ({(x + 1) / 2} : Set ℝ) = 0
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left (measure_singleton _)

theorem ae_tcdUniformMeasure_mem_Icc :
    ∀ᵐ u ∂tcdUniformMeasure, u ∈ Icc (-1 : ℝ) 1 := by
  rw [tcdUniformMeasure, centeredUniformClockProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  refine (ae_map_iff (by fun_prop) measurableSet_Icc).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  constructor <;> linarith [hu.1, hu.2]

theorem map_neg_tcdUniformMeasure :
    Measure.map (fun u : ℝ => -u) tcdUniformMeasure = tcdUniformMeasure := by
  apply Measure.ext_of_charFun
  funext xi
  rw [charFun_apply_real (μ := Measure.map (fun u : ℝ => -u) tcdUniformMeasure)]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  calc
    (∫ u : ℝ, Complex.exp ((xi : ℂ) * ((-u : ℝ) : ℂ) * Complex.I)
        ∂tcdUniformMeasure) = charFun tcdUniformMeasure (-xi) := by
      rw [charFun_apply_real]
      apply integral_congr_ae
      filter_upwards with u
      congr 1
      push_cast
      ring
    _ = ((Real.sinc (1 * (-xi)) : ℝ) : ℂ) := by
      exact charFun_centeredUniformClockProbabilityMeasure 1 (-xi)
    _ = ((Real.sinc (1 * xi) : ℝ) : ℂ) := by simp [Real.sinc_neg]
    _ = charFun tcdUniformMeasure xi := by
      symm
      exact charFun_centeredUniformClockProbabilityMeasure 1 xi

def tcdUniformEntireSource (z : ℂ) : ℂ := complexMGF id tcdUniformMeasure z

def tcdUniformRealSource (x : ℝ) : ℝ := mgf id tcdUniformMeasure x

theorem analyticAt_tcdUniformEntireSource (z : ℂ) :
    AnalyticAt ℂ tcdUniformEntireSource z := by
  have h := analyticOnNhd_complexMGF_univ_of_bounded
    (μ := tcdUniformMeasure) (X := id) (a := (-1 : ℝ)) (b := 1)
    aemeasurable_id ae_tcdUniformMeasure_mem_Icc
  exact h z (mem_univ z)

theorem tcdUniformEntireSource_ofReal (x : ℝ) :
    tcdUniformEntireSource x = tcdUniformRealSource x := by
  unfold tcdUniformEntireSource tcdUniformRealSource complexMGF mgf
  calc
    (∫ u : ℝ, Complex.exp ((x : ℂ) * (u : ℂ)) ∂tcdUniformMeasure) =
        ∫ u : ℝ, ((Real.exp (x * u) : ℝ) : ℂ) ∂tcdUniformMeasure := by
          apply integral_congr_ae
          filter_upwards with u
          rw [← Complex.ofReal_mul, Complex.ofReal_exp]
    _ = ((∫ u : ℝ, Real.exp (x * u) ∂tcdUniformMeasure : ℝ) : ℂ) := by
          exact integral_ofReal

theorem tcdUniformRealSource_pos (x : ℝ) : 0 < tcdUniformRealSource x := by
  unfold tcdUniformRealSource
  apply integral_exp_pos
  exact integrable_exp_mul_of_mem_Icc aemeasurable_id
    ae_tcdUniformMeasure_mem_Icc

theorem tcdUniformEntireSource_nonreal_zero :
    tcdUniformEntireSource ((Real.pi : ℂ) * Complex.I) = 0 := by
  unfold tcdUniformEntireSource complexMGF
  calc
    (∫ u : ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ))
        ∂tcdUniformMeasure) = charFun tcdUniformMeasure Real.pi := by
      rw [charFun_apply_real]
      apply integral_congr_ae
      filter_upwards with u
      congr 1
      ring
    _ = ((Real.sinc (1 * Real.pi) : ℝ) : ℂ) := by
      exact charFun_centeredUniformClockProbabilityMeasure 1 Real.pi
    _ = 0 := by simp [Real.sinc, Real.sin_pi]

theorem tcdUniformEntireSource_even : Function.Even tcdUniformEntireSource := by
  intro z
  unfold tcdUniformEntireSource complexMGF
  calc
    (∫ u : ℝ, Complex.exp ((-z) * (u : ℂ)) ∂tcdUniformMeasure) =
        ∫ u : ℝ, Complex.exp (z * ((-u : ℝ) : ℂ)) ∂tcdUniformMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      congr 1
      push_cast
      ring
    _ = ∫ u : ℝ, Complex.exp (z * (u : ℂ))
        ∂(Measure.map (fun u : ℝ => -u) tcdUniformMeasure) := by
      symm
      rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ u : ℝ, Complex.exp (z * (u : ℂ)) ∂tcdUniformMeasure := by
      rw [map_neg_tcdUniformMeasure]

private theorem integrable_tcdUniform_complexExp (z : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (z * (u : ℂ))) tcdUniformMeasure := by
  refine Integrable.mono
    (integrable_const (c := ((Real.exp ‖z‖ : ℝ) : ℂ))) (by fun_prop) ?_
  filter_upwards [ae_tcdUniformMeasure_mem_Icc] with u hu
  have huabs : |u| ≤ 1 := abs_le.mpr hu
  have hre : z.re * u ≤ ‖z‖ := by
    calc
      z.re * u ≤ |z.re * u| := le_abs_self _
      _ = |z.re| * |u| := abs_mul _ _
      _ ≤ ‖z‖ * 1 := mul_le_mul (Complex.abs_re_le_norm z) huabs
        (abs_nonneg _) (norm_nonneg _)
      _ = ‖z‖ := mul_one _
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simpa using Real.exp_le_exp.mpr hre

theorem norm_tcdUniformEntireSource_le_exp_norm (z : ℂ) :
    ‖tcdUniformEntireSource z‖ ≤ Real.exp ‖z‖ := by
  unfold tcdUniformEntireSource complexMGF
  let f : ℝ → ℂ := fun u => Complex.exp (z * (u : ℂ))
  have hf : Integrable f tcdUniformMeasure := integrable_tcdUniform_complexExp z
  calc
    ‖∫ u : ℝ, f u ∂tcdUniformMeasure‖ ≤
        ∫ u : ℝ, ‖f u‖ ∂tcdUniformMeasure :=
      norm_integral_le_integral_norm f
    _ ≤ ∫ _ : ℝ, Real.exp ‖z‖ ∂tcdUniformMeasure := by
      have hg : Integrable (fun _ : ℝ => Real.exp ‖z‖) tcdUniformMeasure :=
        integrable_const (Real.exp ‖z‖)
      apply integral_mono_ae hf.norm hg
      filter_upwards [ae_tcdUniformMeasure_mem_Icc] with u hu
      have huabs : |u| ≤ 1 := abs_le.mpr hu
      have hre : z.re * u ≤ ‖z‖ := by
        calc
          z.re * u ≤ |z.re * u| := le_abs_self _
          _ = |z.re| * |u| := abs_mul _ _
          _ ≤ ‖z‖ * 1 := mul_le_mul (Complex.abs_re_le_norm z) huabs
            (abs_nonneg _) (norm_nonneg _)
          _ = ‖z‖ := mul_one _
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_exp.mpr hre
    _ = Real.exp ‖z‖ := by simp

def tcdUniformReflectedFamily : ReflectedExponentialFamily ℝ where
  base := tcdUniformMeasure
  isProb := by infer_instance
  reflection := fun u => -u
  measurable_reflection := by fun_prop
  reflection_involutive := by intro u; simp
  map_base := map_neg_tcdUniformMeasure
  stat := id
  measurable_stat := measurable_id
  stat_odd := by intro u; rfl

theorem integrable_tcdUniform_exp (x : ℝ) :
    Integrable (fun u : ℝ => Real.exp (x * u)) tcdUniformMeasure := by
  exact integrable_exp_mul_of_mem_Icc aemeasurable_id
    ae_tcdUniformMeasure_mem_Icc

def tcdUniformTiltMeasure (x : ℝ) : Measure ℝ :=
  tcdUniformReflectedFamily.tilt x

noncomputable instance tcdUniformTiltMeasure.instIsProbabilityMeasure (x : ℝ) :
    IsProbabilityMeasure (tcdUniformTiltMeasure x) := by
  unfold tcdUniformTiltMeasure
  exact tcdUniformReflectedFamily.isProbabilityMeasure_tilt x
    (integrable_tcdUniform_exp x)

noncomputable instance tcdUniformTiltMeasure.instNullSingletonClass (x : ℝ) :
    NullSingletonClass (tcdUniformTiltMeasure x) where
  measure_singleton y := by
    apply (tcdUniformReflectedFamily.tilt_absolutelyContinuous_base x)
    change tcdUniformMeasure {y} = 0
    exact measure_singleton y

def tcdUniformGapSquareNode (w : ℝ × ℝ) : ℝ := (w.1 - w.2) ^ 2

theorem tcdUniformGapSquareNode_fiber_countable (a y : ℝ) :
    {b : ℝ | tcdUniformGapSquareNode (a, b) = y}.Countable := by
  apply (by simp : ({a - Real.sqrt y, a + Real.sqrt y} : Set ℝ).Finite).countable.mono
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  unfold tcdUniformGapSquareNode at hb
  have hsqrt : Real.sqrt y = |a - b| := by
    rw [← hb, Real.sqrt_sq_eq_abs]
  by_cases hnonneg : 0 ≤ a - b
  · left
    rw [hsqrt, abs_of_nonneg hnonneg]
    ring
  · right
    rw [hsqrt, abs_of_nonpos (le_of_not_ge hnonneg)]
    ring

def tcdUniformGapSquareMeasure (x : ℝ) : Measure ℝ :=
  HTGeometry.observablePushforwardMeasure
    ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x))
    tcdUniformGapSquareNode

noncomputable instance tcdUniformGapSquareMeasure.instIsProbabilityMeasure (x : ℝ) :
    IsProbabilityMeasure (tcdUniformGapSquareMeasure x) := by
  unfold tcdUniformGapSquareMeasure HTGeometry.observablePushforwardMeasure
  exact Measure.isProbabilityMeasure_map (by
    unfold tcdUniformGapSquareNode
    fun_prop)

noncomputable instance tcdUniformGapSquareMeasure.instNullSingletonClass (x : ℝ) :
    NullSingletonClass (tcdUniformGapSquareMeasure x) := by
  unfold tcdUniformGapSquareMeasure HTGeometry.observablePushforwardMeasure
  exact nullSingletonClass_map_prod_of_countable_fibers
    (tcdUniformTiltMeasure x) (tcdUniformTiltMeasure x)
    tcdUniformGapSquareNode (by
      unfold tcdUniformGapSquareNode
      fun_prop)
    tcdUniformGapSquareNode_fiber_countable

theorem ae_tcdUniformTiltMeasure_mem_Icc (x : ℝ) :
    ∀ᵐ u ∂tcdUniformTiltMeasure x, u ∈ Icc (-1 : ℝ) 1 := by
  apply ae_tcdUniformMeasure_mem_Icc.filter_mono
  exact (tcdUniformReflectedFamily.tilt_absolutelyContinuous_base x).ae_le

private theorem ae_tcdUniformTiltMeasure_fst_mem_Icc (x : ℝ) :
    ∀ᵐ w ∂(tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x),
      w.1 ∈ Icc (-1 : ℝ) 1 := by
  have hzero : (tcdUniformTiltMeasure x) {u | u ∉ Icc (-1 : ℝ) 1} = 0 :=
    ae_iff.mp (ae_tcdUniformTiltMeasure_mem_Icc x)
  apply ae_iff.mpr
  have heq : {w : ℝ × ℝ | w.1 ∉ Icc (-1 : ℝ) 1} =
      {u : ℝ | u ∉ Icc (-1 : ℝ) 1} ×ˢ (Set.univ : Set ℝ) := by
    ext w
    simp
  rw [heq, Measure.prod_prod, hzero, zero_mul]

private theorem ae_tcdUniformTiltMeasure_snd_mem_Icc (x : ℝ) :
    ∀ᵐ w ∂(tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x),
      w.2 ∈ Icc (-1 : ℝ) 1 := by
  have hzero : (tcdUniformTiltMeasure x) {u | u ∉ Icc (-1 : ℝ) 1} = 0 :=
    ae_iff.mp (ae_tcdUniformTiltMeasure_mem_Icc x)
  apply ae_iff.mpr
  have heq : {w : ℝ × ℝ | w.2 ∉ Icc (-1 : ℝ) 1} =
      (Set.univ : Set ℝ) ×ˢ {u : ℝ | u ∉ Icc (-1 : ℝ) 1} := by
    ext w
    simp
  rw [heq, Measure.prod_prod, hzero, mul_zero]

private theorem integrable_tcdUniformGapSquareNode_pow (x : ℝ) (n : ℕ) :
    Integrable (fun w : ℝ × ℝ => tcdUniformGapSquareNode w ^ n)
      ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)) := by
  refine Integrable.mono (integrable_const (μ :=
      (tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)) (4 ^ n : ℝ))
    (by unfold tcdUniformGapSquareNode; fun_prop) ?_
  filter_upwards [ae_tcdUniformTiltMeasure_fst_mem_Icc x,
    ae_tcdUniformTiltMeasure_snd_mem_Icc x] with w hw1 hw2
  have h1 : |w.1| ≤ 1 := abs_le.mpr hw1
  have h2 : |w.2| ≤ 1 := abs_le.mpr hw2
  have hd : |w.1 - w.2| ≤ 2 := by
    calc
      |w.1 - w.2| ≤ |w.1| + |w.2| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hsabs : |w.1 - w.2| ^ 2 ≤ (2 : ℝ) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hd
  have hs : (w.1 - w.2) ^ 2 ≤ 4 := by
    norm_num at hsabs
    simpa [sq_abs] using hsabs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) n),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ n)]
  exact pow_le_pow_left₀ (sq_nonneg _) hs n

def tcdUniformGapSquareMoment (x : ℝ) (n : ℕ) : ℝ :=
  ∫ y : ℝ, y ^ n ∂tcdUniformGapSquareMeasure x

theorem integrable_tcdUniformGapSquareMoment (x : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n) (tcdUniformGapSquareMeasure x) := by
  unfold tcdUniformGapSquareMeasure
  exact HTGeometry.integrable_pow_observablePushforwardMeasure
    ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x))
    (by unfold tcdUniformGapSquareNode; fun_prop)
    (integrable_tcdUniformGapSquareNode_pow x n)

theorem tcdUniformGapSquareMoment_posDef (x : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix (tcdUniformGapSquareMoment x) n).PosDef := by
  apply HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (μ := tcdUniformGapSquareMeasure x) (tcdUniformGapSquareMoment x)
  · intro k
    rfl
  · exact integrable_tcdUniformGapSquareMoment x
  · intro F
    change 0 < (tcdUniformGapSquareMeasure x) ((↑F : Set ℝ)ᶜ)
    have hFzero : (tcdUniformGapSquareMeasure x) (↑F : Set ℝ) = 0 := by
      induction F using Finset.induction with
      | empty => simp
      | @insert a F ha ih =>
          rw [Finset.coe_insert, Set.insert_eq]
          exact measure_union_null (measure_singleton a) ih
    have hFtop : (tcdUniformGapSquareMeasure x) (↑F : Set ℝ) ≠ ∞ := by
      rw [hFzero]
      simp
    rw [measure_compl F.measurableSet hFtop, hFzero]
    simp

theorem mgf_tcdUniformTiltMeasure (x t : ℝ) :
    mgf id (tcdUniformTiltMeasure x) t =
      tcdUniformRealSource (x + t) / tcdUniformRealSource x := by
  unfold tcdUniformTiltMeasure ReflectedExponentialFamily.tilt
  rw [mgf, MeasureTheory.integral_tilted]
  unfold tcdUniformRealSource mgf
  let A : ℝ := ∫ u : ℝ, Real.exp (x * u) ∂tcdUniformMeasure
  let B : ℝ := ∫ u : ℝ, Real.exp ((x + t) * u) ∂tcdUniformMeasure
  change (∫ u : ℝ, (Real.exp (x * u) / A) • Real.exp (t * u)
      ∂tcdUniformMeasure) = B / A
  calc
    (∫ u : ℝ, (Real.exp (x * u) / A) • Real.exp (t * u)
        ∂tcdUniformMeasure) =
        ∫ u : ℝ, A⁻¹ * Real.exp ((x + t) * u) ∂tcdUniformMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      rw [smul_eq_mul]
      calc
        Real.exp (x * u) / A * Real.exp (t * u) =
            A⁻¹ * (Real.exp (x * u) * Real.exp (t * u)) := by ring
        _ = A⁻¹ * Real.exp ((x + t) * u) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
    _ = A⁻¹ * B := by rw [MeasureTheory.integral_const_mul]
    _ = B / A := by rw [div_eq_mul_inv]; ring

theorem mgf_tcdUniformGap_factor (x t : ℝ) :
    mgf (fun w : ℝ × ℝ => w.1 - w.2)
        ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)) t =
      mgf id (tcdUniformTiltMeasure x) t *
        mgf id (tcdUniformTiltMeasure x) (-t) := by
  unfold mgf
  rw [show (fun w : ℝ × ℝ => Real.exp (t * (w.1 - w.2))) =
      fun w : ℝ × ℝ => Real.exp (t * w.1) * Real.exp ((-t) * w.2) by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring]
  exact MeasureTheory.integral_prod_mul
    (fun u : ℝ => Real.exp (t * u))
    (fun v : ℝ => Real.exp ((-t) * v))

theorem tcdUniformReflected_product_identity (x t : ℝ) :
    tcdUniformRealSource (x + t) * tcdUniformRealSource (x - t) =
      tcdUniformRealSource x ^ 2 *
        mgf (fun w : ℝ × ℝ => w.1 - w.2)
          ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)) t := by
  rw [mgf_tcdUniformGap_factor,
    mgf_tcdUniformTiltMeasure, mgf_tcdUniformTiltMeasure]
  have hx : tcdUniformRealSource x ≠ 0 := ne_of_gt (tcdUniformRealSource_pos x)
  field_simp
  ring_nf

private theorem ae_tcdUniformGap_mem_Icc (x : ℝ) :
    ∀ᵐ w ∂(tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x),
      w.1 - w.2 ∈ Icc (-2 : ℝ) 2 := by
  filter_upwards [ae_tcdUniformTiltMeasure_fst_mem_Icc x,
    ae_tcdUniformTiltMeasure_snd_mem_Icc x] with w hw1 hw2
  constructor <;> linarith [hw1.1, hw1.2, hw2.1, hw2.2]

def tcdUniformReflectedMoment (x : ℝ) (n : ℕ) : ℝ :=
  tcdUniformRealSource x ^ 2 * tcdUniformGapSquareMoment x n

theorem tcdUniformGapSquareMoment_eq_evenGapJet (x : ℝ) (n : ℕ) :
    tcdUniformGapSquareMoment x n =
      iteratedDeriv (2 * n)
        (mgf (fun w : ℝ × ℝ => w.1 - w.2)
          ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x))) 0 := by
  let mu : Measure (ℝ × ℝ) :=
    (tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)
  let X : ℝ × ℝ → ℝ := fun w => w.1 - w.2
  have hset : integrableExpSet X mu = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_mem_Icc (by fun_prop)
      (ae_tcdUniformGap_mem_Icc x)
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X mu) := by
    rw [hset]
    simp
  have hderiv := iteratedDeriv_mgf_zero h0 (2 * n)
  rw [hderiv]
  unfold tcdUniformGapSquareMoment tcdUniformGapSquareMeasure
  rw [HTGeometry.integral_pow_observablePushforwardMeasure]
  · simp only [tcdUniformGapSquareNode]
    apply integral_congr_ae
    filter_upwards with w
    simp [X, pow_mul]
  · unfold tcdUniformGapSquareNode
    fun_prop

theorem tcdUniformReflectedMoment_eq_evenJet (x : ℝ) (n : ℕ) :
    tcdUniformReflectedMoment x n =
      iteratedDeriv (2 * n)
        (fun t : ℝ => tcdUniformRealSource (x + t) *
          tcdUniformRealSource (x - t)) 0 := by
  have hfun :
      (fun t : ℝ => tcdUniformRealSource (x + t) *
        tcdUniformRealSource (x - t)) =
      fun t : ℝ => tcdUniformRealSource x ^ 2 *
        mgf (fun w : ℝ × ℝ => w.1 - w.2)
          ((tcdUniformTiltMeasure x).prod (tcdUniformTiltMeasure x)) t := by
    funext t
    exact tcdUniformReflected_product_identity x t
  rw [hfun, iteratedDeriv_const_mul_field,
    ← tcdUniformGapSquareMoment_eq_evenGapJet]
  rfl

theorem tcdUniformReflectedMoment_posDef (x : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix (tcdUniformReflectedMoment x) n).PosDef := by
  have hmatrix :
      HTGeometry.momentHankelMatrix (tcdUniformReflectedMoment x) n =
        tcdUniformRealSource x ^ 2 •
          HTGeometry.momentHankelMatrix (tcdUniformGapSquareMoment x) n := by
    ext i j
    simp [HTGeometry.momentHankelMatrix, tcdUniformReflectedMoment]
  rw [hmatrix]
  exact (tcdUniformGapSquareMoment_posDef x n).smul
    (sq_pos_of_pos (tcdUniformRealSource_pos x))

theorem tcdUniform_strictReflectedEvenJetHankel_posDef (x : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun k : ℕ => iteratedDeriv (2 * k)
        (fun t : ℝ => tcdUniformRealSource (x + t) *
          tcdUniformRealSource (x - t)) 0) n).PosDef := by
  have hseq :
      (fun k : ℕ => iteratedDeriv (2 * k)
        (fun t : ℝ => tcdUniformRealSource (x + t) *
          tcdUniformRealSource (x - t)) 0) = tcdUniformReflectedMoment x := by
    funext k
    exact (tcdUniformReflectedMoment_eq_evenJet x k).symm
  rw [hseq]
  exact tcdUniformReflectedMoment_posDef x n

/-- Complete strict reflected-Hankel positivity, evenness, positivity on the real
axis, and exponential type do not imply that an entire function is real-rooted. -/
theorem completeStrictReflectedHankel_exponentialType_realRootedness_noGo :
    ∃ (F : ℂ → ℂ) (f : ℝ → ℝ),
      (∀ z : ℂ, AnalyticAt ℂ F z) ∧
      Function.Even F ∧
      (∀ z : ℂ, ‖F z‖ ≤ Real.exp ‖z‖) ∧
      (∀ x : ℝ, F x = f x) ∧
      (∀ x : ℝ, 0 < f x) ∧
      (∀ (x : ℝ) (n : ℕ),
        (HTGeometry.momentHankelMatrix
          (fun k : ℕ => iteratedDeriv (2 * k)
            (fun t : ℝ => f (x + t) * f (x - t)) 0) n).PosDef) ∧
      ¬ ∀ z : ℂ, F z = 0 → z.im = 0 := by
  refine ⟨tcdUniformEntireSource, tcdUniformRealSource,
    analyticAt_tcdUniformEntireSource, tcdUniformEntireSource_even,
    norm_tcdUniformEntireSource_le_exp_norm, tcdUniformEntireSource_ofReal,
    tcdUniformRealSource_pos, tcdUniform_strictReflectedEvenJetHankel_posDef, ?_⟩
  intro hreal
  have hpi := hreal ((Real.pi : ℂ) * Complex.I)
    tcdUniformEntireSource_nonreal_zero
  simp at hpi

end

end RHTower
