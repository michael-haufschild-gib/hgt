import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity
import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence

/-!
# Radial Poisson mixtures in continuous circle-density space

This module packages the radial Poisson kernels on a compact subinterval of the unit disk as
continuous real functions on the circle. It proves joint parameter continuity, exact Fourier
moments, Bochner-barycenter formulas, closed-convex-hull membership, and the continuous Hankel
half-space separation needed to recognize the reflected moment cone.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev RadialPoissonParameter (R : ℝ) := Set.Icc (0 : ℝ) R

/-- Continuous projection of the real line onto a nonempty radial aperture. -/
def clampRadialPoissonParameter {R : ℝ} (hR0 : 0 ≤ R) (x : ℝ) :
    RadialPoissonParameter R :=
  ⟨max 0 (min R x),
    ⟨le_max_left _ _, max_le hR0 (min_le_left _ _)⟩⟩

theorem continuous_clampRadialPoissonParameter {R : ℝ} (hR0 : 0 ≤ R) :
    Continuous (clampRadialPoissonParameter hR0) := by
  apply Continuous.subtype_mk
  fun_prop

theorem clampRadialPoissonParameter_eq_of_mem {R : ℝ} (hR0 : 0 ≤ R)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) R) :
    (clampRadialPoissonParameter hR0 x : ℝ) = x := by
  simp [clampRadialPoissonParameter, min_eq_right hx.2, max_eq_right hx.1]

theorem symmetricCircleFourierDensity_div
    {a : ℕ → ℝ} (ha : Summable fun n : ℕ => |a (n + 1)|)
    {c : ℝ} (hc : c ≠ 0) (z : Circle) :
    symmetricCircleFourierDensity (fun n => a n / c) z =
      symmetricCircleFourierDensity a z / c := by
  rw [symmetricCircleFourierDensity, symmetricCircleFourierDensity]
  have hs := summable_symmetricCircleFourierDensity_terms ha z
  have htail : (∑' n : ℕ,
      a (n + 1) / c * ((z : ℂ) ^ (n + 1)).re) =
      (∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re) / c := by
    calc
      _ = ∑' n : ℕ,
          (a (n + 1) * ((z : ℂ) ^ (n + 1)).re) * c⁻¹ := by
        apply tsum_congr
        intro n
        rw [div_eq_mul_inv]
        ring
      _ = (∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re) * c⁻¹ := by
        rw [tsum_mul_right]
      _ = _ := by rw [div_eq_mul_inv]
  rw [htail]
  field_simp [hc]

def radialToCirclePoissonParameter {R : ℝ} (hR : R < 1)
    (r : RadialPoissonParameter R) : CirclePoissonParameter :=
  ⟨(r : ℝ), by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg r.2.1]
    exact r.2.2.trans_lt hR⟩

def radialPoissonKernel {R : ℝ} (hR : R < 1)
    (r : RadialPoissonParameter R) : C(Circle, ℝ) :=
  ⟨fun z => poissonKernel 0
      (radialToCirclePoissonParameter hR r : ℂ) (z : ℂ),
    continuous_circlePoissonDensity_real (radialToCirclePoissonParameter hR r)⟩

theorem continuous_radialPoissonKernel {R : ℝ} (hR : R < 1) :
    Continuous (radialPoissonKernel hR :
      RadialPoissonParameter R → C(Circle, ℝ)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun p : RadialPoissonParameter R × Circle =>
    poissonKernel 0 (p.1 : ℝ) (p.2 : ℂ)
  simp_rw [poissonKernel_def, sub_zero]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    rw [pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff, sub_ne_zero]
    intro h
    have hn := congrArg norm h
    simp only [Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg p.1.2.1] at hn
    exact (p.1.2.2.trans_lt hR).ne hn.symm

theorem isCompact_range_radialPoissonKernel {R : ℝ} (hR : R < 1) :
    IsCompact (Set.range (radialPoissonKernel hR)) := by
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_radialPoissonKernel hR)

theorem radialPoissonKernel_nonneg {R : ℝ} (hR : R < 1)
    (r : RadialPoissonParameter R) (z : Circle) :
    0 ≤ radialPoissonKernel hR r z :=
  circlePoissonDensity_nonneg (radialToCirclePoissonParameter hR r) z

/-- Absolute Fourier expansion of every radial Poisson kernel. -/
theorem radialPoissonKernel_eq_one_add_two_tsum
    {R : ℝ} (hR : R < 1) (r : RadialPoissonParameter R) (z : Circle) :
    radialPoissonKernel hR r z = 1 + 2 * ∑' n : ℕ,
      (r : ℝ) ^ (n + 1) * ((z : ℂ) ^ (n + 1)).re := by
  let x : ℂ := ((r : ℝ) : ℂ) * (z : ℂ)⁻¹
  have hxnorm : ‖x‖ < 1 := by
    dsimp only [x]
    rw [norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.2.1]
    exact r.2.2.trans_lt hR
  have hgeo : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_norm_lt_one hxnorm
  have htail : Summable (fun n : ℕ => x ^ (n + 1)) := by
    exact (hgeo.mul_left x).congr fun n => by rw [pow_succ']
  have htsum : ∑' n : ℕ, x ^ (n + 1) = x / (1 - x) := by
    calc
      ∑' n : ℕ, x ^ (n + 1) = x * ∑' n : ℕ, x ^ n := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ']
      _ = x / (1 - x) := by
        rw [tsum_geometric_of_norm_lt_one hxnorm, div_eq_mul_inv]
  have hterm (n : ℕ) :
      (x ^ (n + 1)).re =
        (r : ℝ) ^ (n + 1) * ((z : ℂ) ^ (n + 1)).re := by
    dsimp only [x]
    rw [mul_pow, Complex.inv_eq_conj (Circle.norm_coe z), ← map_pow]
    rw [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re]
    ring
  have hre := Complex.reCLM.map_tsum htail
  have hre' : (∑' n : ℕ,
      (r : ℝ) ^ (n + 1) * ((z : ℂ) ^ (n + 1)).re) =
      (∑' n : ℕ, x ^ (n + 1)).re := by
    calc
      _ = ∑' n : ℕ, (x ^ (n + 1)).re := by
        apply tsum_congr
        intro n
        exact (hterm n).symm
      _ = _ := hre.symm
  change poissonKernel 0 ((r : ℝ) : ℂ) (z : ℂ) = _
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simp only [Function.comp_apply, herglotzRieszKernel, sub_zero]
  rw [hre', htsum]
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hden : 1 - x ≠ 0 := by
    rw [sub_ne_zero]
    intro hx
    rw [← hx, norm_one] at hxnorm
    exact lt_irrefl 1 hxnorm
  have hzr : (z : ℂ) - ((r : ℝ) : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hn := congrArg norm heq
    rw [Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.2.1] at hn
    exact (r.2.2.trans_lt hR).ne hn.symm
  have hratio : ((z : ℂ) + (r : ℝ)) / ((z : ℂ) - (r : ℝ)) =
      1 + 2 * (x / (1 - x)) := by
    dsimp only [x]
    field_simp [hz, hden, hzr]
    ring
  rw [hratio]
  norm_num [Complex.mul_re]

theorem integral_radialPoissonKernel_mul_coe_pow
    {R : ℝ} (hR : R < 1) (r : RadialPoissonParameter R) (n : ℕ) :
    (∫ z : Circle, (radialPoissonKernel hR r z : ℂ) * (z : ℂ) ^ n
        ∂circleLebesgue) = ((r : ℝ) : ℂ) ^ n := by
  let a := radialToCirclePoissonParameter hR r
  have hdens : AEMeasurable (circlePoissonDensity a) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp
      (continuous_circlePoissonDensity_real a)).measurable.aemeasurable
  have htop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity a z < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hwith := integral_withDensity_eq_integral_toReal_smul₀ hdens htop
    (fun z : Circle => (z : ℂ) ^ n)
  calc
    (∫ z : Circle, (radialPoissonKernel hR r z : ℂ) * (z : ℂ) ^ n
        ∂circleLebesgue) =
        ∫ z : Circle, (circlePoissonDensity a z).toReal • (z : ℂ) ^ n
          ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards with z
      rw [circlePoissonDensity, ENNReal.toReal_ofReal
        (circlePoissonDensity_nonneg a z)]
      change (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) * (z : ℂ) ^ n = _
      rw [Complex.real_smul]
    _ = ∫ z : Circle, (z : ℂ) ^ n ∂(circlePoissonMeasure a) := by
      rw [circlePoissonMeasure]
      exact hwith.symm
    _ = (a : ℂ) ^ n := integral_circlePoissonMeasure_coe_pow a n
    _ = ((r : ℝ) : ℂ) ^ n := rfl

/-- Fourier-coefficient evaluation as a bounded real-linear functional on circle densities. -/
def realContinuousCircleFourierMomentCLM (n : ℕ) :
    C(Circle, ℝ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z : Circle, (f z : ℂ) * (z : ℂ) ^ n ∂circleLebesgue
      map_add' := by
        intro f g
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards with z
          simp only [ContinuousMap.add_apply, Complex.ofReal_add]
          ring
        · exact (show Continuous fun z : Circle => (f z : ℂ) * (z : ℂ) ^ n by
            fun_prop).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (show Continuous fun z : Circle => (g z : ℂ) * (z : ℂ) ^ n by
            fun_prop).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with z
        simp [Complex.real_smul]
        ring }
    1
    (fun f => by
      have h : ‖∫ z : Circle, (f z : ℂ) * (z : ℂ) ^ n ∂circleLebesgue‖ ≤
          ‖f‖ * circleLebesgue.real Set.univ :=
        norm_integral_le_of_norm_le_const (μ := circleLebesgue)
        (show ∀ᵐ z : Circle ∂circleLebesgue,
            ‖(f z : ℂ) * (z : ℂ) ^ n‖ ≤ ‖f‖ from
          Filter.Eventually.of_forall fun z => by
          rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one]
          simpa [Complex.norm_real, Real.norm_eq_abs] using f.norm_coe_le_norm z)
      simpa using h)

@[simp] theorem realContinuousCircleFourierMomentCLM_apply
    (n : ℕ) (f : C(Circle, ℝ)) :
    realContinuousCircleFourierMomentCLM n f =
      ∫ z : Circle, (f z : ℂ) * (z : ℂ) ^ n ∂circleLebesgue := rfl

theorem integrable_radialPoissonKernel {R : ℝ} (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) [IsFiniteMeasure ν] :
    Integrable (radialPoissonKernel hR) ν :=
  (continuous_radialPoissonKernel hR).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Uniform-norm Bochner barycenter of radial Poisson kernels. -/
def radialPoissonBarycenter {R : ℝ} (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) : C(Circle, ℝ) :=
  ∫ r, radialPoissonKernel hR r ∂ν

theorem radialPoissonBarycenter_apply {R : ℝ} (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) [IsFiniteMeasure ν]
    (z : Circle) :
    radialPoissonBarycenter hR ν z =
      ∫ r, radialPoissonKernel hR r z ∂ν := by
  have h := ContinuousLinearMap.integral_comp_comm
    (ContinuousMap.evalCLM ℝ z) (integrable_radialPoissonKernel hR ν)
  exact h.symm

/-- A radial Poisson barycenter is exactly the symmetric Fourier density of the radial power
moments, with convergence in uniform norm. -/
theorem radialPoissonBarycenter_eq_symmetricCircleFourierDensity_moments
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) [IsProbabilityMeasure ν]
    (z : Circle) :
    radialPoissonBarycenter hR ν z =
      symmetricCircleFourierDensity
        (fun n => ∫ r, (r : ℝ) ^ n ∂ν) z := by
  let F : ℕ → RadialPoissonParameter R → ℝ := fun n r =>
    (r : ℝ) ^ (n + 1) * ((z : ℂ) ^ (n + 1)).re
  have hFint : ∀ n, Integrable (F n) ν := by
    intro n
    exact (show Continuous (F n) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFbound (n : ℕ) :
      ∫ r, ‖F n r‖ ∂ν ≤ R ^ (n + 1) := by
    calc
      ∫ r, ‖F n r‖ ∂ν ≤ ∫ _r, R ^ (n + 1) ∂ν := by
        apply integral_mono_ae (hFint n).norm (integrable_const _)
        exact Filter.Eventually.of_forall fun r => by
          dsimp only [F]
          rw [Real.norm_eq_abs, abs_mul]
          calc
            |(r : ℝ) ^ (n + 1)| * |((z : ℂ) ^ (n + 1)).re| ≤
                (r : ℝ) ^ (n + 1) * 1 := by
              rw [abs_pow, abs_of_nonneg r.2.1]
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg r.2.1 _)
              calc
                |((z : ℂ) ^ (n + 1)).re| ≤ ‖(z : ℂ) ^ (n + 1)‖ :=
                  abs_re_le_norm _
                _ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
            _ ≤ R ^ (n + 1) := by
              simpa using pow_le_pow_left₀ r.2.1 r.2.2 (n + 1)
      _ = R ^ (n + 1) := by simp
  have hgeoTail : Summable (fun n : ℕ => R ^ (n + 1)) := by
    exact ((summable_geometric_of_lt_one hR0 hR).mul_left R).congr
      fun n => by rw [pow_succ']
  have hFsum : Summable (fun n : ℕ => ∫ r, ‖F n r‖ ∂ν) :=
    Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _)
      hFbound hgeoTail
  have hIntegralTsum :
      ∫ r, ∑' n : ℕ, F n r ∂ν =
        ∑' n : ℕ, ∫ r, F n r ∂ν :=
    (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  have htailIntegrable : Integrable (fun r => ∑' n : ℕ, F n r) ν := by
    have hpoint : (fun r => ∑' n : ℕ, F n r) =
        fun r => (radialPoissonKernel hR r z - 1) / 2 := by
      funext r
      have h := radialPoissonKernel_eq_one_add_two_tsum hR r z
      change radialPoissonKernel hR r z = 1 + 2 * ∑' n : ℕ, F n r at h
      linarith
    rw [hpoint]
    exact (((ContinuousMap.evalCLM ℝ z).continuous.comp
      (continuous_radialPoissonKernel hR)).sub continuous_const |>.div_const 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [radialPoissonBarycenter_apply]
  calc
    ∫ r, radialPoissonKernel hR r z ∂ν =
        ∫ r, (1 + 2 * ∑' n : ℕ, F n r) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r =>
        radialPoissonKernel_eq_one_add_two_tsum hR r z
    _ = 1 + 2 * ∫ r, ∑' n : ℕ, F n r ∂ν := by
      rw [integral_add (integrable_const 1) (htailIntegrable.const_mul 2),
        integral_const, probReal_univ, one_smul,
        integral_const_mul]
    _ = 1 + 2 * ∑' n : ℕ, ∫ r, F n r ∂ν := by rw [hIntegralTsum]
    _ = symmetricCircleFourierDensity
        (fun n => ∫ r, (r : ℝ) ^ n ∂ν) z := by
      rw [symmetricCircleFourierDensity]
      simp only [pow_zero, integral_const, probReal_univ, one_smul]
      congr 2
      apply tsum_congr
      intro n
      dsimp only [F]
      rw [integral_mul_const]

/-- Every nonnegative Fourier coefficient of a radial Poisson barycenter is the corresponding
power moment of its radial law. -/
theorem integral_radialPoissonBarycenter_mul_coe_pow
    {R : ℝ} (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) [IsFiniteMeasure ν]
    (n : ℕ) :
    (∫ z : Circle, (radialPoissonBarycenter hR ν z : ℂ) * (z : ℂ) ^ n
        ∂circleLebesgue) =
      ∫ r, (((r : ℝ) : ℂ) ^ n) ∂ν := by
  rw [← realContinuousCircleFourierMomentCLM_apply]
  rw [radialPoissonBarycenter]
  have hcomm := ContinuousLinearMap.integral_comp_comm
    (realContinuousCircleFourierMomentCLM n)
    (integrable_radialPoissonKernel hR ν)
  rw [← hcomm]
  apply integral_congr_ae
  filter_upwards with r
  exact integral_radialPoissonKernel_mul_coe_pow hR r n

/-- Reflected finite Hankel form as a bounded functional of a continuous circle density. -/
def circleDensityHankelFormCLM {n : ℕ} (v : Fin n → ℝ) :
    C(Circle, ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (v i * v j) •
      (Complex.reCLM.comp (realContinuousCircleFourierMomentCLM
        ((i : ℕ) + (j : ℕ))))

theorem circleDensityHankelFormCLM_apply {n : ℕ} (v : Fin n → ℝ)
    (f : C(Circle, ℝ)) :
    circleDensityHankelFormCLM v f =
      ∑ i : Fin n, ∑ j : Fin n, v i * v j *
        (∫ z : Circle, (f z : ℂ) * (z : ℂ) ^ ((i : ℕ) + (j : ℕ))
          ∂circleLebesgue).re := by
  simp [circleDensityHankelFormCLM, mul_assoc]

theorem circleDensityHankelFormCLM_radialPoissonKernel
    {R : ℝ} (hR : R < 1) {n : ℕ} (v : Fin n → ℝ)
    (r : RadialPoissonParameter R) :
    circleDensityHankelFormCLM v (radialPoissonKernel hR r) =
      (∑ i : Fin n, v i * (r : ℝ) ^ (i : ℕ)) ^ 2 := by
  rw [circleDensityHankelFormCLM_apply]
  simp_rw [integral_radialPoissonKernel_mul_coe_pow hR r]
  have hpow (k : ℕ) : ((((r : ℝ) : ℂ) ^ k).re) = (r : ℝ) ^ k := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [hpow]
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

theorem radialPoissonBarycenter_mem_closedConvexHull
    {R : ℝ} (hR : R < 1)
    (ν : Measure (RadialPoissonParameter R)) [IsProbabilityMeasure ν] :
    radialPoissonBarycenter hR ν ∈
      closedConvexHull ℝ (Set.range (radialPoissonKernel hR)) := by
  apply Convex.integral_mem convex_closedConvexHull isClosed_closedConvexHull
  · exact Filter.Eventually.of_forall fun r =>
      subset_closedConvexHull (Set.mem_range_self r)
  · exact integrable_radialPoissonKernel hR ν

theorem circleDensityHankelFormCLM_nonneg_of_mem_closedConvexHull
    {R : ℝ} (hR : R < 1) {n : ℕ} (v : Fin n → ℝ)
    {f : C(Circle, ℝ)}
    (hf : f ∈ closedConvexHull ℝ (Set.range (radialPoissonKernel hR))) :
    0 ≤ circleDensityHankelFormCLM v f := by
  let H : Set C(Circle, ℝ) := {g | 0 ≤ circleDensityHankelFormCLM v g}
  have hrange : Set.range (radialPoissonKernel hR) ⊆ H := by
    rintro _ ⟨r, rfl⟩
    change 0 ≤ circleDensityHankelFormCLM v (radialPoissonKernel hR r)
    rw [circleDensityHankelFormCLM_radialPoissonKernel]
    exact sq_nonneg _
  have hconv : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ circleDensityHankelFormCLM v x at hx
    change 0 ≤ circleDensityHankelFormCLM v y at hy
    change 0 ≤ circleDensityHankelFormCLM v (a • x + b • y)
    rw [map_add, map_smul, map_smul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hclosed : IsClosed H := by
    exact isClosed_le continuous_const (circleDensityHankelFormCLM v).continuous
  exact closedConvexHull_min hrange hconv hclosed hf

end

end GaloisForLFunctions.HTGeometry

