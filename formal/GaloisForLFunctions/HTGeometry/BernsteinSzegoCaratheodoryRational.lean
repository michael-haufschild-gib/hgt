import GaloisForLFunctions.HTGeometry.CircleCaratheodoryApproximation
import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Rational Carathéodory transforms of Bernstein--Szegő laws

This module supplies the rational/differential-algebraic half of the cofinal boundary card.  The
key finite-order fact is stronger than ordinary OPUC orthogonality: for a Bernstein--Szegő weight,
the terminal OPUC polynomial remains orthogonal after multiplication by every nonnegative
monomial.  This gives a constant-coefficient recurrence for the complete Fourier tail and hence a
rational Carathéodory series with the reversed OPUC polynomial as denominator.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial MeasureTheory Filter Topology Set
open scoped ComplexConjugate ComplexOrder BigOperators Topology

noncomputable section

/-- The terminal Bernstein--Szegő polynomial is orthogonal to every nonnegative forward shift,
not only to the finite lower monomials used in the prefix theorem. -/
theorem bernsteinSzego_polynomial_forwardShift_orthogonal
    {N : ℕ} (hN : 0 < N) (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (k : ℕ) :
    Real.circleAverage
        (fun z : ℂ => (finiteOPUCPolynomial c hG).eval z * z ^ k *
          bernsteinSzegoComplexWeight c hG z) 0 1 = 0 := by
  rw [Real.circleAverage_congr_sphere (f₂ := fun z : ℂ =>
    z ^ (N + k) * ((finiteOPUCReversedPolynomial c hG).eval z)⁻¹) (by
      intro z hz
      have hznorm : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hbase := bernsteinSzego_monomial_integrand_identity
        (show 0 ≤ N from Nat.zero_le N) c hG hznorm
      simp only [pow_zero, star_one, mul_one, Nat.sub_zero] at hbase
      change
        (finiteOPUCPolynomial c hG).eval z * z ^ k *
            (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹ = _
      calc
        (finiteOPUCPolynomial c hG).eval z * z ^ k *
            (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹ =
          z ^ k * ((finiteOPUCPolynomial c hG).eval z *
            (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹) := by ring
        _ = z ^ k * (z ^ N * ((finiteOPUCReversedPolynomial c hG).eval z)⁻¹) := by
          rw [hbase]
        _ = z ^ (N + k) * ((finiteOPUCReversedPolynomial c hG).eval z)⁻¹ := by
          rw [pow_add]
          ring)]
  rw [polynomial_power_div_circleAverage]
  · have hNk : N + k ≠ 0 := Nat.ne_of_gt (Nat.add_pos_left hN k)
    rw [zero_pow hNk, zero_mul]
  · intro z hz
    exact finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG hz

/-- The reversed terminal polynomial annihilates every sufficiently deep positive Fourier
coordinate of the Bernstein--Szegő moment sequence. -/
theorem bernsteinSzego_reversedPolynomial_tail_orthogonal
    {N : ℕ} (hN : 0 < N) (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) {n : ℕ} (hn : N < n) :
    Real.circleAverage
        (fun z : ℂ => (finiteOPUCReversedPolynomial c hG).eval z *
          z ^ (-(n : ℤ)) * bernsteinSzegoComplexWeight c hG z) 0 1 = 0 := by
  let p := finiteOPUCPolynomial c hG
  let q := finiteOPUCReversedPolynomial c hG
  let k := n - N
  let f : ℂ → ℂ := fun z => p.eval z * z ^ k * bernsteinSzegoComplexWeight c hG z
  have hf : CircleIntegrable f 0 1 := by
    apply ContinuousOn.circleIntegrable zero_le_one
    exact (((p.continuous.comp continuous_id).mul (continuous_id.pow k)).continuousOn.mul
      (bernsteinSzegoComplexWeight_continuousOn_sphere c hG))
  calc
    Real.circleAverage
        (fun z : ℂ => q.eval z * z ^ (-(n : ℤ)) *
          bernsteinSzegoComplexWeight c hG z) 0 1 =
      Real.circleAverage (fun z : ℂ => star (f z)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hznorm : ‖z‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using hz
        have heval : q.eval z = z ^ N * star (p.eval z) := by
          exact finiteOPUCReversedPolynomial_eval_unitCircle c hG hznorm
        have hzneg : z ^ (-(n : ℤ)) = star (z ^ n) := by
          simpa using unitCircle_zpow_neg_sub n 0 hznorm
        have hdecomp : N + k = n := by
          exact Nat.add_sub_of_le hn.le
        have hunit : z ^ N * star (z ^ N) = 1 := by
          change z ^ N * (starRingEnd ℂ) (z ^ N) = 1
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hznorm]
          norm_num
        have hpow : z ^ N * z ^ (-(n : ℤ)) = star (z ^ k) := by
          rw [hzneg, ← hdecomp, pow_add]
          change z ^ N * (starRingEnd ℂ) (z ^ N * z ^ k) = star (z ^ k)
          rw [map_mul]
          calc
            z ^ N * (star (z ^ N) * star (z ^ k)) =
                (z ^ N * star (z ^ N)) * star (z ^ k) := by ring
            _ = star (z ^ k) := by rw [hunit, one_mul]
        have hweight : star (bernsteinSzegoComplexWeight c hG z) =
            bernsteinSzegoComplexWeight c hG z := by
          simp [bernsteinSzegoComplexWeight]
        change q.eval z * z ^ (-(n : ℤ)) * bernsteinSzegoComplexWeight c hG z =
          star (p.eval z * z ^ k * bernsteinSzegoComplexWeight c hG z)
        rw [heval, star_mul, star_mul, hweight]
        calc
          z ^ N * star (p.eval z) * z ^ (-(n : ℤ)) *
              bernsteinSzegoComplexWeight c hG z =
            (z ^ N * z ^ (-(n : ℤ))) * star (p.eval z) *
              bernsteinSzegoComplexWeight c hG z := by ring
          _ = star (z ^ k) * star (p.eval z) *
              bernsteinSzegoComplexWeight c hG z := by rw [hpow]
          _ = bernsteinSzegoComplexWeight c hG z * star (z ^ k) *
              star (p.eval z) := by ring
          _ = bernsteinSzegoComplexWeight c hG z *
              (star (z ^ k) * star (p.eval z)) := by ring
    _ = star (Real.circleAverage f 0 1) := by
      have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).circleAverage_comp_comm hf
      simpa only [Function.comp_apply] using hcomm
    _ = 0 := by
      rw [bernsteinSzego_polynomial_forwardShift_orthogonal hN c hG k]
      simp

/-- Complete autoregressive recurrence for the positive Fourier tail.  The coefficients are those
of the reversed terminal OPUC polynomial, and the recurrence starts strictly beyond the original
Toeplitz depth. -/
theorem bernsteinSzegoMoment_reversedPolynomial_recurrence
    {N : ℕ} (hN : 0 < N) (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) {n : ℕ} (hn : N < n) :
    ∑ j ∈ Finset.range ((finiteOPUCReversedPolynomial c hG).natDegree + 1),
        (finiteOPUCReversedPolynomial c hG).coeff j *
          bernsteinSzegoMoment c hG ((n - j : ℕ) : ℤ) = 0 := by
  let q := finiteOPUCReversedPolynomial c hG
  have hqdeg : q.natDegree ≤ N := by
    calc
      q.natDegree ≤ ((finiteOPUCPolynomial c hG).map (starRingEnd ℂ)).natDegree := by
        exact Polynomial.reverse_natDegree_le _
      _ ≤ (finiteOPUCPolynomial c hG).natDegree := natDegree_map_le
      _ = N := finiteOPUCPolynomial_natDegree c hG
  have hjle : ∀ j ∈ Finset.range (q.natDegree + 1), j ≤ n := by
    intro j hj
    have hjq : j ≤ q.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact hjq.trans (hqdeg.trans hn.le)
  have htermInt : ∀ j ∈ Finset.range (q.natDegree + 1),
      CircleIntegrable
        (fun z : ℂ => q.coeff j *
          (z ^ (-((n - j : ℕ) : ℤ)) * bernsteinSzegoComplexWeight c hG z)) 0 1 := by
    intro j hj
    apply ContinuousOn.circleIntegrable zero_le_one
    have hpow : ContinuousOn (fun z : ℂ => z ^ (-((n - j : ℕ) : ℤ)))
        (Metric.sphere (0 : ℂ) 1) := by
      apply (continuousOn_zpow₀ (-((n - j : ℕ) : ℤ))).mono
      intro z hz
      have : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      exact norm_ne_zero_iff.mp (by simp [this])
    exact continuousOn_const.mul
      (hpow.mul (bernsteinSzegoComplexWeight_continuousOn_sphere c hG))
  calc
    (∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j *
        bernsteinSzegoMoment c hG ((n - j : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (q.natDegree + 1),
        Real.circleAverage
          (fun z : ℂ => q.coeff j *
            (z ^ (-((n - j : ℕ) : ℤ)) * bernsteinSzegoComplexWeight c hG z)) 0 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [bernsteinSzegoMoment]
        change q.coeff j • Real.circleAverage
            (fun z : ℂ => z ^ (-((n - j : ℕ) : ℤ)) *
              bernsteinSzegoComplexWeight c hG z) 0 1 = _
        rw [← Real.circleAverage_fun_smul]
        rfl
    _ = Real.circleAverage
        (fun z : ℂ => ∑ j ∈ Finset.range (q.natDegree + 1),
          q.coeff j *
            (z ^ (-((n - j : ℕ) : ℤ)) * bernsteinSzegoComplexWeight c hG z)) 0 1 := by
      rw [Real.circleAverage_fun_sum]
      intro j hj
      exact htermInt j hj
    _ = Real.circleAverage
        (fun z : ℂ => q.eval z * z ^ (-(n : ℤ)) *
          bernsteinSzegoComplexWeight c hG z) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hznorm : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hznorm])
      change (∑ j ∈ Finset.range (q.natDegree + 1),
        q.coeff j * (z ^ (-((n - j : ℕ) : ℤ)) *
          bernsteinSzegoComplexWeight c hG z)) =
        q.eval z * z ^ (-(n : ℤ)) * bernsteinSzegoComplexWeight c hG z
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := hjle j hj
      have hpow : z ^ (-((n - j : ℕ) : ℤ)) = z ^ j * z ^ (-(n : ℤ)) := by
        rw [← zpow_natCast]
        rw [← zpow_add₀ hz0]
        congr 1
        omega
      rw [hpow]
      ring
    _ = 0 := bernsteinSzego_reversedPolynomial_tail_orthogonal hN c hG hn

/-- Taylor coefficients of the normalized circle Carathéodory transform. -/
def circleCaratheodorySeriesCoefficient (mu : Measure Circle) (n : ℕ) : ℂ :=
  if n = 0 then 1 else 2 * circleMeasureMomentZ mu (n : ℤ)

/-- Fourier moments of a circle probability law have modulus at most one. -/
theorem norm_circleMeasureMomentZ_le_one_probability
    (mu : ProbabilityMeasure Circle) (q : ℤ) :
    ‖circleMeasureMomentZ (mu : Measure Circle) q‖ ≤ 1 := by
  unfold circleMeasureMomentZ
  calc
    ‖∫ z : Circle, (z : ℂ) ^ (-q) ∂(mu : Measure Circle)‖ ≤
        1 * (mu : Measure Circle).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z => by
        simp [norm_zpow])
    _ = 1 := by simp

/-- Uniform coefficient bound for every probability-law Carathéodory series. -/
theorem norm_circleCaratheodorySeriesCoefficient_le_two
    (mu : ProbabilityMeasure Circle) (n : ℕ) :
    ‖circleCaratheodorySeriesCoefficient (mu : Measure Circle) n‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [circleCaratheodorySeriesCoefficient, hn]
  · rw [circleCaratheodorySeriesCoefficient, if_neg hn, norm_mul]
    simpa using mul_le_mul_of_nonneg_left
      (norm_circleMeasureMomentZ_le_one_probability mu (n : ℤ)) (by norm_num : (0 : ℝ) ≤ 2)

/-- The Carathéodory moment series is absolutely summable throughout the open disk. -/
theorem summable_norm_circleCaratheodorySeries
    (mu : ProbabilityMeasure Circle) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n =>
      ‖circleCaratheodorySeriesCoefficient (mu : Measure Circle) n * w ^ n‖) := by
  have hmajor : Summable (fun n : ℕ => 2 * ‖w‖ ^ n) := by
    simpa only [norm_pow] using
      (summable_geometric_of_norm_lt_one hw).norm.mul_left 2
  have hs : Summable (fun n =>
      circleCaratheodorySeriesCoefficient (mu : Measure Circle) n * w ^ n) := by
    apply Summable.of_norm_bounded hmajor
    intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (norm_circleCaratheodorySeriesCoefficient_le_two mu n) (by positivity)
  exact hs.norm

/-- Geometric-series expansion of the circle Carathéodory kernel at a disk point. -/
theorem circleCaratheodoryKernel_sub_one_hasSum
    {w : ℂ} (hw : ‖w‖ < 1) (z : Circle) :
    HasSum (fun n : ℕ => 2 * (w / (z : ℂ)) ^ (n + 1))
      (circleCaratheodoryKernel w z - 1) := by
  let x : ℂ := w / (z : ℂ)
  have hxnorm : ‖x‖ < 1 := by
    simp only [x, norm_div, Circle.norm_coe, div_one]
    exact hw
  have hsum := (hasSum_geometric_of_norm_lt_one hxnorm).mul_left (2 * x)
  convert hsum using 1
  · funext n
    dsimp only [x]
    rw [pow_succ']
    ring
  · dsimp only [x, circleCaratheodoryKernel]
    have hz0 : (z : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by simp)
    have hzw : (z : ℂ) - w ≠ 0 := by
      intro h
      have heq : (z : ℂ) = w := sub_eq_zero.mp h
      have : ‖w‖ = 1 := by rw [← heq, Circle.norm_coe]
      linarith
    field_simp
    ring

/-- The genuine integral Carathéodory transform equals its absolutely convergent Fourier-moment
series throughout the open disk. -/
theorem circleCaratheodoryTransform_eq_tsum
    (mu : ProbabilityMeasure Circle) {w : ℂ} (hw : ‖w‖ < 1) :
    circleCaratheodoryTransform (mu : Measure Circle) w =
      ∑' n : ℕ, circleCaratheodorySeriesCoefficient (mu : Measure Circle) n * w ^ n := by
  let T : ℕ → Circle → ℂ := fun n z => 2 * (w / (z : ℂ)) ^ (n + 1)
  have hTint : ∀ n, Integrable (T n) (mu : Measure Circle) := by
    intro n
    have hcont : Continuous (T n) := by
      dsimp only [T]
      apply continuous_const.mul
      apply Continuous.pow
      apply Continuous.div continuous_const continuous_subtype_val
      intro z hz
      exact norm_ne_zero_iff.mp (by simp) hz
    exact (BoundedContinuousFunction.mkOfCompact
      (⟨T n, hcont⟩ : C(Circle, ℂ))).integrable (mu : Measure Circle)
  have hnormIntegral (n : ℕ) :
      ∫ z : Circle, ‖T n z‖ ∂(mu : Measure Circle) = 2 * ‖w‖ ^ (n + 1) := by
    have hfun : (fun z : Circle => ‖T n z‖) = fun _ => 2 * ‖w‖ ^ (n + 1) := by
      funext z
      simp [T, norm_pow]
    rw [hfun]
    simp
  have hnormSummable : Summable (fun n =>
      ∫ z : Circle, ‖T n z‖ ∂(mu : Measure Circle)) := by
    simp_rw [hnormIntegral]
    have hgeom : Summable (fun n : ℕ => ‖w‖ ^ n) := by
      simpa only [norm_pow] using (summable_geometric_of_norm_lt_one hw).norm
    exact (summable_nat_add_iff 1).2
      (hgeom.mul_left 2)
  have hIntSum : HasSum (fun n => ∫ z, T n z ∂(mu : Measure Circle))
      (∫ z, circleCaratheodoryKernel w z - 1 ∂(mu : Measure Circle)) := by
    have hraw := hasSum_integral_of_summable_integral_norm hTint hnormSummable
    convert hraw using 1
    apply integral_congr_ae
    filter_upwards [] with z
    exact (circleCaratheodoryKernel_sub_one_hasSum hw z).tsum_eq.symm
  have hterm (n : ℕ) :
      (∫ z, T n z ∂(mu : Measure Circle)) =
        2 * circleMeasureMomentZ (mu : Measure Circle) ((n + 1 : ℕ) : ℤ) * w ^ (n + 1) := by
    unfold circleMeasureMomentZ
    have hfun : T n = fun z : Circle =>
        (2 * w ^ (n + 1)) * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      funext z
      dsimp only [T]
      rw [div_pow]
      rw [_root_.zpow_neg, zpow_natCast]
      ring
    rw [hfun, integral_const_mul]
    ring
  have htail :
      (∑' n, 2 * circleMeasureMomentZ (mu : Measure Circle) ((n + 1 : ℕ) : ℤ) *
        w ^ (n + 1)) =
        ∫ z, circleCaratheodoryKernel w z - 1 ∂(mu : Measure Circle) := by
    rw [← hIntSum.tsum_eq]
    apply tsum_congr
    intro n
    exact (hterm n).symm
  have hs : Summable (fun n =>
      circleCaratheodorySeriesCoefficient (mu : Measure Circle) n * w ^ n) :=
    (summable_norm_circleCaratheodorySeries mu hw).of_norm
  calc
    circleCaratheodoryTransform (mu : Measure Circle) w =
        1 + ∫ z, circleCaratheodoryKernel w z - 1 ∂(mu : Measure Circle) := by
      unfold circleCaratheodoryTransform
      have hkernel := circleCaratheodoryKernel_integrable_probability mu hw
      have hone : Integrable (fun _ : Circle => (1 : ℂ)) (mu : Measure Circle) :=
        integrable_const 1
      rw [integral_sub hkernel hone]
      simp
    _ = 1 + ∑' n, 2 * circleMeasureMomentZ (mu : Measure Circle)
        ((n + 1 : ℕ) : ℤ) * w ^ (n + 1) := by rw [htail]
    _ = ∑' n : ℕ,
        circleCaratheodorySeriesCoefficient (mu : Measure Circle) n * w ^ n := by
      rw [hs.tsum_eq_zero_add]
      simp only [circleCaratheodorySeriesCoefficient, if_pos, pow_zero, mul_one]
      congr 1

/-- Reversed OPUC denominator of the `N`-th canonical probability approximation. -/
def bernsteinSzegoCaratheodoryDenominator
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) : Polynomial ℂ :=
  finiteOPUCReversedPolynomial (circleMeasureMomentZ (mu : Measure Circle))
    (circleMeasureGramTower_posDef_of_infiniteSupport
      (mu : Measure Circle) hmu (N + 1))

/-- Cauchy-product coefficient of the reversed OPUC denominator and the genuine transform series
of the canonical probability approximation. -/
def bernsteinSzegoCaratheodoryConvolutionCoefficient
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (bernsteinSzegoCaratheodoryDenominator mu hmu N).coeff k *
      circleCaratheodorySeriesCoefficient
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) (n - k)

/-- The finite numerator left after the autoregressive tail cancels. -/
def bernsteinSzegoCaratheodoryNumerator
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (N + 2),
    Polynomial.C (bernsteinSzegoCaratheodoryConvolutionCoefficient mu hmu N n) *
      Polynomial.X ^ n

/-- Every Cauchy-product coefficient beyond the OPUC depth vanishes. -/
theorem bernsteinSzegoCaratheodoryConvolutionCoefficient_eq_zero
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) {n : ℕ} (hn : N + 1 < n) :
    bernsteinSzegoCaratheodoryConvolutionCoefficient mu hmu N n = 0 := by
  let c := circleMeasureMomentZ (mu : Measure Circle)
  let hG := circleMeasureGramTower_posDef_of_infiniteSupport
    (mu : Measure Circle) hmu (N + 1)
  let q := finiteOPUCReversedPolynomial c hG
  let nu := bernsteinSzegoProbabilityApproximation mu hmu N
  have hqdeg : q.natDegree ≤ N + 1 := by
    calc
      q.natDegree ≤ ((finiteOPUCPolynomial c hG).map (starRingEnd ℂ)).natDegree := by
        exact Polynomial.reverse_natDegree_le _
      _ ≤ (finiteOPUCPolynomial c hG).natDegree := natDegree_map_le
      _ = N + 1 := finiteOPUCPolynomial_natDegree c hG
  have hsubset : Finset.range (q.natDegree + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ (hqdeg.trans hn.le))
  have htruncate :
      (∑ k ∈ Finset.range (n + 1), q.coeff k *
        circleCaratheodorySeriesCoefficient (nu : Measure Circle) (n - k)) =
      ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k *
        circleCaratheodorySeriesCoefficient (nu : Measure Circle) (n - k) := by
    symm
    apply Finset.sum_subset hsubset
    intro k hkbig hksmall
    have hkgt : q.natDegree < k := by
      simpa only [Finset.mem_range, not_lt] using hksmall
    rw [q.coeff_eq_zero_of_natDegree_lt hkgt, zero_mul]
  change (∑ k ∈ Finset.range (n + 1), q.coeff k *
    circleCaratheodorySeriesCoefficient (nu : Measure Circle) (n - k)) = 0
  rw [htruncate]
  have hklt : ∀ k ∈ Finset.range (q.natDegree + 1), k < n := by
    intro k hk
    have hkq : k ≤ q.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    exact lt_of_le_of_lt (hkq.trans hqdeg) hn
  calc
    (∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k *
        circleCaratheodorySeriesCoefficient (nu : Measure Circle) (n - k)) =
      2 * ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k *
        bernsteinSzegoMoment c hG ((n - k : ℕ) : ℤ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hnk : n - k ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (hklt k hk)
        rw [circleCaratheodorySeriesCoefficient, if_neg hnk]
        have hmom := bernsteinSzegoProbabilityApproximation_moment mu hmu N
          ((n - k : ℕ) : ℤ)
        change circleMeasureMomentZ (nu : Measure Circle) ((n - k : ℕ) : ℤ) = _ at hmom
        rw [hmom]
        ring
    _ = 0 := by
      rw [bernsteinSzegoMoment_reversedPolynomial_recurrence
        (show 0 < N + 1 by omega) c hG hn, mul_zero]

@[simp]
theorem bernsteinSzegoCaratheodoryNumerator_eval
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) (w : ℂ) :
    (bernsteinSzegoCaratheodoryNumerator mu hmu N).eval w =
      ∑ n ∈ Finset.range (N + 2),
        bernsteinSzegoCaratheodoryConvolutionCoefficient mu hmu N n * w ^ n := by
  simp [bernsteinSzegoCaratheodoryNumerator, Polynomial.eval_finsetSum]

/-- The genuine integral transform of every canonical Bernstein--Szegő approximation is the
quotient of its finite convolution numerator by its zero-free reversed OPUC denominator. -/
theorem bernsteinSzegoProbabilityApproximation_caratheodory_eq_polynomial_div
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    circleCaratheodoryTransform
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w =
      (bernsteinSzegoCaratheodoryNumerator mu hmu N).eval w /
        (bernsteinSzegoCaratheodoryDenominator mu hmu N).eval w := by
  let nu := bernsteinSzegoProbabilityApproximation mu hmu N
  let q := bernsteinSzegoCaratheodoryDenominator mu hmu N
  let a : ℕ → ℂ := circleCaratheodorySeriesCoefficient (nu : Measure Circle)
  let b : ℕ → ℂ := bernsteinSzegoCaratheodoryConvolutionCoefficient mu hmu N
  have hqnorm : Summable (fun n : ℕ => ‖q.coeff n * w ^ n‖) := by
    apply summable_of_ne_finset_zero (s := Finset.range (q.natDegree + 1))
    intro n hn
    have hnlarge : q.natDegree < n := by
      simpa only [Finset.mem_range, not_lt] using hn
    rw [q.coeff_eq_zero_of_natDegree_lt hnlarge, zero_mul, norm_zero]
  have hqsum : (∑' n : ℕ, q.coeff n * w ^ n) = q.eval w := by
    rw [tsum_eq_sum (s := Finset.range (q.natDegree + 1)) (fun n hn => by
      have hnlarge : q.natDegree < n := by
        simpa only [Finset.mem_range, not_lt] using hn
      rw [q.coeff_eq_zero_of_natDegree_lt hnlarge, zero_mul])]
    exact (Polynomial.eval_eq_sum_range w).symm
  have hanorm : Summable (fun n : ℕ => ‖a n * w ^ n‖) := by
    exact summable_norm_circleCaratheodorySeries nu hw
  have hproduct :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hqnorm hanorm
  have hconv (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (q.coeff k * w ^ k) * (a (n - k) * w ^ (n - k))) = b n * w ^ n := by
    unfold b bernsteinSzegoCaratheodoryConvolutionCoefficient
    change (∑ k ∈ Finset.range (n + 1),
      (q.coeff k * w ^ k) * (a (n - k) * w ^ (n - k))) =
      (∑ k ∈ Finset.range (n + 1), q.coeff k * a (n - k)) * w ^ n
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    calc
      (q.coeff k * w ^ k) * (a (n - k) * w ^ (n - k)) =
          q.coeff k * a (n - k) * (w ^ k * w ^ (n - k)) := by ring
      _ = q.coeff k * a (n - k) * w ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
  have hseries : q.eval w * circleCaratheodoryTransform (nu : Measure Circle) w =
      ∑' n : ℕ, b n * w ^ n := by
    rw [← hqsum, circleCaratheodoryTransform_eq_tsum nu hw]
    exact hproduct.trans (tsum_congr hconv)
  have hfinite : (∑' n : ℕ, b n * w ^ n) =
      ∑ n ∈ Finset.range (N + 2), b n * w ^ n := by
    apply tsum_eq_sum
    intro n hn
    have htail : N + 1 < n := by
      have : N + 2 ≤ n := by
        simpa only [Finset.mem_range, not_lt] using hn
      omega
    dsimp only [b]
    rw [bernsteinSzegoCaratheodoryConvolutionCoefficient_eq_zero
      mu hmu N htail, zero_mul]
  have hpoly : q.eval w * circleCaratheodoryTransform (nu : Measure Circle) w =
      (bernsteinSzegoCaratheodoryNumerator mu hmu N).eval w := by
    rw [hseries, hfinite, bernsteinSzegoCaratheodoryNumerator_eval]
  have hqne : q.eval w ≠ 0 := by
    exact finiteOPUCReversedPolynomial_ne_zero_on_closedBall
      (circleMeasureMomentZ (mu : Measure Circle))
      (circleMeasureGramTower_posDef_of_infiniteSupport
        (mu : Measure Circle) hmu (N + 1)) hw.le
  apply (eq_div_iff hqne).2
  simpa only [mul_comm] using hpoly

/-- The canonical rational-function object represented by the finite numerator and the reversed
OPUC denominator. -/
def bernsteinSzegoCaratheodoryRatFunc
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (bernsteinSzegoCaratheodoryNumerator mu hmu N) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (bernsteinSzegoCaratheodoryDenominator mu hmu N)

/-- An order-zero polynomial relation with a nonzero coefficient of the value variable is a local
differential-algebraic certificate. -/
theorem differentiallyAlgebraicOn_of_polynomial_value_relation
    {f : ℂ → ℂ} {U : Set ℂ} (p q : Polynomial ℂ)
    (hq : ∃ z : ℂ, q.eval z ≠ 0)
    (hrel : ∀ z ∈ U, q.eval z * f z = p.eval z) :
    GaloisForLFunctions.DifferentiallyAlgebraicOn f U := by
  let P : MvPolynomial (Fin 2) ℂ :=
    Polynomial.aeval (MvPolynomial.X 0) q * MvPolynomial.X 1 -
      Polynomial.aeval (MvPolynomial.X 0) p
  refine ⟨0, P, ?_, ?_⟩
  · obtain ⟨z0, hqz⟩ := hq
    intro hP
    let g0 : Fin 2 → ℂ := Fin.cons z0 (fun _ : Fin 1 => 0)
    let g1 : Fin 2 → ℂ := Fin.cons z0 (fun _ : Fin 1 => 1)
    have h0 := congrArg (MvPolynomial.eval g0) hP
    have h1 := congrArg (MvPolynomial.eval g1) hP
    have h0' : -(p.eval z0) = 0 := by
      simpa [P, g0, GaloisForLFunctions.eval_aeval_X0] using h0
    have h1' : q.eval z0 - p.eval z0 = 0 := by
      simpa [P, g1, GaloisForLFunctions.eval_aeval_X0] using h1
    apply hqz
    have hpz : p.eval z0 = 0 := neg_eq_zero.mp h0'
    rw [hpz] at h1'
    simpa using h1'
  · intro z hz
    change MvPolynomial.eval
      (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z)) P = 0
    simp only [P, map_sub, map_mul, MvPolynomial.eval_X]
    have hvalue : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) f z) :
        Fin 2 → ℂ) 1 = f z := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    rw [hvalue]
    simpa [GaloisForLFunctions.eval_aeval_X0] using sub_eq_zero.mpr (hrel z hz)

/-- Every finite canonical transform is locally differentially algebraic on the disk because its
genuine integral is represented by the explicit rational function above. -/
theorem bernsteinSzegoProbabilityApproximation_caratheodory_differentiallyAlgebraicOn_disk
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) :
    GaloisForLFunctions.DifferentiallyAlgebraicOn
      (fun w => circleCaratheodoryTransform
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w)
      {w : ℂ | ‖w‖ < 1} := by
  let p := bernsteinSzegoCaratheodoryNumerator mu hmu N
  let q := bernsteinSzegoCaratheodoryDenominator mu hmu N
  apply differentiallyAlgebraicOn_of_polynomial_value_relation p q
  · refine ⟨0, ?_⟩
    exact finiteOPUCReversedPolynomial_ne_zero_on_closedBall
      (circleMeasureMomentZ (mu : Measure Circle))
      (circleMeasureGramTower_posDef_of_infiniteSupport
        (mu : Measure Circle) hmu (N + 1)) (by simp)
  · intro w hw
    have hrat :=
      bernsteinSzegoProbabilityApproximation_caratheodory_eq_polynomial_div
        mu hmu N hw
    have hqne : q.eval w ≠ 0 :=
      finiteOPUCReversedPolynomial_ne_zero_on_closedBall
        (circleMeasureMomentZ (mu : Measure Circle))
        (circleMeasureGramTower_posDef_of_infiniteSupport
          (mu : Measure Circle) hmu (N + 1)) hw.le
    have hmul := (eq_div_iff hqne).mp hrat
    simpa only [mul_comm] using hmul

end

end GaloisForLFunctions.HTGeometry
