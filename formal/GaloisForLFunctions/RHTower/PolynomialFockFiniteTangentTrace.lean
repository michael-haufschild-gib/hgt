import GaloisForLFunctions.RHTower.PolynomialFockFiniteTangentJensen
import GaloisForLFunctions.RHTower.PolynomialFockTangentBallAdaptedCellMass
import GaloisForLFunctions.HTGeometry.SVDExpansion

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open ContinuousLinearMap

theorem sum_polynomialMomentFockWeightedNormSq_svVec_le_kernelDiagonalDensity
    {m : ℝ} (hm2 : 2 ≤ m) (hm4 : 4 ≤ m) (hm : 4 < m)
    (S : Finset ℕ) (z : ℂ) :
    (∑ j ∈ S, polynomialMomentFockWeightedNormSq m hm2
      (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m hm4)) j) z) ≤
      polynomialMomentFockKernelDiagonalDensity m hm2 z := by
  have hcpt := polynomialCriticalPrimeSamplingIncidence_isCompactOperator hm
  let K : MomentFock := momentFockKernel (polynomialMomentFockData m hm2) z
  have hbessel := sum_inner_svVec_sq_le hcpt K S
  unfold polynomialMomentFockWeightedNormSq polynomialMomentFockKernelDiagonalDensity
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  simpa only [polynomialMomentFockFunction_eq_evaluation,
    polynomialMomentFockEvaluation, momentFockEvaluation_apply,
    K, norm_inner_symm] using hbessel

theorem integrableOn_polynomialMomentFockKernelDiagonalDensity_tangentBall
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    IntegrableOn (polynomialMomentFockKernelDiagonalDensity m (by linarith))
      (ball (x : ℂ) (polynomialFockTangentRadius m x)) := by
  let C : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
    Real.pi * 3 ^ (m / 2 - 1) * (m * (1 + x ^ 2) ^ (m / 2 - 1))
  have hCint : Integrable (fun _ : ℂ => C)
      (volume.restrict (ball (x : ℂ) (polynomialFockTangentRadius m x))) :=
    integrableOn_const
  apply hCint.mono'
    (measurable_polynomialMomentFockKernelDiagonalDensity m
      (by linarith)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [Real.norm_of_nonneg
    (polynomialMomentFockKernelDiagonalDensity_nonneg m (by linarith) z)]
  exact polynomialFockKernelDiagonalDensity_le_anchorCurvature_of_mem_tangentBall hm hx hz

theorem integral_rpow_finiteCriticalPrimeTangentBallMass_mul_kernelDiagonalDensity_le
    {m q : ℝ} (hm : 4 ≤ m) (hq : 1 < q)
    (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, 2 ≤ Real.log (p : ℝ)) :
    (∫ z in finiteCriticalPrimeTangentClosedBallUnion m T,
      finiteCriticalPrimeTangentBallMass m T z ^ q *
        polynomialMomentFockKernelDiagonalDensity m (by linarith) z) ≤
      (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        3 ^ (m / 2 - 1)) *
        ∑ p ∈ T, criticalPrimeSamplingWeight p *
          criticalPrimeFockScaledAdaptedCellMass m
            (criticalPrimeFockOverlapCellScale m)
            (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))) ^ (q - 1) := by
  classical
  have hm2 : 2 ≤ m := by linarith
  let W : ℂ → ℝ := finiteCriticalPrimeTangentBallMass m T
  let K : ℂ → ℝ := polynomialMomentFockKernelDiagonalDensity m hm2
  let U : Set ℂ := finiteCriticalPrimeTangentClosedBallUnion m T
  let A : Nat.Primes → Set ℂ := fun p => ball
    ((Real.log (p : ℝ) : ℝ) : ℂ)
    (polynomialFockTangentRadius m (Real.log (p : ℝ)))
  let M : Nat.Primes → ℝ := fun p =>
    criticalPrimeFockScaledAdaptedCellMass m
      (criticalPrimeFockOverlapCellScale m)
      (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)))
  let F : ℂ → ℝ := fun z => W z ^ (q - 1) * K z
  let C : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
    3 ^ (m / 2 - 1)
  have hqm1 : 0 ≤ q - 1 := by linarith
  have hWmeas : Measurable W := measurable_finiteCriticalPrimeTangentBallMass m T
  have hKmeas : Measurable K :=
    measurable_polynomialMomentFockKernelDiagonalDensity m hm2
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ((Real.continuous_rpow_const hqm1).measurable.comp hWmeas).mul hKmeas
  have hW0 : ∀ z, 0 ≤ W z := finiteCriticalPrimeTangentBallMass_nonneg m T
  have hK0 : ∀ z, 0 ≤ K z :=
    polynomialMomentFockKernelDiagonalDensity_nonneg m hm2
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    mul_nonneg (Real.rpow_nonneg (hW0 z) _) (hK0 z)
  have hM0 : ∀ p, 0 ≤ M p := by
    intro p
    exact criticalPrimeFockScaledAdaptedCellMass_nonneg
      (criticalPrimeFockOverlapCellScale_pos m).le m _
  have hWle : ∀ p ∈ T, ∀ z ∈ A p, W z ≤ M p := by
    intro p hp z hz
    exact sum_criticalPrimeSamplingWeight_overlapping_anchorBall_le_cellMass
      hm p (hT p hp) (by simpa [A, mem_ball] using hz) T
  have hFint : ∀ p ∈ T, Integrable F (volume.restrict (A p)) := by
    intro p hp
    have hp1 : 1 ≤ Real.log (p : ℝ) := by linarith [hT p hp]
    have hKint : Integrable K (volume.restrict (A p)) := by
      change IntegrableOn K (A p)
      simpa only [K, A] using
        integrableOn_polynomialMomentFockKernelDiagonalDensity_tangentBall hm hp1
    have hright : Integrable (fun z => M p ^ (q - 1) * K z)
        (volume.restrict (A p)) := hKint.const_mul _
    apply hright.mono' hFmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_of_nonneg (hF0 z)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hW0 z) (hWle p hp z hz) hqm1) (hK0 z)
  let g : Nat.Primes → ℂ → ℝ := fun p =>
    (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z)
  have hgint : ∀ p ∈ T, Integrable (g p) := by
    intro p hp
    have hOn : IntegrableOn (fun z => criticalPrimeSamplingWeight p * F z) (A p) :=
      (hFint p hp).const_mul (criticalPrimeSamplingWeight p)
    exact hOn.integrable_indicator measurableSet_ball
  have hWF : ∀ z, W z ^ q * K z = W z * F z := by
    intro z
    by_cases hz : W z = 0
    · simp [hz, F, Real.zero_rpow (by linarith : q ≠ 0)]
    · have hzpos : 0 < W z := lt_of_le_of_ne (hW0 z) (Ne.symm hz)
      dsimp [F]
      rw [show q = 1 + (q - 1) by ring, Real.rpow_add hzpos, Real.rpow_one]
      ring
  have hsumg : ∀ z, (∑ p ∈ T, g p z) = W z * F z := by
    intro z
    change (∑ p ∈ T, g p z) =
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) * F z
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hz : z ∈ A p
    · have hdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
        simpa [A, mem_ball] using hz
      change (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z) z = _
      rw [Set.indicator_of_mem hz, if_pos hdist]
    · have hdist : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
        simpa [A, mem_ball] using hz
      change (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z) z = _
      rw [Set.indicator, if_neg hz, if_neg hdist]
      ring
  have hwhole : (∫ z, W z ^ q * K z) =
      ∑ p ∈ T, criticalPrimeSamplingWeight p * ∫ z in A p, F z := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hWF)]
    rw [← integral_congr_ae (Filter.Eventually.of_forall hsumg)]
    rw [MeasureTheory.integral_finsetSum T hgint]
    apply Finset.sum_congr rfl
    intro p hp
    change ∫ z, g p z = criticalPrimeSamplingWeight p * ∫ z in A p, F z
    rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.integral_const_mul]
  have hlocal : ∀ p ∈ T, (∫ z in A p, F z) ≤ M p ^ (q - 1) * C := by
    intro p hp
    have hp1 : 1 ≤ Real.log (p : ℝ) := by linarith [hT p hp]
    have hKint : Integrable K (volume.restrict (A p)) := by
      change IntegrableOn K (A p)
      simpa only [K, A] using
        integrableOn_polynomialMomentFockKernelDiagonalDensity_tangentBall hm hp1
    have hright : Integrable (fun z => M p ^ (q - 1) * K z)
        (volume.restrict (A p)) := hKint.const_mul _
    calc
      ∫ z in A p, F z ≤ ∫ z in A p, M p ^ (q - 1) * K z := by
        apply integral_mono_ae (hFint p hp) hright
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (hW0 z) (hWle p hp z hz) hqm1) (hK0 z)
      _ = M p ^ (q - 1) * ∫ z in A p, K z := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ M p ^ (q - 1) * C := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hM0 p) _)
        simpa [K, A, C] using
          integral_tangentBall_polynomialFockKernelDiagonalDensity_le hm hp1
  have hUcompact := isCompact_finiteCriticalPrimeTangentClosedBallUnion m T
  have hUmeas : MeasurableSet U := hUcompact.measurableSet
  have hrestrict : (∫ z in U, W z ^ q * K z) = ∫ z, W z ^ q * K z := by
    rw [← MeasureTheory.integral_indicator hUmeas]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ U
    · simp [Set.indicator_of_mem hz]
    · have hWzero : W z = 0 :=
        finiteCriticalPrimeTangentBallMass_eq_zero_of_not_mem_closedBallUnion hz
      simp [Set.indicator, hz, hWzero, Real.zero_rpow (by linarith : q ≠ 0)]
  rw [hrestrict, hwhole]
  calc
    (∑ p ∈ T, criticalPrimeSamplingWeight p * ∫ z in A p, F z) ≤
        ∑ p ∈ T, criticalPrimeSamplingWeight p * (M p ^ (q - 1) * C) := by
      exact Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hlocal p hp)
        (criticalPrimeSamplingWeight_pos p).le
    _ = C * ∑ p ∈ T, criticalPrimeSamplingWeight p * M p ^ (q - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end

end RHTower

namespace RHTower

noncomputable section

theorem integrableOn_rpow_finiteCriticalPrimeTangentBallMass_mul_kernelDiagonalDensity
    {m q : ℝ} (hm : 4 ≤ m) (hq : 1 < q)
    (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, 2 ≤ Real.log (p : ℝ)) :
    IntegrableOn (fun z => finiteCriticalPrimeTangentBallMass m T z ^ q *
      polynomialMomentFockKernelDiagonalDensity m (by linarith) z)
      (finiteCriticalPrimeTangentClosedBallUnion m T) := by
  classical
  have hm2 : 2 ≤ m := by linarith
  let W : ℂ → ℝ := finiteCriticalPrimeTangentBallMass m T
  let K : ℂ → ℝ := polynomialMomentFockKernelDiagonalDensity m hm2
  let A : Nat.Primes → Set ℂ := fun p => ball
    ((Real.log (p : ℝ) : ℝ) : ℂ)
    (polynomialFockTangentRadius m (Real.log (p : ℝ)))
  let B : ℝ := ∑ p ∈ T, criticalPrimeSamplingWeight p
  let F : ℂ → ℝ := fun z => W z ^ (q - 1) * K z
  have hqm1 : 0 ≤ q - 1 := by linarith
  have hWmeas : Measurable W := measurable_finiteCriticalPrimeTangentBallMass m T
  have hKmeas : Measurable K :=
    measurable_polynomialMomentFockKernelDiagonalDensity m hm2
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ((Real.continuous_rpow_const hqm1).measurable.comp hWmeas).mul hKmeas
  have hW0 : ∀ z, 0 ≤ W z := finiteCriticalPrimeTangentBallMass_nonneg m T
  have hK0 : ∀ z, 0 ≤ K z :=
    polynomialMomentFockKernelDiagonalDensity_nonneg m hm2
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    mul_nonneg (Real.rpow_nonneg (hW0 z) _) (hK0 z)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun p _ =>
    (criticalPrimeSamplingWeight_pos p).le
  have hWle : ∀ z, W z ≤ B :=
    finiteCriticalPrimeTangentBallMass_le_sum_weight m T
  have hFint : ∀ p ∈ T, Integrable F (volume.restrict (A p)) := by
    intro p hp
    have hp1 : 1 ≤ Real.log (p : ℝ) := by linarith [hT p hp]
    have hKint : Integrable K (volume.restrict (A p)) := by
      change IntegrableOn K (A p)
      simpa only [K, A] using
        integrableOn_polynomialMomentFockKernelDiagonalDensity_tangentBall hm hp1
    have hright : Integrable (fun z => B ^ (q - 1) * K z)
        (volume.restrict (A p)) := hKint.const_mul _
    apply hright.mono' hFmeas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (hF0 z)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hW0 z) (hWle z) hqm1) (hK0 z)
  let g : Nat.Primes → ℂ → ℝ := fun p =>
    (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z)
  have hgint : ∀ p ∈ T, Integrable (g p) := by
    intro p hp
    have hOn : IntegrableOn (fun z => criticalPrimeSamplingWeight p * F z) (A p) :=
      (hFint p hp).const_mul (criticalPrimeSamplingWeight p)
    exact hOn.integrable_indicator measurableSet_ball
  have hWF : ∀ z, W z ^ q * K z = W z * F z := by
    intro z
    by_cases hz : W z = 0
    · simp [hz, F, Real.zero_rpow (by linarith : q ≠ 0)]
    · have hzpos : 0 < W z := lt_of_le_of_ne (hW0 z) (Ne.symm hz)
      dsimp [F]
      rw [show q = 1 + (q - 1) by ring, Real.rpow_add hzpos, Real.rpow_one]
      ring
  have hsumg : ∀ z, (∑ p ∈ T, g p z) = W z * F z := by
    intro z
    change (∑ p ∈ T, g p z) =
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) * F z
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hz : z ∈ A p
    · have hdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
        simpa [A, mem_ball] using hz
      change (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z) z = _
      rw [Set.indicator_of_mem hz, if_pos hdist]
    · have hdist : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
        simpa [A, mem_ball] using hz
      change (A p).indicator (fun z => criticalPrimeSamplingWeight p * F z) z = _
      rw [Set.indicator, if_neg hz, if_neg hdist]
      ring
  have hsumint : Integrable (fun z => ∑ p ∈ T, g p z) :=
    integrable_finsetSum T hgint
  have hwhole : Integrable (fun z => W z ^ q * K z) := by
    apply hsumint.congr
    filter_upwards with z
    rw [hWF z, ← hsumg z]
  exact hwhole.integrableOn

end

end RHTower
