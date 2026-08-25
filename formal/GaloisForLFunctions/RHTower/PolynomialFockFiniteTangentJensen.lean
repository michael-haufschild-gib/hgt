import GaloisForLFunctions.RHTower.WeightedIntegralJensen
import GaloisForLFunctions.RHTower.PolynomialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.PolynomialFockTangentBallKernelTrace

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

/-- Finite weighted overlap multiplicity of the critical-prime tangent balls. -/
def finiteCriticalPrimeTangentBallMass
    (m : ℝ) (T : Finset Nat.Primes) (z : ℂ) : ℝ :=
  ∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ))
    then criticalPrimeSamplingWeight p else 0

/-- Compact union of closed tangent balls carrying a finite overlap symbol. -/
def finiteCriticalPrimeTangentClosedBallUnion
    (m : ℝ) (T : Finset Nat.Primes) : Set ℂ :=
  ⋃ p ∈ T, closedBall ((Real.log (p : ℝ) : ℝ) : ℂ)
    (polynomialFockTangentRadius m (Real.log (p : ℝ)))

theorem measurable_finiteCriticalPrimeTangentBallMass
    (m : ℝ) (T : Finset Nat.Primes) :
    Measurable (finiteCriticalPrimeTangentBallMass m T) := by
  classical
  unfold finiteCriticalPrimeTangentBallMass
  apply Finset.measurable_sum
  intro p hp
  exact measurable_const.ite measurableSet_ball measurable_const

theorem finiteCriticalPrimeTangentBallMass_nonneg
    (m : ℝ) (T : Finset Nat.Primes) (z : ℂ) :
    0 ≤ finiteCriticalPrimeTangentBallMass m T z := by
  classical
  unfold finiteCriticalPrimeTangentBallMass
  exact Finset.sum_nonneg fun p _ => by
    split_ifs
    · exact (criticalPrimeSamplingWeight_pos p).le
    · exact le_rfl

theorem finiteCriticalPrimeTangentBallMass_le_sum_weight
    (m : ℝ) (T : Finset Nat.Primes) (z : ℂ) :
    finiteCriticalPrimeTangentBallMass m T z ≤
      ∑ p ∈ T, criticalPrimeSamplingWeight p := by
  classical
  unfold finiteCriticalPrimeTangentBallMass
  exact Finset.sum_le_sum fun p _ => by
    split_ifs
    · exact le_rfl
    · exact (criticalPrimeSamplingWeight_pos p).le

theorem isCompact_finiteCriticalPrimeTangentClosedBallUnion
    (m : ℝ) (T : Finset Nat.Primes) :
    IsCompact (finiteCriticalPrimeTangentClosedBallUnion m T) := by
  unfold finiteCriticalPrimeTangentClosedBallUnion
  exact T.isCompact_biUnion fun p hp => isCompact_closedBall _ _

theorem finiteCriticalPrimeTangentBallMass_eq_zero_of_not_mem_closedBallUnion
    {m : ℝ} {T : Finset Nat.Primes} {z : ℂ}
    (hz : z ∉ finiteCriticalPrimeTangentClosedBallUnion m T) :
    finiteCriticalPrimeTangentBallMass m T z = 0 := by
  classical
  unfold finiteCriticalPrimeTangentBallMass
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg]
  intro hdist
  apply hz
  unfold finiteCriticalPrimeTangentClosedBallUnion
  rw [mem_iUnion]
  refine ⟨p, ?_⟩
  rw [mem_iUnion]
  refine ⟨hp, ?_⟩
  exact ball_subset_closedBall (by simpa [mem_ball] using hdist)

/-- Jensen--Hölder turns the `q`-power of finite critical-prime sampling energy into the
`q`-power overlap integral. The density is localized to its literal compact support, so no global
boundedness premise is introduced. -/
theorem sum_normSq_criticalPrimeKernelRestriction_rpow_le_weightedOverlapIntegral
    {m q : ℝ} (hm : 4 ≤ m) (hq : 1 < q)
    (f : MomentFock) (hf : ‖f‖ ≤ 1) (T : Finset Nat.Primes) :
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2) ^ q ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) ^ q *
        ∫ z in finiteCriticalPrimeTangentClosedBallUnion m T,
          finiteCriticalPrimeTangentBallMass m T z ^ q *
            polynomialMomentFockWeightedNormSq m (by linarith) f z := by
  classical
  have hm2 : 2 ≤ m := by linarith
  let D : ℂ → ℝ := polynomialMomentFockWeightedNormSq m hm2 f
  let W : ℂ → ℝ := finiteCriticalPrimeTangentBallMass m T
  let U : Set ℂ := finiteCriticalPrimeTangentClosedBallUnion m T
  let C : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  have hlocal : ∀ p : Nat.Primes,
      ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2 ≤
        C * (criticalPrimeSamplingWeight p *
          ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) := by
    intro p
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hx : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have heval := normSq_inner_normalizedPolynomialMomentFockKernel_le_localIntegral
      hm hx f
    have hweight : 0 ≤ criticalPrimeSamplingWeight p :=
      (criticalPrimeSamplingWeight_pos p).le
    have hcoord :
        ‖criticalPrimeKernelRestriction
            (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2 =
          criticalPrimeSamplingWeight p *
            ‖inner ℂ (normalizedMomentFockKernel
              (polynomialMomentFockData m hm2) (Real.log (p : ℝ) : ℂ)) f‖ ^ 2 := by
      rw [criticalPrimeKernelRestriction_apply, norm_mul, mul_pow]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hweight]
      rfl
    rw [hcoord]
    calc
      criticalPrimeSamplingWeight p *
          ‖inner ℂ (normalizedMomentFockKernel
            (polynomialMomentFockData m hm2) (Real.log (p : ℝ) : ℂ)) f‖ ^ 2 ≤
        criticalPrimeSamplingWeight p *
          (C * ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) :=
        mul_le_mul_of_nonneg_left heval hweight
      _ = C * (criticalPrimeSamplingWeight p *
          ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) := by ring
  have hDint : Integrable D := integrable_polynomialMomentFockWeightedNormSq m hm2 f
  have hsumEq :
      (∑ p ∈ T, criticalPrimeSamplingWeight p *
        ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
            (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) =
        ∫ z, W z * D z := by
    let A : Nat.Primes → Set ℂ := fun p => ball
      ((Real.log (p : ℝ) : ℝ) : ℂ)
      (polynomialFockTangentRadius m (Real.log (p : ℝ)))
    let g : Nat.Primes → ℂ → ℝ := fun p =>
      (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z)
    have hgint : ∀ p, Integrable (g p) := by
      intro p
      exact (hDint.const_mul (criticalPrimeSamplingWeight p)).indicator measurableSet_ball
    have heq : ∀ z, (∑ p ∈ T, g p z) = W z * D z := by
      intro z
      change (∑ p ∈ T, g p z) =
        (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) * D z
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hz : z ∈ A p
      · have hdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
          simpa [A, mem_ball] using hz
        change (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z) z = _
        rw [Set.indicator_of_mem hz, if_pos hdist]
      · have hdist : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
          simpa [A, mem_ball] using hz
        change (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z) z = _
        rw [Set.indicator, if_neg hz, if_neg hdist]
        ring
    rw [← integral_congr_ae (Filter.Eventually.of_forall heq),
      MeasureTheory.integral_finsetSum T (fun p _ => hgint p)]
    apply Finset.sum_congr rfl
    intro p hp
    change criticalPrimeSamplingWeight p * (∫ z in A p, D z) = ∫ z, g p z
    rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.integral_const_mul]
  have hUcompact : IsCompact U :=
    isCompact_finiteCriticalPrimeTangentClosedBallUnion m T
  have hUmeas : MeasurableSet U := hUcompact.measurableSet
  have hrestrict : (∫ z, W z * D z) = ∫ z in U, W z * D z := by
    rw [← MeasureTheory.integral_indicator hUmeas]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ U
    · simp [Set.indicator_of_mem hz]
    · have hWzero : W z = 0 :=
        finiteCriticalPrimeTangentBallMass_eq_zero_of_not_mem_closedBallUnion hz
      simp [Set.indicator, hz, hWzero]
  have henergy :
      (∑ p ∈ T, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2) ≤
        C * ∫ z in U, W z * D z := by
    calc
      _ ≤ ∑ p ∈ T, C * (criticalPrimeSamplingWeight p *
          ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
            (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) :=
        Finset.sum_le_sum fun p _ => hlocal p
      _ = C * (∑ p ∈ T, criticalPrimeSamplingWeight p *
          ∫ z in ball ((Real.log (p : ℝ) : ℝ) : ℂ)
            (polynomialFockTangentRadius m (Real.log (p : ℝ))), D z) := by
        rw [Finset.mul_sum]
      _ = C * ∫ z in U, W z * D z := by rw [hsumEq, hrestrict]
  let μ : Measure ℂ := volume.restrict U
  let Cw : ℝ := ∑ p ∈ T, criticalPrimeSamplingWeight p
  have hCw0 : 0 ≤ Cw := Finset.sum_nonneg fun p _ =>
    (criticalPrimeSamplingWeight_pos p).le
  let Cg : ℝ := Classical.choose
    (hUcompact.exists_bound_of_continuousOn
      (continuous_polynomialMomentFockWeightedNormSq m hm2 f).continuousOn)
  have hCg : ∀ z ∈ U, D z ≤ Cg := by
    intro z hz
    have h := Classical.choose_spec
      (hUcompact.exists_bound_of_continuousOn
        (continuous_polynomialMomentFockWeightedNormSq m hm2 f).continuousOn) z hz
    rwa [Real.norm_of_nonneg (polynomialMomentFockWeightedNormSq_nonneg m hm2 f z)] at h
  letI : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hUcompact.measure_lt_top⟩
  have hmass : ∫ z, D z ∂μ ≤ 1 := by
    calc
      ∫ z, D z ∂μ ≤ ∫ z, D z := integral_mono_measure
        Measure.restrict_le_self
        (Filter.Eventually.of_forall fun z => polynomialMomentFockWeightedNormSq_nonneg m hm2 f z)
        hDint
      _ = ‖f‖ ^ 2 := integral_polynomialMomentFockWeightedNormSq m hm2 f
      _ ≤ 1 := by nlinarith [norm_nonneg f]
  have hjensen := rpow_integral_mul_le_integral_rpow_mul
    (μ := μ) (q := q) (Cw := Cw) (Cg := Cg) hq hCw0
    (W := W) (g := D)
    (measurable_finiteCriticalPrimeTangentBallMass m T)
    (continuous_polynomialMomentFockWeightedNormSq m hm2 f).measurable
    (finiteCriticalPrimeTangentBallMass_nonneg m T)
    (polynomialMomentFockWeightedNormSq_nonneg m hm2 f)
    (finiteCriticalPrimeTangentBallMass_le_sum_weight m T)
    (by
      filter_upwards [ae_restrict_mem hUmeas] with z hz
      exact hCg z hz)
    hmass
  have hC0 : 0 ≤ C := Real.exp_nonneg _
  have hI0 : 0 ≤ ∫ z in U, W z * D z := integral_nonneg fun z =>
    mul_nonneg (finiteCriticalPrimeTangentBallMass_nonneg m T z)
      (polynomialMomentFockWeightedNormSq_nonneg m hm2 f z)
  have hpow := Real.rpow_le_rpow
    (Finset.sum_nonneg fun p _ => sq_nonneg _)
    henergy (by linarith : 0 ≤ q)
  calc
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2) ^ q ≤
        (C * ∫ z in U, W z * D z) ^ q := hpow
    _ = C ^ q * (∫ z in U, W z * D z) ^ q :=
      Real.mul_rpow hC0 hI0
    _ ≤ C ^ q * ∫ z in U, W z ^ q * D z := by
      exact mul_le_mul_of_nonneg_left hjensen (Real.rpow_nonneg hC0 q)

end

end RHTower
