import GaloisForLFunctions.RHTower.RapidExponentialFockWeightedPrimeOverlap
import GaloisForLFunctions.RHTower.CriticalPrimeKernelSamplingCompact
import GaloisForLFunctions.RHTower.ScaleIncompatibility

/-!
# Critical-prime sampling on the rapid exponential moment-Fock carrier

Weighted local evaluation and quantitative prime-ball overlap construct the literal normalized
all-prime sampler.  Weighted finite-head tails prove compactness, while normalized coordinate norms
retain the non-Hilbert--Schmidt and non-trace-class endpoints.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

theorem sum_criticalPrimeWeightFactor_mul_rapidLocalBallIntegral_le
    {a B : ℝ} (ha : 0 < a)
    (f : MomentFock) (T : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤ B) :
    (∑ p ∈ T, (criticalPrimeSamplingWeight p *
        rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))) *
      ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
          (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))),
        rapidExponentialMomentFockWeightedNormSq a ha f z) ≤
      B * ‖f‖ ^ 2 := by
  classical
  let D : ℂ → ℝ := rapidExponentialMomentFockWeightedNormSq a ha f
  let A : Nat.Primes → Set ℂ := fun p => Metric.ball
    ((Real.log (p : ℝ) : ℝ) : ℂ)
    (rapidExponentialFockLocalRadius a (Real.log (p : ℝ)))
  let q : Nat.Primes → ℝ := fun p => criticalPrimeSamplingWeight p *
    rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))
  let g : Nat.Primes → ℂ → ℝ := fun p => (A p).indicator (fun z => q p * D z)
  have hDint : Integrable D := integrable_rapidExponentialMomentFockWeightedNormSq a ha f
  have hgint : ∀ p, Integrable (g p) := by
    intro p
    exact (hDint.const_mul (q p)).indicator measurableSet_ball
  have hsumint : Integrable (fun z => ∑ p ∈ T, g p z) :=
    integrable_finsetSum T (fun p _ => hgint p)
  have hBint : Integrable (fun z => B * D z) := hDint.const_mul B
  have hpoint : ∀ z : ℂ, (∑ p ∈ T, g p z) ≤ B * D z := by
    intro z
    have hD : 0 ≤ D z := rapidExponentialMomentFockWeightedNormSq_nonneg a ha f z
    calc
      (∑ p ∈ T, g p z) =
          (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
            then criticalPrimeSamplingWeight p *
              rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) *
            D z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hz : z ∈ A p
        · have hdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
            simpa [A, Metric.mem_ball] using hz
          change (A p).indicator (fun z => q p * D z) z = _
          rw [Set.indicator_of_mem hz, if_pos hdist]
        · have hdist : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
            simpa [A, Metric.mem_ball] using hz
          change (A p).indicator (fun z => q p * D z) z = _
          rw [Set.indicator, if_neg hz, if_neg hdist]
          ring
      _ ≤ B * D z := mul_le_mul_of_nonneg_right (hoverlap z) hD
  have hint : (∫ z, ∑ p ∈ T, g p z) ≤ ∫ z, B * D z :=
    MeasureTheory.integral_mono hsumint hBint hpoint
  have hsumEq :
      (∑ p ∈ T, q p * ∫ z in A p, D z) = ∫ z, ∑ p ∈ T, g p z := by
    rw [MeasureTheory.integral_finsetSum T (fun p _ => hgint p)]
    apply Finset.sum_congr rfl
    intro p hp
    change q p * (∫ z in A p, D z) =
      ∫ z, (A p).indicator (fun z => q p * D z) z
    rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.integral_const_mul]
  rw [← hsumEq] at hint
  rw [MeasureTheory.integral_const_mul,
    integral_rapidExponentialMomentFockWeightedNormSq a ha] at hint
  simpa [D, A, q] using hint

/-- Finite normalized sampling energy is controlled by weighted rapid-ball overlap. -/
theorem sum_normSq_criticalPrimeKernelRestriction_rapid_le
    {a B : ℝ} (ha : 0 < a)
    (f : MomentFock) (T : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤ B) :
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
      B * ‖f‖ ^ 2 := by
  have hlocal : ∀ p : Nat.Primes,
      ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2 ≤
        (criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))) *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))),
              rapidExponentialMomentFockWeightedNormSq a ha f z := by
    intro p
    have hx : 1 / 2 ≤ Real.log (p : ℝ) := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      exact log_two_gt_half.le.trans (Real.log_le_log (by norm_num) hp2)
    have heval :=
      normSq_inner_normalizedRapidExponentialMomentFockKernel_le_localIntegral ha hx f
    have hweight : 0 ≤ criticalPrimeSamplingWeight p :=
      (criticalPrimeSamplingWeight_pos p).le
    have hcoord :
        ‖criticalPrimeKernelRestriction
            (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2 =
          criticalPrimeSamplingWeight p *
            ‖inner ℂ (normalizedMomentFockKernel
              (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)) f‖ ^ 2 := by
      rw [criticalPrimeKernelRestriction_apply, norm_mul, mul_pow]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hweight]
      rfl
    rw [hcoord]
    calc
      criticalPrimeSamplingWeight p *
          ‖inner ℂ (normalizedMomentFockKernel
            (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)) f‖ ^ 2 ≤
        criticalPrimeSamplingWeight p *
          (rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))),
              rapidExponentialMomentFockWeightedNormSq a ha f z) :=
        mul_le_mul_of_nonneg_left heval hweight
      _ = (criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))) *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))),
              rapidExponentialMomentFockWeightedNormSq a ha f z := by ring
  calc
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
      ∑ p ∈ T, (criticalPrimeSamplingWeight p *
        rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))) *
          ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))),
            rapidExponentialMomentFockWeightedNormSq a ha f z :=
      Finset.sum_le_sum fun p _ => hlocal p
    _ ≤ B * ‖f‖ ^ 2 :=
      sum_criticalPrimeWeightFactor_mul_rapidLocalBallIntegral_le ha f T hoverlap

/-- Canonical weighted-overlap tail heads. -/
def rapidCriticalPrimeTailHeads (a : ℝ) (ha : 0 < a) : ℕ → Finset Nat.Primes :=
  Classical.choose (exists_criticalPrime_weightedRapidLocalBallTail_bound ha)

theorem rapidCriticalPrimeTailHeads_bound
    (a : ℝ) (ha : 0 < a) (n : ℕ) (z : ℂ) (T : Finset Nat.Primes) :
    (∑ p ∈ T.filter (· ∉ rapidCriticalPrimeTailHeads a ha n),
      if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤
      ((n : ℝ) + 1)⁻¹ :=
  Classical.choose_spec (exists_criticalPrime_weightedRapidLocalBallTail_bound ha) n z T

theorem sum_normSq_criticalPrimeKernelRestriction_rapid_tail_le
    {a δ : ℝ} (ha : 0 < a) (P : Finset Nat.Primes)
    (hoverlap : ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p *
            rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤ δ)
    (f : MomentFock) (T : Finset Nat.Primes) :
    (∑ p ∈ T, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
      δ * ‖f‖ ^ 2 := by
  have hbase := sum_normSq_criticalPrimeKernelRestriction_rapid_le ha f
    (T.filter (· ∉ P)) (fun z => hoverlap z T)
  calc
    (∑ p ∈ T, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) =
      ∑ p ∈ T.filter (· ∉ P), ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpP : p ∈ P <;> simp [hpP]
    _ ≤ δ * ‖f‖ ^ 2 := hbase

/-- A normalized prime coordinate is bounded by its literal arithmetic weight. -/
theorem normSq_criticalPrimeKernelRestriction_rapid_le_weight
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) (f : MomentFock) :
    ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2 ≤
      criticalPrimeSamplingWeight p * ‖f‖ ^ 2 := by
  have hweight : 0 ≤ criticalPrimeSamplingWeight p :=
    (criticalPrimeSamplingWeight_pos p).le
  have hinner :
      ‖inner ℂ (normalizedMomentFockKernel
        (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)) f‖ ≤ ‖f‖ := by
    calc
      ‖inner ℂ (normalizedMomentFockKernel
          (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)) f‖ ≤
        ‖normalizedMomentFockKernel
          (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)‖ * ‖f‖ :=
        norm_inner_le_norm _ _
      _ = ‖f‖ := by rw [norm_normalizedMomentFockKernel, one_mul]
  have hinnerSq :
      ‖inner ℂ (normalizedMomentFockKernel
        (rapidExponentialMomentFockData a ha) (Real.log (p : ℝ) : ℂ)) f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hinner
  rw [criticalPrimeKernelRestriction_apply, norm_mul, mul_pow]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hweight]
  exact mul_le_mul_of_nonneg_left hinnerSq hweight

/-- Finite arithmetic mass of the canonical zeroth tail head. -/
def rapidCriticalPrimeHeadMass (a : ℝ) (ha : 0 < a) : ℝ :=
  ∑ p ∈ rapidCriticalPrimeTailHeads a ha 0, criticalPrimeSamplingWeight p

theorem rapidCriticalPrimeHeadMass_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ rapidCriticalPrimeHeadMass a ha := by
  unfold rapidCriticalPrimeHeadMass
  exact Finset.sum_nonneg fun p _ => (criticalPrimeSamplingWeight_pos p).le

/-- Canonical Bessel constant: finite head mass plus the zeroth weighted-overlap tail bound. -/
def rapidCriticalPrimeBesselBound (a : ℝ) (ha : 0 < a) : ℝ :=
  rapidCriticalPrimeHeadMass a ha + 1

theorem rapidCriticalPrimeBesselBound_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ rapidCriticalPrimeBesselBound a ha := by
  unfold rapidCriticalPrimeBesselBound
  linarith [rapidCriticalPrimeHeadMass_nonneg a ha]

theorem sum_normSq_criticalPrimeKernelRestriction_rapid_le_canonical
    {a : ℝ} (ha : 0 < a) (f : MomentFock) (T : Finset Nat.Primes) :
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
      rapidCriticalPrimeBesselBound a ha * ‖f‖ ^ 2 := by
  classical
  let P : Finset Nat.Primes := rapidCriticalPrimeTailHeads a ha 0
  let H : Finset Nat.Primes := T.filter (· ∈ P)
  let U : Finset Nat.Primes := T.filter (· ∉ P)
  have hdisj : Disjoint H U := by
    rw [Finset.disjoint_left]
    intro p hpH hpU
    have hpP : p ∈ P := (Finset.mem_filter.mp hpH).2
    exact (Finset.mem_filter.mp hpU).2 hpP
  have hunion : H ∪ U = T := by
    simpa [H, U] using Finset.filter_union_filter_not_eq (fun p : Nat.Primes => p ∈ P) T
  have hheadWeight : (∑ p ∈ H, criticalPrimeSamplingWeight p) ≤
      rapidCriticalPrimeHeadMass a ha := by
    unfold rapidCriticalPrimeHeadMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hpP hpH
      exact (criticalPrimeSamplingWeight_pos p).le
  have hhead :
      (∑ p ∈ H, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
        rapidCriticalPrimeHeadMass a ha * ‖f‖ ^ 2 := by
    calc
      (∑ p ∈ H, ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
        ∑ p ∈ H, criticalPrimeSamplingWeight p * ‖f‖ ^ 2 :=
          Finset.sum_le_sum fun p _ =>
            normSq_criticalPrimeKernelRestriction_rapid_le_weight ha p f
      _ = (∑ p ∈ H, criticalPrimeSamplingWeight p) * ‖f‖ ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ rapidCriticalPrimeHeadMass a ha * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hheadWeight (sq_nonneg _)
  have htailOverlap : ∀ z : ℂ,
      (∑ p ∈ U, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p *
          rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤ 1 := by
    intro z
    simpa [U, P] using rapidCriticalPrimeTailHeads_bound a ha 0 z T
  have htail :
      (∑ p ∈ U, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) ≤
        ‖f‖ ^ 2 := by
    have h := sum_normSq_criticalPrimeKernelRestriction_rapid_le ha f U htailOverlap
    simpa using h
  calc
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) =
      (∑ p ∈ H, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2) +
      ∑ p ∈ U, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ 2 := by
      rw [← Finset.sum_union hdisj, hunion]
    _ ≤ rapidCriticalPrimeHeadMass a ha * ‖f‖ ^ 2 + ‖f‖ ^ 2 :=
      add_le_add hhead htail
    _ = rapidCriticalPrimeBesselBound a ha * ‖f‖ ^ 2 := by
      unfold rapidCriticalPrimeBesselBound
      ring

theorem summable_normSq_criticalPrimeKernelRestriction_rapid
    {a : ℝ} (ha : 0 < a) (f : MomentFock) :
    Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℝ) := by
  have hs : Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℕ) := by
    refine summable_of_sum_le
      (c := rapidCriticalPrimeBesselBound a ha * ‖f‖ ^ 2)
      (fun p => by positivity) ?_
    intro T
    exact sum_normSq_criticalPrimeKernelRestriction_rapid_le_canonical ha f T
  exact hs.congr fun p => (Real.rpow_two _).symm

theorem tsum_normSq_criticalPrimeKernelRestriction_rapid_le
    {a : ℝ} (ha : 0 < a) (f : MomentFock) :
    ∑' p, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℝ) ≤
      (Real.sqrt (rapidCriticalPrimeBesselBound a ha) * ‖f‖) ^ (2 : ℝ) := by
  have hsNat : Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℕ) := by
    have hs := summable_normSq_criticalPrimeKernelRestriction_rapid ha f
    exact hs.congr fun p => Real.rpow_two _
  have hNat := le_of_tendsto hsNat.hasSum (Filter.Eventually.of_forall fun T =>
    sum_normSq_criticalPrimeKernelRestriction_rapid_le_canonical ha f T)
  have hleft :
      (∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℝ)) =
      ∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℕ) := by
    apply tsum_congr
    intro p
    exact Real.rpow_two _
  rw [hleft]
  calc
    (∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℕ)) ≤
      rapidCriticalPrimeBesselBound a ha * ‖f‖ ^ 2 := hNat
    _ = (Real.sqrt (rapidCriticalPrimeBesselBound a ha) * ‖f‖) ^ (2 : ℝ) := by
      rw [Real.rpow_two, mul_pow,
        Real.sq_sqrt (rapidCriticalPrimeBesselBound_nonneg a ha)]

/-- Literal all-prime normalized evaluation operator on the rapid exponential moment carrier. -/
def rapidCriticalPrimeSamplingOperator (a : ℝ) (ha : 0 < a) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo :=
  criticalPrimeKernelSamplingOperator
    (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha))
    (summable_normSq_criticalPrimeKernelRestriction_rapid ha)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_rapid_le ha)

@[simp] theorem rapidCriticalPrimeSamplingOperator_apply
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (p : Nat.Primes) :
    rapidCriticalPrimeSamplingOperator a ha f p =
      criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f := rfl

theorem rapidCriticalPrimeSamplingOperator_not_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ¬ (rapidCriticalPrimeSamplingOperator a ha).IsHilbertSchmidt := by
  unfold rapidCriticalPrimeSamplingOperator
  exact criticalPrimeKernelSamplingOperator_not_isHilbertSchmidt
    (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha))
    (fun p => norm_criticalPrimeMomentFockKernel _ p)
    (summable_normSq_criticalPrimeKernelRestriction_rapid ha)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_rapid_le ha)

/-- Positive rapid-Fock critical-prime incidence operator. -/
def rapidCriticalPrimeSamplingIncidence (a : ℝ) (ha : 0 < a) :
    MomentFock →L[ℂ] MomentFock :=
  criticalPrimeSamplingIncidence (rapidCriticalPrimeSamplingOperator a ha)

theorem rapidCriticalPrimeSamplingIncidence_isPositive
    (a : ℝ) (ha : 0 < a) :
    (rapidCriticalPrimeSamplingIncidence a ha).IsPositive :=
  criticalPrimeSamplingIncidence_isPositive _

theorem rapidCriticalPrimeSamplingIncidence_not_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) :
    ¬ MemSchattenClass 1 (rapidCriticalPrimeSamplingIncidence a ha) := by
  unfold rapidCriticalPrimeSamplingIncidence rapidCriticalPrimeSamplingOperator
  exact criticalPrimeKernelSamplingIncidence_not_memSchattenClass_one
    (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha))
    (fun p => norm_criticalPrimeMomentFockKernel _ p)
    (summable_normSq_criticalPrimeKernelRestriction_rapid ha)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_rapid_le ha)

theorem tsum_normSq_criticalPrimeKernelRestriction_rapid_tail_le
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (P : Finset Nat.Primes)
    (hoverlap : ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p *
            rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤ δ)
    (f : MomentFock) :
    ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p f‖ ^ (2 : ℝ) ≤
      (Real.sqrt δ * ‖f‖) ^ (2 : ℝ) := by
  let k : Nat.Primes → MomentFock :=
    criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)
  have hsFull : Summable fun p => ‖criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ) := by
    have hs := summable_normSq_criticalPrimeKernelRestriction_rapid ha f
    exact hs.congr fun p => Real.rpow_two _
  have hsTail : Summable fun p => ‖if p ∈ P then 0 else
      criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hsFull
    by_cases hp : p ∈ P
    · rw [if_pos hp]
      norm_num
      positivity
    · rw [if_neg hp]
  have hNat := le_of_tendsto hsTail.hasSum (Filter.Eventually.of_forall fun T =>
    sum_normSq_criticalPrimeKernelRestriction_rapid_tail_le ha P hoverlap f T)
  have hleft :
      (∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℝ)) =
        ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ) := by
    apply tsum_congr
    intro p
    exact Real.rpow_two _
  rw [hleft]
  calc
    (∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ)) ≤
      δ * ‖f‖ ^ 2 := hNat
    _ = (Real.sqrt δ * ‖f‖) ^ (2 : ℝ) := by
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ]

/-- Normalized critical-prime evaluation on the rapid exponential carrier is compact. -/
theorem rapidCriticalPrimeSamplingOperator_isCompactOperator
    {a : ℝ} (ha : 0 < a) :
    IsCompactOperator (rapidCriticalPrimeSamplingOperator a ha) := by
  let P : ℕ → Finset Nat.Primes := rapidCriticalPrimeTailHeads a ha
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let ε : ℕ → ℝ := fun n => Real.sqrt (δ n)
  have hδ : ∀ n, 0 ≤ δ n := by intro n; dsimp [δ]; positivity
  have hδ0 : Tendsto δ atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hshift
    have hinv := hcast.inv_tendsto_atTop
    have hfun : (fun n : ℕ => ((n + 1 : ℕ) : ℝ))⁻¹ = δ := by
      funext n
      simp [δ]
    rw [hfun] at hinv
    exact hinv
  have hε : ∀ n, 0 ≤ ε n := by intro n; dsimp [ε]; exact Real.sqrt_nonneg _
  have hε0 : Tendsto ε atTop (nhds 0) := by
    simpa [ε, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hδ0
  unfold rapidCriticalPrimeSamplingOperator
  apply criticalPrimeKernelSamplingOperator_isCompactOperator_of_tailBessel
    (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha))
    (summable_normSq_criticalPrimeKernelRestriction_rapid ha)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_rapid_le ha)
    P ε hε hε0
  intro n f
  exact tsum_normSq_criticalPrimeKernelRestriction_rapid_tail_le
    ha (hδ n) (P n) (by
      intro z T
      exact rapidCriticalPrimeTailHeads_bound a ha n z T) f

theorem rapidCriticalPrimeSamplingIncidence_isCompactOperator
    {a : ℝ} (ha : 0 < a) :
    IsCompactOperator (rapidCriticalPrimeSamplingIncidence a ha) :=
  criticalPrimeSamplingIncidence_isCompactOperator
    (rapidCriticalPrimeSamplingOperator_isCompactOperator ha)

end

end RHTower
