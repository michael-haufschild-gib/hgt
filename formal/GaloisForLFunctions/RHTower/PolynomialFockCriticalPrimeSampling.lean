import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.RHTower.CriticalPrimeKernelSamplingCompact

/-!
# Critical-prime sampling on polynomial moment-Fock carriers

Local weighted evaluation plus exact prime tangent-ball overlap constructs the literal normalized
all-prime sampler for every `m ≥ 4`. Its positive incidence is not trace class. For `m > 4`, a
finite-prime exhaustion has Bessel tails tending to zero, proving compactness of sampler and
incidence.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

theorem sum_criticalPrimeWeight_mul_tangentBallIntegral_le
    {m B : ℝ} (hm : 4 ≤ m)
    (f : MomentFock) (T : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B) :
    (∑ p ∈ T, criticalPrimeSamplingWeight p *
      ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
          (polynomialFockTangentRadius m (Real.log (p : ℝ))),
        polynomialMomentFockWeightedNormSq m (by linarith) f z) ≤
      B * ‖f‖ ^ 2 := by
  classical
  have hm2 : 2 ≤ m := by linarith
  let D : ℂ → ℝ := polynomialMomentFockWeightedNormSq m hm2 f
  let A : Nat.Primes → Set ℂ := fun p => Metric.ball
    ((Real.log (p : ℝ) : ℝ) : ℂ)
    (polynomialFockTangentRadius m (Real.log (p : ℝ)))
  let g : Nat.Primes → ℂ → ℝ := fun p =>
    (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z)
  have hDint : Integrable D := integrable_polynomialMomentFockWeightedNormSq m hm2 f
  have hgint : ∀ p, Integrable (g p) := by
    intro p
    exact (hDint.const_mul (criticalPrimeSamplingWeight p)).indicator measurableSet_ball
  have hsumint : Integrable (fun z => ∑ p ∈ T, g p z) :=
    integrable_finsetSum T (fun p _ => hgint p)
  have hBint : Integrable (fun z => B * D z) := hDint.const_mul B
  have hpoint : ∀ z : ℂ, (∑ p ∈ T, g p z) ≤ B * D z := by
    intro z
    have hD : 0 ≤ D z := polynomialMomentFockWeightedNormSq_nonneg m hm2 f z
    calc
      (∑ p ∈ T, g p z) =
          (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              polynomialFockTangentRadius m (Real.log (p : ℝ))
            then criticalPrimeSamplingWeight p else 0) * D z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hz : z ∈ A p
        · have hdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
            simpa [A, Metric.mem_ball] using hz
          change (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z) z = _
          rw [Set.indicator_of_mem hz, if_pos hdist]
        · have hdist : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
            simpa [A, Metric.mem_ball] using hz
          change (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z) z = _
          rw [Set.indicator, if_neg hz, if_neg hdist]
          ring
      _ ≤ B * D z := mul_le_mul_of_nonneg_right (hoverlap z) hD
  have hint : (∫ z, ∑ p ∈ T, g p z) ≤ ∫ z, B * D z :=
    MeasureTheory.integral_mono hsumint hBint hpoint
  have hsumEq :
      (∑ p ∈ T, criticalPrimeSamplingWeight p *
        ∫ z in A p, D z) = ∫ z, ∑ p ∈ T, g p z := by
    rw [MeasureTheory.integral_finsetSum T (fun p _ => hgint p)]
    apply Finset.sum_congr rfl
    intro p hp
    change criticalPrimeSamplingWeight p * (∫ z in A p, D z) =
      ∫ z, (A p).indicator (fun z => criticalPrimeSamplingWeight p * D z) z
    rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.integral_const_mul]
  rw [← hsumEq] at hint
  rw [MeasureTheory.integral_const_mul,
    integral_polynomialMomentFockWeightedNormSq m hm2] at hint
  simpa [D, A, hm2] using hint

/-- Finite normalized critical-prime evaluation energy is controlled by the tangent-ball overlap
constant. -/
theorem sum_normSq_criticalPrimeKernelRestriction_polynomial_le
    {m B : ℝ} (hm : 4 ≤ m)
    (f : MomentFock) (T : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B) :
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2) ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hlocal : ∀ p : Nat.Primes,
      ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2 ≤
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
          (criticalPrimeSamplingWeight p *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (polynomialFockTangentRadius m (Real.log (p : ℝ))),
              polynomialMomentFockWeightedNormSq m hm2 f z) := by
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
          (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (polynomialFockTangentRadius m (Real.log (p : ℝ))),
              polynomialMomentFockWeightedNormSq m hm2 f z) :=
        mul_le_mul_of_nonneg_left heval hweight
      _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
          (criticalPrimeSamplingWeight p *
            ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
                (polynomialFockTangentRadius m (Real.log (p : ℝ))),
              polynomialMomentFockWeightedNormSq m hm2 f z) := by ring
  calc
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p f‖ ^ 2) ≤
      ∑ p ∈ T, Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        (criticalPrimeSamplingWeight p *
          ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (polynomialFockTangentRadius m (Real.log (p : ℝ))),
            polynomialMomentFockWeightedNormSq m hm2 f z) :=
      Finset.sum_le_sum fun p _ => hlocal p
    _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        (∑ p ∈ T, criticalPrimeSamplingWeight p *
          ∫ z in Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
              (polynomialFockTangentRadius m (Real.log (p : ℝ))),
            polynomialMomentFockWeightedNormSq m hm2 f z) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        (B * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left
      (sum_criticalPrimeWeight_mul_tangentBallIntegral_le hm f T hoverlap)
      (Real.exp_nonneg _)
    _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 := by ring

/-- Canonical uniform tangent-ball overlap bound selected from the unconditional arithmetic
overlap theorem. -/
def polynomialCriticalPrimeOverlapBound (m : ℝ) (hm : 4 ≤ m) : ℝ :=
  Classical.choose (exists_uniform_criticalPrime_tangentBallMass_bound hm)

theorem polynomialCriticalPrimeOverlapBound_nonneg (m : ℝ) (hm : 4 ≤ m) :
    0 ≤ polynomialCriticalPrimeOverlapBound m hm :=
  (Classical.choose_spec (exists_uniform_criticalPrime_tangentBallMass_bound hm)).1

theorem sum_criticalPrime_tangentBallMass_le_overlapBound
    (m : ℝ) (hm : 4 ≤ m) (z : ℂ) (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) ≤
      polynomialCriticalPrimeOverlapBound m hm :=
  (Classical.choose_spec (exists_uniform_criticalPrime_tangentBallMass_bound hm)).2 z T

/-- Explicit Bessel constant produced by local weighted evaluation and prime tangent-ball overlap. -/
def polynomialCriticalPrimeBesselBound (m : ℝ) (hm : 4 ≤ m) : ℝ :=
  Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
    polynomialCriticalPrimeOverlapBound m hm

theorem polynomialCriticalPrimeBesselBound_nonneg (m : ℝ) (hm : 4 ≤ m) :
    0 ≤ polynomialCriticalPrimeBesselBound m hm := by
  unfold polynomialCriticalPrimeBesselBound
  exact mul_nonneg (Real.exp_nonneg _)
    (polynomialCriticalPrimeOverlapBound_nonneg m hm)

theorem sum_normSq_criticalPrimeKernelRestriction_polynomial_le_canonical
    {m : ℝ} (hm : 4 ≤ m) (f : MomentFock) (T : Finset Nat.Primes) :
    (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2) ≤
      polynomialCriticalPrimeBesselBound m hm * ‖f‖ ^ 2 := by
  simpa [polynomialCriticalPrimeBesselBound] using
    sum_normSq_criticalPrimeKernelRestriction_polynomial_le hm
      f T (fun z => sum_criticalPrime_tangentBallMass_le_overlapBound m hm z T)

theorem summable_normSq_criticalPrimeKernelRestriction_polynomial
    {m : ℝ} (hm : 4 ≤ m) (f : MomentFock) :
    Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℝ) := by
  have hs : Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℕ) := by
    refine summable_of_sum_le
      (c := polynomialCriticalPrimeBesselBound m hm * ‖f‖ ^ 2)
      (fun p => by positivity) ?_
    intro T
    exact sum_normSq_criticalPrimeKernelRestriction_polynomial_le_canonical hm f T
  exact hs.congr fun p => (Real.rpow_two _).symm

theorem tsum_normSq_criticalPrimeKernelRestriction_polynomial_le
    {m : ℝ} (hm : 4 ≤ m) (f : MomentFock) :
    ∑' p, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℝ) ≤
      (Real.sqrt (polynomialCriticalPrimeBesselBound m hm) * ‖f‖) ^ (2 : ℝ) := by
  have hsNat : Summable fun p => ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℕ) := by
    have hs := summable_normSq_criticalPrimeKernelRestriction_polynomial hm f
    exact hs.congr fun p => Real.rpow_two _
  have hNat := le_of_tendsto hsNat.hasSum (Filter.Eventually.of_forall fun T =>
    sum_normSq_criticalPrimeKernelRestriction_polynomial_le_canonical hm f T)
  have hleft :
      (∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℝ)) =
      ∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℕ) := by
    apply tsum_congr
    intro p
    exact Real.rpow_two _
  rw [hleft]
  calc
    (∑' p, ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℕ)) ≤
      polynomialCriticalPrimeBesselBound m hm * ‖f‖ ^ 2 := hNat
    _ = (Real.sqrt (polynomialCriticalPrimeBesselBound m hm) * ‖f‖) ^ (2 : ℝ) := by
      rw [Real.rpow_two, mul_pow,
        Real.sq_sqrt (polynomialCriticalPrimeBesselBound_nonneg m hm)]

/-- Literal all-prime normalized evaluation operator on the polynomial moment-Fock carrier. -/
def polynomialCriticalPrimeSamplingOperator (m : ℝ) (hm : 4 ≤ m) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo :=
  criticalPrimeKernelSamplingOperator
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith)))
    (summable_normSq_criticalPrimeKernelRestriction_polynomial hm)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_polynomial_le hm)

@[simp] theorem polynomialCriticalPrimeSamplingOperator_apply
    (m : ℝ) (hm : 4 ≤ m) (f : MomentFock) (p : Nat.Primes) :
    polynomialCriticalPrimeSamplingOperator m hm f p =
      criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f := rfl

theorem polynomialCriticalPrimeSamplingOperator_not_isHilbertSchmidt
    (m : ℝ) (hm : 4 ≤ m) :
    ¬ (polynomialCriticalPrimeSamplingOperator m hm).IsHilbertSchmidt := by
  unfold polynomialCriticalPrimeSamplingOperator
  exact criticalPrimeKernelSamplingOperator_not_isHilbertSchmidt
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith)))
    (fun p => norm_criticalPrimeMomentFockKernel _ p)
    (summable_normSq_criticalPrimeKernelRestriction_polynomial hm)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_polynomial_le hm)

/-- Positive polynomial-Fock critical-prime incidence operator. -/
def polynomialCriticalPrimeSamplingIncidence (m : ℝ) (hm : 4 ≤ m) :
    MomentFock →L[ℂ] MomentFock :=
  criticalPrimeSamplingIncidence (polynomialCriticalPrimeSamplingOperator m hm)

theorem polynomialCriticalPrimeSamplingIncidence_isPositive
    (m : ℝ) (hm : 4 ≤ m) :
    (polynomialCriticalPrimeSamplingIncidence m hm).IsPositive := by
  exact criticalPrimeSamplingIncidence_isPositive _

theorem polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_one
    (m : ℝ) (hm : 4 ≤ m) :
    ¬ MemSchattenClass 1 (polynomialCriticalPrimeSamplingIncidence m hm) := by
  unfold polynomialCriticalPrimeSamplingIncidence polynomialCriticalPrimeSamplingOperator
  exact criticalPrimeKernelSamplingIncidence_not_memSchattenClass_one
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith)))
    (fun p => norm_criticalPrimeMomentFockKernel _ p)
    (summable_normSq_criticalPrimeKernelRestriction_polynomial hm)
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_polynomial_le hm)

/-- Superquartic prime tangent-ball overlaps admit finite prime heads with a quantitative vanishing
tail bound. -/
theorem exists_polynomialCriticalPrime_tangentBallTail_bound
    {m : ℝ} (hm : 4 < m) :
    ∃ P : ℕ → Finset Nat.Primes, ∀ (n : ℕ) (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P n),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤
        ((n : ℝ) + 1)⁻¹ := by
  classical
  let c : ℝ := 2 ^ (m / 2 - 1)
  let W : ℝ → ℝ := fun x =>
    primeLogWindowMass x (c * criticalPrimeFockRadius m x)
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hW : Tendsto W atTop (nhds 0) :=
    tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_zero hm hc
  have hδpos : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hexists : ∀ n : ℕ, ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |W x| < δ n := by
    intro n
    have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) (hδpos n))
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    exact ⟨X, fun x hx => by simpa [Real.dist_eq] using hX x hx⟩
  choose X hX using hexists
  let Y : ℕ → ℝ := fun n => max 1 (X n)
  let P : ℕ → Finset Nat.Primes := fun n =>
    GaloisForLFunctions.primesBelowSubtype
      (⌊Real.exp (Y n + 1 / 2)⌋₊ + 1)
  refine ⟨P, fun n z T => ?_⟩
  let S : Finset Nat.Primes := (T.filter (· ∉ P n)).filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ))
  by_cases hS : S.Nonempty
  · obtain ⟨p, hpS⟩ := hS
    have hpTail : p ∉ P n := (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2
    have hpBall : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ)) :=
      (Finset.mem_filter.mp hpS).2
    have hpLower : ⌊Real.exp (Y n + 1 / 2)⌋₊ + 1 ≤ (p : ℕ) := by
      have hnotlt : ¬ (p : ℕ) < ⌊Real.exp (Y n + 1 / 2)⌋₊ + 1 := by
        intro hlt
        apply hpTail
        rw [mem_primesBelowSubtype_iff]
        exact hlt
      omega
    have hexplt : Real.exp (Y n + 1 / 2) < (p : ℝ) := by
      apply (Nat.floor_lt' p.2.ne_zero).mp
      omega
    have hplog : Y n + 1 / 2 < Real.log (p : ℝ) := by
      have hpcastpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
      have := Real.log_lt_log (Real.exp_pos _) hexplt
      simpa using this
    let xp : ℝ := Real.log (p : ℝ)
    have hnorm : ‖(xp : ℂ) - z‖ < polynomialFockTangentRadius m xp := by
      rw [norm_sub_rev]
      simpa [xp, dist_eq_norm] using hpBall
    have habs : |xp - z.re| ≤ ‖(xp : ℂ) - z‖ := by
      simpa using Complex.abs_re_le_norm ((xp : ℂ) - z)
    have hlocal : |xp - z.re| < polynomialFockTangentRadius m xp := habs.trans_lt hnorm
    have hhalf : |xp - z.re| < 1 / 2 :=
      hlocal.trans_le (polynomialFockTangentRadius_le_half (le_of_lt hm))
    have hYz : Y n < z.re := by
      have hright := (abs_lt.mp hhalf).2
      dsimp [xp] at hright
      linarith
    have hzre : 1 ≤ z.re := (le_max_left 1 (X n)).trans hYz.le
    have hWX : |W z.re| < δ n := hX n z.re ((le_max_right 1 (X n)).trans hYz.le)
    have hsumWindow := sum_criticalPrimeSamplingWeight_tangentBalls_le_windowMass
      (le_of_lt hm) hzre (T.filter (· ∉ P n))
    have hWnonneg : 0 ≤ W z.re := by
      have hempty := sum_criticalPrimeSamplingWeight_tangentBalls_le_windowMass
        (le_of_lt hm) hzre (∅ : Finset Nat.Primes)
      simpa [W, c] using hempty
    calc
      (∑ p ∈ T.filter (· ∉ P n),
          if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              polynomialFockTangentRadius m (Real.log (p : ℝ))
            then criticalPrimeSamplingWeight p else 0) ≤ W z.re := by
        simpa [W, c] using hsumWindow
      _ ≤ |W z.re| := le_abs_self _
      _ ≤ δ n := hWX.le
      _ = ((n : ℝ) + 1)⁻¹ := rfl
  · have hzero : ∀ p ∈ T.filter (· ∉ P n),
        (if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) = 0 := by
      intro p hp
      have hpnot : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ)) := by
        intro hpball
        apply hS
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpball⟩⟩
      exact if_neg hpnot
    rw [Finset.sum_eq_zero hzero]
    positivity

theorem sum_normSq_criticalPrimeKernelRestriction_polynomial_tail_le
    {m δ : ℝ} (hm : 4 ≤ m) (P : Finset Nat.Primes)
    (hoverlap : ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤ δ)
    (f : MomentFock) (T : Finset Nat.Primes) :
    (∑ p ∈ T, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2) ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * δ * ‖f‖ ^ 2 := by
  have hbase := sum_normSq_criticalPrimeKernelRestriction_polynomial_le hm f
    (T.filter (· ∉ P)) (fun z => hoverlap z T)
  calc
    (∑ p ∈ T, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2) =
      ∑ p ∈ T.filter (· ∉ P), ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpP : p ∈ P <;> simp [hpP]
    _ ≤ Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * δ * ‖f‖ ^ 2 := hbase

theorem tsum_normSq_criticalPrimeKernelRestriction_polynomial_tail_le
    {m δ : ℝ} (hm : 4 ≤ m) (hδ : 0 ≤ δ) (P : Finset Nat.Primes)
    (hoverlap : ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤ δ)
    (f : MomentFock) :
    ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f‖ ^ (2 : ℝ) ≤
      (Real.sqrt (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * δ) * ‖f‖) ^
        (2 : ℝ) := by
  let k : Nat.Primes → MomentFock :=
    criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))
  have hsFull : Summable fun p => ‖criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ) := by
    have hs := summable_normSq_criticalPrimeKernelRestriction_polynomial hm f
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
    sum_normSq_criticalPrimeKernelRestriction_polynomial_tail_le hm P hoverlap f T)
  have hleft :
      (∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℝ)) =
        ∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ) := by
    apply tsum_congr
    intro p
    exact Real.rpow_two _
  rw [hleft]
  calc
    (∑' p, ‖if p ∈ P then 0 else criticalPrimeKernelRestriction k p f‖ ^ (2 : ℕ)) ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * δ * ‖f‖ ^ 2 := hNat
    _ = (Real.sqrt (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * δ) * ‖f‖) ^
        (2 : ℝ) := by
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt]
      exact mul_nonneg (Real.exp_nonneg _) hδ

/-- Superquartic normalized critical-prime evaluation is compact. -/
theorem polynomialCriticalPrimeSamplingOperator_isCompactOperator
    {m : ℝ} (hm : 4 < m) :
    IsCompactOperator (polynomialCriticalPrimeSamplingOperator m (le_of_lt hm)) := by
  obtain ⟨P, hP⟩ := exists_polynomialCriticalPrime_tangentBallTail_bound hm
  let a : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let ε : ℕ → ℝ := fun n => Real.sqrt (a * δ n)
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
    have hprod : Tendsto (fun n => a * δ n) atTop (nhds 0) := by
      simpa using hδ0.const_mul a
    simpa [ε, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hprod
  unfold polynomialCriticalPrimeSamplingOperator
  apply criticalPrimeKernelSamplingOperator_isCompactOperator_of_tailBessel
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith)))
    (summable_normSq_criticalPrimeKernelRestriction_polynomial (le_of_lt hm))
    (Real.sqrt_nonneg _)
    (tsum_normSq_criticalPrimeKernelRestriction_polynomial_le (le_of_lt hm))
    P ε hε hε0
  intro n f
  exact tsum_normSq_criticalPrimeKernelRestriction_polynomial_tail_le
    (le_of_lt hm) (hδ n) (P n) (hP n) f

theorem polynomialCriticalPrimeSamplingIncidence_isCompactOperator
    {m : ℝ} (hm : 4 < m) :
    IsCompactOperator (polynomialCriticalPrimeSamplingIncidence m (le_of_lt hm)) := by
  exact criticalPrimeSamplingIncidence_isCompactOperator
    (polynomialCriticalPrimeSamplingOperator_isCompactOperator hm)

end

end RHTower
