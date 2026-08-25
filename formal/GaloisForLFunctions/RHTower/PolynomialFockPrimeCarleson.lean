import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap

/-!
# Concrete critical-prime Carleson estimate for the polynomial moment Fock carrier

The local normalized-evaluation estimate is summed over finite prime packets.  Finite tangent-ball
overlap is controlled by one prime-log window, so the exact plane norm identity gives a uniform
Bessel estimate.  A fixed finite prime head handles the bounded real region.
-/

open MeasureTheory Set Metric Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Real logarithmic coordinate of a prime node. -/
def criticalPrimeLog (p : Nat.Primes) : ℝ :=
  Real.log ((p : ℕ) : ℝ)

/-- Fixed recentering dilation for polynomial tangent balls. -/
def polynomialFockPrimeCoverFactor (m : ℝ) : ℝ :=
  2 ^ (m / 2 - 1)

/-- Finite tangent-ball overlap mass at a point. -/
noncomputable def polynomialFockPrimeTangentBallMass
    (m : ℝ) (P : Finset Nat.Primes) (z : ℂ) : ℝ := by
  classical
  exact ∑ p ∈ P, if z ∈ Metric.ball
      ((criticalPrimeLog p : ℝ) : ℂ)
      (polynomialFockTangentRadius m (criticalPrimeLog p))
    then criticalPrimeSamplingWeight p else 0

/-- If all prime centers lie beyond `Y + 1`, tangent-ball overlap is controlled by the scaled
critical-window mass on the ray `x ≥ Y`. -/
theorem polynomialFockPrimeTangentBallMass_le_of_tailWindow
    {m B Y : ℝ} (hm : 4 ≤ m) (hY : 2 ≤ Y)
    (hB : ∀ x : ℝ, Y ≤ x →
      primeLogWindowMass x
        (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m x) ≤ B)
    (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, Y + 1 < criticalPrimeLog p) (z : ℂ) :
    polynomialFockPrimeTangentBallMass m P z ≤ B := by
  classical
  by_cases hzre : Y ≤ z.re
  · have hsum := sum_criticalPrimeSamplingWeight_tangentBalls_le_windowMass hm
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) (hY.trans hzre)) P
    calc
      polynomialFockPrimeTangentBallMass m P z ≤ primeLogWindowMass z.re
          (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m z.re) := by
        simpa [polynomialFockPrimeTangentBallMass, criticalPrimeLog,
          polynomialFockPrimeCoverFactor, Metric.mem_ball] using hsum
      _ ≤ B := hB z.re hzre
  · have hzlt : z.re < Y := lt_of_not_ge hzre
    have hzero : ∀ p ∈ P, z ∉ Metric.ball
        ((criticalPrimeLog p : ℝ) : ℂ)
        (polynomialFockTangentRadius m (criticalPrimeLog p)) := by
      intro p hp hzball
      have habs : |criticalPrimeLog p - z.re| ≤
          ‖z - ((criticalPrimeLog p : ℝ) : ℂ)‖ := by
        have h := Complex.abs_re_le_norm
          (z - ((criticalPrimeLog p : ℝ) : ℂ))
        simpa [abs_sub_comm] using h
      have hdist : ‖z - ((criticalPrimeLog p : ℝ) : ℂ)‖ <
          polynomialFockTangentRadius m (criticalPrimeLog p) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzball
      have hhalf := polynomialFockTangentRadius_le_half
        (m := m) (x := criticalPrimeLog p) hm
      have hdiff : 1 < criticalPrimeLog p - z.re := by linarith [hP p hp]
      linarith [le_abs_self (criticalPrimeLog p - z.re)]
    have hBnonneg : 0 ≤ B := by
      have hmassNonneg : 0 ≤ primeLogWindowMass Y
          (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m Y) := by
        rw [primeLogWindowMass_eq_sum Y
          (mul_nonneg (by unfold polynomialFockPrimeCoverFactor; positivity)
            (criticalPrimeFockRadius_pos (by linarith)).le)]
        exact Finset.sum_nonneg fun n hn => primeLogPowWeight_two_nonneg n
      exact hmassNonneg.trans (hB Y le_rfl)
    calc
      polynomialFockPrimeTangentBallMass m P z = 0 := by
        unfold polynomialFockPrimeTangentBallMass
        apply Finset.sum_eq_zero
        intro p hp
        rw [if_neg (hzero p hp)]
      _ ≤ B := hBnonneg

/-- Weighted tangent-ball integrals sum to at most the overlap bound times the exact carrier norm. -/
theorem sum_criticalPrimeSamplingWeight_mul_tangentBallIntegral_le
    {m B Y : ℝ} (hm : 4 ≤ m) (hm2 : 2 ≤ m) (hY : 2 ≤ Y)
    (hB : ∀ x : ℝ, Y ≤ x →
      primeLogWindowMass x
        (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m x) ≤ B)
    (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, Y + 1 < criticalPrimeLog p) (f : MomentFock) :
    ∑ p ∈ P, criticalPrimeSamplingWeight p *
        ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
          (polynomialFockTangentRadius m (criticalPrimeLog p)),
          polynomialMomentFockWeightedNormSq m hm2 f z ≤
      B * ‖f‖ ^ 2 := by
  classical
  let W : ℂ → ℝ := polynomialMomentFockWeightedNormSq m hm2 f
  have hWint : Integrable W := integrable_polynomialMomentFockWeightedNormSq m hm2 f
  have htermInt : ∀ p ∈ P, Integrable (fun z : ℂ =>
      criticalPrimeSamplingWeight p *
        (Metric.ball (((criticalPrimeLog p : ℝ) : ℂ))
          (polynomialFockTangentRadius m (criticalPrimeLog p))).indicator W z) := by
    intro p hp
    exact (hWint.indicator measurableSet_ball).const_mul _
  have hsumIntegral :
      ∑ p ∈ P, criticalPrimeSamplingWeight p *
          ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
            (polynomialFockTangentRadius m (criticalPrimeLog p)), W z =
        ∫ z : ℂ, W z * polynomialFockPrimeTangentBallMass m P z := by
    calc
      ∑ p ∈ P, criticalPrimeSamplingWeight p *
          ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
            (polynomialFockTangentRadius m (criticalPrimeLog p)), W z =
          ∑ p ∈ P, ∫ z : ℂ, criticalPrimeSamplingWeight p *
            (Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
              (polynomialFockTangentRadius m (criticalPrimeLog p))).indicator W z := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator measurableSet_ball]
      _ = ∫ z : ℂ, ∑ p ∈ P, criticalPrimeSamplingWeight p *
            (Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
              (polynomialFockTangentRadius m (criticalPrimeLog p))).indicator W z :=
        (MeasureTheory.integral_finsetSum P htermInt).symm
      _ = ∫ z : ℂ, W z * polynomialFockPrimeTangentBallMass m P z := by
        congr 1
        funext z
        unfold polynomialFockPrimeTangentBallMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hz : z ∈ Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
            (polynomialFockTangentRadius m (criticalPrimeLog p))
        · simp [hz]
          ring
        · simp [hz]
  have hoverlapInt : Integrable
      (fun z : ℂ => W z * polynomialFockPrimeTangentBallMass m P z) := by
    have hsumInt := MeasureTheory.integrable_finsetSum P htermInt
    apply hsumInt.congr
    filter_upwards with z
    unfold polynomialFockPrimeTangentBallMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hz : z ∈ Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
        (polynomialFockTangentRadius m (criticalPrimeLog p))
    · simp [hz]
      ring
    · simp [hz]
  have hBint : Integrable (fun z : ℂ => W z * B) := hWint.mul_const B
  have hint : (∫ z : ℂ, W z * polynomialFockPrimeTangentBallMass m P z) ≤
      ∫ z : ℂ, W z * B := by
    exact MeasureTheory.integral_mono hoverlapInt hBint fun z =>
      mul_le_mul_of_nonneg_left
        (polynomialFockPrimeTangentBallMass_le_of_tailWindow hm hY hB P hP z)
        (polynomialMomentFockWeightedNormSq_nonneg m hm2 f z)
  calc
    ∑ p ∈ P, criticalPrimeSamplingWeight p *
        ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
          (polynomialFockTangentRadius m (criticalPrimeLog p)),
          polynomialMomentFockWeightedNormSq m hm2 f z =
        ∫ z : ℂ, W z * polynomialFockPrimeTangentBallMass m P z := hsumIntegral
    _ ≤ ∫ z : ℂ, W z * B := hint
    _ = B * ‖f‖ ^ 2 := by
      rw [MeasureTheory.integral_mul_const,
        integral_polynomialMomentFockWeightedNormSq]
      ring

/-- Finite tail Bessel estimate from the local normalized-evaluation and overlap laws. -/
theorem finite_criticalPrimePolynomialMomentFock_tailBessel
    {m B Y : ℝ} (hm : 4 ≤ m) (hm2 : 2 ≤ m) (hY : 2 ≤ Y)
    (hB : ∀ x : ℝ, Y ≤ x →
      primeLogWindowMass x
        (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m x) ≤ B)
    (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, Y + 1 < criticalPrimeLog p) (f : MomentFock) :
    ∑ p ∈ P, criticalPrimeSamplingWeight p *
        ‖inner ℂ (criticalPrimePolynomialMomentFockKernel m hm2 p) f‖ ^ 2 ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 := by
  let C := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  have hlocal : ∀ p ∈ P,
      ‖inner ℂ (criticalPrimePolynomialMomentFockKernel m hm2 p) f‖ ^ 2 ≤
        C * ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
          (polynomialFockTangentRadius m (criticalPrimeLog p)),
          polynomialMomentFockWeightedNormSq m hm2 f z := by
    intro p hp
    change ‖inner ℂ (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
      ((criticalPrimeLog p : ℝ) : ℂ)) f‖ ^ 2 ≤ _
    simpa only [C] using
      normSq_inner_normalizedPolynomialMomentFockKernel_le_localIntegral
        (m := m) (x := criticalPrimeLog p) hm (by have := hP p hp; linarith) f
  have hballs := sum_criticalPrimeSamplingWeight_mul_tangentBallIntegral_le
    hm hm2 hY hB P hP f
  calc
    ∑ p ∈ P, criticalPrimeSamplingWeight p *
        ‖inner ℂ (criticalPrimePolynomialMomentFockKernel m hm2 p) f‖ ^ 2 ≤
        ∑ p ∈ P, criticalPrimeSamplingWeight p *
          (C * ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
            (polynomialFockTangentRadius m (criticalPrimeLog p)),
            polynomialMomentFockWeightedNormSq m hm2 f z) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hlocal p hp)
        (criticalPrimeSamplingWeight_pos p).le
    _ = C * (∑ p ∈ P, criticalPrimeSamplingWeight p *
        ∫ z in Metric.ball ((criticalPrimeLog p : ℝ) : ℂ)
          (polynomialFockTangentRadius m (criticalPrimeLog p)),
          polynomialMomentFockWeightedNormSq m hm2 f z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ C * (B * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hballs (by dsimp [C]; positivity)
    _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 := by
      dsimp [C]
      ring

/-- Fixed finite prime head below logarithmic coordinate `3`. -/
noncomputable def criticalPrimePolynomialFockHead : Finset Nat.Primes :=
  (Nat.primesLE ⌊Real.exp 3⌋₊).subtype Nat.Prime

theorem mem_criticalPrimePolynomialFockHead (p : Nat.Primes) :
    p ∈ criticalPrimePolynomialFockHead ↔ (p : ℕ) ≤ ⌊Real.exp 3⌋₊ := by
  constructor
  · intro hp
    exact (Nat.mem_primesLE.1 (Finset.mem_subtype.1 hp)).1
  · intro hp
    exact Finset.mem_subtype.2 (Nat.mem_primesLE.2 ⟨hp, p.2⟩)

theorem criticalPrimeLog_gt_three_of_not_mem_head
    {p : Nat.Primes} (hp : p ∉ criticalPrimePolynomialFockHead) :
    3 < criticalPrimeLog p := by
  have hfloor : ⌊Real.exp 3⌋₊ < (p : ℕ) := by
    rw [mem_criticalPrimePolynomialFockHead] at hp
    omega
  have hexp : Real.exp 3 < ((p : ℕ) : ℝ) :=
    (Nat.floor_lt' (Nat.Prime.ne_zero p.2)).mp hfloor
  have hlog := Real.log_lt_log (Real.exp_pos 3) hexp
  simpa [criticalPrimeLog] using hlog

/-- Literal weighted normalized-kernel energy at one prime. -/
def criticalPrimePolynomialFockEnergy
    (m : ℝ) (hm2 : 2 ≤ m) (f : MomentFock) (p : Nat.Primes) : ℝ :=
  criticalPrimeSamplingWeight p *
    ‖inner ℂ (criticalPrimePolynomialMomentFockKernel m hm2 p) f‖ ^ 2

theorem criticalPrimePolynomialFockEnergy_nonneg
    (m : ℝ) (hm2 : 2 ≤ m) (f : MomentFock) (p : Nat.Primes) :
    0 ≤ criticalPrimePolynomialFockEnergy m hm2 f p := by
  unfold criticalPrimePolynomialFockEnergy
  exact mul_nonneg (criticalPrimeSamplingWeight_pos p).le (sq_nonneg _)

/-- The fixed finite prime head is bounded by its total sampling weight. -/
theorem finite_criticalPrimePolynomialMomentFock_headBessel
    (m : ℝ) (hm2 : 2 ≤ m) (P : Finset Nat.Primes) (f : MomentFock) :
    ∑ p ∈ P.filter (· ∈ criticalPrimePolynomialFockHead),
        criticalPrimePolynomialFockEnergy m hm2 f p ≤
      (∑ p ∈ criticalPrimePolynomialFockHead, criticalPrimeSamplingWeight p) * ‖f‖ ^ 2 := by
  classical
  let H := P.filter (· ∈ criticalPrimePolynomialFockHead)
  have hpoint : ∀ p ∈ H,
      criticalPrimePolynomialFockEnergy m hm2 f p ≤
        criticalPrimeSamplingWeight p * ‖f‖ ^ 2 := by
    intro p hp
    have hin := norm_inner_le_norm (𝕜 := ℂ)
      (criticalPrimePolynomialMomentFockKernel m hm2 p) f
    rw [norm_criticalPrimePolynomialMomentFockKernel, one_mul] at hin
    have hsq : ‖inner ℂ (criticalPrimePolynomialMomentFockKernel m hm2 p) f‖ ^ 2 ≤
        ‖f‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hin
    exact mul_le_mul_of_nonneg_left hsq (criticalPrimeSamplingWeight_pos p).le
  have hHsub : H ⊆ criticalPrimePolynomialFockHead := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  calc
    ∑ p ∈ P.filter (· ∈ criticalPrimePolynomialFockHead),
        criticalPrimePolynomialFockEnergy m hm2 f p =
      ∑ p ∈ H, criticalPrimePolynomialFockEnergy m hm2 f p := by rfl
    _ ≤ ∑ p ∈ H, criticalPrimeSamplingWeight p * ‖f‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ criticalPrimePolynomialFockHead,
        criticalPrimeSamplingWeight p * ‖f‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hHsub
        (fun p hp hnot => mul_nonneg (criticalPrimeSamplingWeight_pos p).le (sq_nonneg _))
    _ = (∑ p ∈ criticalPrimePolynomialFockHead, criticalPrimeSamplingWeight p) * ‖f‖ ^ 2 := by
      rw [Finset.sum_mul]

/-- Uniform finite-packet Bessel bound for every polynomial degree `m ≥ 4`. -/
theorem finite_criticalPrimePolynomialMomentFock_bessel
    {m B : ℝ} (hm : 4 ≤ m) (hm2 : 2 ≤ m)
    (hB : ∀ x : ℝ, 2 ≤ x →
      primeLogWindowMass x
        (polynomialFockPrimeCoverFactor m * criticalPrimeFockRadius m x) ≤ B)
    (P : Finset Nat.Primes) (f : MomentFock) :
    ∑ p ∈ P, criticalPrimePolynomialFockEnergy m hm2 f p ≤
      ((∑ p ∈ criticalPrimePolynomialFockHead, criticalPrimeSamplingWeight p) +
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B) * ‖f‖ ^ 2 := by
  classical
  let H := P.filter (· ∈ criticalPrimePolynomialFockHead)
  let T := P.filter (· ∉ criticalPrimePolynomialFockHead)
  have hTlog : ∀ p ∈ T, (2 : ℝ) + 1 < criticalPrimeLog p := by
    intro p hp
    norm_num
    exact criticalPrimeLog_gt_three_of_not_mem_head (Finset.mem_filter.mp hp).2
  have hhead := finite_criticalPrimePolynomialMomentFock_headBessel m hm2 P f
  have htailRaw := finite_criticalPrimePolynomialMomentFock_tailBessel hm hm2
    (by norm_num : (2 : ℝ) ≤ 2) hB T hTlog f
  have htail : ∑ p ∈ T, criticalPrimePolynomialFockEnergy m hm2 f p ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 := by
    simpa [criticalPrimePolynomialFockEnergy] using htailRaw
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (· ∈ criticalPrimePolynomialFockHead)
    (criticalPrimePolynomialFockEnergy m hm2 f)
  change (∑ p ∈ H, criticalPrimePolynomialFockEnergy m hm2 f p) +
      (∑ p ∈ T, criticalPrimePolynomialFockEnergy m hm2 f p) =
        ∑ p ∈ P, criticalPrimePolynomialFockEnergy m hm2 f p at hsplit
  rw [← hsplit]
  calc
    (∑ p ∈ H, criticalPrimePolynomialFockEnergy m hm2 f p) +
        ∑ p ∈ T, criticalPrimePolynomialFockEnergy m hm2 f p ≤
      (∑ p ∈ criticalPrimePolynomialFockHead, criticalPrimeSamplingWeight p) * ‖f‖ ^ 2 +
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B * ‖f‖ ^ 2 :=
      add_le_add (by simpa [H] using hhead) htail
    _ = ((∑ p ∈ criticalPrimePolynomialFockHead, criticalPrimeSamplingWeight p) +
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B) * ‖f‖ ^ 2 := by
      ring

end

end RHTower
