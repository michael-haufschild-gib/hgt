import GaloisForLFunctions.RHTower.RapidExponentialFockNormalizedLocalEvaluation
import GaloisForLFunctions.RHTower.RapidExponentialFockPrimeBallOverlap
import GaloisForLFunctions.RHTower.PrimeLogPowRapidWindow

/-!
# Effective rapid-Fock prime weight and vanishing local overlap

The explicit normalized-kernel estimate loses only a quadratic polynomial in the prime-log center.
Multiplying this loss into the critical weight is dominated by fourth prime-log mass.  Higher
Mertens convergence on exponentially shrinking adapted windows then gives a uniform overlap bound
and finite prime heads whose effective overlap tails vanish.  These are the exact Bessel and
compactness inputs for the concrete rapid normalized-prime sampler.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

def rapidExponentialFockEffectiveSamplingWeight
    (a : ℝ) (p : Nat.Primes) : ℝ :=
  criticalPrimeSamplingWeight p *
    rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ))

def rapidExponentialFockLocalEvaluationPolynomialBound (a : ℝ) : ℝ :=
  512 * Real.exp 2 * (a + 1) ^ 4 / a ^ 2

theorem rapidExponentialFockLocalEvaluationFactor_eq
    {a x : ℝ} (ha : 0 < a) :
    rapidExponentialFockLocalEvaluationFactor a x =
      128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2 *
        (1 + max 1 (2 * a * x)) ^ 2 := by
  unfold rapidExponentialFockLocalEvaluationFactor
    rapidExponentialFockTangentCurvature rapidExponentialFockLocalRadius
  have ha0 : a ≠ 0 := ha.ne'
  have ha1 : a + 1 ≠ 0 := by positivity
  have hmax : 1 + max 1 (2 * a * x) ≠ 0 := by
    have : 0 < 1 + max 1 (2 * a * x) := by linarith [le_max_left 1 (2 * a * x)]
    exact this.ne'
  have hexp : Real.exp (2 * a * x) * Real.exp (-a * x) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
    simp
  have hexp' : Real.exp (2 * a * x) * Real.exp (-(a * x)) ^ 2 = 1 := by
    convert hexp using 1 <;> ring
  field_simp [ha0, ha1, hmax]
  nlinarith [hexp']

theorem rapidExponentialFockLocalEvaluationFactor_le_polynomial
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    rapidExponentialFockLocalEvaluationFactor a x ≤
      rapidExponentialFockLocalEvaluationPolynomialBound a * (x + 1) ^ 2 := by
  have hax : 0 ≤ 2 * a * x := by positivity
  have hmax : max 1 (2 * a * x) ≤ 1 + 2 * a * x := by
    exact max_le (by linarith) (by linarith)
  have hone : 1 + max 1 (2 * a * x) ≤ 2 * (1 + a * x) := by linarith
  have hscale : 1 + a * x ≤ (a + 1) * (x + 1) := by nlinarith
  have hsquare : (1 + max 1 (2 * a * x)) ^ 2 ≤
      4 * (a + 1) ^ 2 * (x + 1) ^ 2 := by
    have hnonneg : 0 ≤ 1 + max 1 (2 * a * x) := by
      linarith [le_max_left 1 (2 * a * x)]
    have hright : 0 ≤ 2 * ((a + 1) * (x + 1)) := by positivity
    have := (sq_le_sq₀ hnonneg hright).2 (hone.trans (by nlinarith))
    nlinarith
  rw [rapidExponentialFockLocalEvaluationFactor_eq ha]
  unfold rapidExponentialFockLocalEvaluationPolynomialBound
  have hcoeff : 0 ≤ 128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2 := by positivity
  calc
    128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2 *
        (1 + max 1 (2 * a * x)) ^ 2 ≤
      (128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2) *
        (4 * (a + 1) ^ 2 * (x + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hsquare hcoeff
    _ = 512 * Real.exp 2 * (a + 1) ^ 4 / a ^ 2 * (x + 1) ^ 2 := by ring

theorem rapidExponentialFockEffectiveSamplingWeight_nonneg
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    0 ≤ rapidExponentialFockEffectiveSamplingWeight a p := by
  unfold rapidExponentialFockEffectiveSamplingWeight
    rapidExponentialFockLocalEvaluationFactor
    rapidExponentialFockTangentCurvature rapidExponentialFockLocalRadius
  have hmax : 0 < 1 + max 1 (2 * a * Real.log (p : ℝ)) := by
    linarith [le_max_left 1 (2 * a * Real.log (p : ℝ))]
  exact mul_nonneg (criticalPrimeSamplingWeight_pos p).le (by positivity)

theorem rapidExponentialFockEffectiveSamplingWeight_le_logPowFour
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes)
    (hpLog : 1 ≤ Real.log (p : ℝ)) :
    rapidExponentialFockEffectiveSamplingWeight a p ≤
      4 * rapidExponentialFockLocalEvaluationPolynomialBound a *
        primeLogPowWeight 4 p := by
  let x : ℝ := Real.log (p : ℝ)
  have hx : 0 ≤ x := zero_le_one.trans hpLog
  have hfactor := rapidExponentialFockLocalEvaluationFactor_le_polynomial ha hx
  have hxplus : (x + 1) ^ 2 ≤ 4 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hw : criticalPrimeSamplingWeight p = x ^ 2 / p := by
    rw [criticalPrimeSamplingWeight]
  have hpow : primeLogPowWeight 4 p = x ^ 4 / p := by
    rw [primeLogPowWeight, if_pos p.prop]
  have hpPos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hB : 0 ≤ rapidExponentialFockLocalEvaluationPolynomialBound a := by
    unfold rapidExponentialFockLocalEvaluationPolynomialBound
    positivity
  unfold rapidExponentialFockEffectiveSamplingWeight
  rw [hw, hpow]
  calc
    x ^ 2 / (p : ℝ) * rapidExponentialFockLocalEvaluationFactor a x ≤
      x ^ 2 / (p : ℝ) *
        (rapidExponentialFockLocalEvaluationPolynomialBound a * (x + 1) ^ 2) := by
      gcongr
    _ ≤ x ^ 2 / (p : ℝ) *
        (rapidExponentialFockLocalEvaluationPolynomialBound a * (4 * x ^ 2)) := by
      gcongr
    _ = 4 * rapidExponentialFockLocalEvaluationPolynomialBound a *
        (x ^ 4 / (p : ℝ)) := by ring

/-- Effective normalized-evaluation mass on rapid local balls is dominated by fourth prime-log
mass in one adapted window. -/
theorem sum_rapidExponentialFockEffectiveSamplingWeight_localBalls_le
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hzre : 2 ≤ z.re)
    (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      then rapidExponentialFockEffectiveSamplingWeight a p else 0) ≤
      (4 * rapidExponentialFockLocalEvaluationPolynomialBound a) *
        primeLogPowWindowMass 4 z.re
          (rapidExponentialFockOverlapFactor a *
            rapidExponentialFockAdaptedRadius a z.re) := by
  classical
  let R : ℝ := rapidExponentialFockOverlapFactor a *
    rapidExponentialFockAdaptedRadius a z.re
  let S : Finset Nat.Primes := T.filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
  let C : ℝ := 4 * rapidExponentialFockLocalEvaluationPolynomialBound a
  have hzOne : 1 ≤ z.re := by linarith
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (rapidExponentialFockOverlapFactor_pos ha)
      (rapidExponentialFockAdaptedRadius_pos ha (by linarith))
  have hC : 0 ≤ C := by
    dsimp [C, rapidExponentialFockLocalEvaluationPolynomialBound]
    positivity
  have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
      Finset.Ioc ⌊Real.exp (z.re - R)⌋₊ ⌊Real.exp (z.re + R)⌋₊ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hpS, rfl⟩ := hn
    have hpball : z ∈ Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
        (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))) := by
      simpa [Metric.mem_ball] using (Finset.mem_filter.mp hpS).2
    apply mem_primeLogWindow_of_abs_log_sub_lt p.prop
    simpa [R] using
      abs_primeLog_sub_re_lt_rapidExponentialFockOverlapRadius ha p hzOne hpball
  have hpLog : ∀ p ∈ S, 1 ≤ Real.log (p : ℝ) := by
    intro p hpS
    have hp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
    have hpdist := (Finset.mem_filter.mp hpS).2
    have habs : |Real.log (p : ℝ) - z.re| <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
      have hre := Complex.abs_re_le_norm
        (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
      have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        rw [norm_sub_rev]
        simpa [dist_eq_norm] using hpdist
      exact hre.trans_lt hnorm
    have hleft := (abs_lt.mp (habs.trans_le hr)).1
    linarith
  rw [primeLogPowWindowMass_eq_sum 4 z.re hR.le]
  rw [← Finset.sum_filter]
  change (∑ p ∈ S, rapidExponentialFockEffectiveSamplingWeight a p) ≤ _
  calc
    (∑ p ∈ S, rapidExponentialFockEffectiveSamplingWeight a p) ≤
        ∑ p ∈ S, C * primeLogPowWeight 4 p := by
      exact Finset.sum_le_sum fun p hp =>
        rapidExponentialFockEffectiveSamplingWeight_le_logPowFour ha p (hpLog p hp)
    _ = C * ∑ p ∈ S, primeLogPowWeight 4 p := by rw [Finset.mul_sum]
    _ = C * ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)),
        primeLogPowWeight 4 n := by
      congr 1
      exact (Finset.sum_image (fun p _ q _ h => Subtype.ext h)).symm
    _ ≤ C * ∑ n ∈ Finset.Ioc ⌊Real.exp (z.re - R)⌋₊
        ⌊Real.exp (z.re + R)⌋₊, primeLogPowWeight 4 n := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by unfold primeLogPowWeight; split <;> positivity)
    _ = (4 * rapidExponentialFockLocalEvaluationPolynomialBound a) *
        ∑ n ∈ Finset.Ioc
          ⌊Real.exp (z.re -
            rapidExponentialFockOverlapFactor a *
              rapidExponentialFockAdaptedRadius a z.re)⌋₊
          ⌊Real.exp (z.re +
            rapidExponentialFockOverlapFactor a *
              rapidExponentialFockAdaptedRadius a z.re)⌋₊,
          primeLogPowWeight 4 n := by rfl

theorem tendsto_rapidExponentialFockEffectiveWindow_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      (4 * rapidExponentialFockLocalEvaluationPolynomialBound a) *
        primeLogPowWindowMass 4 x
          (rapidExponentialFockOverlapFactor a *
            rapidExponentialFockAdaptedRadius a x)) atTop (nhds 0) := by
  have h :=
    tendsto_primeLogPowWindowMass_four_rapidExponentialFockAdaptedRadius_zero
      ha (rapidExponentialFockOverlapFactor_pos ha)
  simpa using h.const_mul (4 * rapidExponentialFockLocalEvaluationPolynomialBound a)

theorem exists_uniform_rapidExponentialFockEffectiveLocalBallMass_bound
    {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then rapidExponentialFockEffectiveSamplingWeight a p else 0) ≤ B := by
  classical
  let W : ℝ → ℝ := fun x =>
    (4 * rapidExponentialFockLocalEvaluationPolynomialBound a) *
      primeLogPowWindowMass 4 x
        (rapidExponentialFockOverlapFactor a *
          rapidExponentialFockAdaptedRadius a x)
  have hW : Tendsto W atTop (nhds 0) :=
    tendsto_rapidExponentialFockEffectiveWindow_zero ha
  have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  let Y : ℝ := max 2 X
  let P : Finset Nat.Primes := GaloisForLFunctions.primesBelowSubtype
    (⌊Real.exp (Y + 1)⌋₊ + 1)
  let B : ℝ := max 1 (∑ p ∈ P, rapidExponentialFockEffectiveSamplingWeight a p)
  refine ⟨B, zero_le_one.trans (le_max_left _ _), fun z T => ?_⟩
  by_cases hY : Y ≤ z.re
  · have hsum := sum_rapidExponentialFockEffectiveSamplingWeight_localBalls_le
      ha ((le_max_left 2 X).trans hY) T
    have hdist := hX z.re ((le_max_right 2 X).trans hY)
    have habs : |W z.re| < 1 := by simpa [Real.dist_eq] using hdist
    exact hsum.trans (le_max_of_le_left
      ((le_abs_self (W z.re)).trans habs.le))
  · apply le_max_of_le_right
    let S : Finset Nat.Primes := T.filter fun p =>
      dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
    have hsub : S ⊆ P := by
      intro p hpS
      have hp0 : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
      have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
      have hpdist := (Finset.mem_filter.mp hpS).2
      have habs : |Real.log (p : ℝ) - z.re| <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        have hre := Complex.abs_re_le_norm
          (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
        have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
          rw [norm_sub_rev]
          simpa [dist_eq_norm] using hpdist
        exact hre.trans_lt hnorm
      have hlog : Real.log (p : ℝ) < Y + 1 := by
        have hright := (abs_lt.mp (habs.trans_le hr)).2
        linarith [lt_of_not_ge hY]
      change p ∈ GaloisForLFunctions.primesBelowSubtype
        (⌊Real.exp (Y + 1)⌋₊ + 1)
      rw [mem_primesBelowSubtype_iff]
      have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
      apply Nat.lt_succ_of_le
      apply Nat.le_floor
      rw [← Real.exp_log hpReal]
      exact Real.exp_le_exp.mpr hlog.le
    rw [← Finset.sum_filter]
    change (∑ p ∈ S, rapidExponentialFockEffectiveSamplingWeight a p) ≤ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => rapidExponentialFockEffectiveSamplingWeight_nonneg ha p)

/-- Effective rapid local-ball overlaps admit finite prime heads with tails tending to zero. -/
theorem exists_rapidExponentialFockEffectiveLocalBallTail_bound
    {a : ℝ} (ha : 0 < a) :
    ∃ P : ℕ → Finset Nat.Primes, ∀ (n : ℕ) (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P n),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then rapidExponentialFockEffectiveSamplingWeight a p else 0) ≤
        ((n : ℝ) + 1)⁻¹ := by
  classical
  let W : ℝ → ℝ := fun x =>
    (4 * rapidExponentialFockLocalEvaluationPolynomialBound a) *
      primeLogPowWindowMass 4 x
        (rapidExponentialFockOverlapFactor a *
          rapidExponentialFockAdaptedRadius a x)
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hW : Tendsto W atTop (nhds 0) :=
    tendsto_rapidExponentialFockEffectiveWindow_zero ha
  have hδpos : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hexists : ∀ n : ℕ, ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |W x| < δ n := by
    intro n
    have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) (hδpos n))
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    exact ⟨X, fun x hx => by simpa [Real.dist_eq] using hX x hx⟩
  choose X hX using hexists
  let Y : ℕ → ℝ := fun n => max 2 (X n)
  let P : ℕ → Finset Nat.Primes := fun n =>
    GaloisForLFunctions.primesBelowSubtype
      (⌊Real.exp (Y n + 1 / 4)⌋₊ + 1)
  refine ⟨P, fun n z T => ?_⟩
  let S : Finset Nat.Primes := (T.filter (· ∉ P n)).filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
  by_cases hS : S.Nonempty
  · obtain ⟨p, hpS⟩ := hS
    have hpTail : p ∉ P n := (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2
    have hpBall := (Finset.mem_filter.mp hpS).2
    have hpLower : ⌊Real.exp (Y n + 1 / 4)⌋₊ + 1 ≤ (p : ℕ) := by
      have hnotlt : ¬ (p : ℕ) < ⌊Real.exp (Y n + 1 / 4)⌋₊ + 1 := by
        intro hlt
        apply hpTail
        rw [mem_primesBelowSubtype_iff]
        exact hlt
      omega
    have hexplt : Real.exp (Y n + 1 / 4) < (p : ℝ) := by
      apply (Nat.floor_lt' p.prop.ne_zero).mp
      omega
    have hplog : Y n + 1 / 4 < Real.log (p : ℝ) := by
      have hpcastpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hlog := Real.log_lt_log (Real.exp_pos _) hexplt
      simpa using hlog
    have hp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
    have habs : |Real.log (p : ℝ) - z.re| <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
      have hre := Complex.abs_re_le_norm
        (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
      have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        rw [norm_sub_rev]
        simpa [dist_eq_norm] using hpBall
      exact hre.trans_lt hnorm
    have hzY : Y n < z.re := by
      have hright := (abs_lt.mp (habs.trans_le hr)).2
      linarith
    have hzre : 2 ≤ z.re := (le_max_left 2 (X n)).trans hzY.le
    have hWX : |W z.re| < δ n := hX n z.re
      ((le_max_right 2 (X n)).trans hzY.le)
    have hsum := sum_rapidExponentialFockEffectiveSamplingWeight_localBalls_le
      ha hzre (T.filter (· ∉ P n))
    have hWnonneg : 0 ≤ W z.re := by
      have hempty := sum_rapidExponentialFockEffectiveSamplingWeight_localBalls_le
        ha hzre (∅ : Finset Nat.Primes)
      simpa [W] using hempty
    calc
      (∑ p ∈ T.filter (· ∉ P n),
          if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
            then rapidExponentialFockEffectiveSamplingWeight a p else 0) ≤
          W z.re := by simpa [W] using hsum
      _ ≤ |W z.re| := le_abs_self _
      _ ≤ δ n := hWX.le
      _ = ((n : ℝ) + 1)⁻¹ := rfl
  · have hzero : ∀ p ∈ T.filter (· ∉ P n),
        (if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then rapidExponentialFockEffectiveSamplingWeight a p else 0) = 0 := by
      intro p hp
      have hpnot : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        intro hpball
        apply hS
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpball⟩⟩
      exact if_neg hpnot
    rw [Finset.sum_eq_zero hzero]
    positivity

end

end RHTower
