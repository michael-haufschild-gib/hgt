import GaloisForLFunctions.RHTower.PrimeSamplingMicrolocalizationRate
import GaloisForLFunctions.RHTower.RapidExponentialFockNormalizedLocalEvaluation
import GaloisForLFunctions.RHTower.RapidExponentialFockPrimeBallOverlap

/-!
# Polynomially weighted rapid-Fock prime overlap

The explicit tangent-vector kernel lower bound costs a quadratic prime-log factor.  The
de la Vallée Poussin remainder already available in the corpus proves that this factor times the
rapid adapted prime-window mass still vanishes.  This is the quantitative arithmetic input needed
for compact normalized sampling.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

private theorem tendsto_pow_mul_exp_neg_sqrt_atTop
    (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ N * Real.exp (-c * Real.sqrt L)) atTop (nhds 0) := by
  have hbase : Tendsto (fun s : ℝ => s ^ (2 * N) * Real.exp (-s)) atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * N)
  have hscale : Tendsto (fun s : ℝ => c * s) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc
  have hsqrt : Tendsto (fun L : ℝ => Real.sqrt L) atTop atTop := Real.tendsto_sqrt_atTop
  have hcomp : Tendsto (fun L : ℝ => (c * Real.sqrt L) ^ (2 * N) *
      Real.exp (-(c * Real.sqrt L))) atTop (nhds 0) :=
    hbase.comp (hscale.comp hsqrt)
  have hfinal := hcomp.const_mul (c ^ (2 * N))⁻¹
  rw [mul_zero] at hfinal
  refine Tendsto.congr' ?_ hfinal
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
  have hcne : c ^ (2 * N) ≠ 0 := by positivity
  have hexp : Real.exp (-(c * Real.sqrt L)) = Real.exp (-c * Real.sqrt L) := by
    congr 1
    ring
  have hpow : (c * Real.sqrt L) ^ (2 * N) = c ^ (2 * N) * L ^ N := by
    rw [mul_pow]
    congr 1
    rw [pow_mul, hsq]
  rw [hpow, hexp]
  field_simp

/-- The quadratic loss from tangent-vector normalization still leaves vanishing prime-window
mass. -/
theorem tendsto_sqGrowth_mul_primeLogWindowMass_rapidExponential_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      (1 + x) ^ 2 * primeLogWindowMass x
        (rapidExponentialFockOverlapFactor a *
          rapidExponentialFockAdaptedRadius a x))
      atTop (nhds 0) := by
  obtain ⟨B, c, Y, hc, hB, hY, hrem⟩ := exists_primeLogSquareRemainder_bound
  let k : ℝ := rapidExponentialFockOverlapFactor a
  let R : ℝ → ℝ := fun x => k * rapidExponentialFockAdaptedRadius a x
  let C : ℝ := k * (2 * a)⁻¹
  let L : ℝ → ℝ := fun x => x - R x
  have hk : 0 < k := rapidExponentialFockOverlapFactor_pos ha
  have hC : 0 < C := by dsimp [C]; positivity
  have hRzero : Tendsto R atTop (nhds 0) := by
    simpa [R, k] using
      (tendsto_rapidExponentialFockAdaptedRadius_atTop ha).const_mul k
  have hRsmall : ∀ᶠ x : ℝ in atTop, R x ≤ 1 := by
    have hev := hRzero.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    simpa only [mem_Iic] using hev
  have hRnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ R x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg hk.le (rapidExponentialFockAdaptedRadius_pos ha hx).le
  have hRupper : ∀ᶠ x : ℝ in atTop, R x ≤ C * Real.exp (-a * x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hr := rapidExponentialFockAdaptedRadius_upper ha hx
    exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq (by simp [C, k]; ring)
  have hLatTop : Tendsto L atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (b + 1), hRsmall] with x hx hsmall
    dsimp [L]
    linarith
  have hmainZero : Tendsto
      (fun x : ℝ => 8 * C * (x ^ 3 * Real.exp (-a * x))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha).const_mul (8 * C)
    simpa [Real.rpow_natCast] using h
  have hremZero : Tendsto
      (fun x : ℝ => 12 * B * (L x ^ 3 * Real.exp (-c * Real.sqrt (L x))))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_pow_mul_exp_neg_sqrt_atTop 3 hc).comp hLatTop).const_mul (12 * B)
  have hupperZero := hmainZero.add hremZero
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hRnonneg] with x hx hR0
    have hwindow : 0 ≤ primeLogWindowMass x (R x) := by
      rw [primeLogWindowMass_eq_sum x hR0]
      exact Finset.sum_nonneg fun n _ => primeLogPowWeight_two_nonneg n
    exact mul_nonneg (sq_nonneg _) hwindow
  · filter_upwards [eventually_ge_atTop (max (Y + 1) 3), hRsmall, hRnonneg, hRupper]
      with x hx hsmall hR0 hRup
    have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
    have hxY : Y + 1 ≤ x := (le_max_left _ _).trans hx
    have hLlower : Y ≤ L x := by dsimp [L]; linarith
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hLpos : 0 < L x := hYpos.trans_le hLlower
    have hplusLower : Y ≤ x + R x := by linarith
    have hLx : x - 1 ≤ L x := by dsimp [L]; linarith
    have hxOneL : 1 + x ≤ 2 * L x := by
      dsimp [L]
      nlinarith
    have hplusL : x + R x ≤ 2 * L x := by
      dsimp [L]
      nlinarith
    have hmain : 2 * x * R x ≤ 2 * C * x * Real.exp (-a * x) := by
      calc
        2 * x * R x ≤ 2 * x * (C * Real.exp (-a * x)) := by
          exact mul_le_mul_of_nonneg_left hRup (by positivity)
        _ = 2 * C * x * Real.exp (-a * x) := by ring
    have hremPlus := hrem (x + R x) hplusLower
    have hremMinus := hrem (L x) hLlower
    have hsqrtPlus : Real.sqrt (L x) ≤ Real.sqrt (x + R x) := by
      exact Real.sqrt_le_sqrt (by dsimp [L]; linarith)
    have hexpPlus : Real.exp (-c * Real.sqrt (x + R x)) ≤
        Real.exp (-c * Real.sqrt (L x)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hremPlus' : |primeLogSquareRemainder (x + R x)| ≤
        2 * B * L x * Real.exp (-c * Real.sqrt (L x)) := by
      calc
        |primeLogSquareRemainder (x + R x)| ≤
            B * (x + R x) * Real.exp (-c * Real.sqrt (x + R x)) := hremPlus
        _ ≤ B * (2 * L x) * Real.exp (-c * Real.sqrt (L x)) := by gcongr
        _ = 2 * B * L x * Real.exp (-c * Real.sqrt (L x)) := by ring
    have hwindow : primeLogWindowMass x (R x) ≤
        2 * C * x * Real.exp (-a * x) +
          3 * B * L x * Real.exp (-c * Real.sqrt (L x)) := by
      rw [primeLogWindowMass_eq_main_add_remainders]
      have hp := le_abs_self (primeLogSquareRemainder (x + R x))
      have hm := neg_le_abs (primeLogSquareRemainder (L x))
      calc
        2 * x * R x + primeLogSquareRemainder (x + R x) -
            primeLogSquareRemainder (L x) ≤
          2 * x * R x + |primeLogSquareRemainder (x + R x)| +
            |primeLogSquareRemainder (L x)| := by linarith
        _ ≤ 2 * C * x * Real.exp (-a * x) +
            3 * B * L x * Real.exp (-c * Real.sqrt (L x)) := by
          have hminusNonneg : 0 ≤ B * L x * Real.exp (-c * Real.sqrt (L x)) := by
            positivity
          nlinarith
    have hx0 : 0 ≤ x := by linarith
    have hmainScale : (1 + x) ^ 2 *
        (2 * C * x * Real.exp (-a * x)) ≤
          8 * C * (x ^ 3 * Real.exp (-a * x)) := by
      have hsquare : (1 + x) ^ 2 ≤ (2 * x) ^ 2 :=
        (sq_le_sq₀ (by linarith) (by positivity)).2 (by linarith)
      calc
        (1 + x) ^ 2 * (2 * C * x * Real.exp (-a * x)) ≤
            (2 * x) ^ 2 * (2 * C * x * Real.exp (-a * x)) := by
          exact mul_le_mul_of_nonneg_right hsquare (by positivity)
        _ = 8 * C * (x ^ 3 * Real.exp (-a * x)) := by ring
    have hremScale : (1 + x) ^ 2 *
        (3 * B * L x * Real.exp (-c * Real.sqrt (L x))) ≤
          12 * B * (L x ^ 3 * Real.exp (-c * Real.sqrt (L x))) := by
      have hsquare : (1 + x) ^ 2 ≤ (2 * L x) ^ 2 :=
        (sq_le_sq₀ (by linarith) (by positivity)).2 hxOneL
      calc
        (1 + x) ^ 2 *
            (3 * B * L x * Real.exp (-c * Real.sqrt (L x))) ≤
          (2 * L x) ^ 2 *
            (3 * B * L x * Real.exp (-c * Real.sqrt (L x))) := by
          exact mul_le_mul_of_nonneg_right hsquare (by positivity)
        _ = 12 * B * (L x ^ 3 * Real.exp (-c * Real.sqrt (L x))) := by ring
    calc
      (1 + x) ^ 2 * primeLogWindowMass x
          (rapidExponentialFockOverlapFactor a *
            rapidExponentialFockAdaptedRadius a x) =
        (1 + x) ^ 2 * primeLogWindowMass x (R x) := by rfl
      _ ≤ (1 + x) ^ 2 *
          (2 * C * x * Real.exp (-a * x) +
            3 * B * L x * Real.exp (-c * Real.sqrt (L x))) := by
        gcongr
      _ ≤ 8 * C * (x ^ 3 * Real.exp (-a * x)) +
          12 * B * (L x ^ 3 * Real.exp (-c * Real.sqrt (L x))) := by
        nlinarith
  · simpa only [add_zero] using hupperZero

/-- Positive coefficient separating the quadratic observation-point growth from the local
evaluation loss. -/
def rapidExponentialFockLocalEvaluationPolynomialConstant (a : ℝ) : ℝ :=
  128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2 * (1 + 2 * a) ^ 2

theorem rapidExponentialFockLocalEvaluationPolynomialConstant_pos
    {a : ℝ} (ha : 0 < a) :
    0 < rapidExponentialFockLocalEvaluationPolynomialConstant a := by
  unfold rapidExponentialFockLocalEvaluationPolynomialConstant
  positivity

theorem rapidExponentialFockLocalEvaluationFactor_eq
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    rapidExponentialFockLocalEvaluationFactor a x =
      (128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2) *
        (1 + max 1 (2 * a * x)) ^ 2 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hden : 8 * (a + 1) ≠ 0 := by positivity
  have hexp : Real.exp (2 * a * x) * Real.exp (-a * x) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
    simp
  unfold rapidExponentialFockLocalEvaluationFactor
    rapidExponentialFockTangentCurvature rapidExponentialFockLocalRadius
  field_simp [ha0, hden, Real.exp_ne_zero]
  rw [show Real.exp (-(a * x)) = Real.exp (-a * x) by congr 1; ring]
  calc
    4 * 8 ^ 2 = 2 * 1 * 128 := by norm_num
    _ = 2 * (Real.exp (2 * a * x) * Real.exp (-a * x) ^ 2) * 128 := by rw [hexp]
    _ = 2 * Real.exp (2 * a * x) * Real.exp (-a * x) ^ 2 * 128 := by ring

/-- On a local prime ball, tangent-vector normalization costs at most a fixed coefficient times
quadratic growth in the observation coordinate. -/
theorem rapidExponentialFockLocalEvaluationFactor_primeBall_le
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) {z : ℂ} (hzre : 1 ≤ z.re)
    (hz : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))) :
    rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) ≤
      rapidExponentialFockLocalEvaluationPolynomialConstant a * (1 + z.re) ^ 2 := by
  let xp : ℝ := Real.log (p : ℝ)
  have hxp0 : 0 ≤ xp := by
    dsimp [xp]
    exact Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hradius := rapidExponentialFockLocalRadius_le_one_eighth ha hxp0
  have hnorm : ‖(xp : ℂ) - z‖ < rapidExponentialFockLocalRadius a xp := by
    rw [norm_sub_rev]
    simpa [xp, dist_eq_norm] using hz
  have habs : |xp - z.re| ≤ ‖(xp : ℂ) - z‖ := by
    simpa using Complex.abs_re_le_norm ((xp : ℂ) - z)
  have hxpUpper : xp ≤ z.re + 1 := by
    have hlocal := habs.trans_lt hnorm
    have hright := (abs_lt.mp (hlocal.trans_le hradius)).2
    linarith
  have hmax : max 1 (2 * a * xp) ≤ 1 + 2 * a * (z.re + 1) := by
    rw [max_le_iff]
    constructor
    · have : 0 ≤ 2 * a * (z.re + 1) := by positivity
      linarith
    · nlinarith
  have hfactor :
      1 + max 1 (2 * a * xp) ≤ (1 + 2 * a) * (1 + z.re) := by
    calc
      1 + max 1 (2 * a * xp) ≤ 1 + (1 + 2 * a * (z.re + 1)) := by gcongr
      _ ≤ (1 + 2 * a) * (1 + z.re) := by
        nlinarith
  have hsquare : (1 + max 1 (2 * a * xp)) ^ 2 ≤
      ((1 + 2 * a) * (1 + z.re)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hfactor
  rw [rapidExponentialFockLocalEvaluationFactor_eq ha]
  unfold rapidExponentialFockLocalEvaluationPolynomialConstant
  calc
    (128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2) *
        (1 + max 1 (2 * a * xp)) ^ 2 ≤
      (128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2) *
        ((1 + 2 * a) * (1 + z.re)) ^ 2 := by gcongr
    _ = 128 * Real.exp 2 * (a + 1) ^ 2 / a ^ 2 *
        (1 + 2 * a) ^ 2 * (1 + z.re) ^ 2 := by ring

/-- Finite prime-ball mass with the exact local-evaluation loss is controlled by a quadratic
multiple of one rapid adapted prime window. -/
theorem sum_criticalPrimeSamplingWeight_mul_localEvaluationFactor_rapidLocalBalls_le
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hzre : 1 ≤ z.re)
    (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p *
        rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤
      rapidExponentialFockLocalEvaluationPolynomialConstant a * (1 + z.re) ^ 2 *
        primeLogWindowMass z.re
          (rapidExponentialFockOverlapFactor a *
            rapidExponentialFockAdaptedRadius a z.re) := by
  classical
  let Q : ℝ := rapidExponentialFockLocalEvaluationPolynomialConstant a * (1 + z.re) ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (rapidExponentialFockLocalEvaluationPolynomialConstant_pos ha).le
      (sq_nonneg _)
  have hwindow := sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass ha hzre T
  calc
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p *
        rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤
      ∑ p ∈ T, Q *
        (if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hball : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      · rw [if_pos hball, if_pos hball]
        have hfactor := rapidExponentialFockLocalEvaluationFactor_primeBall_le ha p hzre hball
        simpa [Q, mul_comm] using
          (mul_le_mul_of_nonneg_left hfactor (criticalPrimeSamplingWeight_pos p).le)
      · rw [if_neg hball, if_neg hball]
        positivity
    _ = Q * (∑ p ∈ T,
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) := by rw [Finset.mul_sum]
    _ ≤ Q * primeLogWindowMass z.re
        (rapidExponentialFockOverlapFactor a *
          rapidExponentialFockAdaptedRadius a z.re) :=
      mul_le_mul_of_nonneg_left hwindow hQ
    _ = _ := rfl

/-- Weighted rapid local-ball overlaps admit finite prime heads with tails tending to zero. -/
theorem exists_criticalPrime_weightedRapidLocalBallTail_bound
    {a : ℝ} (ha : 0 < a) :
    ∃ P : ℕ → Finset Nat.Primes, ∀ (n : ℕ) (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P n),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p *
            rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤
        ((n : ℝ) + 1)⁻¹ := by
  classical
  let C : ℝ := rapidExponentialFockLocalEvaluationPolynomialConstant a
  let W : ℝ → ℝ := fun x => C * (1 + x) ^ 2 *
    primeLogWindowMass x
      (rapidExponentialFockOverlapFactor a * rapidExponentialFockAdaptedRadius a x)
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hW : Tendsto W atTop (nhds 0) := by
    simpa [W, C, mul_assoc] using
      (tendsto_sqGrowth_mul_primeLogWindowMass_rapidExponential_zero ha).const_mul
        (rapidExponentialFockLocalEvaluationPolynomialConstant a)
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
      (⌊Real.exp (Y n + 1 / 4)⌋₊ + 1)
  refine ⟨P, fun n z T => ?_⟩
  let S : Finset Nat.Primes := (T.filter (· ∉ P n)).filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
  by_cases hS : S.Nonempty
  · obtain ⟨p, hpS⟩ := hS
    have hpTail : p ∉ P n := (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2
    have hpBall : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) :=
      (Finset.mem_filter.mp hpS).2
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
    have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
      rw [norm_sub_rev]
      simpa [dist_eq_norm] using hpBall
    have habs : |Real.log (p : ℝ) - z.re| ≤
        ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        Complex.abs_re_le_norm (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
    have hlocal : |Real.log (p : ℝ) - z.re| <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := habs.trans_lt hnorm
    have hzY : Y n < z.re := by
      have hright := (abs_lt.mp (hlocal.trans_le hr)).2
      linarith
    have hzre : 1 ≤ z.re := (le_max_left 1 (X n)).trans hzY.le
    have hWX : |W z.re| < δ n :=
      hX n z.re ((le_max_right 1 (X n)).trans hzY.le)
    have hsumWindow :=
      sum_criticalPrimeSamplingWeight_mul_localEvaluationFactor_rapidLocalBalls_le
        ha hzre (T.filter (· ∉ P n))
    calc
      (∑ p ∈ T.filter (· ∉ P n),
          if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
            then criticalPrimeSamplingWeight p *
              rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) ≤
        W z.re := by simpa [W, C, mul_assoc] using hsumWindow
      _ ≤ |W z.re| := le_abs_self _
      _ ≤ δ n := hWX.le
      _ = ((n : ℝ) + 1)⁻¹ := rfl
  · have hzero : ∀ p ∈ T.filter (· ∉ P n),
        (if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p *
            rapidExponentialFockLocalEvaluationFactor a (Real.log (p : ℝ)) else 0) = 0 := by
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
