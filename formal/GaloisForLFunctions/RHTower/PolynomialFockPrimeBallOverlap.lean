import GaloisForLFunctions.RHTower.PolynomialFockLocalEvaluation
import GaloisForLFunctions.RHTower.CriticalPrimeFockWindowPhaseTransition
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Polynomial Fock critical-prime tangent-ball overlap

The exact tangent radius is dominated by the classical polynomial critical radius. Uniform
prime-log window asymptotics then give bounded quartic overlap and vanishing superquartic tail
overlap for the literal weights `(log p)^2 / p`. The capstone is a uniform finite-sum bound valid at
every complex point, including the bounded real head.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

theorem polynomialFockTangentRadius_le_criticalPrimeFockRadius
    {m x : ℝ} (hm : 2 ≤ m) (hx : 0 < x) :
    polynomialFockTangentRadius m x ≤ criticalPrimeFockRadius m x := by
  have hm0 : 0 < m := by linarith
  have hβ : 0 ≤ m / 2 - 1 := by linarith
  have hx0 : 0 ≤ x := hx.le
  have hbase : x ^ 2 ≤ 1 + x ^ 2 := by linarith
  have hpow : (x ^ 2) ^ (m / 2 - 1) ≤
      (1 + x ^ 2) ^ (m / 2 - 1) :=
    Real.rpow_le_rpow (sq_nonneg x) hbase hβ
  have hxpow : (x ^ 2) ^ (m / 2 - 1) = x ^ (m - 2) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0]
    congr 1
    ring
  have hden : x ^ (m - 2) ≤
      m * (1 + x ^ 2) ^ (m / 2 - 1) := by
    rw [← hxpow]
    exact hpow.trans (by
      nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 1 + x ^ 2) (m / 2 - 1)])
  have hsq : polynomialFockTangentRadius m x ^ 2 ≤
      criticalPrimeFockRadius m x ^ 2 := by
    rw [polynomialFockTangentRadius_sq hm0,
      criticalPrimeFockRadius_eq_rpow hx0]
    rw [← Real.rpow_natCast (x ^ (1 - m / 2)) 2, ← Real.rpow_mul hx0]
    norm_num
    rw [show (1 - m / 2) * (2 : ℝ) = -(m - 2) by ring,
      Real.rpow_neg hx0]
    simpa [mul_inv_rev] using inv_anti₀ (Real.rpow_pos_of_pos hx (m - 2)) hden
  exact (sq_le_sq₀ (polynomialFockTangentRadius_pos hm0).le
    (criticalPrimeFockRadius_pos hx).le).mp hsq

theorem criticalPrimeFockRadius_anti
    {m x y : ℝ} (hm : 2 ≤ m) (hx : 0 < x) (hxy : x ≤ y) :
    criticalPrimeFockRadius m y ≤ criticalPrimeFockRadius m x := by
  rw [criticalPrimeFockRadius_eq_rpow (le_trans hx.le hxy),
    criticalPrimeFockRadius_eq_rpow hx.le]
  have hβ : 0 ≤ m / 2 - 1 := by linarith
  rw [show 1 - m / 2 = -(m / 2 - 1) by ring]
  exact rpow_neg_anti hx hxy hβ

theorem criticalPrimeFockRadius_half
    {m x : ℝ} (hx : 0 ≤ x) :
    criticalPrimeFockRadius m (x / 2) =
      2 ^ (m / 2 - 1) * criticalPrimeFockRadius m x := by
  rw [criticalPrimeFockRadius_eq_rpow (div_nonneg hx (by norm_num)),
    criticalPrimeFockRadius_eq_rpow hx, Real.div_rpow hx (by norm_num)]
  have htwo : (2 : ℝ) ^ (1 - m / 2) ≠ 0 := by positivity
  rw [div_eq_mul_inv]
  rw [show ((2 : ℝ) ^ (1 - m / 2))⁻¹ = 2 ^ (m / 2 - 1) by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring]
  ring

theorem abs_primeLog_sub_re_lt_overlapRadius
    {m : ℝ} (hm : 4 ≤ m) (p : Nat.Primes) {z : ℂ}
    (hzre : 1 ≤ z.re)
    (hz : z ∈ Metric.ball
      ((Real.log (p : ℝ) : ℝ) : ℂ)
      (polynomialFockTangentRadius m (Real.log (p : ℝ)))) :
    |Real.log (p : ℝ) - z.re| <
      2 ^ (m / 2 - 1) * criticalPrimeFockRadius m z.re := by
  let xp : ℝ := Real.log (p : ℝ)
  have hnorm : ‖(xp : ℂ) - z‖ < polynomialFockTangentRadius m xp := by
    rw [norm_sub_rev]
    simpa [xp, Metric.mem_ball, dist_eq_norm] using hz
  have habs : |xp - z.re| ≤ ‖(xp : ℂ) - z‖ := by
    simpa using Complex.abs_re_le_norm ((xp : ℂ) - z)
  have hlocal : |xp - z.re| < polynomialFockTangentRadius m xp := habs.trans_lt hnorm
  have hhalf : |xp - z.re| < 1 / 2 :=
    hlocal.trans_le (polynomialFockTangentRadius_le_half hm)
  have hxp : z.re / 2 ≤ xp := by
    have hleft := (abs_lt.mp hhalf).1
    linarith
  have hhalfpos : 0 < z.re / 2 := by linarith
  have hxppos : 0 < xp := lt_of_lt_of_le hhalfpos hxp
  calc
    |Real.log (p : ℝ) - z.re| = |xp - z.re| := by rfl
    _ < polynomialFockTangentRadius m xp := hlocal
    _ ≤ criticalPrimeFockRadius m xp :=
      polynomialFockTangentRadius_le_criticalPrimeFockRadius (by linarith) hxppos
    _ ≤ criticalPrimeFockRadius m (z.re / 2) :=
      criticalPrimeFockRadius_anti (by linarith) hhalfpos hxp
    _ = 2 ^ (m / 2 - 1) * criticalPrimeFockRadius m z.re :=
      criticalPrimeFockRadius_half (le_trans zero_le_one hzre)

theorem tendsto_primeLogWindowMass_sub_main_of_admissibleRadius
    (r : ℝ → ℝ)
    (hrpos : ∀ᶠ x in atTop, 0 < r x)
    (hrone : ∀ᶠ x in atTop, r x ≤ 1) :
    Tendsto (fun x => primeLogWindowMass x (r x) - 2 * x * r x)
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨X, hX⟩ := primeLogWindowMass_uniform_asymptotic hε
  filter_upwards [hrpos, hrone, eventually_ge_atTop X] with x hxpos hxone hxX
  simpa [Real.dist_eq] using hX x hxX (r x) hxpos hxone

theorem tendsto_criticalPrimeFockRadius_zero
    {m : ℝ} (hm : 2 < m) :
    Tendsto (criticalPrimeFockRadius m) atTop (nhds 0) := by
  have hβ : 0 < m / 2 - 1 := by linarith
  have h := tendsto_rpow_neg_atTop hβ
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [criticalPrimeFockRadius_eq_rpow hx.le]
  congr 1
  ring

theorem tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_four
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => primeLogWindowMass x
      (c * criticalPrimeFockRadius 4 x)) atTop (nhds (2 * c)) := by
  have hr0 : Tendsto (fun x => c * criticalPrimeFockRadius 4 x) atTop (nhds 0) := by
    simpa using
      (tendsto_criticalPrimeFockRadius_zero (m := (4 : ℝ)) (by norm_num)).const_mul c
  have hrpos : ∀ᶠ x : ℝ in atTop, 0 < c * criticalPrimeFockRadius 4 x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (criticalPrimeFockRadius_pos hx)
  have hrone : ∀ᶠ x : ℝ in atTop, c * criticalPrimeFockRadius 4 x ≤ 1 := by
    filter_upwards [hr0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have habs : |c * criticalPrimeFockRadius 4 x| < 1 := by
      simpa [Real.dist_eq] using hx
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have herr := tendsto_primeLogWindowMass_sub_main_of_admissibleRadius
    (fun x => c * criticalPrimeFockRadius 4 x) hrpos hrone
  have hmain : Tendsto (fun x : ℝ => 2 * x *
      (c * criticalPrimeFockRadius 4 x)) atTop (nhds (2 * c)) := by
    have h := (tendsto_criticalPrimeFockWindowMain_four.const_mul c)
    simpa [criticalPrimeFockWindowMain, mul_comm, mul_left_comm, mul_assoc] using h
  have := herr.add hmain
  convert this using 1 <;> ring

theorem tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_zero
    {m c : ℝ} (hm : 4 < m) (hc : 0 < c) :
    Tendsto (fun x => primeLogWindowMass x
      (c * criticalPrimeFockRadius m x)) atTop (nhds 0) := by
  have hr0 : Tendsto (fun x => c * criticalPrimeFockRadius m x) atTop (nhds 0) := by
    simpa using
      (tendsto_criticalPrimeFockRadius_zero (m := m) (by linarith)).const_mul c
  have hrpos : ∀ᶠ x : ℝ in atTop, 0 < c * criticalPrimeFockRadius m x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (criticalPrimeFockRadius_pos hx)
  have hrone : ∀ᶠ x : ℝ in atTop, c * criticalPrimeFockRadius m x ≤ 1 := by
    filter_upwards [hr0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have habs : |c * criticalPrimeFockRadius m x| < 1 := by
      simpa [Real.dist_eq] using hx
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have herr := tendsto_primeLogWindowMass_sub_main_of_admissibleRadius
    (fun x => c * criticalPrimeFockRadius m x) hrpos hrone
  have hmain : Tendsto (fun x : ℝ => 2 * x *
      (c * criticalPrimeFockRadius m x)) atTop (nhds 0) := by
    have h := (tendsto_criticalPrimeFockWindowMain_zero hm).const_mul c
    simpa [criticalPrimeFockWindowMain, mul_comm, mul_left_comm, mul_assoc] using h
  have := herr.add hmain
  convert this using 1 <;> ring

@[simp] theorem criticalPrimeSamplingWeight_eq_primeLogPowWeight
    (p : Nat.Primes) :
    criticalPrimeSamplingWeight p = primeLogPowWeight 2 p := by
  simp [criticalPrimeSamplingWeight, primeLogPowWeight, p.2]

theorem mem_primeLogWindow_of_abs_log_sub_lt
    {n : ℕ} (hn : n.Prime) {x r : ℝ}
    (h : |Real.log n - x| < r) :
    n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊ := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hbounds := abs_lt.mp h
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt' hn0).mpr
    rw [← Real.exp_log hnpos]
    exact Real.exp_lt_exp.mpr (by linarith)
  · apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    rw [← Real.exp_log hnpos]
    exact Real.exp_le_exp.mpr (by linarith)

theorem sum_criticalPrimeSamplingWeight_tangentBalls_le_windowMass
    {m : ℝ} (hm : 4 ≤ m) {z : ℂ} (hzre : 1 ≤ z.re)
    (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) ≤
      primeLogWindowMass z.re
        (2 ^ (m / 2 - 1) * criticalPrimeFockRadius m z.re) := by
  classical
  let R : ℝ := 2 ^ (m / 2 - 1) * criticalPrimeFockRadius m z.re
  let S : Finset Nat.Primes := T.filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ))
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (criticalPrimeFockRadius_pos (lt_of_lt_of_le zero_lt_one hzre))
  have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
      Finset.Ioc ⌊Real.exp (z.re - R)⌋₊ ⌊Real.exp (z.re + R)⌋₊ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hpS, rfl⟩ := hn
    have hpball : z ∈ Metric.ball
        ((Real.log (p : ℝ) : ℝ) : ℂ)
        (polynomialFockTangentRadius m (Real.log (p : ℝ))) := by
      simpa [Metric.mem_ball] using (Finset.mem_filter.mp hpS).2
    apply mem_primeLogWindow_of_abs_log_sub_lt p.2
    simpa [R] using abs_primeLog_sub_re_lt_overlapRadius hm p hzre hpball
  rw [primeLogWindowMass_eq_sum z.re hR.le]
  rw [← Finset.sum_filter]
  change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ _
  calc
    (∑ p ∈ S, criticalPrimeSamplingWeight p) =
        ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n := by
      symm
      calc
        (∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n) =
            ∑ p ∈ S, primeLogPowWeight 2 (p : ℕ) :=
          Finset.sum_image (fun p _ q _ h => Subtype.ext h)
        _ = ∑ p ∈ S, criticalPrimeSamplingWeight p := by simp
    _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (z.re - R)⌋₊ ⌊Real.exp (z.re + R)⌋₊,
        primeLogPowWeight 2 n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => primeLogPowWeight_two_nonneg n)

theorem exists_uniform_scaledCriticalPrimeFockWindowMass_bound
    {m c : ℝ} (hm : 4 ≤ m) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      primeLogWindowMass x (c * criticalPrimeFockRadius m x) ≤ B := by
  by_cases hm4 : m = 4
  · subst m
    let W : ℝ → ℝ := fun x =>
      primeLogWindowMass x (c * criticalPrimeFockRadius 4 x)
    have hW : Tendsto W atTop (nhds (2 * c)) :=
      tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_four hc
    have hev := hW.eventually (Metric.ball_mem_nhds (2 * c) zero_lt_one)
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    let Y : ℝ := max 1 X
    let B : ℝ := max (|2 * c| + 1) (primeLogPowSum 2 (Real.exp (Y + c)))
    refine ⟨B, (primeLogPowSum_nonneg 2 _).trans (le_max_right _ _), fun x hx => ?_⟩
    by_cases hYx : Y ≤ x
    · have hdist := hX x (le_trans (le_max_right 1 X) hYx)
      have habs : |W x - 2 * c| < 1 := by simpa [Real.dist_eq] using hdist
      exact le_max_of_le_left (le_of_lt (by
        have := (abs_lt.mp habs).2
        linarith [le_abs_self (2 * c)]))
    · have hxY : x < Y := lt_of_not_ge hYx
      have hrle : criticalPrimeFockRadius 4 x ≤ 1 :=
        criticalPrimeFockRadius_le_one (by norm_num) hx
      have hupper : x + c * criticalPrimeFockRadius 4 x ≤ Y + c := by
        nlinarith [mul_le_mul_of_nonneg_left hrle hc.le]
      have hmono := primeLogPowSum_mono 2 (Real.exp_le_exp.mpr hupper)
      have hlow := primeLogPowSum_nonneg 2
        (Real.exp (x - c * criticalPrimeFockRadius 4 x))
      apply le_max_of_le_right
      rw [primeLogWindowMass]
      linarith

  · have hmgt : 4 < m := lt_of_le_of_ne hm (Ne.symm hm4)
    let W : ℝ → ℝ := fun x =>
      primeLogWindowMass x (c * criticalPrimeFockRadius m x)
    have hW : Tendsto W atTop (nhds 0) :=
      tendsto_primeLogWindowMass_scaledCriticalPrimeFockRadius_zero hmgt hc
    have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    let Y : ℝ := max 1 X
    let B : ℝ := max 1 (primeLogPowSum 2 (Real.exp (Y + c)))
    refine ⟨B, (primeLogPowSum_nonneg 2 _).trans (le_max_right _ _), fun x hx => ?_⟩
    by_cases hYx : Y ≤ x
    · have hdist := hX x (le_trans (le_max_right 1 X) hYx)
      have habs : |W x| < 1 := by simpa [Real.dist_eq] using hdist
      exact le_max_of_le_left (le_of_lt (lt_of_le_of_lt (le_abs_self _) habs))
    · have hxY : x < Y := lt_of_not_ge hYx
      have hrle : criticalPrimeFockRadius m x ≤ 1 :=
        criticalPrimeFockRadius_le_one (by linarith) hx
      have hupper : x + c * criticalPrimeFockRadius m x ≤ Y + c := by
        nlinarith [mul_le_mul_of_nonneg_left hrle hc.le]
      have hmono := primeLogPowSum_mono 2 (Real.exp_le_exp.mpr hupper)
      have hlow := primeLogPowSum_nonneg 2
        (Real.exp (x - c * criticalPrimeFockRadius m x))
      apply le_max_of_le_right
      rw [primeLogWindowMass]
      linarith

theorem sum_criticalPrimeSamplingWeight_tangentBalls_low_re_le
    {m : ℝ} (hm : 4 ≤ m) {z : ℂ} (hzre : z.re < 1)
    (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) ≤
      primeLogPowSum 2 (Real.exp (3 / 2)) := by
  classical
  let S : Finset Nat.Primes := T.filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ))
  have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
      Finset.Icc 0 ⌊Real.exp (3 / 2)⌋₊ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hpS, rfl⟩ := hn
    have hpdist : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (p : ℝ)) :=
      (Finset.mem_filter.mp hpS).2
    let xp : ℝ := Real.log (p : ℝ)
    have hnorm : ‖(xp : ℂ) - z‖ < polynomialFockTangentRadius m xp := by
      rw [norm_sub_rev]
      simpa [xp, dist_eq_norm] using hpdist
    have habs : |xp - z.re| ≤ ‖(xp : ℂ) - z‖ := by
      simpa using Complex.abs_re_le_norm ((xp : ℂ) - z)
    have hlocal : |xp - z.re| < polynomialFockTangentRadius m xp := habs.trans_lt hnorm
    have hhalf : |xp - z.re| < 1 / 2 :=
      hlocal.trans_le (polynomialFockTangentRadius_le_half hm)
    have hxp : xp < 3 / 2 := by
      have hright := (abs_lt.mp hhalf).2
      linarith
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
      have hpcastpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
      rw [← Real.exp_log hpcastpos]
      exact Real.exp_le_exp.mpr hxp.le
  rw [primeLogPowSum]
  rw [← Finset.sum_filter]
  change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ _
  calc
    (∑ p ∈ S, criticalPrimeSamplingWeight p) =
        ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n := by
      symm
      calc
        (∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n) =
            ∑ p ∈ S, primeLogPowWeight 2 (p : ℕ) :=
          Finset.sum_image (fun p _ q _ h => Subtype.ext h)
        _ = ∑ p ∈ S, criticalPrimeSamplingWeight p := by simp
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊Real.exp (3 / 2)⌋₊, primeLogPowWeight 2 n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => primeLogPowWeight_two_nonneg n)

/-- Uniform finite overlap of all critical-prime tangent balls in every polynomial carrier of
quartic or larger degree. -/
theorem exists_uniform_criticalPrime_tangentBallMass_bound
    {m : ℝ} (hm : 4 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B := by
  let c : ℝ := 2 ^ (m / 2 - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Btail, hBtail, htail⟩ :=
    exists_uniform_scaledCriticalPrimeFockWindowMass_bound hm hc
  let Blow : ℝ := primeLogPowSum 2 (Real.exp (3 / 2))
  let B : ℝ := max Btail Blow
  refine ⟨B, hBtail.trans (le_max_left _ _), fun z T => ?_⟩
  by_cases hzre : 1 ≤ z.re
  · calc
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤
          primeLogWindowMass z.re
            (2 ^ (m / 2 - 1) * criticalPrimeFockRadius m z.re) :=
        sum_criticalPrimeSamplingWeight_tangentBalls_le_windowMass hm hzre T
      _ ≤ Btail := by simpa [c] using htail z.re hzre
      _ ≤ B := le_max_left _ _
  · have hzre' : z.re < 1 := lt_of_not_ge hzre
    calc
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            polynomialFockTangentRadius m (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤ Blow := by
        simpa [Blow] using
          sum_criticalPrimeSamplingWeight_tangentBalls_low_re_le hm hzre' T
      _ ≤ B := le_max_right _ _

end

end RHTower
