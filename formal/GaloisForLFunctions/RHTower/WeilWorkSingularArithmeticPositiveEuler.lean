import GaloisForLFunctions.RHTower.ZetaEulerLogPrimeSum
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# A fractional lower bound for strict multiplicative Euler series

A strict prime-power coefficient bound gives a uniform local logarithm
estimate with a summable quadratic remainder. Exact Euler-product
convergence and the canonical zeta Euler logarithm then bound the actual
Dirichlet series below by a positive constant times a fractional inverse
power of the zeta norm. This is the arithmetic lower bound for C49's
analytic endpoint argument; endpoint positivity itself is not asserted.
-/

open ArithmeticFunction Filter Topology

noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem summable_real_bounded_geometric {a : ℕ → ℝ} {C r : ℝ}
    (ha : ∀ k, |a k| ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k => a k * r ^ k) := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 k)]
  exact mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hr0 k)

theorem abs_real_bounded_geometric_le {a : ℕ → ℝ} {C r : ℝ}
    (ha : ∀ k, |a k| ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    |∑' k, a k * r ^ k| ≤ C / (1 - r) := by
  have hs := summable_real_bounded_geometric ha hr0 hr1
  calc
    _ ≤ ∑' k, ‖a k * r ^ k‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k, C * r ^ k := hs.norm.tsum_le_tsum (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 k)]
      exact mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hr0 k))
        ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; rfl

theorem real_localEuler_lower {a : ℕ → ℝ} (ha0 : a 0 = 1) {θ r : ℝ}
    (ha : ∀ k : ℕ, 1 ≤ k → |a k| ≤ θ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 - θ * r / (1 - r) ≤ ∑' k, a k * r ^ k := by
  have hb (k : ℕ) : |a k| ≤ max 1 θ := by
    by_cases hk : k = 0
    · simp [hk, ha0]
    · exact (ha k (by omega)).trans (le_max_right _ _)
  have hs := summable_real_bounded_geometric hb hr0 hr1
  have he : (∑' k, a k * r ^ k) = 1 + r * ∑' k, a (k + 1) * r ^ k := by
    calc
      _ = a 0 + ∑' k, a (k + 1) * r ^ (k + 1) := by
        simpa using (hs.sum_add_tsum_nat_add 1).symm
      _ = _ := by
        rw [ha0, ← tsum_mul_left]
        congr 1
        apply tsum_congr
        intro k
        rw [pow_succ]
        ring
  have ht := abs_real_bounded_geometric_le (fun k => ha (k + 1) (by omega)) hr0 hr1
  rw [he]
  have htail : -(θ / (1 - r)) ≤ ∑' k, a (k + 1) * r ^ k := (abs_le.mp ht).1
  have h := mul_le_mul_of_nonneg_left htail hr0
  have heq : r * -(θ / (1 - r)) = -(θ * r / (1 - r)) := by ring
  rw [heq] at h
  linarith

/-- A uniform logarithmic lower bound, with a summable quadratic remainder. -/
theorem real_localEuler_log_taylor_lower {θ q L : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hq0 : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (hL : 1 - θ * q / (1 - q) ≤ L) :
    -θ * q - (2 * θ + 4 * θ ^ 2 / (1 - θ)) * q ^ 2 ≤ Real.log L := by
  have hq1 : q < 1 := by linarith
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  let u : ℝ := θ * q / (1 - q)
  have hu0 : 0 ≤ u := div_nonneg (mul_nonneg hθ0 hq0) hden.le
  have huθ : u ≤ θ := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hθ0 (show 0 ≤ 1 - 2 * q by linarith)]
  have hu1 : u < 1 := huθ.trans_lt hθ1
  have hueq : u * (1 - q) = θ * q := div_mul_cancel₀ _ hden.ne'
  have hu2 : u ≤ 2 * θ * q := by nlinarith
  have huadd : u ≤ θ * q + 2 * θ * q ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hu2 hq0]
  have husq : u ^ 2 ≤ 4 * θ ^ 2 * q ^ 2 := by
    have h := pow_le_pow_left₀ hu0 hu2 2
    nlinarith
  have hrem := Real.abs_log_sub_add_sum_range_le
    (show |u| < 1 by rw [abs_of_nonneg hu0]; exact hu1) 1
  simp only [Finset.sum_range_one, zero_add, pow_one,
    abs_of_nonneg hu0] at hrem
  have hlog : -u - u ^ 2 / (1 - u) ≤ Real.log (1 - u) := by
    have h := (abs_le.mp hrem).1
    linarith
  have hquot : u ^ 2 / (1 - u) ≤ (4 * θ ^ 2 / (1 - θ)) * q ^ 2 := by
    calc
      _ ≤ u ^ 2 / (1 - θ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hθ1) (by linarith)
      _ ≤ (4 * θ ^ 2 * q ^ 2) / (1 - θ) :=
        div_le_div_of_nonneg_right husq (sub_pos.mpr hθ1).le
      _ = _ := by ring
  have hlogL : Real.log (1 - u) ≤ Real.log L := Real.log_le_log (sub_pos.mpr hu1) hL
  nlinarith

def realDirichletWeight (f : ArithmeticFunction ℝ) (σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * (n : ℝ) ^ (-σ), by simp⟩

theorem realDirichletWeight_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (σ : ℝ) : (realDirichletWeight f σ).IsMultiplicative := by
  constructor
  · simp [realDirichletWeight, hf.map_one]
  · intro m n hmn
    change f (m * n) * ((m * n : ℕ) : ℝ) ^ (-σ) = _
    rw [hf.map_mul_of_coprime hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    change _ = (f m * (m : ℝ) ^ (-σ)) * (f n * (n : ℝ) ^ (-σ))
    ring

theorem realDirichletWeight_summable {f : ArithmeticFunction ℝ}
    (hb : ∀ n, |f n| ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖realDirichletWeight f σ n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  change ‖f n * (n : ℝ) ^ (-σ)‖ ≤ (n : ℝ) ^ (-σ)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hb n)

theorem realDirichletWeight_prime_euler {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => ∑' k : ℕ, f ((p : ℕ) ^ k) *
      (((p : ℕ) : ℝ) ^ (-σ)) ^ k) (∑' n : ℕ, realDirichletWeight f σ n) := by
  have h := (realDirichletWeight_multiplicative hf σ).eulerProduct_hasProd
    (realDirichletWeight_summable hb hσ)
  have he (p : Nat.Primes) : (∑' k : ℕ, realDirichletWeight f σ ((p : ℕ) ^ k)) =
      ∑' k : ℕ, f ((p : ℕ) ^ k) * (((p : ℕ) : ℝ) ^ (-σ)) ^ k := by
    apply tsum_congr
    intro k
    change f ((p : ℕ) ^ k) * (((p : ℕ) ^ k : ℕ) : ℝ) ^ (-σ) = _
    rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
  simpa only [he] using h

/-- Uniform lower bound before identifying the prime sum with the zeta logarithm. -/
theorem realDirichletWeight_lower_exp {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpowers : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {σ : ℝ} (hσ : 1 < σ) :
    Real.exp (-θ * (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)) -
      (2 * θ + 4 * θ ^ 2 / (1 - θ)) * invSquareTailConst) ≤
      ∑' n : ℕ, realDirichletWeight f σ n := by
  classical
  let q (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ) ^ (-σ)
  let L (p : Nat.Primes) : ℝ := ∑' k : ℕ, f ((p : ℕ) ^ k) * q p ^ k
  let C : ℝ := 2 * θ + 4 * θ ^ 2 / (1 - θ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 (p : Nat.Primes) : 0 ≤ q p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hqhalf (p : Nat.Primes) : q p ≤ 1 / 2 := norm_primeRpow_le_half hσ.le p
  have hlocal (p : Nat.Primes) : 1 - θ * q p / (1 - q p) ≤ L p :=
    real_localEuler_lower (by simp [hf.map_one]) (hpowers p p.property) (hq0 p)
      (by linarith [hqhalf p])
  have hpos (p : Nat.Primes) : 0 < L p := by
    have hq1 : q p < 1 := by linarith [hqhalf p]
    have hu : θ * q p / (1 - q p) ≤ θ := by
      apply (div_le_iff₀ (sub_pos.mpr hq1)).2
      nlinarith [mul_nonneg hθ0 (show 0 ≤ 1 - 2 * q p by linarith [hqhalf p])]
    linarith [hlocal p]
  have hlog (p : Nat.Primes) : -θ * q p - C * q p ^ 2 ≤ Real.log (L p) :=
    real_localEuler_log_taylor_lower hθ0 hθ1 (hq0 p) (hqhalf p) (hlocal p)
  have hprod := realDirichletWeight_prime_euler hf hb hσ
  apply ge_of_tendsto hprod
  filter_upwards with P
  have hqsum : (∑ p ∈ P, q p) ≤ ∑' p : Nat.Primes, q p :=
    Summable.sum_le_tsum P (fun p _ => hq0 p) (summable_primeRpow hσ)
  have hq2sum : (∑ p ∈ P, q p ^ 2) ≤ invSquareTailConst := by
    calc
      _ ≤ ∑ p ∈ P, 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ) :=
        Finset.sum_le_sum (fun p _ => primeRpow_sq_le_invSq hσ.le p)
      _ = ∑ p ∈ P.image (fun p : Nat.Primes => (p : ℕ)), 1 / (p : ℝ) ^ (2 : ℝ) := by
        exact (Finset.sum_image (s := P) (g := fun p : Nat.Primes => (p : ℕ))
          (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ))
          (fun a _ b _ hab => Nat.Primes.coe_nat_injective hab)).symm
      _ ≤ invSquareTailConst := sum_inv_rpow_two_le _
  have hsum : -θ * (∑' p : Nat.Primes, q p) - C * invSquareTailConst ≤
      ∑ p ∈ P, (-θ * q p - C * q p ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hqsum hθ0, mul_le_mul_of_nonneg_left hq2sum hC]
  calc
    _ ≤ Real.exp (∑ p ∈ P, (-θ * q p - C * q p ^ 2)) := Real.exp_le_exp.mpr hsum
    _ = ∏ p ∈ P, Real.exp (-θ * q p - C * q p ^ 2) := Real.exp_sum _ _
    _ ≤ ∏ p ∈ P, L p := by
      apply Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
      intro p _
      rw [← Real.exp_log (hpos p)]
      exact Real.exp_le_exp.mpr (hlog p)

/-- The actual Euler series cannot vanish faster than a fractional zeta inverse. -/
theorem realDirichletWeight_lower_zeta {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpowers : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {σ : ℝ} (hσ : 1 < σ) :
    Real.exp (-(3 * θ + 4 * θ ^ 2 / (1 - θ)) * invSquareTailConst) *
      ‖riemannZeta (σ : ℂ)‖ ^ (-θ) ≤ ∑' n : ℕ, realDirichletWeight f σ n := by
  have hz : 0 < ‖riemannZeta (σ : ℂ)‖ := by
    apply norm_pos_iff.mpr
    rw [← exp_canonicalEulerLogZeta_eq_riemannZeta (by simpa using hσ)]
    exact Complex.exp_ne_zero _
  have hprime : (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)) ≤
      Real.log ‖riemannZeta (σ : ℂ)‖ + invSquareTailConst := by
    have h := abs_re_eulerLog_sub_primeCosTsum_le (σ := σ) (τ := 0) hσ
    simp only [zetaLinePoint, Complex.ofReal_zero, zero_mul, add_zero, primeCosTsum,
      Real.cos_zero, mul_one] at h
    rw [← log_norm_riemannZeta_eq_re_eulerLog (by simpa using hσ)] at h
    linarith [(abs_le.mp h).1]
  calc
    _ = Real.exp (-θ * Real.log ‖riemannZeta (σ : ℂ)‖ -
        (3 * θ + 4 * θ ^ 2 / (1 - θ)) * invSquareTailConst) := by
      rw [Real.rpow_def_of_pos hz, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-θ * (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)) -
        (2 * θ + 4 * θ ^ 2 / (1 - θ)) * invSquareTailConst) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hprime hθ0]
    _ ≤ _ := realDirichletWeight_lower_exp hf hb hθ0 hθ1 hpowers hσ

end RHTower.WeilSingularArithmetic
