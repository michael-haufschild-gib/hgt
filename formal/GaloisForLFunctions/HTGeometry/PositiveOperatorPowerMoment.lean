import Mathlib.Analysis.InnerProductSpace.Positive
import GaloisForLFunctions.HTGeometry.BesselPSD

/-!
# All-depth moment amplification for positive operators

Vector moments of a positive operator are nonnegative and log-convex. Consequently, for a unit
vector, the `n`-th vector moment dominates the `n`-th power of the first moment. The proof is
elementary: even moments are norm squares, odd moments are positive quadratic forms, and adjacent
log-convexity alternates between ordinary and positive-semidefinite Cauchy--Schwarz.
-/

open RCLike
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every power of a positive operator is symmetric. -/
theorem IsPositive.inner_pow_left_eq_inner_pow_right {T : H →L[ℂ] H}
    (hT : T.IsPositive) (n : ℕ) (x y : H) :
    inner ℂ ((T ^ n) x) y = inner ℂ x ((T ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change inner ℂ (T ((T ^ n) x)) y = inner ℂ x (T ((T ^ n) y))
      rw [hT.inner_left_eq_inner_right, ih]
      change inner ℂ x (((T ^ n) * T) y) = inner ℂ x ((T * (T ^ n)) y)
      rw [(Commute.self_pow T n).eq]

/-- Even vector moments of a positive operator are squared norms. -/
theorem IsPositive.re_inner_pow_two_mul {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (n : ℕ) :
    re (inner ℂ x ((T ^ (2 * n)) x)) = ‖(T ^ n) x‖ ^ 2 := by
  rw [show 2 * n = n + n by omega, pow_add]
  change re (inner ℂ x ((T ^ n) ((T ^ n) x))) = _
  rw [← hT.inner_pow_left_eq_inner_pow_right n]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Odd vector moments of a positive operator are positive quadratic forms of iterates. -/
theorem IsPositive.re_inner_pow_two_mul_add_one {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (n : ℕ) :
    re (inner ℂ x ((T ^ (2 * n + 1)) x)) =
      re (inner ℂ ((T ^ n) x) (T ((T ^ n) x))) := by
  rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
  change re (inner ℂ x ((T ^ n) ((T ^ (n + 1)) x))) = _
  rw [← hT.inner_pow_left_eq_inner_pow_right n]
  rw [pow_succ']
  rfl

/-- Every vector moment of a positive operator is nonnegative. -/
theorem IsPositive.re_inner_pow_nonneg {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (n : ℕ) :
    0 ≤ re (inner ℂ x ((T ^ n) x)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [hT.re_inner_pow_two_mul]
    positivity
  · rw [hT.re_inner_pow_two_mul_add_one]
    exact hT.re_inner_nonneg_right _

/-- Adjacent vector moments of a positive operator are log-convex. -/
theorem IsPositive.re_inner_pow_logConvex {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (n : ℕ) :
    (re (inner ℂ x ((T ^ (n + 1)) x))) ^ 2 ≤
      re (inner ℂ x ((T ^ n) x)) *
        re (inner ℂ x ((T ^ (n + 2)) x)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hcs := norm_inner_le_norm (𝕜 := ℂ) ((T ^ k) x) ((T ^ (k + 1)) x)
    have hre := Complex.abs_re_le_norm
      (inner ℂ ((T ^ k) x) ((T ^ (k + 1)) x))
    have hmoment :
        re (inner ℂ x ((T ^ (2 * k + 1)) x)) =
          re (inner ℂ ((T ^ k) x) ((T ^ (k + 1)) x)) := by
      rw [show 2 * k + 1 = k + (k + 1) by omega, pow_add]
      change re (inner ℂ x ((T ^ k) ((T ^ (k + 1)) x))) = _
      rw [← hT.inner_pow_left_eq_inner_pow_right k]
    rw [hmoment, hT.re_inner_pow_two_mul]
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, hT.re_inner_pow_two_mul]
    have habs : |re (inner ℂ ((T ^ k) x) ((T ^ (k + 1)) x))| ≤
        ‖(T ^ k) x‖ * ‖(T ^ (k + 1)) x‖ := hre.trans hcs
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 habs
    simpa [sq_abs, mul_pow] using hsquare
  · have hform := HTGeometry.cauchy_schwarz_psd
      (fun u v : H => inner ℂ v (T u))
      (fun u v w => by rw [map_add, inner_add_right])
      (fun c u v => by rw [map_smul, inner_smul_right])
      (fun u v => by
        calc
          inner ℂ u (T v) = inner ℂ (T u) v :=
            (hT.inner_left_eq_inner_right u v).symm
          _ = (starRingEnd ℂ) (inner ℂ v (T u)) := (inner_conj_symm _ _).symm)
      hT.re_inner_nonneg_right ((T ^ k) x) ((T ^ (k + 1)) x)
    have hmiddle :
        inner ℂ ((T ^ (k + 1)) x) (T ((T ^ k) x)) =
          inner ℂ ((T ^ (k + 1)) x) ((T ^ (k + 1)) x) := by
      congr 1
      simp [pow_succ']
    rw [hmiddle] at hform
    simp only [inner_self_eq_norm_sq_to_K] at hform
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega,
      hT.re_inner_pow_two_mul, hT.re_inner_pow_two_mul_add_one,
      hT.re_inner_pow_two_mul_add_one]
    simpa [pow_two] using hform

/-- A nonnegative log-convex sequence starting at one dominates powers of its first term. -/
theorem pow_first_le_of_nonneg_logConvex
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hzero : a 0 = 1)
    (hlog : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2)) (n : ℕ) :
    a 1 ^ n ≤ a n := by
  have hratio : ∀ k : ℕ, a 1 * a k ≤ a (k + 1) := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
        by_cases hk : a k = 0
        · have hnext : a (k + 1) = 0 := by
            have hklog := hlog k
            rw [hk, zero_mul] at hklog
            nlinarith [ha (k + 1)]
          rw [hnext, mul_zero]
          exact ha (k + 2)
        · have hkpos : 0 < a k := lt_of_le_of_ne (ha k) (Ne.symm hk)
          have hmul := mul_le_mul_of_nonneg_right ih (ha (k + 1))
          have hchain : a k * (a 1 * a (k + 1)) ≤ a k * a (k + 2) := by
            calc
              a k * (a 1 * a (k + 1)) =
                  (a 1 * a k) * a (k + 1) := by ring
              _ ≤ a (k + 1) * a (k + 1) := hmul
              _ = a (k + 1) ^ 2 := by ring
              _ ≤ a k * a (k + 2) := hlog k
          nlinarith
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih (ha 1)).trans (by
        simpa [mul_comm] using hratio n)

/-- Vector-state Jensen inequality for every natural power of a positive operator. -/
theorem IsPositive.re_inner_pow_ge {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (hx : ‖x‖ = 1) (n : ℕ) :
    (re (inner ℂ x (T x))) ^ n ≤ re (inner ℂ x ((T ^ n) x)) := by
  let a : ℕ → ℝ := fun k => re (inner ℂ x ((T ^ k) x))
  have ha : ∀ k, 0 ≤ a k := fun k => hT.re_inner_pow_nonneg x k
  have hzero : a 0 = 1 := by
    simp [a, inner_self_eq_norm_sq_to_K, hx]
  have hlog : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) :=
    fun k => hT.re_inner_pow_logConvex x k
  simpa [a] using pow_first_le_of_nonneg_logConvex a ha hzero hlog n

end ContinuousLinearMap
