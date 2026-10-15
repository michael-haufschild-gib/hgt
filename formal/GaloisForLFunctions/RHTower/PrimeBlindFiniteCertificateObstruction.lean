import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# No finite node correction of the archimedean functional is Weil-positive

Prime-blind positivity is, by the Farkas lemma, the existence of real weights `lam` on the nodes
`n ≥ 2` with the full Weil functional `W_∞ − Σ_n lam(n) n^{-1/2} (k(log n) + k(−log n))` nonnegative on
every autocorrelation (`exists_weilPositiveFull_iff_primeBlindPositive`), and every such weight
vector equals the von Mangoldt function (`eq_vonMangoldt_of_weilPositiveFull`).

This module records the obstruction that follows for *certificates*: a weight vector with finite
support, or one that vanishes beyond some node, or one that is eventually constant, is never
Weil-positive.  Equivalently, no correction of the archimedean functional `W_∞` by finitely many
node terms, and no correction by a Dirichlet tail with constant coefficients, is nonnegative on all
autocorrelations.  The reason is that Weil positivity pins the weights to `Λ`, which is `log 2` on
every power of `2` and `log 3` on every power of `3`.

Contrast with the finite-level picture: at a finite level the admissible pole weights form a
nonempty window for small levels, and finitely many node weights suffice there; the obstruction is
global, over all levels at once.
-/

open Complex Set

namespace RHTower.WeilOneSided

open WeilSpectral

/-- A Weil-positive weight vector is `log 2 ≠ 0` on every positive power of `2`. -/
theorem weilPositiveFull_apply_two_pow_ne_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℕ} (hk : 1 ≤ k) : lam (2 ^ k) ≠ 0 := by
  have h2 : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [eq_vonMangoldt_of_weilPositiveFull hW (2 ^ k) h2,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact (Real.log_pos (by norm_num)).ne'

/-- The support of a Weil-positive weight vector is infinite: it contains every power of `2`. -/
theorem infinite_support_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (Function.support lam).Infinite := by
  have hsub : Set.range (fun k : ℕ => 2 ^ (k + 1)) ⊆ Function.support lam := by
    rintro _ ⟨k, rfl⟩
    exact weilPositiveFull_apply_two_pow_ne_zero hW (by omega)
  have hinf : (Set.range (fun k : ℕ => 2 ^ (k + 1))).Infinite :=
    Set.infinite_range_of_injective (fun a b h => by
      have := Nat.pow_right_injective (le_refl 2) h
      omega)
  exact fun hfin => hinf (hfin.subset hsub)

/-- **No finite certificate.** A weight vector with finite support is never Weil-positive: no
correction of the archimedean functional by finitely many node terms is nonnegative on all
autocorrelations. -/
theorem not_weilPositiveFull_of_finite_support {lam : ℕ → ℝ}
    (hfin : (Function.support lam).Finite) : ¬ WeilPositiveFull lam :=
  fun hW => infinite_support_of_weilPositiveFull hW hfin

/-- A weight vector vanishing beyond some node is never Weil-positive. -/
theorem not_weilPositiveFull_of_eventually_zero {lam : ℕ → ℝ} {N : ℕ}
    (hN : ∀ n, N ≤ n → lam n = 0) : ¬ WeilPositiveFull lam := by
  apply not_weilPositiveFull_of_finite_support
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  by_contra hlt
  exact hn (hN n (not_lt.mp hlt))

/-- A weight vector that is eventually constant is never Weil-positive: Weil positivity forces the
value `log 2` on large powers of `2` and `log 3` on large powers of `3`. -/
theorem not_weilPositiveFull_of_eventually_const {lam : ℕ → ℝ} {N : ℕ} {c : ℝ}
    (hN : ∀ n, N ≤ n → lam n = c) : ¬ WeilPositiveFull lam := by
  intro hW
  have hpow := eq_vonMangoldt_of_weilPositiveFull hW
  have h2N : N ≤ 2 ^ (N + 1) := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3N : N ≤ 3 ^ (N + 1) := h2N.trans (Nat.pow_le_pow_left (by norm_num) _)
  have h2ge : 2 ≤ 2 ^ (N + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3ge : 2 ≤ 3 ^ (N + 1) := h2ge.trans (Nat.pow_le_pow_left (by norm_num) _)
  have e2 : c = Real.log 2 := by
    rw [← hN _ h2N, hpow _ h2ge, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have e3 : c = Real.log 3 := by
    rw [← hN _ h3N, hpow _ h3ge, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    norm_num
  have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- Prime-blind positivity (hence RH) can only be certified by a weight vector of infinite support:
there is no finitely supported Weil-positive weight vector at all. -/
theorem not_exists_finite_support_weilPositiveFull :
    ¬ ∃ lam : ℕ → ℝ, (Function.support lam).Finite ∧ WeilPositiveFull lam :=
  fun ⟨_, hfin, hW⟩ => not_weilPositiveFull_of_finite_support hfin hW

end RHTower.WeilOneSided
