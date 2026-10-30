import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant

/-!
# The Adams operations of the gauge torus

The ring `ℤ` has no nontrivial endomorphism (`ApproximateRingEndomorphisms`), but its multiplicative
dual has many. Multiplication by `k` on the gauge torus, `ψ^k x = k x` (`adams`), raises every twist
to the `k`-th power: `χ_{ψ^k x}(n) = χ_x(n)^k = χ_x(n^k)` (`twist_adams`, `twist_adams_eq_twist_pow`).
On characters it multiplies every frequency by `k`, as Frobenius multiplies degrees by `q`.

* **Composition** (`adams_adams`). `ψ^k ψ^l = ψ^{kl}`: the operations form a commuting family, the
  structure of a `Λ`-ring on the group ring of the gauge torus.
* **The equation `x^q = x`** (`isAdamsFixed_iff_frobenius`, `isAdamsFixed_iff`). A twist is fixed by
  `ψ^q` exactly when `χ(n)^q = χ(n)` for every `n`, i.e. when it takes values in the `(q − 1)`-th
  roots of unity. These finite-order twists are the "rational points" of `ψ^q`, as the elements of
  `𝔽_q` are the fixed points of Frobenius.
* **Primes suffice** (`isAdamsFixed_iff_primes`). Fixedness is read on the primes.
* **The trivial point** (`isAdamsFixed_two_iff`). `ψ²` has a single fixed twist, the trivial one:
  the special point `0` is the unique rational point of the first Adams operation.
* **Dirichlet gauge points** (`isAdamsFixed_dirichletGauge`). The gauge point of a Dirichlet character
  of order dividing `d` is fixed by `ψ^{d+1}`.

So the Frobenius equation `x^q = x` has a home: not on `ℤ`, where every bounded-defect endomorphism is
the identity or a gauge point, but on the gauge torus, where it cuts out the finite-order twists.
The trivial point and the Dirichlet characters are its solutions; the Liouville point is a solution of
`ψ³` (values `±1`). A producer built from Adams operations acts on characters, not on integers.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The Adams operation `ψ^k x = k x` of the gauge torus. -/
def adams (k : ℕ) (x : GaugeTorus) : GaugeTorus := k • x

/-- **`ψ^k` raises twists to the `k`-th power.** -/
theorem twist_adams (k : ℕ) (x : GaugeTorus) (n : ℕ) : twist (adams k x) n = twist x n ^ k := by
  induction k with
  | zero => simp [adams, twist_zero]
  | succ k ih => rw [adams, succ_nsmul, twist_add, ← adams, ih, pow_succ]

/-- Twists of powers are powers of twists. -/
theorem twist_pow_index (x : GaugeTorus) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    twist x (n ^ k) = twist x n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, twist_mul x (pow_ne_zero k hn) hn, ih, pow_succ]

/-- `ψ^k` evaluates the twist at the `k`-th power. -/
theorem twist_adams_eq_twist_pow (k : ℕ) (x : GaugeTorus) {n : ℕ} (hn : n ≠ 0) :
    twist (adams k x) n = twist x (n ^ k) := by
  rw [twist_adams, twist_pow_index x hn]

/-- **Composition.** `ψ^k ψ^l = ψ^{kl}`. -/
theorem adams_adams (k l : ℕ) (x : GaugeTorus) : adams k (adams l x) = adams (k * l) x := by
  simp only [adams, smul_smul]

/-- A gauge point is fixed by `ψ^k` when its twist is unchanged. -/
def IsAdamsFixed (k : ℕ) (x : GaugeTorus) : Prop := ∀ n, n ≠ 0 → twist (adams k x) n = twist x n

/-- **The Frobenius equation.** `ψ^q` fixes `x` exactly when `χ_x(n)^q = χ_x(n)` for all `n`. -/
theorem isAdamsFixed_iff_frobenius (q : ℕ) (x : GaugeTorus) :
    IsAdamsFixed q x ↔ ∀ n, n ≠ 0 → twist x n ^ q = twist x n := by
  simp only [IsAdamsFixed, twist_adams]

/-- **Fixed twists take values in roots of unity.** For `k ≥ 1`, `ψ^k` fixes `x` exactly when
`χ_x(n)^{k−1} = 1` for all `n`. -/
theorem isAdamsFixed_iff {k : ℕ} (hk : 1 ≤ k) (x : GaugeTorus) :
    IsAdamsFixed k x ↔ ∀ n, n ≠ 0 → twist x n ^ (k - 1) = 1 := by
  rw [isAdamsFixed_iff_frobenius]
  refine forall₂_congr fun n _ => ?_
  have hpow : twist x n ^ k = twist x n ^ (k - 1) * twist x n := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow]
  constructor
  · intro h
    exact mul_right_cancel₀ (twist_ne_zero x n) (h.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

/-- **Primes suffice.** -/
theorem isAdamsFixed_iff_primes {k : ℕ} (hk : 1 ≤ k) (x : GaugeTorus) :
    IsAdamsFixed k x ↔ ∀ p, p.Prime → twist x p ^ (k - 1) = 1 := by
  rw [isAdamsFixed_iff hk]
  refine ⟨fun h p hp => h p hp.ne_zero, fun h n hn => ?_⟩
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => rw [twist_one, one_pow]
  | prime p hp => exact h p hp
  | mul a b ha hb =>
    have ha0 := left_ne_zero_of_mul hn
    have hb0 := right_ne_zero_of_mul hn
    rw [twist_mul x ha0 hb0, mul_pow, ha ha0, hb hb0, one_mul]

/-- **The trivial point is the unique fixed twist of `ψ²`.** -/
theorem isAdamsFixed_two_iff (x : GaugeTorus) :
    IsAdamsFixed 2 x ↔ ∀ n, n ≠ 0 → twist x n = 1 := by
  rw [isAdamsFixed_iff (by norm_num)]
  simp

/-- The trivial point is fixed by every Adams operation. -/
theorem isAdamsFixed_zero (k : ℕ) : IsAdamsFixed k 0 := by
  intro n _
  rw [twist_adams, twist_zero, one_pow]

/-- **Dirichlet gauge points are rational points.** The gauge point of a Dirichlet character of
order dividing `d ≠ 0` is fixed by `ψ^{d+1}`. -/
theorem isAdamsFixed_dirichletGauge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {d : ℕ}
    (hd : d ≠ 0) (hχ : χ ^ d = 1) : IsAdamsFixed (d + 1) (dirichletGauge χ) := by
  rw [isAdamsFixed_iff_primes (by omega), Nat.add_sub_cancel]
  intro p hp
  by_cases hcop : Nat.Coprime p q
  · rw [twist_dirichletGauge χ hp.ne_zero hcop, ← MulChar.pow_apply' χ hd, hχ]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr hcop)
  · rw [twist_prime_apply _ hp]
    simp [dirichletGauge, if_neg hcop]

end GaloisForLFunctions.ArithmeticGaugeTheory
