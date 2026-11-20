import GaloisForLFunctions.ArithmeticProducerTheory.FrobeniusLinearDifferentialOperatorsAreMultiplications

/-!
# The digit operators lift the Hasse derivatives

Over `𝔽_p` the operators that are linear over the Frobenius image are the Hasse derivatives of
order `< pᵏ`. This module identifies their lift to every ring of coefficients.

A *diagonal operator* `diag φ` multiplies the monomial `X^m` by a scalar `φ(m)`.

* `diag_expand_linear_iff`: `diag φ` is linear over the image of `ψ_a = expand a` iff `φ` is
  periodic, `φ(a k + m) = φ(m)`.
* `digitOp a k i`: `X^m ↦ (k-th base-a digit of mᵢ) X^m`. It is linear over the image of
  `ψ_{a^(k+1)}` over every ring (`digitOp_expand_mul`), and the Euler derivation is its `a`-adic
  series: `Xᵢ∂ᵢ = Σ_{k<K} aᵏ · digitOp a k i + a^K · quotOp a K i` (`euler_eq_sum_digitOp`), where
  the remainder is a derivation along `ψ_{a^K}` (`quotOp_expand_mul`).
* `hasseEuler i j`: `X^m ↦ binom(mᵢ, j) X^m`, the Hasse derivative `Xᵢʲ ∂ᵢʲ / j!`. It is a
  differential operator of order `≤ j` over every ring (`hasOrderLE_hasseEuler`).
* `digitOp_eq_hasseEuler`: in characteristic `p`, `digitOp p k i = hasseEuler i (pᵏ)`, by Lucas'
  congruence `binom(n, pᵏ) ≡ digit_k(n) (mod p)`.
* `not_hasOrderLE_digitOp`: if `a ≥ 2` is regular in `R`, no digit operator has finite order.

So the Frobenius-linear operators exist over `ℤ` and reduce to the Hasse derivatives modulo `p`; what
is special to characteristic `p` is that they are differential operators there.
-/

open MvPolynomial

namespace GaloisForLFunctions.ArithmeticProducerTheory

variable {σ R : Type*} [CommRing R]

/-! ### Diagonal operators -/

/-- The diagonal operator with symbol `φ`: `X^m ↦ φ(m) X^m`. -/
noncomputable def diag (φ : (σ →₀ ℕ) → R) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun m => monomial m (φ m)

@[simp]
theorem diag_monomial (φ : (σ →₀ ℕ) → R) (m : σ →₀ ℕ) (c : R) :
    diag φ (monomial m c) = monomial m (φ m * c) := by
  have h : monomial m c = c • basisMonomials σ R m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, diag, Module.Basis.constr_basis, smul_monomial, smul_eq_mul, mul_comm]

theorem coeff_diag (φ : (σ →₀ ℕ) → R) (f : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (diag φ f) = φ m * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [diag_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem diag_congr {φ φ' : (σ →₀ ℕ) → R} (h : ∀ m, φ m = φ' m) : diag φ = diag φ' := by
  rw [funext h]

theorem diag_sub (φ φ' : (σ →₀ ℕ) → R) (f : MvPolynomial σ R) :
    diag (fun m => φ m - φ' m) f = diag φ f - diag φ' f := by
  ext m
  rw [coeff_sub, coeff_diag, coeff_diag, coeff_diag, sub_mul]

/-- `diag φ (X^k f) = X^k · diag (φ(k + ·)) f`. -/
theorem diag_monomial_mul (φ : (σ →₀ ℕ) → R) (k : σ →₀ ℕ) (c : R) (f : MvPolynomial σ R) :
    diag φ (monomial k c * f) = monomial k c * diag (fun m => φ (k + m)) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u d =>
    rw [monomial_mul, diag_monomial, diag_monomial, monomial_mul]
    congr 1
    ring
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]

/-- The commutator of a diagonal operator with a coordinate is the finite difference of its
symbol. -/
theorem commutator_diag_X (φ : (σ →₀ ℕ) → R) (i : σ) :
    commutator (diag φ).toAddMonoidHom (X i) = (AddMonoidHom.mulLeft (X i)).comp
      (diag fun m => φ (Finsupp.single i 1 + m) - φ m).toAddMonoidHom :=
  AddMonoidHom.ext fun g => by
    change diag φ (X i * g) - X i * diag φ g =
      X i * diag (fun m => φ (Finsupp.single i 1 + m) - φ m) g
    rw [diag_sub, mul_sub]
    congr 1
    exact diag_monomial_mul φ (Finsupp.single i 1) 1 g

/-- A periodic symbol gives an operator linear over the Frobenius image. -/
theorem diag_expand_mul {a : ℕ} {φ : (σ →₀ ℕ) → R} (hφ : ∀ k m, φ (a • k + m) = φ m)
    (g f : MvPolynomial σ R) : diag φ (expand a g * f) = expand a g * diag φ f := by
  induction g using MvPolynomial.induction_on' with
  | monomial k c => rw [expand_monomial, diag_monomial_mul, diag_congr (hφ k)]
  | add p q hp hq => rw [map_add, add_mul, map_add, hp, hq, add_mul]

/-- **Frobenius-linear diagonal operators are the periodic symbols.** -/
theorem diag_expand_linear_iff (a : ℕ) (φ : (σ →₀ ℕ) → R) :
    (∀ g f : MvPolynomial σ R, diag φ (expand a g * f) = expand a g * diag φ f) ↔
      ∀ k m, φ (a • k + m) = φ m := by
  classical
  refine ⟨fun h k m => ?_, fun h => diag_expand_mul h⟩
  have h1 := h (monomial k 1) (monomial m 1)
  rw [expand_monomial, monomial_mul, diag_monomial, diag_monomial, monomial_mul] at h1
  have h2 := congrArg (coeff (a • k + m)) h1
  rw [coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl] at h2
  simpa using h2

/-- **Rigidity.** If `a` is regular in `R`, a Frobenius-linear diagonal operator of finite order
has constant symbol. -/
theorem diag_symbol_const_of_hasOrderLE {a : ℕ} (ha : IsRegular (a : R)) {φ : (σ →₀ ℕ) → R}
    (hφ : ∀ k m, φ (a • k + m) = φ m) {n : ℕ} (hn : HasOrderLE n (diag φ).toAddMonoidHom)
    (m : σ →₀ ℕ) : φ m = φ 0 := by
  classical
  have h := hn.eq_mul_of_expand_linear ha (fun g f => diag_expand_mul hφ g f) (monomial m 1)
  change diag φ (monomial m 1) = monomial m 1 * diag φ 1 at h
  have h1 : diag φ (1 : MvPolynomial σ R) = monomial 0 (φ 0) := by
    rw [show (1 : MvPolynomial σ R) = monomial 0 1 from rfl, diag_monomial, mul_one]
  rw [diag_monomial, h1, monomial_mul, mul_one, one_mul, add_zero] at h
  have h2 := congrArg (coeff m) h
  rwa [coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl] at h2

/-! ### The digit operators and the a-adic series of the Euler derivation -/

/-- The `k`-th base-`a` digit operator in the coordinate `i`. -/
noncomputable def digitOp (a k : ℕ) (i : σ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  diag fun m => ((m i / a ^ k % a : ℕ) : R)

/-- The quotient operator `X^m ↦ ⌊mᵢ / a^K⌋ X^m`. -/
noncomputable def quotOp (a K : ℕ) (i : σ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  diag fun m => ((m i / a ^ K : ℕ) : R)

theorem digit_periodic (a k l n : ℕ) : (a ^ (k + 1) * l + n) / a ^ k % a = n / a ^ k % a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · cases k <;> simp
  · rw [pow_succ, mul_assoc, Nat.mul_add_div (pow_pos ha k), Nat.mul_add_mod]

/-- **The digit operators are Frobenius-linear over every ring.** -/
theorem digitOp_expand_mul (a k : ℕ) (i : σ) (g f : MvPolynomial σ R) :
    digitOp a k i (expand (a ^ (k + 1)) g * f) = expand (a ^ (k + 1)) g * digitOp a k i f :=
  diag_expand_mul (fun l m => by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, digit_periodic]) g f

/-- The Euler derivation is the diagonal operator with symbol `mᵢ`. -/
theorem X_mul_pderiv_eq_diag (i : σ) (f : MvPolynomial σ R) :
    X i * pderiv i f = diag (fun m => (m i : R)) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c => rw [X_mul_pderiv_monomial, diag_monomial, smul_monomial, nsmul_eq_mul]
  | add p q hp hq => rw [map_add, mul_add, hp, hq, map_add]

theorem digit_expansion (a n K : ℕ) :
    n = ∑ k ∈ Finset.range K, a ^ k * (n / a ^ k % a) + a ^ K * (n / a ^ K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul, add_assoc, mul_assoc,
      ← mul_add, Nat.mod_add_div]
    exact ih

/-- **The a-adic series of the Euler derivation.** `Xᵢ∂ᵢ` is the sum of `aᵏ` times the `k`-th
digit operator, `k < K`, plus `a^K` times the quotient operator. -/
theorem euler_eq_sum_digitOp (a K : ℕ) (i : σ) (f : MvPolynomial σ R) :
    X i * pderiv i f =
      ∑ k ∈ Finset.range K, (a ^ k : R) • digitOp a k i f + (a ^ K : R) • quotOp a K i f := by
  ext m
  rw [X_mul_pderiv_eq_diag, coeff_diag, coeff_add, coeff_sum, coeff_smul, quotOp, coeff_diag]
  simp only [coeff_smul, digitOp, coeff_diag, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul,
    ← add_mul]
  congr 1
  exact_mod_cast congrArg (Nat.cast : ℕ → R) (digit_expansion a (m i) K)

/-- The quotient operator is a derivation along `ψ_{a^K}`:
`Q(ψ(g) f) = ψ(g) Q(f) + ψ(Xᵢ∂ᵢ g) f`. -/
theorem quotOp_expand_mul {a : ℕ} (ha : 0 < a) (K : ℕ) (i : σ) (g f : MvPolynomial σ R) :
    quotOp a K i (expand (a ^ K) g * f) =
      expand (a ^ K) g * quotOp a K i f + expand (a ^ K) (X i * pderiv i g) * f := by
  induction g using MvPolynomial.induction_on' with
  | monomial l c =>
    have hsym : (fun m : σ →₀ ℕ => ((((a ^ K) • l + m) i / a ^ K : ℕ) : R)) =
        fun m => (l i : R) + ((m i / a ^ K : ℕ) : R) := funext fun m => by
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_add_div (pow_pos ha K),
        Nat.cast_add]
    have hadd : diag (fun m : σ →₀ ℕ => (l i : R) + ((m i / a ^ K : ℕ) : R)) f =
        (l i : R) • f + diag (fun m : σ →₀ ℕ => ((m i / a ^ K : ℕ) : R)) f := by
      ext m
      rw [coeff_diag, coeff_add, coeff_smul, coeff_diag, smul_eq_mul, add_mul]
    simp only [quotOp]
    rw [expand_monomial, diag_monomial_mul, hsym, hadd, X_mul_pderiv_monomial,
      map_nsmul, expand_monomial, mul_add, nsmul_eq_mul, Algebra.smul_def]
    simp only [algebraMap_eq, map_natCast]
    ring
  | add p q hp hq =>
    simp only [map_add, add_mul, mul_add, hp, hq]
    ring

/-! ### The Hasse–Euler operators -/

/-- The Hasse–Euler operator `binom(Xᵢ∂ᵢ, j)`: `X^m ↦ binom(mᵢ, j) X^m`. -/
noncomputable def hasseEuler (i : σ) (j : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  diag fun m => ((m i).choose j : R)

/-- **The Hasse–Euler operator of index `j` has order `≤ j` over every ring.** Pascal's rule is the
commutator relation `[H_{j+1}, Xᵢ] = Xᵢ H_j`. -/
theorem hasOrderLE_hasseEuler (i : σ) (j : ℕ) :
    HasOrderLE j (hasseEuler (R := R) i j).toAddMonoidHom := by
  classical
  induction j with
  | zero =>
    intro f g
    have h1 : ∀ f : MvPolynomial σ R, hasseEuler i 0 f = f := fun f => by
      ext m
      rw [hasseEuler, coeff_diag, Nat.choose_zero_right, Nat.cast_one, one_mul]
    change hasseEuler i 0 (f * g) = f * hasseEuler i 0 g
    rw [h1, h1]
  | succ j ih =>
    refine hasOrderLE_succ_of_X _ fun k => ?_
    rw [hasseEuler, commutator_diag_X]
    by_cases hk : k = i
    · subst hk
      have hsym : (fun m : σ →₀ ℕ =>
          (((Finsupp.single k 1 + m : σ →₀ ℕ) k).choose (j + 1) : R) -
          ((m k).choose (j + 1) : R)) = fun m => ((m k).choose j : R) := funext fun m => by
        rw [Finsupp.add_apply, Finsupp.single_eq_same, add_comm 1 (m k), Nat.choose_succ_succ,
          Nat.cast_add, add_sub_cancel_right]
      rw [hsym]
      exact ((hasOrderLE_mulLeft _).comp ih).mono (Nat.zero_add j).le
    · have hsym : (fun m : σ →₀ ℕ =>
          (((Finsupp.single k 1 + m : σ →₀ ℕ) i).choose (j + 1) : R) -
          ((m i).choose (j + 1) : R)) = fun _ => 0 := funext fun m => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hk, zero_add, sub_self]
      have h0 : (diag fun _ : σ →₀ ℕ => (0 : R)) = 0 := LinearMap.ext fun f => by
        ext m
        rw [coeff_diag, zero_mul]
        rfl
      rw [hsym, h0]
      have hz : HasOrderLE j (0 : MvPolynomial σ R →ₗ[R] MvPolynomial σ R).toAddMonoidHom :=
        hasOrderLE_zero_map j
      exact ((hasOrderLE_mulLeft _).comp hz).mono (Nat.zero_add j).le

/-- Lucas' congruence at a prime power: `binom(n, pᵏ) ≡ ⌊n / pᵏ⌋ (mod p)`. -/
theorem choose_prime_pow_modEq (p : ℕ) [Fact p.Prime] (k n : ℕ) :
    n.choose (p ^ k) ≡ n / p ^ k [MOD p] := by
  induction k generalizing n with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    have hp := (Fact.out : p.Prime).pos
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := p ^ (k + 1))
    have h1 : p ^ (k + 1) % p = 0 := by
      rw [pow_succ]
      exact Nat.mul_mod_left _ _
    have h2 : p ^ (k + 1) / p = p ^ k := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ hp
    rw [h1, h2, Nat.choose_zero_right, one_mul] at h
    have h3 : n / p ^ (k + 1) = n / p / p ^ k := by rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [h3]
    exact h.trans (ih (n / p))

/-- **In characteristic `p` the digit operator is the Hasse derivative of order `pᵏ`.** -/
theorem digitOp_eq_hasseEuler (p : ℕ) [Fact p.Prime] [CharP R p] (k : ℕ) (i : σ) :
    digitOp (R := R) p k i = hasseEuler i (p ^ k) :=
  diag_congr fun m => (CharP.natCast_eq_natCast R p).mpr
    ((Nat.mod_modEq _ _).trans (choose_prime_pow_modEq p k (m i)).symm)

/-- In characteristic `p` the `k`-th digit operator is a differential operator of order `≤ pᵏ`. -/
theorem hasOrderLE_digitOp_of_charP (p : ℕ) [Fact p.Prime] [CharP R p] (k : ℕ) (i : σ) :
    HasOrderLE (p ^ k) (digitOp (R := R) p k i).toAddMonoidHom := by
  rw [digitOp_eq_hasseEuler]
  exact hasOrderLE_hasseEuler i (p ^ k)

/-- **Where `a` is regular, no digit operator is a differential operator.** -/
theorem not_hasOrderLE_digitOp [Nontrivial R] {a : ℕ} (ha : IsRegular (a : R)) (ha2 : 2 ≤ a)
    (k : ℕ) (i : σ) (n : ℕ) : ¬ HasOrderLE n (digitOp (R := R) a k i).toAddMonoidHom := by
  intro h
  have hreg : IsRegular ((a ^ (k + 1) : ℕ) : R) := by
    rw [Nat.cast_pow]
    exact ha.pow _
  have hper : ∀ (l m : σ →₀ ℕ), ((((a ^ (k + 1)) • l + m) i / a ^ k % a : ℕ) : R) =
      ((m i / a ^ k % a : ℕ) : R) := fun l m => by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, digit_periodic]
  have h1 := diag_symbol_const_of_hasOrderLE hreg hper h (Finsupp.single i (a ^ k))
  rw [Finsupp.single_eq_same, Nat.div_self (pow_pos (by omega) k), Nat.mod_eq_of_lt (by omega),
    Finsupp.zero_apply, Nat.zero_div, Nat.zero_mod, Nat.cast_one, Nat.cast_zero] at h1
  exact one_ne_zero h1

end GaloisForLFunctions.ArithmeticProducerTheory
