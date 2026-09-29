import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Derivation.Basic
import GaloisForLFunctions.HTGeometry.MvLinearIrreducible

/-!
# Polynomials constant along the lines of a triangular field

Let `B : Fin n → K[x_0, …, x_{n−1}]` be a *unitriangular* vector field: `B_0 = 1`, `B_i` involves
only
`x_0, …, x_{i−1}`, and `∂B_i/∂x_{i−1} = 1`.  A polynomial `G` constant along every line
`x + s·B(x)`, i.e. `G(x + s·B(x)) = G(x)` in `K[s, x]`, is a constant (characteristic zero).

Write `g_i = (∂_i G)(x + s·B)`.  Differentiating the identity in `s` gives `∑_i g_i B_i = 0`, and
in `x_j` gives `g_j + s·∑_i g_i ∂_j B_i = ∂_j G`.  Contracting the second identity with the iterated
fields `W^{(0)} = B`, `W^{(k+1)}_i = ∑_j ∂_j B_i · W^{(k)}_j` yields `A_k + s·A_{k+1} = c_k` for
`A_k = ⟨g, W^{(k)}⟩`, `c_k = ⟨∇G, W^{(k)}⟩`, and since `W^{(n)} = 0` this telescopes to
`∑_{k<n} (−s)^k c_k = 0`.  The fields `W^{(k)}` are unitriangular, so every `∂_j G` vanishes.

The parameter `s` is the variable `0` of `K[x_0, …, x_n]`, and the coordinates are the variables
`j.succ`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-! ### The chain rule for a derivation -/

/-- **Chain rule.**  A derivation applied to a polynomial expression. -/
theorem derivation_aeval_eq_sum_pderiv {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S]
    [Algebra K S] (D : Derivation K S S) (g : ι → S) (P : MvPolynomial ι K) :
    D (aeval g P) = ∑ i, aeval g (pderiv i P) * D (g i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      rw [map_add, map_add, hP, hQ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add, add_mul]
  | mul_X P k hP =>
      rw [map_mul, aeval_X, Derivation.leibniz, hP, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
      have hterm : ∀ i, aeval g (pderiv i (P * X k)) * D (g i)
          = g k * (aeval g (pderiv i P) * D (g i))
            + if i = k then aeval g P * D (g k) else 0 := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X]
        by_cases hik : i = k
        · subst hik
          simp only [Pi.single_eq_same, map_add, map_mul, aeval_X, map_one, if_true]
          ring
        · have hki : ¬ k = i := fun h => hik h.symm
          simp only [Pi.single_apply, hki, hik, if_false, map_add, map_mul, aeval_X, map_zero]
          ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      ring

/-! ### Constants of the partial derivatives -/

/-- **Zero gradient means constant**, in characteristic zero. -/
theorem eq_C_of_forall_pderiv_eq_zero' [CharZero K] {ι : Type*} [DecidableEq ι]
    {P : MvPolynomial ι K} (h : ∀ j, pderiv j P = 0) : P = C (coeff 0 P) := by
  classical
  ext τ
  by_cases hτ : τ = 0
  · subst hτ
    rw [coeff_C, if_pos rfl]
  · rw [coeff_C, if_neg (Ne.symm hτ)]
    obtain ⟨j, hj⟩ : ∃ j, τ j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hτ (Finsupp.ext fun i => by rw [hc i]; rfl)
    have hdec : τ - Finsupp.single j 1 + Finsupp.single j 1 = τ := by
      ext i
      rw [Finsupp.add_apply, Finsupp.tsub_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg (fun hh => hij hh.symm)]
        omega
    have hcoef := congrArg (coeff (τ - Finsupp.single j 1)) (h j)
    rw [coeff_pderiv, hdec, coeff_zero] at hcoef
    have hsub : ((τ - Finsupp.single j 1 : ι →₀ ℕ)) j + 1 = τ j := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    have hsubK : (((τ - Finsupp.single j 1 : ι →₀ ℕ)) j : K) + 1 = (τ j : K) := by
      exact_mod_cast hsub
    rw [hsubK] at hcoef
    have hne : ((τ j : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hj
    exact (mul_eq_zero.mp hcoef).resolve_right hne

/-! ### The line substitution -/

variable {n : ℕ}

/-- The line substitution `x_j ↦ x_j + s·B_j(x)`, with `s` the variable `0` and `x_j` the variable
`j.succ`. -/
def triLineSubst (B : Fin n → MvPolynomial (Fin n) K) : Fin n → MvPolynomial (Fin (n + 1)) K :=
  fun j => X j.succ + X 0 * rename Fin.succ (B j)

theorem pderiv_zero_rename_succ (P : MvPolynomial (Fin n) K) :
    pderiv (0 : Fin (n + 1)) (rename Fin.succ P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [rename_C, pderiv_C]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, add_zero]
  | mul_X P k hP =>
      rw [map_mul, rename_X, Derivation.leibniz, hP, pderiv_X_of_ne (Fin.succ_ne_zero k)]
      simp

theorem pderiv_succ_rename_succ (j : Fin n) (P : MvPolynomial (Fin n) K) :
    pderiv j.succ (rename Fin.succ P) = rename Fin.succ (pderiv j P) :=
  pderiv_rename (Fin.succ_injective n) j P

theorem pderiv_zero_lineSubst (B : Fin n → MvPolynomial (Fin n) K) (i : Fin n) :
    pderiv (0 : Fin (n + 1)) (triLineSubst B i) = rename Fin.succ (B i) := by
  simp [triLineSubst, Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero i),
    pderiv_zero_rename_succ]

theorem pderiv_succ_lineSubst (B : Fin n → MvPolynomial (Fin n) K) (i j : Fin n) :
    pderiv j.succ (triLineSubst B i)
      = (if i = j then 1 else 0) + X 0 * rename Fin.succ (pderiv j (B i)) := by
  rw [triLineSubst, map_add, Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero j).symm,
    smul_zero, add_zero, pderiv_succ_rename_succ, smul_eq_mul, pderiv_X]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Pi.single_apply, if_neg (fun h => hij (Fin.succ_injective n h)), if_neg hij]

/-! ### The iterated fields -/

/-- The iterated fields `W^{(0)} = B`, `W^{(k+1)}_i = ∑_j ∂_j B_i · W^{(k)}_j`. -/
def iterField (B : Fin n → MvPolynomial (Fin n) K) : ℕ → Fin n → MvPolynomial (Fin n) K
  | 0 => B
  | (k + 1) => fun i => ∑ j, pderiv j (B i) * iterField B k j

/-- A field is unitriangular: `B_0 = 1`, `B_i` involves only `x_j` with `j < i`, and
`∂B_{j+1}/∂x_j = 1`. -/
structure IsUnitriangularField (B : Fin n → MvPolynomial (Fin n) K) : Prop where
  zero : ∀ i : Fin n, (i : ℕ) = 0 → B i = 1
  low : ∀ i j : Fin n, (i : ℕ) ≤ j → pderiv j (B i) = 0
  sub : ∀ i j : Fin n, (j : ℕ) + 1 = i → pderiv j (B i) = 1

theorem IsUnitriangularField.iterField_triangular {B : Fin n → MvPolynomial (Fin n) K}
    (hB : IsUnitriangularField B) (k : ℕ) :
    (∀ i : Fin n, (i : ℕ) < k → iterField B k i = 0) ∧
      (∀ i : Fin n, (i : ℕ) = k → iterField B k i = 1) := by
  induction k with
  | zero =>
      refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
      exact hB.zero i hi
  | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · refine Finset.sum_eq_zero fun j _ => ?_
        rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
        · rw [ih0 j hjk, mul_zero]
        · rw [hB.low i j (by omega), zero_mul]
      · show ∑ j, pderiv j (B i) * iterField B k j = 1
        have hk : k < n := by have := i.isLt; omega
        rw [Finset.sum_eq_single ⟨k, hk⟩]
        · rw [hB.sub i ⟨k, hk⟩ (by simp [hi]), ih1 ⟨k, hk⟩ rfl, mul_one]
        · intro j _ hj
          rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
          · rw [ih0 j hjk, mul_zero]
          · have hjk' : (k : ℕ) < j := by
              rcases Nat.lt_or_eq_of_le hjk with h | h
              · exact h
              · exact absurd (Fin.ext h.symm) hj
            rw [hB.low i j (by omega), zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem IsUnitriangularField.iterField_top {B : Fin n → MvPolynomial (Fin n) K}
    (hB : IsUnitriangularField B) (i : Fin n) : iterField B n i = 0 :=
  (hB.iterField_triangular n).1 i i.isLt

/-! ### Constancy along the lines -/

/-- **A polynomial constant along the lines of a unitriangular field is constant.** -/
theorem eq_C_of_lineSubst_invariant [CharZero K] {B : Fin n → MvPolynomial (Fin n) K}
    (hB : IsUnitriangularField B) {G : MvPolynomial (Fin n) K}
    (hG : aeval (triLineSubst B) G = rename Fin.succ G) : G = C (coeff 0 G) := by
  classical
  set s : MvPolynomial (Fin (n + 1)) K := X 0 with hs
  set ι : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K := rename Fin.succ with hι
  set g : Fin n → MvPolynomial (Fin (n + 1)) K := fun i => aeval (triLineSubst B) (pderiv i G)
    with hg
  -- the `s`-derivative
  have hI : ∑ i, g i * ι (B i) = 0 := by
    have h := congrArg (pderiv (0 : Fin (n + 1))) hG
    rw [derivation_aeval_eq_sum_pderiv, pderiv_zero_rename_succ] at h
    simpa only [pderiv_zero_lineSubst] using h
  -- the coordinate derivatives
  have hII : ∀ j : Fin n, g j + s * ∑ i, g i * ι (pderiv j (B i)) = ι (pderiv j G) := by
    intro j
    have h := congrArg (pderiv j.succ) hG
    rw [derivation_aeval_eq_sum_pderiv, pderiv_succ_rename_succ] at h
    rw [← h]
    simp only [pderiv_succ_lineSubst, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    ring
  -- contraction with the iterated fields
  set A : ℕ → MvPolynomial (Fin (n + 1)) K := fun k => ∑ i, g i * ι (iterField B k i) with hA
  set c : ℕ → MvPolynomial (Fin n) K := fun k => ∑ j, pderiv j G * iterField B k j with hc
  have hstep : ∀ k, A k + s * A (k + 1) = ι (c k) := by
    intro k
    simp only [hA, hc, map_sum, map_mul, iterField]
    rw [Finset.mul_sum]
    have hrhs : ∑ j, ι (pderiv j G) * ι (iterField B k j)
        = ∑ j, (g j + s * ∑ i, g i * ι (pderiv j (B i))) * ι (iterField B k j) :=
      Finset.sum_congr rfl fun j _ => by rw [hII j]
    rw [hrhs]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have htel : ∀ k, (∑ m ∈ Finset.range k, (-s) ^ m * ι (c m)) + (-s) ^ k * A k = A 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ← ih, ← hstep k]
        ring
  have hA0 : A 0 = 0 := by simpa [hA, iterField] using hI
  have hAn : A n = 0 := by
    simp only [hA, hB.iterField_top, map_zero, mul_zero, Finset.sum_const_zero]
  have hsum : ∑ m ∈ Finset.range n, (-s) ^ m * ι (c m) = 0 := by
    have h := htel n
    rw [hAn, hA0, mul_zero, add_zero] at h
    exact h
  -- extract the coefficients in `s`
  have hc0 : ∀ m < n, c m = 0 := by
    intro m hm
    have h := congrArg (fun P => (finSuccEquiv K n P).coeff m) hsum
    simp only [map_sum, map_mul, map_pow, map_neg, finSuccEquiv_X_zero, hs, hι,
      finSuccEquiv_rename_succ, map_zero, Polynomial.coeff_zero] at h
    have hterm : ∀ m' ∈ Finset.range n,
        ((-Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ m' * Polynomial.C (c m')).coeff m
          = if m' = m then (-1) ^ m * c m else 0 := by
      intro m' _
      have hmon : ((-Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ m'
          * Polynomial.C (c m')) = Polynomial.C ((-1) ^ m' * c m') * Polynomial.X ^ m' := by
        rw [neg_pow (Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) m']
        simp only [map_mul, map_pow, map_neg, map_one]
        ring
      rw [hmon, Polynomial.coeff_C_mul_X_pow]
      by_cases h' : m' = m
      · subst h'
        simp
      · rw [if_neg (Ne.symm h'), if_neg h']
    rw [Polynomial.finsetSum_coeff, Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr hm)] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  -- back substitution
  have hgrad' : ∀ m, ∀ j : Fin n, n - (j : ℕ) = m → pderiv j G = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro j hk
    have hcj := hc0 j j.isLt
    simp only [hc] at hcj
    rw [Finset.sum_eq_single j] at hcj
    · rwa [(hB.iterField_triangular j).2 j rfl, mul_one] at hcj
    · intro i _ hij
      rcases Nat.lt_or_ge (i : ℕ) j with hlt | hge
      · rw [(hB.iterField_triangular j).1 i hlt, mul_zero]
      · have hgt : (j : ℕ) < i := lt_of_le_of_ne hge (fun h => hij (Fin.ext h).symm)
        rw [ih (n - i) (by have := i.isLt; omega) i rfl, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hgrad : ∀ j : Fin n, pderiv j G = 0 := fun j => hgrad' _ j rfl
  exact eq_C_of_forall_pderiv_eq_zero' hgrad

end

end GaloisForLFunctions.HTGeometry
