import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Total degree for a polynomial in two variables

A polynomial in two variables written as a polynomial in the outer variable with polynomial
coefficients has total degree at most `d` exactly when the degree of its `k`-th coefficient plus `k`
is at most `d` for every `k`.  In that form the bound needs no truncated subtraction and the zero
coefficients are free, their degree being `⊥`.

This degree is additive on products and subadditive on sums, so a determinant of a matrix of
entries of total degree at most one has total degree at most the size of the matrix.  Mathlib has
total degree only for `MvPolynomial`, where the iterated form is not directly available.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- **The total degree bound for an iterated polynomial.** -/
def TotalDegLE (p : (S[X])[X]) (d : ℕ) : Prop :=
  ∀ k, (p.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((d : ℕ) : WithBot ℕ)

/-- A sum of polynomials whose degrees are shifted-bounded is shifted-bounded. -/
theorem degree_sum_add_le {ι : Type*} (s : Finset ι) (f : ι → S[X]) (k c : ℕ)
    (h : ∀ i ∈ s, (f i).degree + ((k : ℕ) : WithBot ℕ) ≤ ((c : ℕ) : WithBot ℕ)) :
    (∑ i ∈ s, f i).degree + ((k : ℕ) : WithBot ℕ) ≤ ((c : ℕ) : WithBot ℕ) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Polynomial.degree_zero, WithBot.bot_add]
    exact bot_le
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    calc (f a + ∑ x ∈ s, f x).degree + ((k : ℕ) : WithBot ℕ)
        ≤ max ((f a).degree) ((∑ x ∈ s, f x).degree) + ((k : ℕ) : WithBot ℕ) := by
          gcongr
          exact Polynomial.degree_add_le _ _
      _ = max ((f a).degree + ((k : ℕ) : WithBot ℕ))
            ((∑ x ∈ s, f x).degree + ((k : ℕ) : WithBot ℕ)) := (max_add_add_right _ _ _).symm
      _ ≤ ((c : ℕ) : WithBot ℕ) := max_le (h a (Finset.mem_cons_self a s))
          (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem totalDegLE_zero (d : ℕ) : TotalDegLE (0 : (S[X])[X]) d := by
  intro k
  rw [Polynomial.coeff_zero, Polynomial.degree_zero, WithBot.bot_add]
  exact bot_le

theorem totalDegLE_one : TotalDegLE (1 : (S[X])[X]) 0 := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Polynomial.coeff_one_zero, Nat.cast_zero, add_zero]
    exact le_trans Polynomial.degree_one_le (by exact_mod_cast le_refl 0)
  · rw [Polynomial.coeff_one, if_neg (by omega), Polynomial.degree_zero, WithBot.bot_add]
    exact bot_le

theorem TotalDegLE.mono {p : (S[X])[X]} {d e : ℕ} (h : TotalDegLE p d) (hde : d ≤ e) :
    TotalDegLE p e := fun k => le_trans (h k) (by exact_mod_cast hde)

theorem TotalDegLE.add {p q : (S[X])[X]} {d : ℕ} (hp : TotalDegLE p d) (hq : TotalDegLE q d) :
    TotalDegLE (p + q) d := by
  intro k
  rw [Polynomial.coeff_add]
  calc (p.coeff k + q.coeff k).degree + ((k : ℕ) : WithBot ℕ)
      ≤ max ((p.coeff k).degree) ((q.coeff k).degree) + ((k : ℕ) : WithBot ℕ) := by
        gcongr
        exact Polynomial.degree_add_le _ _
    _ = max ((p.coeff k).degree + ((k : ℕ) : WithBot ℕ))
          ((q.coeff k).degree + ((k : ℕ) : WithBot ℕ)) := (max_add_add_right _ _ _).symm
    _ ≤ ((d : ℕ) : WithBot ℕ) := max_le (hp k) (hq k)

theorem TotalDegLE.neg {p : (S[X])[X]} {d : ℕ} (hp : TotalDegLE p d) : TotalDegLE (-p) d := by
  intro k
  rw [Polynomial.coeff_neg, Polynomial.degree_neg]
  exact hp k

theorem TotalDegLE.mul {p q : (S[X])[X]} {d e : ℕ} (hp : TotalDegLE p d) (hq : TotalDegLE q e) :
    TotalDegLE (p * q) (d + e) := by
  classical
  intro k
  rw [Polynomial.coeff_mul]
  refine degree_sum_add_le _ _ k (d + e) ?_
  rintro ⟨i, j⟩ hij
  have hk : i + j = k := Finset.mem_antidiagonal.1 hij
  calc (p.coeff (i, j).1 * q.coeff (i, j).2).degree + ((k : ℕ) : WithBot ℕ)
      ≤ (p.coeff i).degree + (q.coeff j).degree + ((k : ℕ) : WithBot ℕ) := by
        gcongr
        exact Polynomial.degree_mul_le _ _
    _ = (p.coeff i).degree + (q.coeff j).degree + ((k : ℕ) : WithBot ℕ) := rfl
    _
      = ((p.coeff i).degree + ((i : ℕ) : WithBot ℕ))
          + ((q.coeff j).degree + ((j : ℕ) : WithBot ℕ)) := by
        rw [← hk, Nat.cast_add]
        abel
    _ ≤ ((d : ℕ) : WithBot ℕ) + ((e : ℕ) : WithBot ℕ) := add_le_add (hp i) (hq j)
    _ = (((d + e : ℕ) : ℕ) : WithBot ℕ) := (Nat.cast_add d e).symm

theorem TotalDegLE.sum {ι : Type*} (s : Finset ι) (f : ι → (S[X])[X]) (d : ℕ)
    (h : ∀ i ∈ s, TotalDegLE (f i) d) : TotalDegLE (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    exact totalDegLE_zero d
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem TotalDegLE.prod {ι : Type*} (s : Finset ι) (f : ι → (S[X])[X]) (d : ℕ)
    (h : ∀ i ∈ s, TotalDegLE (f i) d) : TotalDegLE (∏ i ∈ s, f i) (s.card * d) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, zero_mul]
    exact totalDegLE_one
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.card_cons, add_mul, one_mul, add_comm ((s.card) * d) d]
    exact (h a (Finset.mem_cons_self a s)).mul
      (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- **A determinant of entries of bounded total degree.** -/
theorem TotalDegLE.det {N : ℕ} (M : Matrix (Fin N) (Fin N) ((S[X])[X])) {d : ℕ}
    (h : ∀ i j, TotalDegLE (M i j) d) : TotalDegLE M.det (N * d) := by
  classical
  rw [Matrix.det_apply']
  refine TotalDegLE.sum _ _ _ fun σ _ => ?_
  have hprod : TotalDegLE (∏ i, M (σ i) i) (N * d) := by
    have := TotalDegLE.prod (Finset.univ : Finset (Fin N)) (fun i => M (σ i) i) d
      (fun i _ => h (σ i) i)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hσ]
    simpa using hprod
  · rw [hσ]
    have hne : ((((-1 : ℤˣ) : ℤ) : (S[X])[X])) * (∏ i, M (σ i) i)
        = -(∏ i, M (σ i) i) := by
      push_cast
      ring
    rw [hne]
    exact hprod.neg


/-- **A total degree bound bounds the degree in the outer variable.** -/
theorem TotalDegLE.natDegree_le {p : (S[X])[X]} {d : ℕ} (h : TotalDegLE p d) :
    p.natDegree ≤ d := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_
  by_contra hne
  have hdeg : (0 : WithBot ℕ) ≤ (p.coeff k).degree := Polynomial.zero_le_degree_iff.2 hne
  have hle : ((k : ℕ) : WithBot ℕ) ≤ ((d : ℕ) : WithBot ℕ) :=
    calc ((k : ℕ) : WithBot ℕ) = 0 + ((k : ℕ) : WithBot ℕ) := (zero_add _).symm
      _ ≤ (p.coeff k).degree + ((k : ℕ) : WithBot ℕ) := by gcongr
      _ ≤ ((d : ℕ) : WithBot ℕ) := h k
  have : k ≤ d := by exact_mod_cast hle
  omega

end GaloisForLFunctions.HTGeometry
