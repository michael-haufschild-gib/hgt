import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.LinearCombination

/-!
# Binomial coefficients at distinct nodes form a nonsingular matrix

The binomial coefficient `binom(m,k)` is the falling factorial of `m` of length `k` divided by
`k!`, and the falling factorials are monic of strictly increasing degree.  So the matrix of
binomial coefficients at a family of nodes factors as a Vandermonde matrix in those nodes times a
triangular change of basis with the reciprocal factorials on the diagonal.

At distinct nodes the Vandermonde factor is nonsingular, hence so is the binomial matrix: a linear
combination of the binomials vanishing at as many distinct nodes as there are terms is trivial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-! ## The falling factorial polynomial -/

/-- The falling factorial of length `k`, as a polynomial in the node. -/
def fallingFactorialPoly (K : Type*) [Field K] (k : ℕ) : Polynomial K :=
  ∏ t ∈ Finset.range k, (Polynomial.X - Polynomial.C (t : K))

omit [CharZero K] in
theorem fallingFactorialPoly_monic (k : ℕ) : (fallingFactorialPoly K k).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

omit [CharZero K] in
@[simp]
theorem fallingFactorialPoly_natDegree (k : ℕ) :
    (fallingFactorialPoly K k).natDegree = k := by
  rw [fallingFactorialPoly,
    Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C (R := K) _]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

/-- **The falling factorial evaluates to the binomial coefficient times the factorial.** -/
theorem eval_fallingFactorialPoly (m k : ℕ) :
    (fallingFactorialPoly K k).eval (m : K) =
      (Nat.choose m k : K) * (Nat.factorial k : K) := by
  induction k with
  | zero => simp [fallingFactorialPoly]
  | succ k ih =>
      have hsplit : fallingFactorialPoly K (k + 1) =
          fallingFactorialPoly K k * (Polynomial.X - Polynomial.C ((k : ℕ) : K)) := by
        rw [fallingFactorialPoly, fallingFactorialPoly, Finset.prod_range_succ]
      rw [hsplit, Polynomial.eval_mul, ih, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      rcases le_or_gt k m with hkm | hkm
      · have hnat : (Nat.choose m (k + 1) : K) * ((k : K) + 1) =
            (Nat.choose m k : K) * ((m : K) - (k : K)) := by
          have h := Nat.choose_succ_right_eq m k
          have h' : ((Nat.choose m (k + 1) * (k + 1) : ℕ) : K) =
              ((Nat.choose m k * (m - k) : ℕ) : K) := by rw [h]
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hkm] at h'
          push_cast at h' ⊢
          exact h'
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        rw [show (Nat.choose m (k + 1) : K) * (((k : K) + 1) * (Nat.factorial k : K)) =
            ((Nat.choose m (k + 1) : K) * ((k : K) + 1)) * (Nat.factorial k : K) from by ring,
          hnat]
        ring
      · have h1 : Nat.choose m k = 0 := Nat.choose_eq_zero_of_lt hkm
        have h2 : Nat.choose m (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [h1, h2]
        simp

/-! ## The binomial matrix and its triangular factor -/

/-- The matrix of binomial coefficients at a family of nodes. -/
def binomNodeMatrix (K : Type*) [Field K] {n : ℕ} (m : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i k => (Nat.choose (m i) (k : ℕ) : K)

/-- The change of basis from powers of the node to binomial coefficients. -/
def fallingCoeffMatrix (K : Type*) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k =>
    (fallingFactorialPoly K (k : ℕ)).coeff (j : ℕ) / (Nat.factorial (k : ℕ) : K)

/-- **The binomial matrix factors through the Vandermonde matrix of its nodes.** -/
theorem binomNodeMatrix_eq (m : Fin n → ℕ) :
    binomNodeMatrix K m =
      Matrix.vandermonde (fun i => ((m i : ℕ) : K)) * fallingCoeffMatrix K n := by
  ext i k
  rw [Matrix.mul_apply, binomNodeMatrix, Matrix.of_apply]
  have hfac : (Nat.factorial (k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hdeg : (fallingFactorialPoly K (k : ℕ)).natDegree < n := by
    rw [fallingFactorialPoly_natDegree]
    exact k.2
  have hev : (fallingFactorialPoly K (k : ℕ)).eval ((m i : ℕ) : K) =
      ∑ j : Fin n, (fallingFactorialPoly K (k : ℕ)).coeff (j : ℕ) * ((m i : ℕ) : K) ^ (j : ℕ) := by
    rw [Polynomial.eval_eq_sum_range' hdeg ((m i : ℕ) : K), ← Fin.sum_univ_eq_sum_range]
  have key : ∑ j : Fin n, Matrix.vandermonde (fun i => ((m i : ℕ) : K)) i j *
      fallingCoeffMatrix K n j k =
      (∑ j : Fin n, (fallingFactorialPoly K (k : ℕ)).coeff (j : ℕ) * ((m i : ℕ) : K) ^ (j : ℕ)) *
        ((Nat.factorial (k : ℕ) : K))⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vandermonde_apply, fallingCoeffMatrix, Matrix.of_apply, div_eq_mul_inv]
    ring
  rw [key, ← hev, eval_fallingFactorialPoly]
  field_simp

theorem det_fallingCoeffMatrix_ne_zero (n : ℕ) : (fallingCoeffMatrix K n).det ≠ 0 := by
  have htri : (fallingCoeffMatrix K n).BlockTriangular id := by
    intro j k hkj
    have hlt : (k : ℕ) < (j : ℕ) := hkj
    rw [fallingCoeffMatrix, Matrix.of_apply,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simp [hlt]), zero_div]
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
  rw [fallingCoeffMatrix, Matrix.of_apply]
  have hcoeff : (fallingFactorialPoly K (j : ℕ)).coeff (j : ℕ) = 1 := by
    have h := (fallingFactorialPoly_monic (K := K) (j : ℕ)).coeff_natDegree
    rwa [fallingFactorialPoly_natDegree] at h
  rw [hcoeff]
  exact one_div_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

/-- **The binomial matrix at distinct nodes is nonsingular.** -/
theorem det_binomNodeMatrix_ne_zero {m : Fin n → ℕ} (hm : Function.Injective m) :
    (binomNodeMatrix K m).det ≠ 0 := by
  rw [binomNodeMatrix_eq, Matrix.det_mul]
  refine mul_ne_zero ?_ (det_fallingCoeffMatrix_ne_zero n)
  refine Matrix.det_vandermonde_ne_zero_iff.2 ?_
  exact fun a b hab => hm (Nat.cast_injective hab)

/-- **A linear relation among the binomials holding at enough distinct nodes is trivial.**  This is
the statement that the binomial coefficients `binom(-,k)` for `k < n`, read as functions of the
node, are linearly independent on any `n` distinct nodes. -/
theorem eq_zero_of_binom_combination_eq_zero {m : Fin n → ℕ} (hm : Function.Injective m)
    {a : Fin n → K} (h : ∀ i : Fin n, ∑ k : Fin n, (Nat.choose (m i) (k : ℕ) : K) * a k = 0) :
    a = 0 := by
  refine Matrix.eq_zero_of_mulVec_eq_zero (det_binomNodeMatrix_ne_zero (K := K) hm) ?_
  funext i
  rw [Matrix.mulVec, dotProduct]
  simpa [binomNodeMatrix] using h i

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-! ## The alternating two-block binomial matrix

The reconstruction system pairs the jets of an observable with the jets of its reciprocal.  Under
the exponential specialisation the reciprocal jets alternate in sign, so the system matrix has one
plain binomial block and one alternating binomial block, read at the same nodes.
-/

/-- The two-block matrix with an alternating binomial block and a plain binomial block, read at a
family of even nodes and a family of odd nodes. -/
def alternatingBinomBlock (K : Type*) [Field K] {n : ℕ} (e o : Fin n → ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r =>
    Sum.elim
      (fun k : Fin n => (-1 : K) ^ (Sum.elim e o r + (k : ℕ)) *
        (Nat.choose (Sum.elim e o r) (k : ℕ) : K))
      (fun j : Fin n => (Nat.choose (Sum.elim e o r) (j : ℕ) : K))

/-- **The alternating two-block binomial matrix is nonsingular.**  Splitting the rows by the parity
of their node turns each half into a plain binomial system, which is nonsingular at distinct
nodes; the two halves then separate the alternating unknowns from the plain ones. -/
theorem det_alternatingBinomBlock_ne_zero {e o : Fin n → ℕ}
    (he : Function.Injective e) (ho : Function.Injective o)
    (hep : ∀ i, Even (e i)) (hop : ∀ i, Odd (o i)) :
    (alternatingBinomBlock K e o).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hrow : ∀ r : Fin n ⊕ Fin n,
      (∑ k : Fin n, (-1 : K) ^ (Sum.elim e o r + (k : ℕ)) *
          (Nat.choose (Sum.elim e o r) (k : ℕ) : K) * v (Sum.inl k)) +
        (∑ j : Fin n, (Nat.choose (Sum.elim e o r) (j : ℕ) : K) * v (Sum.inr j)) = 0 := by
    intro r
    have h := congrFun hv r
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at h
    simpa [alternatingBinomBlock] using h
  have hcomb : ∀ (m : ℕ) (s : K), s * s = 1 →
      (∑ k : Fin n, (-1 : K) ^ (m + (k : ℕ)) * (Nat.choose m (k : ℕ) : K) * v (Sum.inl k)) +
        (∑ j : Fin n, (Nat.choose m (j : ℕ) : K) * v (Sum.inr j)) = 0 →
      (-1 : K) ^ m = s →
      ∑ k : Fin n, (Nat.choose m (k : ℕ) : K) *
        (s * (-1 : K) ^ (k : ℕ) * v (Sum.inl k) + v (Sum.inr k)) = 0 := by
    intro m s _ h hs
    rw [← h]
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hs, pow_add]
    ring
  have heven : (fun k : Fin n => (-1 : K) ^ (k : ℕ) * v (Sum.inl k) + v (Sum.inr k)) = 0 := by
    refine eq_zero_of_binom_combination_eq_zero (K := K) he fun i => ?_
    have hs : (-1 : K) ^ (e i) = 1 := (hep i).neg_one_pow
    have h := hcomb (e i) 1 (by norm_num) (hrow (Sum.inl i)) hs
    simpa using h
  have hodd : (fun k : Fin n => -((-1 : K) ^ (k : ℕ) * v (Sum.inl k)) + v (Sum.inr k)) = 0 := by
    refine eq_zero_of_binom_combination_eq_zero (K := K) ho fun i => ?_
    have hs : (-1 : K) ^ (o i) = -1 := (hop i).neg_one_pow
    have h := hcomb (o i) (-1) (by norm_num) (hrow (Sum.inr i)) hs
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h
    ring
  refine hv0 ?_
  funext r
  have he' := congrFun heven
  have ho' := congrFun hodd
  cases r with
  | inl k =>
      have h1 := he' k
      have h2 := ho' k
      simp only [Pi.zero_apply] at h1 h2
      have hsub : (2 : K) * ((-1 : K) ^ (k : ℕ) * v (Sum.inl k)) = 0 := by
        linear_combination h1 - h2
      have : (-1 : K) ^ (k : ℕ) * v (Sum.inl k) = 0 := by
        rcases mul_eq_zero.1 hsub with h | h
        · exact absurd h two_ne_zero
        · exact h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (pow_ne_zero _ (by norm_num))
      · exact h
  | inr k =>
      have h1 := he' k
      have h2 := ho' k
      simp only [Pi.zero_apply] at h1 h2
      have hadd : (2 : K) * v (Sum.inr k) = 0 := by linear_combination h1 + h2
      rcases mul_eq_zero.1 hadd with h | h
      · exact absurd h two_ne_zero
      · exact h

end

end GaloisForLFunctions.HTGeometry
