import GaloisForLFunctions.HTGeometry.ProjectiveJetHorizon
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Finite-jet Page transition for reciprocal projective horizons

For a differential-generic scalar `x`, compare the finite raw packet
`x_m,...,x_N` with the reciprocal packet `(x⁻¹)⁽ⁿ⁾,...,(x⁻¹)⁽ᴺ⁾`.  The paper
proof linearizes reciprocal jets at `X(t)=exp(-t/2)`.  There the relevant
Jacobian minor is the negative shifted Pascal matrix

`(-choose (n+i) k)_(0 ≤ i,k < r)`.

This file verifies its determinant in every size and the exact natural-number
rank balance.  Together with the characteristic-zero Jacobian criterion, these
are the formal algebraic core of the finite-resolution horizon theorem: hidden
source transcendence decreases to zero at `N=m+n-1`, after which independent
compatibility relations increase from zero.

The order `N` is derivative resolution, not a time parameter.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- The consecutive shifted Pascal matrix with rows starting at `n`. -/
def shiftedPascalMatrix (n r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => (Nat.choose (n + i) j : ℤ)

/-- The upper-unitriangular column shift implementing Pascal recurrence. -/
def shiftedPascalStep (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => if i = j then 1 else if (i : ℕ) + 1 = j then 1 else 0

private lemma shiftedPascalStep_upperTriangular (r : ℕ) :
    (shiftedPascalStep r).BlockTriangular id := by
  intro i j h
  simp only [shiftedPascalStep]
  split_ifs with h₁ h₂
  · subst j
    exact (lt_irrefl _ h).elim
  · have hji : (j : ℕ) < i := by exact_mod_cast h
    omega
  · rfl

/-- The Pascal column step has determinant one. -/
theorem shiftedPascalStep_det (r : ℕ) : (shiftedPascalStep r).det = 1 := by
  rw [Matrix.det_of_upperTriangular (shiftedPascalStep_upperTriangular r)]
  simp [shiftedPascalStep]

/-- Increasing the row shift by one is an upper-unitriangular column operation. -/
theorem shiftedPascalMatrix_succ (n r : ℕ) :
    shiftedPascalMatrix (n + 1) r =
      shiftedPascalMatrix n r * shiftedPascalStep r := by
  classical
  ext i j
  simp only [Matrix.mul_apply, shiftedPascalMatrix, shiftedPascalStep,
    mul_ite, mul_one, mul_zero]
  by_cases hj : (j : ℕ) = 0
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro b _ hbj
      simp only [hbj, ↓reduceIte]
      have hbpos : 0 < (b : ℕ) + 1 := Nat.zero_lt_succ _
      simp [hj]
    · simp
  · let p : Fin r := ⟨(j : ℕ) - 1, by omega⟩
    have hpj : (p : ℕ) + 1 = j := by
      dsimp [p]
      omega
    have hpne : p ≠ j := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j)
      (fun x => if x = j then ((Nat.choose (n + i) x : ℤ))
        else if (x : ℕ) + 1 = j then (Nat.choose (n + i) x : ℤ) else 0)]
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single p]
    · simp only [hpne, hpj, ↓reduceIte, add_comm]
      norm_cast
      rw [show (i : ℕ) + (n + 1) = (n + (i : ℕ)) + 1 by omega,
        show (j : ℕ) = (p : ℕ) + 1 by omega, Nat.choose_succ_succ']
      omega
    · intro b hb hbp
      have hbj : b ≠ j := by simpa using hb
      simp only [hbj, ↓reduceIte]
      by_cases hsucc : (b : ℕ) + 1 = j
      · have hbp' : b = p := Fin.ext (by omega)
        exact (hbp hbp').elim
      · simp [hsucc]
    · simp [hpne]

private lemma shiftedPascalMatrix_zero_det (r : ℕ) :
    (shiftedPascalMatrix 0 r).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (shiftedPascalMatrix 0 r)]
  · simp [shiftedPascalMatrix]
  · intro i j h
    change i < j at h
    simp only [shiftedPascalMatrix]
    norm_cast
    exact Nat.choose_eq_zero_of_lt (by simpa using h)

/-- Every consecutive shifted Pascal window is unimodular. -/
theorem shiftedPascalMatrix_det (n r : ℕ) :
    (shiftedPascalMatrix n r).det = 1 := by
  induction n with
  | zero => exact shiftedPascalMatrix_zero_det r
  | succ n hn =>
      rw [shiftedPascalMatrix_succ, Matrix.det_mul,
        hn, shiftedPascalStep_det, one_mul]

/-- Exponentially weighted Pascal window.  This is the linearization block produced when a
transition Jacobian has scalar channel `exp(q t)`. -/
def exponentialPascalMatrix (q : ℤ) (n r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => (Nat.choose (n + i) j : ℤ) * q ^ (n + i - j)

/-- Weighted upper-unitriangular Pascal step. -/
def exponentialPascalStep (q : ℤ) (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => if i = j then q else if (i : ℕ) + 1 = j then 1 else 0

private lemma exponentialPascalStep_upperTriangular (q : ℤ) (r : ℕ) :
    (exponentialPascalStep q r).BlockTriangular id := by
  intro i j h
  simp only [exponentialPascalStep]
  split_ifs with h₁ h₂
  · subst j
    exact (lt_irrefl _ h).elim
  · have hji : (j : ℕ) < i := by exact_mod_cast h
    omega
  · rfl

/-- The determinant of the weighted Pascal step is `q^r`. -/
theorem exponentialPascalStep_det (q : ℤ) (r : ℕ) :
    (exponentialPascalStep q r).det = q ^ r := by
  rw [Matrix.det_of_upperTriangular (exponentialPascalStep_upperTriangular q r)]
  simp [exponentialPascalStep]

/-- Increasing the row shift of a weighted window applies one weighted Pascal step. -/
theorem exponentialPascalMatrix_succ (q : ℤ) (n r : ℕ) :
    exponentialPascalMatrix q (n + 1) r =
      exponentialPascalMatrix q n r * exponentialPascalStep q r := by
  classical
  ext i j
  simp only [Matrix.mul_apply, exponentialPascalMatrix, exponentialPascalStep,
    mul_ite, mul_one, mul_zero]
  by_cases hj : (j : ℕ) = 0
  · rw [Finset.sum_eq_single j]
    · simp only [hj, Nat.choose_zero_right, Nat.cast_one, one_mul, ↓reduceIte]
      simp only [Nat.sub_zero]
      rw [show n + 1 + (i : ℕ) = (n + (i : ℕ)) + 1 by omega, pow_succ]
    · intro b _ hbj
      simp only [hbj, ↓reduceIte]
      have hbpos : 0 < (b : ℕ) + 1 := Nat.zero_lt_succ _
      simp [hj]
    · simp
  · let p : Fin r := ⟨(j : ℕ) - 1, by omega⟩
    have hpj : (p : ℕ) + 1 = j := by
      dsimp [p]
      omega
    have hpne : p ≠ j := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ j)
      (fun x => if x = j then
          (Nat.choose (n + i) x : ℤ) * q ^ (n + i - x) * q
        else if (x : ℕ) + 1 = j then
          (Nat.choose (n + i) x : ℤ) * q ^ (n + i - x)
        else 0)]
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single p]
    · simp only [hpne, hpj, ↓reduceIte]
      have hrow : n + 1 + (i : ℕ) = (n + (i : ℕ)) + 1 := by omega
      rw [hrow, show (j : ℕ) = (p : ℕ) + 1 by omega, Nat.choose_succ_succ']
      push_cast
      rw [add_mul]
      apply congrArg₂ (fun a b : ℤ => a + b)
      · congr 2
      · by_cases hle : (p : ℕ) + 1 ≤ n + (i : ℕ)
        · rw [show n + (i : ℕ) - (p : ℕ) =
              (n + (i : ℕ) - ((p : ℕ) + 1)) + 1 by omega,
            pow_succ]
          ring
        · have hz : Nat.choose (n + (i : ℕ)) ((p : ℕ) + 1) = 0 :=
            Nat.choose_eq_zero_of_lt (by omega)
          simp [hz]
    · intro b hb hbp
      have hbj : b ≠ j := by simpa using hb
      simp only [hbj, ↓reduceIte]
      by_cases hsucc : (b : ℕ) + 1 = j
      · have hbp' : b = p := Fin.ext (by omega)
        exact (hbp hbp').elim
      · simp [hsucc]
    · simp [hpne]

private lemma exponentialPascalMatrix_zero_det (q : ℤ) (r : ℕ) :
    (exponentialPascalMatrix q 0 r).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (exponentialPascalMatrix q 0 r)]
  · simp [exponentialPascalMatrix]
  · intro i j h
    change i < j at h
    simp only [exponentialPascalMatrix]
    norm_cast
    simp [Nat.choose_eq_zero_of_lt (by simpa using h)]

/-- Exact determinant of every exponentially weighted Pascal window. -/
theorem exponentialPascalMatrix_det (q : ℤ) (n r : ℕ) :
    (exponentialPascalMatrix q n r).det = q ^ (r * n) := by
  induction n with
  | zero => simpa using exponentialPascalMatrix_zero_det q r
  | succ n hn =>
      rw [exponentialPascalMatrix_succ, Matrix.det_mul, hn,
        exponentialPascalStep_det, ← pow_add]
      congr 1

/-- Longitudinal block of the projective chart transition
`(p,u) ↦ (p⁻¹,u/p)` at `p(t)=exp(-t)`, `u(t)=0`. -/
def projectiveLongitudinalLinearizationMinor (n r : ℕ) :
    Matrix (Fin r) (Fin r) ℤ :=
  -(exponentialPascalMatrix 2 n r)

/-- The longitudinal projective block has determinant `(-1)^r 2^(rn)`. -/
theorem projectiveLongitudinalLinearizationMinor_det (n r : ℕ) :
    (projectiveLongitudinalLinearizationMinor n r).det =
      (-1 : ℤ) ^ r * 2 ^ (r * n) := by
  simp [projectiveLongitudinalLinearizationMinor, Matrix.det_neg,
    exponentialPascalMatrix_det]

/-- The longitudinal projective channel is nonsingular at every depth and window size. -/
theorem projectiveLongitudinalLinearizationMinor_det_ne_zero (n r : ℕ) :
    (projectiveLongitudinalLinearizationMinor n r).det ≠ 0 := by
  rw [projectiveLongitudinalLinearizationMinor_det]
  exact mul_ne_zero (pow_ne_zero r (by norm_num)) (pow_ne_zero (r * n) (by norm_num))

/-- The reciprocal-jet linearization minor at `X(t)=exp(-t/2)`.

Writing exponential Taylor coordinates, `d(X⁻¹)=-X⁻² dX`; at the chosen
formal jet, `X⁻²=exp(t)`, so the coefficient matrix is exactly negative
shifted Pascal. -/
def reciprocalJetLinearizationMinor (n r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  -(shiftedPascalMatrix n r)

/-- Exact determinant of the reciprocal-jet Jacobian minor. -/
theorem reciprocalJetLinearizationMinor_det (n r : ℕ) :
    (reciprocalJetLinearizationMinor n r).det = (-1 : ℤ) ^ r := by
  simp [reciprocalJetLinearizationMinor, Matrix.det_neg, shiftedPascalMatrix_det]

/-- Every finite reciprocal-jet linearization window detects all low-mode directions. -/
theorem reciprocalJetLinearizationMinor_det_ne_zero (n r : ℕ) :
    (reciprocalJetLinearizationMinor n r).det ≠ 0 := by
  rw [reciprocalJetLinearizationMinor_det]
  exact pow_ne_zero r (by norm_num)

/-- Number of scalar jet coordinates through resolution `N`. -/
def finiteJetAmbientCount (N : ℕ) : ℕ := N + 1

/-- Number of displayed coordinates in one depth-`d` packet through order `N`. -/
def finiteHorizonObservableCount (N d : ℕ) : ℕ := N + 1 - d

/-- Transcendence degrees not yet visible to a depth pair `(m,n)` at order `N`. -/
def finiteHorizonHiddenCount (m n N : ℕ) : ℕ := m + n - (N + 1)

/-- Independent compatibility relations after the pair has saturated the ambient jet. -/
def finiteHorizonRelationCount (m n N : ℕ) : ℕ := N + 1 - (m + n)

/-- Rank supplied by the raw packet plus a maximal reciprocal Pascal minor. -/
def finiteHorizonObservationRank (m n N : ℕ) : ℕ :=
  finiteHorizonObservableCount N m + min m (finiteHorizonObservableCount N n)

/-- The Jacobian rank is the smaller of ambient dimension and observable count. -/
theorem finiteHorizonObservationRank_eq_min {m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteHorizonObservationRank m n N =
      min (finiteJetAmbientCount N)
        (finiteHorizonObservableCount N m + finiteHorizonObservableCount N n) := by
  simp only [finiteHorizonObservationRank, finiteHorizonObservableCount,
    finiteJetAmbientCount]
  omega

/-- The rank deficit is exactly the hidden-source count. -/
theorem finiteJetAmbientCount_sub_observationRank_eq_hidden {m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteJetAmbientCount N - finiteHorizonObservationRank m n N =
      finiteHorizonHiddenCount m n N := by
  simp only [finiteHorizonObservationRank, finiteHorizonObservableCount,
    finiteJetAmbientCount, finiteHorizonHiddenCount]
  omega

/-- The observable-count excess is exactly the compatibility-relation count. -/
theorem finiteHorizonObservableCount_sub_rank_eq_relations {m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteHorizonObservableCount N m + finiteHorizonObservableCount N n -
        finiteHorizonObservationRank m n N =
      finiteHorizonRelationCount m n N := by
  simp only [finiteHorizonObservationRank, finiteHorizonObservableCount,
    finiteHorizonRelationCount]
  omega

/-- Static Page balance: displayed data plus hidden freedom equals ambient data plus relations. -/
theorem finiteHorizon_page_balance {m n N : ℕ}
    (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteHorizonObservableCount N m + finiteHorizonObservableCount N n +
        finiteHorizonHiddenCount m n N =
      finiteJetAmbientCount N + finiteHorizonRelationCount m n N := by
  simp only [finiteHorizonObservableCount, finiteHorizonHiddenCount,
    finiteJetAmbientCount, finiteHorizonRelationCount]
  omega

/-- Hidden transcendence vanishes at the critical resolution `N=m+n-1`. -/
theorem finiteHorizonHiddenCount_at_page (m n : ℕ) :
    finiteHorizonHiddenCount m n (m + n - 1) = 0 := by
  simp only [finiteHorizonHiddenCount]
  omega

/-- No compatibility relation appears before the critical resolution. -/
theorem finiteHorizonRelationCount_at_page (m n : ℕ) (h : 0 < m + n) :
    finiteHorizonRelationCount m n (m + n - 1) = 0 := by
  simp only [finiteHorizonRelationCount]
  omega

end GaloisForLFunctions.HTGeometry
