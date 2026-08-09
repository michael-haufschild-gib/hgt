import GaloisForLFunctions.HTGeometry.AnticommutingInvolutionCarrier
import GaloisForLFunctions.HTGeometry.AnticommutingPauliObserverRankDominance
import Mathlib.Analysis.Matrix.Normed

/-!
# The refocusing carrier of a pairwise anticommuting Pauli family

The matrix of a Pauli word is a Hermitian involution, and two Pauli words whose symplectic inner
product is one have anticommuting matrices.  A real combination of a pairwise anticommuting family
therefore squares to the sum of the squared coefficients, and the unitary it generates is an exact
cosine–sine pair whose angle is the Euclidean length of the coefficients.

Every sphere of radius in `2πℕ` is consequently an exact identity-return set: the carrier refocuses
exactly, with angular dimension one less than the family size and radial recurrence rank one.
-/

open scoped BigOperators

noncomputable section

namespace Quantum

open NQubitPauliOperator Matrix

variable {n : ℕ}

/-- A Pauli word carries the phase-free group element with the same matrix. -/
theorem toMatrix_phaseFree (p : NQubitPauliOperator n) :
    (⟨0, p⟩ : NQubitPauliGroupElement n).toMatrix = p.toMatrix := by
  rw [NQubitPauliGroupElement.toMatrix]
  simp

/-- **A Pauli word is an involution.** -/
theorem toMatrix_mul_self (p : NQubitPauliOperator n) :
    p.toMatrix * p.toMatrix = 1 := by
  have hinv : (⟨0, p⟩ : NQubitPauliGroupElement n)⁻¹ = ⟨0, p⟩ := by
    ext <;> simp [NQubitPauliGroupElement.inv_eq, NQubitPauliGroupElement.inv]
  have hgroup : (⟨0, p⟩ : NQubitPauliGroupElement n) * ⟨0, p⟩ = 1 := by
    nth_rewrite 2 [← hinv]
    exact NQubitPauliGroupElement.mul_right_inv _
  have h := congrArg NQubitPauliGroupElement.toMatrix hgroup
  rwa [NQubitPauliGroupElement.toMatrix_mul, NQubitPauliGroupElement.toMatrix_one,
    toMatrix_phaseFree] at h

/-- **Symplectically paired Pauli words have anticommuting matrices.** -/
theorem toMatrix_add_toMatrix_swap_eq_zero (p q : NQubitPauliOperator n)
    (h : symplecticInner p q = 1) :
    p.toMatrix * q.toMatrix + q.toMatrix * p.toMatrix = 0 := by
  have hanti : NQubitPauliGroupElement.Anticommute (⟨0, p⟩ : NQubitPauliGroupElement n) ⟨0, q⟩ :=
    (anticommutes_iff_symplectic_inner_one (⟨0, p⟩ : NQubitPauliGroupElement n) ⟨0, q⟩).mpr h
  have hmat := congrArg NQubitPauliGroupElement.toMatrix hanti
  rw [NQubitPauliGroupElement.toMatrix_mul, NQubitPauliGroupElement.toMatrix_mul,
    NQubitPauliGroupElement.toMatrix_mul, NQubitPauliGroupElement.minusOne_toMatrix,
    toMatrix_phaseFree, toMatrix_phaseFree] at hmat
  rw [hmat]
  simp

/-- **A Pauli word is Hermitian.**  It is unitary and an involution, so its adjoint is itself. -/
theorem star_toMatrix (p : NQubitPauliOperator n) :
    star p.toMatrix = p.toMatrix := by
  have hu : p.toMatrix ∈ Matrix.unitaryGroup (NQubitBasis n) ℂ := toMatrix_mem_unitaryGroup p
  have hstar : star p.toMatrix * p.toMatrix = 1 := hu.1
  calc star p.toMatrix = star p.toMatrix * (p.toMatrix * p.toMatrix) := by
        rw [toMatrix_mul_self, mul_one]
    _ = (star p.toMatrix * p.toMatrix) * p.toMatrix := by rw [mul_assoc]
    _ = p.toMatrix := by rw [hstar, one_mul]

/-- **The transverse codimension of an anticommuting carrier is at least the observer rank.**
This is the subtraction form of the dominance inequality. -/
theorem observerRank_le_pauliWeightCount_sub_card (A : Finset (NQubitPauliOperator n)) (q : ℕ)
    (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hanti : ∀ p ∈ A, ∀ r ∈ A, p ≠ r → symplecticInner p r = 1) :
    productInputObserverRank n q ≤ nonidentityPauliWeightCount n q - A.card := by
  have h := pairwiseAnticommutingPauli_card_add_observerRank_le_pauliWeightCount A q hn hq hanti
  omega

/-- The Hermitian carrier of a real coefficient vector on a Pauli family. -/
def pauliCarrier (A : Finset (NQubitPauliOperator n)) (a : NQubitPauliOperator n → ℝ) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  HTGeometry.anticommutingCombination A (fun p => p.toMatrix) a

/-- **The carrier squares to the squared Euclidean length.**  This is the exact refocusing
identity of a pairwise anticommuting Pauli family. -/
theorem pauliCarrier_mul_self (A : Finset (NQubitPauliOperator n))
    (a : NQubitPauliOperator n → ℝ)
    (hanti : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → symplecticInner p q = 1) :
    pauliCarrier A a * pauliCarrier A a
      = (((∑ p ∈ A, a p ^ 2 : ℝ) : ℂ)) • (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) :=
  HTGeometry.anticommutingCombination_mul_self A (fun p => p.toMatrix) a
    (fun p _ => toMatrix_mul_self p)
    (fun p hp q hq hpq => toMatrix_add_toMatrix_swap_eq_zero p q (hanti p hp q hq hpq))

open scoped Matrix.Norms.Operator in
/-- **The carrier generates an exact cosine–sine pair.**  The unitary of a pairwise anticommuting
Pauli carrier is `cos` on the identity and `-i sinc` on the carrier, with the Euclidean length of
the coefficients as angle. -/
theorem exp_neg_I_smul_pauliCarrier (A : Finset (NQubitPauliOperator n))
    (a : NQubitPauliOperator n → ℝ)
    (hanti : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → symplecticInner p q = 1) :
    NormedSpace.exp ((-Complex.I) • pauliCarrier A a)
      = ((Real.cos (Real.sqrt (∑ p ∈ A, a p ^ 2)) : ℝ) : ℂ) •
          (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ)
        - (Complex.I * ((Real.sinc (Real.sqrt (∑ p ∈ A, a p ^ 2)) : ℝ) : ℂ)) • pauliCarrier A a :=
  HTGeometry.exp_neg_I_smul_anticommutingCombination A (fun p => p.toMatrix) a
    (fun p _ => toMatrix_mul_self p)
    (fun p hp q hq hpq => toMatrix_add_toMatrix_swap_eq_zero p q (hanti p hp q hq hpq))

open scoped Matrix.Norms.Operator in
/-- **Every sphere of radius in `2πℕ` is an exact identity-return set.** -/
theorem exp_neg_I_smul_pauliCarrier_eq_one (A : Finset (NQubitPauliOperator n))
    (a : NQubitPauliOperator n → ℝ)
    (hanti : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → symplecticInner p q = 1)
    (k : ℕ) (hk : Real.sqrt (∑ p ∈ A, a p ^ 2) = 2 * Real.pi * k) :
    NormedSpace.exp ((-Complex.I) • pauliCarrier A a)
      = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  rw [exp_neg_I_smul_pauliCarrier A a hanti, hk]
  have hcos : Real.cos (2 * Real.pi * k) = 1 := by
    have : (2 : ℝ) * Real.pi * k = (k : ℤ) * (2 * Real.pi) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hzero : pauliCarrier A a = 0 := by
      have hsum : (∑ p ∈ A, a p ^ 2) = 0 := by
        have hnn : (0 : ℝ) ≤ ∑ p ∈ A, a p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
        have h0 : Real.sqrt (∑ p ∈ A, a p ^ 2) = 0 := by rw [hk]; simp
        exact (Real.sqrt_eq_zero hnn).mp h0
      have hcoef : ∀ p ∈ A, a p = 0 := by
        intro p hp
        have := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => sq_nonneg (a q)).mp hsum p hp
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      rw [pauliCarrier, HTGeometry.anticommutingCombination]
      exact Finset.sum_eq_zero fun p hp => by rw [hcoef p hp]; simp
    rw [hzero, hcos]
    simp
  · have hsin : Real.sinc (2 * Real.pi * k) = 0 := by
      have hne : (2 : ℝ) * Real.pi * k ≠ 0 := by
        have hpi := Real.pi_pos
        have hkr : (0 : ℝ) < k := by exact_mod_cast hkpos
        positivity
      rw [Real.sinc_of_ne_zero hne]
      have : (2 : ℝ) * Real.pi * k = ((2 * k : ℕ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, Real.sin_nat_mul_pi]
      simp
    rw [hcos, hsin]
    simp

end Quantum

end
