import GaloisForLFunctions.HTGeometry.BalancedTernaryUniqueness
import GaloisForLFunctions.HTGeometry.EulerPrimeOrbitFourOrganLaw

/-!
# Cyclicity of the balanced ternary spectrum

The signed sums `∑_j 3^j εⱼ` with `εⱼ = ±1` are pairwise distinct, so a diagonal operator with
those eigenvalues has simple spectrum.  Against any vector with no vanishing coordinate its Krylov
family is therefore a square weighted Vandermonde family, hence linearly independent: the vector is
cyclic and the cyclicity determinant does not vanish.

This is the Vandermonde step of the explicit two-local witness `H₀ = ∑_j 3^j X_j`, whose `X`-basis
eigenvalues are exactly these signed sums and against which `|0⟩^⊗ⁿ` has constant nonzero overlap.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BalancedTernary

open Finset

/-- The balanced ternary value of a sign pattern. -/
def ternaryValue {n : ℕ} (ε : Fin n → Bool) : ℤ :=
  ∑ j : Fin n, 3 ^ (j : ℕ) * (if ε j then 1 else -1)

/-- The sign pattern read as a function on all of `ℕ`, extended by `1`. -/
private def extend {n : ℕ} (ε : Fin n → Bool) : ℕ → ℤ :=
  fun j => if h : j < n then (if ε ⟨j, h⟩ then 1 else -1) else 1

private theorem extend_sign {n : ℕ} (ε : Fin n → Bool) (j : ℕ) :
    extend ε j = 1 ∨ extend ε j = -1 := by
  unfold extend
  split_ifs <;> simp

private theorem sum_extend {n : ℕ} (ε : Fin n → Bool) :
    ∑ j ∈ range n, (3 : ℤ) ^ j * extend ε j = ternaryValue ε := by
  rw [ternaryValue, ← Fin.sum_univ_eq_sum_range (fun j => (3 : ℤ) ^ j * extend ε j) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold extend
  rw [dif_pos j.isLt]

/-- **The balanced ternary values are pairwise distinct.** -/
theorem injective_ternaryValue {n : ℕ} : Function.Injective (ternaryValue (n := n)) := by
  intro ε δ h
  have hsum : ∑ j ∈ range n, (3 : ℤ) ^ j * extend ε j
      = ∑ j ∈ range n, (3 : ℤ) ^ j * extend δ j := by
    rw [sum_extend, sum_extend, h]
  have hall := sum_pow_three_sign_injOn n (extend_sign ε) (extend_sign δ) hsum
  funext j
  have hj := hall (j : ℕ) j.isLt
  unfold extend at hj
  rw [dif_pos j.isLt, dif_pos j.isLt] at hj
  have hfin : (⟨(j : ℕ), j.isLt⟩ : Fin n) = j := Fin.eta j j.isLt
  rw [hfin] at hj
  rcases Bool.eq_false_or_eq_true (ε j) with hε | hε <;>
    rcases Bool.eq_false_or_eq_true (δ j) with hδ | hδ <;>
      simp [hε, hδ] at hj ⊢

/-- **Cyclicity of the balanced ternary spectrum.**  Against any weight with no vanishing
coordinate, the Krylov family of the diagonal operator with balanced ternary eigenvalues is
linearly independent. -/
theorem linearIndependent_krylov_ternaryValue {n : ℕ} (weight : (Fin n → Bool) → ℂ)
    (hweight : ∀ ε, weight ε ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (Fintype.card (Fin n → Bool)) =>
      finiteDiagonalKrylovVector (fun ε => ((ternaryValue ε : ℤ) : ℂ)) weight (k : ℕ)) := by
  refine finiteDiagonalKrylovVector_linearIndependent ?_ hweight
  intro ε δ h
  have h' : ((ternaryValue ε : ℤ) : ℂ) = ((ternaryValue δ : ℤ) : ℂ) := h
  exact injective_ternaryValue (by exact_mod_cast h')

end BalancedTernary

end GaloisForLFunctions.HTGeometry
