import GaloisForLFunctions.HTGeometry.FreeGradedCommutativeAlgebra
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Independence of the weight components

The weight action realises the grading of a free graded-commutative algebra as a family of algebra
maps.  Over an infinite field the action separates weights: a vanishing sum of homogeneous elements
of distinct weights has all its terms zero.  The mechanism is Vandermonde — the weight action
evaluated at enough distinct parameters gives an invertible linear system.

Together with the spanning statement this makes the weight decomposition direct, so the homogeneous
components of an element are well defined.

* `eq_zero_of_matrix_smul_eq_zero` : a module-valued vector killed by an invertible matrix is zero.
* `eq_zero_of_forall_sum_pow_smul_eq_zero` : a power sum vanishing identically has zero coefficients.
* `deningerGCAHomogeneous_eq_zero_of_sum_eq_zero` : homogeneous elements of distinct weights are
  independent.
* `deningerGCAHomogeneous_ext` : the homogeneous components of an element are unique.
-/

namespace HTGeometry

section Independence

/-- **A vector killed by an invertible matrix is zero.**  The inverse matrix reconstructs each
coordinate from the vanishing combinations. -/
theorem eq_zero_of_matrix_smul_eq_zero {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    {n : Type*} [Fintype n] [DecidableEq n] (V : Matrix n n k) (hV : IsUnit V.det)
    (v : n → M) (h : ∀ j, ∑ i, V j i • v i = 0) (l : n) : v l = 0 := by
  have key : (∑ j, V⁻¹ l j • ∑ i, V j i • v i) = v l := by
    have e1 : ∀ j : n, V⁻¹ l j • (∑ i, V j i • v i) = ∑ i, (V⁻¹ l j * V j i) • v i := by
      intro j
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_comm]
    have e2 : ∀ i : n, ∑ j, (V⁻¹ l j * V j i) • v i = ((V⁻¹ * V) l i) • v i := by
      intro i
      rw [← Finset.sum_smul, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun i _ => e2 i, Matrix.nonsing_inv_mul V hV]
    simp [Matrix.one_apply]
  rw [← key]
  simp [h]

/-- **A power sum vanishing at every parameter has zero coefficients.**  Over an infinite field the
Vandermonde matrix on enough distinct parameters is invertible. -/
theorem eq_zero_of_forall_sum_pow_smul_eq_zero {k M : Type*} [Field k] [Infinite k]
    [AddCommGroup M] [Module k M] {m : ℕ} (v : ℕ → M)
    (h : ∀ t : k, ∑ i ∈ Finset.range m, (t ^ i) • v i = 0) (i : ℕ) (hi : i < m) : v i = 0 := by
  classical
  set f : Fin m → k := fun j => Infinite.natEmbedding k (j : ℕ) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    exact Fin.val_injective ((Infinite.natEmbedding k).injective hab)
  have hdet : IsUnit (Matrix.vandermonde f).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hinj)
  have hsum : ∀ j : Fin m, ∑ l : Fin m, (Matrix.vandermonde f) j l • v (l : ℕ) = 0 := by
    intro j
    have hj := h (f j)
    rw [← Fin.sum_univ_eq_sum_range (fun i => (f j ^ i) • v i) m] at hj
    exact hj
  exact eq_zero_of_matrix_smul_eq_zero (Matrix.vandermonde f) hdet
    (fun l : Fin m => v (l : ℕ)) hsum ⟨i, hi⟩

variable {k : Type*} [Field k] {G : Type*} {deg : G → ℕ}

theorem deningerGCAHomogeneous_neg {n : ℕ} {z : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) : DeningerGCAHomogeneous k deg n (-z) := by
  intro t
  rw [map_neg, hz t, smul_neg]

theorem deningerGCAHomogeneous_sub {n : ℕ} {z w : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) (hw : DeningerGCAHomogeneous k deg n w) :
    DeningerGCAHomogeneous k deg n (z - w) := by
  rw [sub_eq_add_neg]
  exact deningerGCAHomogeneous_add hz (deningerGCAHomogeneous_neg hw)

/-- **Homogeneous elements of distinct weights are independent.**  Applying the weight action to a
vanishing sum turns it into a power sum in the parameter, which vanishes identically only if every
term does.  With the spanning statement this makes the weight decomposition direct. -/
theorem deningerGCAHomogeneous_eq_zero_of_sum_eq_zero [Infinite k] {m : ℕ}
    (z : ℕ → DeningerFreeGCA k G deg) (hz : ∀ i, DeningerGCAHomogeneous k deg i (z i))
    (h0 : ∑ i ∈ Finset.range m, z i = 0) (i : ℕ) (hi : i < m) : z i = 0 := by
  refine eq_zero_of_forall_sum_pow_smul_eq_zero (k := k) z (fun t => ?_) i hi
  have hw := congrArg (deningerGCAWeight k deg t) h0
  rw [map_zero, map_sum] at hw
  calc ∑ j ∈ Finset.range m, (t ^ j) • z j
      = ∑ j ∈ Finset.range m, deningerGCAWeight k deg t (z j) :=
        Finset.sum_congr rfl fun j _ => (hz j t).symm
    _ = 0 := hw

/-- **The homogeneous components of an element are unique.**  Two homogeneous decompositions of the
same element agree weight by weight, so the weight decomposition determines well-defined
projections. -/
theorem deningerGCAHomogeneous_ext [Infinite k] {m : ℕ}
    (z w : ℕ → DeningerFreeGCA k G deg) (hz : ∀ i, DeningerGCAHomogeneous k deg i (z i))
    (hw : ∀ i, DeningerGCAHomogeneous k deg i (w i))
    (h : ∑ i ∈ Finset.range m, z i = ∑ i ∈ Finset.range m, w i) (i : ℕ) (hi : i < m) :
    z i = w i := by
  have hsub : ∑ j ∈ Finset.range m, (z j - w j) = 0 := by
    rw [Finset.sum_sub_distrib, h, sub_self]
  have := deningerGCAHomogeneous_eq_zero_of_sum_eq_zero (fun j => z j - w j)
    (fun j => deningerGCAHomogeneous_sub (hz j) (hw j)) hsub i hi
  exact sub_eq_zero.1 this

end Independence

end HTGeometry
