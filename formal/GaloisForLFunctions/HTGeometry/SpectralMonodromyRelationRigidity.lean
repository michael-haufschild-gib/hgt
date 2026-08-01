import GaloisForLFunctions.HTGeometry.CenteredGenericField

/-!
# Spectral monodromy relation rigidity

A linear relation among distinct labelled roots that survives every permutation has constant
coefficients.  For centered roots, these are exactly the scalar multiples of the trace relation.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial
open scoped BigOperators

/-- Swapping two coefficient labels changes a weighted sum by its exact two-point defect. -/
theorem weightedSum_swap_sub
    {ι L : Type*} [Fintype ι] [DecidableEq ι] [CommRing L]
    (a b : ι) (c x : ι → L) :
    (∑ i, c ((Equiv.swap a b) i) * x i) - (∑ i, c i * x i) =
      (c b - c a) * x a + (c a - c b) * x b := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, (c ((Equiv.swap a b) i) * x i - c i * x i)) =
        ∑ i, if i = a then (c b - c a) * x a
          else if i = b then (c a - c b) * x b else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Equiv.swap_apply_def]
      split_ifs with hia hib
      · subst i
        ring
      · subst i
        ring
      · ring
    _ = ∑ i, ((if i = a then (c b - c a) * x a else 0) +
          (if i = b then (c a - c b) * x b else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hia hib <;> simp_all
    _ = (c b - c a) * x a + (c a - c b) * x b := by
      rw [Finset.sum_add_distrib]
      simp

/-- If a constant-coefficient relation among distinct labels survives every permutation, then all
coefficients coincide.  This is the algebraic rigidity used after full symmetric monodromy. -/
theorem coefficients_eq_of_all_permuted_relations
    {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Field L] [Algebra K L]
    (c : ι → K) (x : ι → L) (hinj : Function.Injective x)
    (h : ∀ e : Equiv.Perm ι, ∑ i, algebraMap K L (c i) * x (e i) = 0) :
    ∀ a b, c a = c b := by
  intro a b
  by_contra hab
  have h0 := h (1 : Equiv.Perm ι)
  have hs := h (Equiv.swap a b)
  have hreindex :
      (∑ i, algebraMap K L (c i) * x ((Equiv.swap a b) i)) =
        ∑ i, algebraMap K L (c ((Equiv.swap a b) i)) * x i := by
    symm
    simpa [mul_comm] using
      (Equiv.sum_comp (Equiv.swap a b)
        (fun i => algebraMap K L (c i) * x ((Equiv.swap a b) i)))
  rw [hreindex] at hs
  have hd :
      (∑ i, algebraMap K L (c ((Equiv.swap a b) i)) * x i) -
          (∑ i, algebraMap K L (c i) * x i) = 0 := by
    rw [hs]
    simpa using h0
  rw [weightedSum_swap_sub a b (fun i => algebraMap K L (c i)) x] at hd
  have hprod :
      (algebraMap K L (c b) - algebraMap K L (c a)) * (x a - x b) = 0 := by
    linear_combination hd
  rcases mul_eq_zero.mp hprod with hc | hx
  · exact hab ((algebraMap K L).injective (sub_eq_zero.mp hc)).symm
  · exact (fun hidx => hab (congrArg c hidx)) (hinj (sub_eq_zero.mp hx))

/-- A relation among the centered generic roots has equal coefficients. -/
theorem centeredRoot_coefficients_constant
    {K : Type*} [Field K] {d : ℕ} (c : Fin d → K)
    (h : ∑ i, algebraMap K (SymmetricRationalField K d) (c i) * centeredRoot K d i = 0) :
    ∀ a b, c a = c b := by
  apply coefficients_eq_of_all_permuted_relations c (centeredRoot K d) centeredRoot_injective
  intro e
  have he := congrArg (fun z : SymmetricRationalField K d => e • z) h
  simp only [Finset.smul_sum, smul_mul', smul_algebraMap, smul_centeredRoot, smul_zero] at he
  exact he

/-- For a nonempty centered generic spectrum, the only constant-coefficient linear relations are
the scalar multiples of the trace relation. -/
theorem centeredRoot_linearRelation_iff_coefficients_constant
    {K : Type*} [Field K] [CharZero K] {d : ℕ} (hd : d ≠ 0) (c : Fin d → K) :
    (∑ i, algebraMap K (SymmetricRationalField K d) (c i) * centeredRoot K d i = 0) ↔
      ∀ a b, c a = c b := by
  constructor
  · exact centeredRoot_coefficients_constant c
  · intro hc
    let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have heq : c = fun _ => c i0 := by
      funext i
      exact hc i i0
    rw [heq]
    rw [← Finset.mul_sum]
    rw [sum_centeredRoot hd, mul_zero]

end GaloisForLFunctions.HTGeometry
