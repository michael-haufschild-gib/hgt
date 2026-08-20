/-
# Room beside a whole family of greedy truncations

A linear operator pencil is truncated coefficient by coefficient, so the block that corrects its
low power traces must sit beside *all* of the finitely many truncations at once.  Their carriers
span one finite-dimensional subspace, and in an infinite-dimensional space its orthogonal complement
still contains an orthonormal family of any prescribed size.  A block placed there annihilates every
truncated coefficient, hence the whole truncated pencil, in both orders.

Main results:
* `greedyFamilySupport` — the finite-dimensional carrier of a family of greedy truncations.
* `exists_orthonormal_beside_greedyFamily` — **an orthonormal family beside the whole family**.
* `pencilOperator_apply_eq_zero`, `inner_pencilOperator_eq_zero` — the truncated pencil is
  annihilated on both sides.
-/
import GaloisForLFunctions.HTGeometry.GreedySupportComplement
import GaloisForLFunctions.HTGeometry.OperatorDeterminantScaling

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The generators of the carrier of a whole family of greedy truncations. -/
def greedyFamilyGens {d : ℕ} (A : Fin d → (H →L[ℂ] H)) (n : ℕ) : Set H :=
  ⋃ j : Fin d,
    (((fun k => svVec (energyOp (A j)) k) '' ((Finset.range n : Finset ℕ) : Set ℕ)) ∪
      ((fun k => (A j) (svVec (energyOp (A j)) k)) '' ((Finset.range n : Finset ℕ) : Set ℕ)))

theorem finite_greedyFamilyGens {d : ℕ} (A : Fin d → (H →L[ℂ] H)) (n : ℕ) :
    (greedyFamilyGens A n).Finite := by
  refine Set.finite_iUnion fun j => ?_
  exact ((Finset.range n).finite_toSet.image _).union ((Finset.range n).finite_toSet.image _)

/-- The finite-dimensional carrier of a whole family of greedy truncations. -/
def greedyFamilySupport {d : ℕ} (A : Fin d → (H →L[ℂ] H)) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (greedyFamilyGens A n)

instance finiteDimensional_greedyFamilySupport {d : ℕ} (A : Fin d → (H →L[ℂ] H)) (n : ℕ) :
    FiniteDimensional ℂ (greedyFamilySupport A n) :=
  FiniteDimensional.span_of_finite ℂ (finite_greedyFamilyGens A n)

theorem greedySupport_le_greedyFamilySupport {d : ℕ} (A : Fin d → (H →L[ℂ] H)) (n : ℕ)
    (j : Fin d) : greedySupport (A j) n ≤ greedyFamilySupport A n := by
  refine Submodule.span_mono ?_
  intro x hx
  exact Set.mem_iUnion.mpr ⟨j, hx⟩

/-- **An orthonormal family of any size beside a whole family of greedy truncations.** -/
theorem exists_orthonormal_beside_greedyFamily (hH : ¬ FiniteDimensional ℂ H) {d : ℕ}
    (A : Fin d → (H →L[ℂ] H)) (n mm : ℕ) :
    ∃ e : Fin mm → H, Orthonormal ℂ e ∧
      (∀ (j : Fin d) (i : Fin mm), greedyTrunc (A j) n (e i) = 0) ∧
      (∀ (j : Fin d) (i : Fin mm) (x : H), ⟪e i, greedyTrunc (A j) n x⟫_ℂ = 0) := by
  obtain ⟨e, he, hmem⟩ :=
    exists_orthonormal_mem_orthogonal hH mm (greedyFamilySupport A n)
      (finiteDimensional_greedyFamilySupport A n)
  refine ⟨e, he, ?_, ?_⟩
  · intro j i
    exact greedyTrunc_apply_eq_zero_of_mem_orthogonal (A j) n
      (Submodule.orthogonal_le (greedySupport_le_greedyFamilySupport A n j) (hmem i))
  · intro j i x
    exact inner_greedyTrunc_eq_zero_of_mem_orthogonal (A j) n
      (Submodule.orthogonal_le (greedySupport_le_greedyFamilySupport A n j) (hmem i)) x

/-! ## The truncated pencil is annihilated on both sides -/

omit [CompleteSpace H] in
theorem pencilOperator_apply {d : ℕ} (B : Fin d → (H →L[ℂ] H)) (v : Fin d → ℂ) (x : H) :
    pencilOperator B v x = ∑ j, v j • (B j x) := by
  rw [pencilOperator, sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

omit [CompleteSpace H] in
theorem pencilOperator_apply_eq_zero {d : ℕ} {B : Fin d → (H →L[ℂ] H)} {y : H}
    (hy : ∀ j, B j y = 0) (v : Fin d → ℂ) : pencilOperator B v y = 0 := by
  rw [pencilOperator_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [hy j, smul_zero]

omit [CompleteSpace H] in
theorem inner_pencilOperator_eq_zero {d : ℕ} {B : Fin d → (H →L[ℂ] H)} {y : H}
    (hy : ∀ (j : Fin d) (x : H), ⟪y, B j x⟫_ℂ = 0) (v : Fin d → ℂ) (x : H) :
    ⟪y, pencilOperator B v x⟫_ℂ = 0 := by
  rw [pencilOperator_apply, inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_right, hy j x, mul_zero]

end

end GaloisForLFunctions.HTGeometry
