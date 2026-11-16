import GaloisForLFunctions.RepresentationLifting.ModularTrace
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The complete trace kernel of the dual numbers

For the dual-number algebra, He's cocenter decomposition
(arXiv:2611.16847, Lemma 2.4) is explicit in every characteristic.
Every finite-dimensional representation has trace `dimension * residue`.
The invisible part is exactly the square-zero direction, while the
span of idempotents is exactly the scalar line. This distinguishes
universal trace invisibility from the corpus's vanishing regular trace.
-/

namespace GaloisForLFunctions.RepresentationLifting
noncomputable section
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Scalar and infinitesimal coordinates of the dual-number algebra. -/
theorem dualNumber_scalar_nilpotent_split (x : DualNumber K) :
    x = x.fst • (1 : DualNumber K) + TrivSqZeroExt.inr x.snd := by
  ext <;> simp

/-- Every representation kills the infinitesimal direction after taking trace. -/
theorem dualNumber_representation_trace_inr
    (ρ : DualNumber K →ₐ[K] Matrix n n K) (b : K) :
    Matrix.trace (ρ (TrivSqZeroExt.inr b)) = 0 := by
  apply IsNilpotent.eq_zero
  apply Matrix.isNilpotent_trace_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero]

/-- The trace of an arbitrary representation sees only the scalar residue. -/
theorem dualNumber_representation_trace
    (ρ : DualNumber K →ₐ[K] Matrix n n K) (x : DualNumber K) :
    Matrix.trace (ρ x) = (Fintype.card n : K) * x.fst := by
  conv_lhs => rw [dualNumber_scalar_nilpotent_split x]
  rw [map_add, map_smul, map_one, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, dualNumber_representation_trace_inr, add_zero, smul_eq_mul, mul_comm]

/-- The one-dimensional residue representation detects every nonzero scalar part. -/
def dualNumberResidueMatrix : DualNumber K →ₐ[K] Matrix (Fin 1) (Fin 1) K :=
  (Matrix.scalarAlgHom (Fin 1) K).comp (TrivSqZeroExt.fstHom K K K)

/-- Universal trace invisibility is exactly vanishing residue, in every characteristic. -/
theorem dualNumber_all_traces_zero_iff (x : DualNumber K) :
    (∀ (d : ℕ) (ρ : DualNumber K →ₐ[K] Matrix (Fin d) (Fin d) K),
      Matrix.trace (ρ x) = 0) ↔ x.fst = 0 := by
  constructor
  · intro h
    have hz := h 1 dualNumberResidueMatrix
    simpa only [dualNumber_representation_trace, Fintype.card_fin,
      Nat.cast_one, one_mul] using hz
  · intro hx d ρ
    rw [dualNumber_representation_trace, hx, mul_zero]

/-- Two dual numbers have identical traces in all representations exactly when
their residues agree; arbitrary nilpotent extension data remain invisible. -/
theorem dualNumber_all_traces_equal_iff (x y : DualNumber K) :
    (∀ (d : ℕ) (ρ : DualNumber K →ₐ[K] Matrix (Fin d) (Fin d) K),
      Matrix.trace (ρ x) = Matrix.trace (ρ y)) ↔ x.fst = y.fst := by
  constructor
  · intro h
    have hz := h 1 dualNumberResidueMatrix
    simpa only [dualNumber_representation_trace, Fintype.card_fin,
      Nat.cast_one, one_mul] using hz
  · intro h d ρ
    rw [dualNumber_representation_trace, dualNumber_representation_trace, h]

/-- The trace kernel consists precisely of the infinitesimal line. -/
theorem dualNumber_trace_kernel_iff (x : DualNumber K) :
    (∀ (d : ℕ) (ρ : DualNumber K →ₐ[K] Matrix (Fin d) (Fin d) K),
      Matrix.trace (ρ x) = 0) ↔ ∃ b : K, x = TrivSqZeroExt.inr b := by
  rw [dualNumber_all_traces_zero_iff]
  constructor
  · intro h
    refine ⟨x.snd, ?_⟩
    ext <;> simp [h]
  · rintro ⟨b, rfl⟩
    rfl

/-- The only idempotents in the dual numbers over a field are zero and one. -/
theorem dualNumber_idempotent_iff (x : DualNumber K) :
    x * x = x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have ha : x.fst * x.fst = x.fst := congrArg TrivSqZeroExt.fst h
    have hb : x.fst * x.snd + x.snd * x.fst = x.snd := by
      simpa only [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul] using
        congrArg TrivSqZeroExt.snd h
    have hz : x.fst * (x.fst - 1) = 0 := by linear_combination ha
    rcases mul_eq_zero.mp hz with hzero | hone
    · left
      have hs : x.snd = 0 := by simpa only [hzero, zero_mul, mul_zero, zero_add] using hb.symm
      ext <;> simp [hzero, hs]
    · right
      have ho : x.fst = 1 := sub_eq_zero.mp hone
      have hs : x.snd = 0 := by
        rw [ho, one_mul, mul_one] at hb
        exact add_left_cancel (show x.snd + x.snd = x.snd + 0 by simpa using hb)
      ext <;> simp [ho, hs]
  · rintro (rfl | rfl) <;> simp

/-- The idempotent-generated complement in the cocenter is exactly the scalar line. -/
theorem dualNumber_idempotent_span :
    Submodule.span K {x : DualNumber K | x * x = x} =
      Submodule.span K {(1 : DualNumber K)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases (dualNumber_idempotent_iff x).mp hx with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (Set.mem_singleton 1)
  · apply Submodule.span_le.mpr
    intro x hx
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    exact Submodule.subset_span (by simp)

/-- Every element has one and only one invisible remainder after removing its residue. -/
theorem dualNumber_unique_trace_decomposition (x : DualNumber K) :
    ∃! y : DualNumber K, y.fst = 0 ∧ x = x.fst • (1 : DualNumber K) + y := by
  refine ⟨TrivSqZeroExt.inr x.snd, ⟨rfl, dualNumber_scalar_nilpotent_split x⟩, ?_⟩
  intro y hy
  exact add_left_cancel (hy.2.symm.trans (dualNumber_scalar_nilpotent_split x))

/-- In characteristic two the regular representation loses even the scalar part,
although the residue representation still detects the unit. -/
theorem dualNumber_modular_regular_vs_residue [CharP K 2] :
    Matrix.trace (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0 1) = 0 ∧
      Matrix.trace (dualNumberResidueMatrix (1 : DualNumber K)) = 1 := by
  constructor
  · rw [trace_dualNumberBlock, two_mul, CharTwo.add_self_eq_zero]
  · rw [dualNumber_representation_trace]
    simp

#print axioms dualNumber_representation_trace
#print axioms dualNumber_all_traces_equal_iff
#print axioms dualNumber_trace_kernel_iff
#print axioms dualNumber_idempotent_span
#print axioms dualNumber_unique_trace_decomposition
#print axioms dualNumber_modular_regular_vs_residue

end
end GaloisForLFunctions.RepresentationLifting
