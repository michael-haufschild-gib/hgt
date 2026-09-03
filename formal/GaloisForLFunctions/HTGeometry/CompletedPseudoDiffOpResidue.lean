import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpIntegerPrincipal

/-!
# Residue skew field of completed pseudodifferential operators

The strict unit ball in the completed valuation ring is a two-sided maximal ideal.  Its quotient
is therefore a division ring.  This is the residue object needed to prove uniqueness of completed
Cartan coweights without a commutative determinant.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- Strict valuation ideal of the completed pseudodifferential valuation ring. -/
noncomputable def completedPseudoDiffOpMaximalIdeal :
    Ideal (CompletedPseudoDiffOpInteger (K := K)) where
  carrier := {x | completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (completedPseudoDiffOpValuation.map_add (x : CompletedPseudoDiffOp K)
      (y : CompletedPseudoDiffOp K)).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro a x hx
    change completedPseudoDiffOpValuation
        ((a : CompletedPseudoDiffOp K) * (x : CompletedPseudoDiffOp K)) < 1
    rw [Valuation.map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right a.property (bot_le) hx

@[simp]
theorem mem_completedPseudoDiffOpMaximalIdeal_iff
    (x : CompletedPseudoDiffOpInteger (K := K)) :
    x ∈ completedPseudoDiffOpMaximalIdeal (K := K) ↔
      completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) < 1 :=
  Iff.rfl

/-- The strict valuation ideal is stable under multiplication on the right as well. -/
noncomputable instance completedPseudoDiffOpMaximalIdeal_isTwoSided :
    (completedPseudoDiffOpMaximalIdeal (K := K)).IsTwoSided where
  mul_mem_of_left b ha := by
    change completedPseudoDiffOpValuation
        (((_ : CompletedPseudoDiffOpInteger (K := K)) : CompletedPseudoDiffOp K) *
          (b : CompletedPseudoDiffOp K)) < 1
    rw [Valuation.map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (bot_le) ha b.property

/-- An integral completed operator outside the strict valuation ideal is a unit of the valuation
ring. -/
theorem isUnit_of_not_mem_completedPseudoDiffOpMaximalIdeal
    (x : CompletedPseudoDiffOpInteger (K := K))
    (hx : x ∉ completedPseudoDiffOpMaximalIdeal (K := K)) : IsUnit x := by
  have hxval : completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) = 1 :=
    le_antisymm x.property (le_of_not_gt hx)
  have hx0 : (x : CompletedPseudoDiffOp K) ≠ 0 := by
    intro h
    have : completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) = 0 := by rw [h, map_zero]
    rw [hxval] at this
    exact one_ne_zero this
  let y : CompletedPseudoDiffOpInteger (K := K) :=
    ⟨(x : CompletedPseudoDiffOp K)⁻¹, by
      rw [Valuation.mem_integer_iff, Valuation.map_inv, hxval, inv_one]⟩
  apply isUnit_iff_exists.mpr
  refine ⟨y, ?_, ?_⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hx0
  · apply Subtype.ext
    exact inv_mul_cancel₀ hx0

/-- The strict valuation ideal is maximal. -/
theorem completedPseudoDiffOpMaximalIdeal_isMaximal :
    (completedPseudoDiffOpMaximalIdeal (K := K)).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · simp [completedPseudoDiffOpMaximalIdeal]
  · intro J x _ hx hxJ
    have hxunit := isUnit_of_not_mem_completedPseudoDiffOpMaximalIdeal x hx
    rw [J.eq_top_of_isUnit_mem hxJ hxunit]
    exact Submodule.mem_top

noncomputable instance completedPseudoDiffOpMaximalIdeal_instIsMaximal :
    (completedPseudoDiffOpMaximalIdeal (K := K)).IsMaximal :=
  completedPseudoDiffOpMaximalIdeal_isMaximal (K := K)

/-- Residue skew field of the completed pseudodifferential valuation ring. -/
abbrev CompletedPseudoDiffOpResidue (K : Type u) [Field K] [Differential K] : Type u :=
  CompletedPseudoDiffOpInteger (K := K) ⧸ completedPseudoDiffOpMaximalIdeal (K := K)

/-- Maximality and two-sidedness make the completed residue a division ring. -/
noncomputable instance completedPseudoDiffOpResidue_divisionRing :
    DivisionRing (CompletedPseudoDiffOpResidue K) :=
  Ideal.Quotient.divisionRing (completedPseudoDiffOpMaximalIdeal (K := K))

/-- Canonical reduction into the completed residue skew field. -/
noncomputable def completedPseudoDiffOpResidueMap :
    CompletedPseudoDiffOpInteger (K := K) →+* CompletedPseudoDiffOpResidue K :=
  Ideal.Quotient.mk (completedPseudoDiffOpMaximalIdeal (K := K))

theorem completedPseudoDiffOpResidueMap_surjective :
    Function.Surjective (completedPseudoDiffOpResidueMap (K := K)) :=
  Ideal.Quotient.mk_surjective

theorem completedPseudoDiffOpResidueMap_eq_zero_iff
    (x : CompletedPseudoDiffOpInteger (K := K)) :
    completedPseudoDiffOpResidueMap x = 0 ↔
      x ∈ completedPseudoDiffOpMaximalIdeal (K := K) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem completedPseudoDiffOpResidueMap_ne_zero_iff
    (x : CompletedPseudoDiffOpInteger (K := K)) :
    completedPseudoDiffOpResidueMap x ≠ 0 ↔
      completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) = 1 := by
  rw [ne_eq, completedPseudoDiffOpResidueMap_eq_zero_iff,
    mem_completedPseudoDiffOpMaximalIdeal_iff]
  exact ⟨fun h => le_antisymm x.property (le_of_not_gt h), fun h hx => by rw [h] at hx; exact hx.false⟩

end

end DiffOp

end GaloisForLFunctions.HTGeometry
