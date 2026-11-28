import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic

/-! In the finite splitting field of a monic irreducible, the
automorphism carrying one root to another is a Frobenius power. -/

noncomputable section

open Polynomial

namespace WindowedLandauTheory.CyclotomicNorms

theorem exists_frobenius_pow_eq_of_roots {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [IsAlgClosed L] {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {x y : L}
    (hx : aeval x P = 0) (hy : aeval y P = 0) : ∃ n : ℕ, y = x ^ Fintype.card K ^ n := by
  let E : IntermediateField K L := IntermediateField.adjoin K (P.rootSet L)
  have hxE : x ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hm.ne_zero).2 hx)
  have hyE : y ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hm.ne_zero).2 hy)
  let u : E := ⟨x, hxE⟩
  let v : E := ⟨y, hyE⟩
  letI : IsSplittingField K E P := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  letI : Normal K E := Normal.of_isSplittingField P
  letI : FiniteDimensional K E := IsSplittingField.finiteDimensional E P
  letI : Finite E := Module.finite_of_finite K
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  have hc : minpoly K v = minpoly K u := by
    rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
    exact (minpoly.eq_of_irreducible_of_monic hi hy hm).symm.trans
      (minpoly.eq_of_irreducible_of_monic hi hx hm)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).mp hc
  obtain ⟨j, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
  have he : (FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ (j : ℕ)) u = v := hσ
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at he
  refine ⟨(j : ℕ), ?_⟩
  exact congrArg (fun z : E => (z : L)) he.symm

end WindowedLandauTheory.CyclotomicNorms

#print axioms WindowedLandauTheory.CyclotomicNorms.exists_frobenius_pow_eq_of_roots
