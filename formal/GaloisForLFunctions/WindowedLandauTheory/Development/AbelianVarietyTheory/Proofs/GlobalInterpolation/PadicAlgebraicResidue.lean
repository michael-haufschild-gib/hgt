import GaloisForLFunctions.HTGeometry.ValuationSubringResidueAlgebraic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Valuation.LocalSubring

/-! The valuation of the algebraic closure of the p-adic field has residue field
the algebraic closure of the prime field. -/

noncomputable section

open IsLocalRing Polynomial
open scoped NNReal

namespace GlobalTheory.TeichPlace

/-- Lift a monic polynomial, take an integral root in the ambient field, and reduce it. -/
theorem isAlgClosed_residueField_valuationSubring {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hi
  have hlift : f ∈ lifts (residue A) :=
    mem_lifts_of_surjective residue_surjective f
  obtain ⟨g, hg, hdegree, hmonic⟩ := lifts_and_degree_eq_and_monic hlift hf
  have hpos : (g.map (algebraMap A K)).degree ≠ 0 := by
    rw [hmonic.degree_map, hdegree]
    exact ne_of_gt (degree_pos_of_irreducible hi)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (g.map (algebraMap A K)) hpos
  have hroot : aeval x g = 0 := by
    simpa only [aeval_def, IsRoot.def, eval_map] using hx
  obtain ⟨y, hxy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (show IsIntegral A x from ⟨g, hmonic, hroot⟩)
  have hy : g.eval y = 0 := by
    apply IsFractionRing.injective A K
    rw [map_zero, ← eval₂_hom, ← eval_map, hxy]
    exact hx
  refine ⟨residue A y, ?_⟩
  rw [← hg, eval_map, eval₂_hom, hy, map_zero]

/-- The valuation subring of the algebraic closure of the p-adic field. -/
abbrev padicAlgClIntegers (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) :=
  (PadicAlgCl.valued p).v.valuationSubring

private theorem mem_padicAlgClIntegers_padic {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) :
    algebraMap ℚ_[p] (PadicAlgCl p) x ∈ padicAlgClIntegers p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe,
    PadicAlgCl.valuation_coe, NNReal.coe_one]
  rw [show (algebraMap ℚ_[p] (PadicAlgCl p)) x = (x : PadicAlgCl p) from rfl, PadicAlgCl.norm_extends]

/-- Reduction on the algebraic closure extends reduction on the p-adic integers,
so its algebraically closed residue field is algebraic over the prime field. -/
theorem nonempty_padicAlgCl_residueField_equiv (p : ℕ) [Fact p.Prime] :
    Nonempty (ResidueField (padicAlgClIntegers p) ≃+* AlgebraicClosure (ZMod p)) := by
  let B := padicAlgClIntegers p
  let O := B.comap (algebraMap ℚ_[p] (PadicAlgCl p))
  let e : ℤ_[p] ≃+* O :=
    { toFun := fun x => ⟨x, (mem_padicAlgClIntegers_padic _).mpr x.2⟩
      invFun := fun x => ⟨x, (mem_padicAlgClIntegers_padic _).mp x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let ρ : ResidueField O ≃+* ZMod p := (ResidueField.mapEquiv e).symm.trans PadicInt.residueField
  letI : Algebra (ZMod p) (ResidueField B) :=
    ((algebraMap (ResidueField O) (ResidueField B)).comp ρ.symm.toRingHom).toAlgebra
  letI : Algebra.IsAlgebraic (ResidueField O) (ResidueField B) :=
    GaloisForLFunctions.HTGeometry.isAlgebraic_residueField_comap B
  letI : Algebra.IsAlgebraic (ZMod p) (ResidueField B) :=
    Algebra.IsAlgebraic.ringHom_of_comp_eq ρ.toRingHom (RingHom.id (ResidueField B))
      ρ.injective Function.surjective_id (by ext x; simp [RingHom.algebraMap_toAlgebra])
  letI : IsAlgClosed (ResidueField B) := isAlgClosed_residueField_valuationSubring B
  letI : IsAlgClosure (ZMod p) (ResidueField B) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod p) (ResidueField B) (AlgebraicClosure (ZMod p))).toRingEquiv⟩

end GlobalTheory.TeichPlace
