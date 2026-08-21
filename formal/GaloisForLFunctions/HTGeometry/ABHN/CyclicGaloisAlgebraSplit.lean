/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebra
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# The split cyclic algebra representation

For the parameter `1`, a cyclic Galois algebra acts on the coefficient field viewed as a
`K`-vector space.  Coefficients act by left multiplication and the cyclic variable acts by the
chosen Galois generator.  This gives a concrete representation of the raw quotient in
`End_K(L)`, proves that its coefficient copy is faithful, and proves the quotient is nontrivial.
The Galois automorphisms form an `L`-basis of `End_K(L)`, and all occur in the representation.
The normal-form dimension bound then upgrades surjectivity to an explicit `K`-algebra equivalence
with `End_K(L)`.  In particular the raw split cyclic Galois algebra is a simple ring.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The coefficient field acts on itself by left multiplication. -/
noncomputable abbrev cyclicGaloisAlgebraSplitCoefficientAction : L →+* Module.End K L :=
  (Algebra.lmul K L).toRingHom

/-- The chosen cyclic Galois generator acts as a `K`-linear endomorphism of its coefficient
field. -/
noncomputable abbrev cyclicGaloisAlgebraSplitGeneratorAction : Module.End K L :=
  (cyclicGaloisGenerator K L).toLinearMap

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Taking powers commutes with passage from the Galois automorphism to its linear action. -/
theorem cyclicGaloisGenerator_toLinearMap_pow (q : ℕ) :
    (cyclicGaloisGenerator K L).toLinearMap ^ q =
      ((cyclicGaloisGenerator K L) ^ q).toLinearMap := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [pow_succ, pow_succ, ih]
    rfl

/-- The generator action has order equal to the degree of the cyclic Galois extension. -/
theorem cyclicGaloisAlgebraSplitGeneratorAction_pow_finrank :
    cyclicGaloisAlgebraSplitGeneratorAction K L ^ Module.finrank K L = 1 := by
  rw [← cyclicGaloisGenerator_orderOf K L]
  rw [cyclicGaloisGenerator_toLinearMap_pow]
  ext x
  simp only [Module.End.one_apply]
  change ((cyclicGaloisGenerator K L) ^ orderOf (cyclicGaloisGenerator K L)) x = x
  rw [pow_orderOf_eq_one]
  simp

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The coefficient and generator actions satisfy every skew commutation relation required by
the universal cyclic-algebra lift. -/
theorem cyclicGaloisAlgebraSplit_actions_commute (m : Multiplicative ℕ) (x : L) :
    cyclicGaloisAlgebraSplitCoefficientAction K L
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) x) *
      cyclicPowerMonoidHom (cyclicGaloisAlgebraSplitGeneratorAction K L) m =
    cyclicPowerMonoidHom (cyclicGaloisAlgebraSplitGeneratorAction K L) m *
      cyclicGaloisAlgebraSplitCoefficientAction K L x := by
  ext z
  unfold cyclicGaloisAlgebraSplitCoefficientAction cyclicGaloisAlgebraSplitGeneratorAction
    cyclicPowerRingAut cyclicPowerMonoidHom
  change (Algebra.lmul K L
      (((cyclicGaloisGenerator K L).toRingEquiv ^ (toAdd m)) x) *
        ((cyclicGaloisGenerator K L).toLinearMap ^ (toAdd m))) z =
    (((cyclicGaloisGenerator K L).toLinearMap ^ (toAdd m)) * Algebra.lmul K L x) z
  rw [cyclicGaloisGenerator_toLinearMap_pow]
  simp [Module.End.mul_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul]

/-- The split raw cyclic Galois algebra acts on `L` through left multiplication by coefficients
and the Galois generator. -/
noncomputable def cyclicGaloisAlgebraSplitRepresentation :
    cyclicGaloisAlgebra K L 1 →+* Module.End K L :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L)
    (cyclicGaloisAlgebraSplit_actions_commute K L) (by
      change cyclicGaloisAlgebraSplitGeneratorAction K L ^ Module.finrank K L =
        cyclicGaloisAlgebraSplitCoefficientAction K L (algebraMap K L (1 : K))
      simp only [map_one]
      exact cyclicGaloisAlgebraSplitGeneratorAction_pow_finrank K L)

/-- The split representation sends a coefficient to its left-multiplication endomorphism. -/
theorem cyclicGaloisAlgebraSplitRepresentation_C (b : L) :
    cyclicGaloisAlgebraSplitRepresentation K L (cyclicGaloisAlgebraC K L 1 b) =
      Algebra.lmul K L b := by
  unfold cyclicGaloisAlgebraSplitRepresentation
  exact cyclicAlgebraLift_C (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L) _ _ b

/-- The split representation sends the cyclic generator to the chosen Galois action. -/
theorem cyclicGaloisAlgebraSplitRepresentation_X :
    cyclicGaloisAlgebraSplitRepresentation K L (cyclicGaloisAlgebraX K L 1) =
      cyclicGaloisAlgebraSplitGeneratorAction K L := by
  unfold cyclicGaloisAlgebraSplitRepresentation
  exact cyclicAlgebraLift_X (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L) _ _

/-- The coefficient field embeds faithfully into the split raw cyclic algebra. -/
theorem cyclicGaloisAlgebraSplit_C_injective :
    Function.Injective (cyclicGaloisAlgebraC K L 1) := by
  intro x y hxy
  have hrepresentation := congrArg (cyclicGaloisAlgebraSplitRepresentation K L) hxy
  rw [cyclicGaloisAlgebraSplitRepresentation_C,
    cyclicGaloisAlgebraSplitRepresentation_C] at hrepresentation
  have hone := LinearMap.congr_fun hrepresentation 1
  change x * 1 = y * 1 at hone
  simpa using hone

/-- The Galois automorphisms, viewed as `K`-linear maps, form an `L`-basis of `End_K(L)`. -/
noncomputable def cyclicGaloisAlgebraSplitEndBasis :
    Module.Basis Gal(L/K) L (Module.End K L) :=
  basisOfLinearIndependentOfCardEqFinrank
    ((linearIndependent_algHom_toLinearMap K L L).comp _ (algEquivEquivAlgHom K L).injective)
    (by
      calc
        Fintype.card Gal(L/K) = Nat.card Gal(L/K) := Fintype.card_eq_nat_card
        _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
        _ = Module.finrank L (Module.End K L) := by
          rw [Module.finrank_linearMap K L L L]
          simp)

omit [IsCyclic Gal(L/K)] in
/-- The Galois endomorphisms span all `K`-linear endomorphisms of the coefficient field. -/
theorem cyclicGaloisAlgebraSplitEndBasis_span_eq_top :
    Submodule.span L (Set.range fun σ : Gal(L/K) => σ.toLinearMap) = ⊤ := by
  have heq : (AlgHom.toLinearMap ∘ ⇑(algEquivEquivAlgHom K L)) =
      fun σ : Gal(L/K) => σ.toLinearMap := by
    rfl
  simpa only [cyclicGaloisAlgebraSplitEndBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    heq] using (cyclicGaloisAlgebraSplitEndBasis K L).span_eq

/-- The image of the split representation is closed under the natural `L`-scalar action on
`End_K(L)`. -/
noncomputable def cyclicGaloisAlgebraSplitRepresentationRange : Submodule L (Module.End K L) where
  carrier := Set.range (cyclicGaloisAlgebraSplitRepresentation K L)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' hx hy := by
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
  smul_mem' c f hf := by
    obtain ⟨x, rfl⟩ := hf
    refine ⟨cyclicGaloisAlgebraC K L 1 c * x, ?_⟩
    rw [map_mul, cyclicGaloisAlgebraSplitRepresentation_C]
    ext z
    simp [Module.End.mul_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul]

/-- Every Galois automorphism occurs in the range of the split cyclic-algebra representation. -/
theorem cyclicGaloisAlgebraSplitGeneratorAction_mem_range (σ : Gal(L/K)) :
    σ.toLinearMap ∈ cyclicGaloisAlgebraSplitRepresentationRange K L := by
  classical
  change σ.toLinearMap ∈ Set.range (cyclicGaloisAlgebraSplitRepresentation K L)
  have hfull := IsCyclic.image_range_orderOf (cyclicGaloisGenerator_spec K L)
  have hmem : σ ∈ (Finset.range (orderOf (cyclicGaloisGenerator K L))).image
      (cyclicGaloisGenerator K L ^ ·) := by
    rw [hfull]
    simp
  obtain ⟨i, _hi, hpower⟩ := Finset.mem_image.mp hmem
  refine ⟨cyclicGaloisAlgebraC K L 1 1 * cyclicGaloisAlgebraX K L 1 ^ i, ?_⟩
  rw [map_mul, map_pow, cyclicGaloisAlgebraSplitRepresentation_C,
    cyclicGaloisAlgebraSplitRepresentation_X]
  simp only [map_one, one_mul]
  rw [cyclicGaloisGenerator_toLinearMap_pow, hpower]

/-- The raw split cyclic Galois algebra maps surjectively onto `End_K(L)`. -/
theorem cyclicGaloisAlgebraSplitRepresentation_surjective :
    Function.Surjective (cyclicGaloisAlgebraSplitRepresentation K L) := by
  classical
  have htop : cyclicGaloisAlgebraSplitRepresentationRange K L = ⊤ := by
    apply top_unique
    rw [← cyclicGaloisAlgebraSplitEndBasis_span_eq_top K L]
    apply Submodule.span_le.2
    rintro _ ⟨σ, rfl⟩
    exact cyclicGaloisAlgebraSplitGeneratorAction_mem_range K L σ
  intro f
  change f ∈ Set.range (cyclicGaloisAlgebraSplitRepresentation K L)
  change f ∈ cyclicGaloisAlgebraSplitRepresentationRange K L
  rw [htop]
  trivial

/-- The split representation preserves the base-field algebra map. -/
theorem cyclicGaloisAlgebraSplitRepresentation_algebraMap (b : K) :
    cyclicGaloisAlgebraSplitRepresentation K L (algebraMap K (cyclicGaloisAlgebra K L 1) b) =
      algebraMap K (Module.End K L) b := by
  change cyclicGaloisAlgebraSplitRepresentation K L
    (cyclicGaloisAlgebraC K L 1 (algebraMap K L b)) = _
  rw [cyclicGaloisAlgebraSplitRepresentation_C]
  ext x
  simp

/-- The split representation promoted to a `K`-algebra homomorphism. -/
noncomputable def cyclicGaloisAlgebraSplitRepresentationAlgHom :
    cyclicGaloisAlgebra K L 1 →ₐ[K] Module.End K L :=
  AlgHom.mk' (cyclicGaloisAlgebraSplitRepresentation K L) (by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    rw [cyclicGaloisAlgebraSplitRepresentation_algebraMap])

/-- The split algebra homomorphism is surjective. -/
theorem cyclicGaloisAlgebraSplitRepresentationAlgHom_surjective :
    Function.Surjective (cyclicGaloisAlgebraSplitRepresentationAlgHom K L) :=
  cyclicGaloisAlgebraSplitRepresentation_surjective K L

/-- The normal-form bound is sharp for the split cyclic Galois algebra. -/
theorem cyclicGaloisAlgebraSplit_finrank_eq_end :
    Module.finrank K (cyclicGaloisAlgebra K L 1) = Module.finrank K (Module.End K L) := by
  apply le_antisymm
  · calc
      Module.finrank K (cyclicGaloisAlgebra K L 1) ≤
          Module.finrank K L * Module.finrank K L :=
        cyclicGaloisAlgebra_finrank_le K L 1
      _ = Module.finrank K (Module.End K L) := by
        rw [Module.finrank_linearMap K K L L]
  · calc
      Module.finrank K (Module.End K L) ≤ Module.finrank K (cyclicGaloisAlgebra K L 1) :=
        LinearMap.finrank_le_finrank_of_surjective
          (f := (cyclicGaloisAlgebraSplitRepresentationAlgHom K L).toLinearMap)
          (cyclicGaloisAlgebraSplitRepresentationAlgHom_surjective K L)

/-- The split algebra homomorphism is injective. -/
theorem cyclicGaloisAlgebraSplitRepresentationAlgHom_injective :
    Function.Injective (cyclicGaloisAlgebraSplitRepresentationAlgHom K L) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (cyclicGaloisAlgebraSplit_finrank_eq_end K L)
    (f := (cyclicGaloisAlgebraSplitRepresentationAlgHom K L).toLinearMap)).mpr
      (cyclicGaloisAlgebraSplitRepresentationAlgHom_surjective K L)

/-- **Split cyclic-algebra theorem.** The raw cyclic Galois algebra with parameter `1` is the
full endomorphism algebra of the coefficient field. -/
noncomputable def cyclicGaloisAlgebraSplitAlgEquiv :
    cyclicGaloisAlgebra K L 1 ≃ₐ[K] Module.End K L :=
  AlgEquiv.ofBijective (cyclicGaloisAlgebraSplitRepresentationAlgHom K L)
    ⟨cyclicGaloisAlgebraSplitRepresentationAlgHom_injective K L,
      cyclicGaloisAlgebraSplitRepresentationAlgHom_surjective K L⟩

omit [IsCyclic Gal(L/K)] [IsGalois K L] in
/-- The endomorphism algebra of a nonzero finite-dimensional vector space over a field is simple. -/
theorem isSimpleRing_moduleEnd : IsSimpleRing (Module.End K L) := by
  letI : Nonempty (Fin (Module.finrank K L)) :=
    ⟨⟨0, Module.finrank_pos (R := K) (M := L)⟩⟩
  exact IsSimpleRing.of_ringEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K L)).symm
    (inferInstance : IsSimpleRing
      (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K))

/-- The raw split cyclic Galois algebra is a simple ring. -/
theorem isSimpleRing_cyclicGaloisAlgebra_split : IsSimpleRing (cyclicGaloisAlgebra K L 1) :=
  IsSimpleRing.of_ringEquiv (cyclicGaloisAlgebraSplitAlgEquiv K L).symm.toRingEquiv
    (isSimpleRing_moduleEnd K L)

/-- The split raw cyclic Galois algebra is not the zero ring. -/
theorem cyclicGaloisAlgebraSplit_one_ne_zero : (1 : cyclicGaloisAlgebra K L 1) ≠ 0 := by
  intro hzero
  have hrepresentation := congrArg (cyclicGaloisAlgebraSplitRepresentation K L) hzero
  rw [map_one, map_zero] at hrepresentation
  exact one_ne_zero hrepresentation

end GaloisForLFunctions.HTGeometry.ABHN
