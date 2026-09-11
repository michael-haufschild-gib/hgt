import GaloisForLFunctions.HTGeometry.DifferentialVariationalAttractingSubspace

/-!
# The canonical boundary pair of a variational automorphism

Stable variational speed is invariant under inversion
(`differentialVariationalEuclideanTranslationLength_inv`), because the canonical action is an
isometry and therefore `d(x, σ^{-n} x) = d(x, σ^n x)`.  The repelling objects are consequently the
attracting objects of `σ⁻¹`, and they are proper exactly when the attracting ones are.

`variationalBoundaryPair_iff` is the resulting dichotomy: `σ` has strictly positive stable
variational speed if and only if it carries **both** a proper canonical attracting subspace and a
proper canonical repelling subspace, each invariant under the corresponding action.  Its complement
`variationalBoundaryPair_eq_top_iff` says that in the bounded phase both canonical subspaces
degenerate to the whole coordinate space, so no boundary datum is produced there.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Stable variational speed is invariant under inversion. -/
theorem differentialVariationalEuclideanTranslationLength_inv
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ⁻¹ =
      differentialVariationalEuclideanTranslationLength b x σ := by
  have hseq : ∀ n : ℕ,
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
          ((σ⁻¹ ^ n).projectiveBuildingAction b x) =
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
          ((σ ^ n).projectiveBuildingAction b x) := by
    intro n
    rw [inv_pow]
    exact differentialVariationalEuclideanVertexDistance_inverseAction (σ ^ n) b x
  have hlim := tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b x σ⁻¹
  have hlim' : Filter.Tendsto (fun n : ℕ =>
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        ((σ ^ n).projectiveBuildingAction b x) / n) Filter.atTop
      (nhds (differentialVariationalEuclideanTranslationLength b x σ⁻¹)) := by
    refine hlim.congr fun n => ?_
    rw [hseq n]
  exact tendsto_nhds_unique hlim'
    (tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b x σ)

/-- The canonical repelling core: the attracting core of the inverse automorphism. -/
def variationalRepellingCore (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    Set (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  variationalAttractingCore σ⁻¹ b L

/-- The canonical repelling subspace. -/
def variationalRepellingSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  variationalAttractingSubspace σ⁻¹ b L

/-- The repelling subspace is invariant under the inverse action. -/
theorem variationalRepellingSubspace_invariant (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalRepellingSubspace σ b L) :
    σ⁻¹.vecBuildingAction b v ∈ variationalRepellingSubspace σ b L :=
  variationalAttractingSubspace_invariant σ⁻¹ b L hv

/-- **The boundary pair.**  Strictly positive stable variational speed produces both a proper
canonical attracting subspace and a proper canonical repelling subspace, and conversely either one
of them being proper already forces the boundary phase. -/
theorem variationalBoundaryPair_iff (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (variationalAttractingSubspace σ b L ≠ ⊤ ∧
        variationalRepellingSubspace σ b L ≠ ⊤) ↔
      0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ := by
  have hrep : variationalRepellingSubspace σ b L ≠ ⊤ ↔
      0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ := by
    rw [variationalRepellingSubspace,
      variationalAttractingSubspace_ne_top_iff_translationLength_pos σ⁻¹ b L,
      differentialVariationalEuclideanTranslationLength_inv]
  rw [variationalAttractingSubspace_ne_top_iff_translationLength_pos σ b L, hrep,
    and_self]

/-- **Bounded phase.**  Zero speed makes both canonical subspaces the whole space. -/
theorem variationalBoundaryPair_eq_top_iff (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (variationalAttractingSubspace σ b L = ⊤ ∧
        variationalRepellingSubspace σ b L = ⊤) ↔
      differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ = 0 := by
  constructor
  · rintro ⟨h1, _⟩
    by_contra hne
    have hpos : 0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ :=
      lt_of_le_of_ne
        ((differentialVariationalEuclideanOrbitGauge b (Quotient.mk _ L)).translationLength_nonneg σ)
        (Ne.symm hne)
    exact ((variationalBoundaryPair_iff σ b L).2 hpos).1 h1
  · intro hzero
    constructor
    · by_contra h
      have := (variationalAttractingSubspace_ne_top_iff_translationLength_pos σ b L).1 h
      rw [hzero] at this
      exact lt_irrefl 0 this
    · by_contra h
      have hpos :=
        (variationalAttractingSubspace_ne_top_iff_translationLength_pos σ⁻¹ b L).1 h
      rw [differentialVariationalEuclideanTranslationLength_inv, hzero] at hpos
      exact lt_irrefl 0 hpos

end

end GaloisForLFunctions.HTGeometry
