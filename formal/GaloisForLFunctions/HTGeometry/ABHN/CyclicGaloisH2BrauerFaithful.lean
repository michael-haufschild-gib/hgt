import GaloisForLFunctions.HTGeometry.ABHN.BrauerMoritaCancellation
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraNormCriterion
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerAdditive

/-!
# Faithfulness of cyclic degree-two cohomology in the Brauer group

Brauer--Morita cancellation upgrades the explicit cyclic-algebra norm criterion to quotient-level
faithfulness.  Consequently the cyclic `H² → Br(K)` map has zero kernel and identifies cyclic
degree-two cohomology directly with the relative cyclic Brauer subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- A cyclic algebra has split Brauer class exactly when its raw algebra is explicitly the
endomorphism algebra of the defining cyclic extension. -/
theorem cyclicGaloisAlgebra_brauerClass_eq_split_iff_explicitSplit
    (a : K) (ha : a ≠ 0) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) = brauerSplitClass K ↔
      Nonempty (cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) := by
  constructor
  · intro h
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      (brauerClass_eq_split_iff_exists_matrixAlgEquiv K
        (cyclicGaloisAlgebraCSA K L a ha)).mp h
    have hfin := e.toLinearEquiv.finrank_eq
    have hsquare : Module.finrank K L ^ 2 = n ^ 2 := by
      change Module.finrank K (cyclicGaloisAlgebra K L a) =
        Module.finrank K (Matrix (Fin n) (Fin n) K) at hfin
      rw [cyclicGaloisAlgebra_finrank_eq_square K L a] at hfin
      simpa [Module.finrank_matrix, pow_two] using hfin
    have hdegree : Module.finrank K L = n :=
      Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hsquare
    let b := Module.finBasisOfFinrankEq K L hdegree
    exact ⟨e.trans (Matrix.toLinAlgEquiv b)⟩
  · rintro ⟨e⟩
    letI : NeZero (Module.finrank K L) :=
      ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
    exact (brauerClass_eq_of_algEquiv (cyclicGaloisAlgebraCSA K L a ha)
      (matrixFinCSA (scalarCSA K) (Module.finrank K L))
      (e.trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K L)))).trans
      (brauerClass_matrixFinCSA_scalar_eq (Module.finrank K L))

/-- **Brauer norm criterion.** A cyclic algebra represents zero in the Brauer group exactly when
its defining parameter is a field norm. -/
theorem cyclicGaloisAlgebra_brauerClass_eq_split_iff_exists_normUnit
    (a : K) (ha : a ≠ 0) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) = brauerSplitClass K ↔
      ∃ c : Lˣ, a = Algebra.norm K (c : L) := by
  rw [cyclicGaloisAlgebra_brauerClass_eq_split_iff_explicitSplit K L a ha,
    cyclicGaloisAlgebra_split_iff_exists_normUnit K L a ha]

/-- A cyclic degree-two cohomology class has split Brauer image exactly when it is zero. -/
theorem cyclicGaloisH2BrauerMap_eq_split_iff (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerMap K L z = brauerSplitClass K ↔ z = 0 := by
  let u : Kˣ := cyclicGaloisH2FixedBaseUnit K L (cyclicGaloisH2Representative K L z)
  change brauerClass (cyclicGaloisAlgebraCSA K L (u : K) u.ne_zero) =
      brauerSplitClass K ↔ z = 0
  rw [cyclicGaloisAlgebra_brauerClass_eq_split_iff_explicitSplit K L (u : K) u.ne_zero]
  exact cyclicGaloisH2ClassCyclicAlgebra_split_iff_eq_zero K L z

/-- The additive cyclic `H² → Br(K)` realization is injective. -/
theorem cyclicGaloisH2BrauerAddHom_injective :
    Function.Injective (cyclicGaloisH2BrauerAddHom K L) := by
  apply (injective_iff_map_eq_zero (cyclicGaloisH2BrauerAddHom K L)).mpr
  intro z hz
  exact (cyclicGaloisH2BrauerMap_eq_split_iff K L z).mp hz

/-- Every finite cyclic invariant coordinate maps injectively into the Brauer group. -/
theorem cyclicGaloisH2InvariantBrauerAddHom_injective
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) :
    Function.Injective (cyclicGaloisH2InvariantBrauerAddHom K L n e) :=
  (cyclicGaloisH2BrauerAddHom_injective K L).comp e.symm.injective

/-- Cyclic degree-two cohomology is additively equivalent to the cyclic relative Brauer
subgroup, with no quotient by an unknown kernel. -/
noncomputable def cyclicGaloisH2BrauerSubgroupAddEquiv :
    cyclicGaloisH2 K L ≃+ cyclicGaloisBrauerSubgroup K L :=
  AddEquiv.ofBijective (cyclicGaloisH2BrauerSubgroupAddHom K L)
    ⟨fun _ _ h => cyclicGaloisH2BrauerAddHom_injective K L (congrArg Subtype.val h),
      cyclicGaloisH2BrauerSubgroupAddHom_surjective K L⟩

/-- Any cyclic invariant coordinate is the actual cyclic Brauer subgroup in those coordinates. -/
noncomputable def cyclicGaloisInvariantBrauerSubgroupAddEquiv
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) :
    ZMod n ≃+ cyclicGaloisBrauerSubgroup K L :=
  e.symm.trans (cyclicGaloisH2BrauerSubgroupAddEquiv K L)

end

end GaloisForLFunctions.HTGeometry.ABHN
