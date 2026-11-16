import GaloisForLFunctions.RepresentationLifting.Probability.FittingStrata
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting ordered complementary subspaces

The general linear group acts transitively on complementary pairs of fixed
dimensions. The stabilizer is the product of the general linear groups of
the two summands. Orbit--stabilizer gives the exact count used in Fitting
stratification of finite-field endomorphisms.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Transport a complementary pair by an ambient automorphism. -/
def mapComplementaryPair (e : V ≃ₗ[K] V) (P : ComplementaryPair K V) :
    ComplementaryPair K V :=
  ⟨(P.1.1.map e.toLinearMap, P.1.2.map e.toLinearMap),
    (Submodule.orderIsoMapComap e).isCompl_iff.mp P.2⟩

private theorem map_linearEquiv_mul (e f : V ≃ₗ[K] V) (U : Submodule K V) :
    U.map (e * f).toLinearMap = (U.map f.toLinearMap).map e.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

instance complementaryPairAction : MulAction (V ≃ₗ[K] V) (ComplementaryPair K V) where
  smul := mapComplementaryPair
  one_smul P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Submodule.map_id P.1.1
    · exact Submodule.map_id P.1.2
  mul_smul e f P := by
    apply Subtype.ext
    exact Prod.ext (map_linearEquiv_mul e f P.1.1) (map_linearEquiv_mul e f P.1.2)

/-- Assemble isomorphisms between the two corresponding summands. -/
def complementaryPairEquiv (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm.trans
    ((a.prodCongr b).trans (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2))

/-- Assembly agrees with the first chosen isomorphism on the first summand. -/
theorem complementaryPairEquiv_left (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) (x : P.1.1) :
    complementaryPairEquiv P Q a b x = (a x : V) := by
  change (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2)
    ((a.prodCongr b) ((Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm x)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  change (a x : V) + (b 0 : V) = (a x : V)
  rw [map_zero, Submodule.coe_zero, add_zero]

/-- Assembly agrees with the second chosen isomorphism on the second summand. -/
theorem complementaryPairEquiv_right (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) (x : P.1.2) :
    complementaryPairEquiv P Q a b x = (b x : V) := by
  change (Submodule.prodEquivOfIsCompl Q.1.1 Q.1.2 Q.2)
    ((a.prodCongr b) ((Submodule.prodEquivOfIsCompl P.1.1 P.1.2 P.2).symm x)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  change (a 0 : V) + (b x : V) = (b x : V)
  rw [map_zero, Submodule.coe_zero, zero_add]

/-- The assembled isomorphism sends the whole ordered pair to the target pair. -/
theorem complementaryPairEquiv_smul (P Q : ComplementaryPair K V)
    (a : P.1.1 ≃ₗ[K] Q.1.1) (b : P.1.2 ≃ₗ[K] Q.1.2) :
    complementaryPairEquiv P Q a b • P = Q := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change complementaryPairEquiv P Q a b u ∈ Q.1.1
      rw [complementaryPairEquiv_left P Q a b ⟨u, hu⟩]
      exact (a ⟨u, hu⟩).2
    · intro hx
      refine ⟨(a.symm ⟨x, hx⟩ : V), (a.symm ⟨x, hx⟩).2, ?_⟩
      rw [complementaryPairEquiv_left]
      exact congrArg Subtype.val (a.apply_symm_apply ⟨x, hx⟩)
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change complementaryPairEquiv P Q a b u ∈ Q.1.2
      rw [complementaryPairEquiv_right P Q a b ⟨u, hu⟩]
      exact (b ⟨u, hu⟩).2
    · intro hx
      refine ⟨(b.symm ⟨x, hx⟩ : V), (b.symm ⟨x, hx⟩).2, ?_⟩
      rw [complementaryPairEquiv_right]
      exact congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩)

variable [FiniteDimensional K V]

/-- The orbit of a complementary pair is determined by the dimension of its first summand. -/
theorem mem_complementaryPair_orbit_iff (P Q : ComplementaryPair K V) :
    Q ∈ MulAction.orbit (V ≃ₗ[K] V) P ↔ Module.finrank K Q.1.1 = Module.finrank K P.1.1 := by
  constructor
  · rintro ⟨e, rfl⟩
    exact (e.submoduleMap P.1.1).finrank_eq.symm
  · intro hdim
    have hP := Submodule.finrank_add_eq_of_isCompl P.2
    have hQ := Submodule.finrank_add_eq_of_isCompl Q.2
    let a : P.1.1 ≃ₗ[K] Q.1.1 := LinearEquiv.ofFinrankEq _ _ hdim.symm
    let b : P.1.2 ≃ₗ[K] Q.1.2 := LinearEquiv.ofFinrankEq _ _ (by omega)
    exact ⟨complementaryPairEquiv P Q a b, complementaryPairEquiv_smul P Q a b⟩

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
