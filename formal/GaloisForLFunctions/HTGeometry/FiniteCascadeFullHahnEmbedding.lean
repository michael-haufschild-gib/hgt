import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeWimanComponents

/-!
# Full-state Hahn embedding for a finite actual cascade

The Wiman Newton weight sees the independent clock together with every positive cascade state.
Accordingly this module embeds the entire `N + 1`-state rational field into an `N + 1`-coordinate
ramified Hahn field, generator by generator, and extends that embedding to the finite field generated
by the actual derivative branches.  Unlike the differential-coefficient model, no clock degree is
discarded into a coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Generator-preserving embedding of the complete actual state field into the full-state ramified
Hahn field. -/
noncomputable def finiteCascadeFullHahnStateEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    NonautonomousRamifiedCascadeStateField hfan N →ₐ[ℂ]
      HahnFraction (mgDeg (N + 1)) ℂ := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let H := HahnFraction (mgDeg (N + 1)) ℂ
  let xE : Fin (N + 1) → E := nonautonomousCascadeStateFamilyInStateField hfan N
  let xH : Fin (N + 1) → H := hahnFractionRamCoordinate r
  have hxE : AlgebraicIndependent ℂ xE :=
    algebraicIndependent_nonautonomousCascadeStateFamilyInStateField hfan hall N
  have hxH : AlgebraicIndependent ℂ xH :=
    algebraicIndependent_hahnFractionRamCoordinateBase r hr
  have htop : IntermediateField.adjoin ℂ (Set.range xE) = ⊤ :=
    adjoin_range_nonautonomousCascadeStateFamilyInStateField_eq_top hfan N
  let sourceEquiv : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) ≃ₐ[ℂ] E :=
    (hxE.aevalEquivField.trans (IntermediateField.equivOfEq htop)).trans
      IntermediateField.topEquiv
  let targetLift : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) →ₐ[ℂ] H :=
    IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.mp hxH)
  exact targetLift.comp sourceEquiv.symm.toAlgHom

set_option maxHeartbeats 1000000 in
/-- Every actual state generator is sent to its corresponding full-state ramified coordinate. -/
theorem finiteCascadeFullHahnStateEmbedding_apply_generator
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (i : Fin (N + 1)) :
    finiteCascadeFullHahnStateEmbedding hfan hall r hr
        (nonautonomousCascadeStateFamilyInStateField hfan N i) =
      hahnFractionRamCoordinate r i := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let H := HahnFraction (mgDeg (N + 1)) ℂ
  let xE : Fin (N + 1) → E := nonautonomousCascadeStateFamilyInStateField hfan N
  let xH : Fin (N + 1) → H := hahnFractionRamCoordinate r
  have hxE : AlgebraicIndependent ℂ xE :=
    algebraicIndependent_nonautonomousCascadeStateFamilyInStateField hfan hall N
  have hxH : AlgebraicIndependent ℂ xH :=
    algebraicIndependent_hahnFractionRamCoordinateBase r hr
  have htop : IntermediateField.adjoin ℂ (Set.range xE) = ⊤ :=
    adjoin_range_nonautonomousCascadeStateFamilyInStateField_eq_top hfan N
  let sourceEquiv : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) ≃ₐ[ℂ] E :=
    (hxE.aevalEquivField.trans (IntermediateField.equivOfEq htop)).trans
      IntermediateField.topEquiv
  let targetLift : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) →ₐ[ℂ] H :=
    IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.mp hxH)
  change targetLift (sourceEquiv.symm (xE i)) = xH i
  have hsource : sourceEquiv
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
        (FractionRing (MvPolynomial (Fin (N + 1)) ℂ)) (MvPolynomial.X i)) = xE i := by
    simp [sourceEquiv, xE]
  have htarget : targetLift
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
        (FractionRing (MvPolynomial (Fin (N + 1)) ℂ)) (MvPolynomial.X i)) = xH i := by
    simp only [targetLift, IsFractionRing.liftAlgHom, IsLocalization.liftAlgHom]
    change (IsLocalization.lift _)
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
        (FractionRing (MvPolynomial (Fin (N + 1)) ℂ)) (MvPolynomial.X i)) = xH i
    rw [IsLocalization.lift_eq]
    simp
  rw [← hsource]
  simp only [AlgEquiv.symm_apply_apply]
  rw [htarget]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- The finite actual derivative-branch field embeds over all state coordinates into the algebraic
closure of the full-state Hahn field. -/
noncomputable def finiteCascadeFullHahnBranchAlgebraicClosureEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    NonautonomousFiniteCascadeBranchField hfan N →ₐ[ℂ]
      AlgebraicClosure (HahnFraction (mgDeg (N + 1)) ℂ) := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let B := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  let H := HahnFraction (mgDeg (N + 1)) ℂ
  let AC := AlgebraicClosure H
  let phi : E →ₐ[ℂ] H := finiteCascadeFullHahnStateEmbedding hfan hall r hr
  let phiAC : E →ₐ[ℂ] AC := (IsScalarTower.toAlgHom ℂ H AC).comp phi
  letI : Algebra E AC := phiAC.toAlgebra
  letI : FiniteDimensional E B :=
    finiteDimensional_nonautonomousFiniteCascadeBranchFieldOverState hfan hall h1
  let lift : B →ₐ[E] AC := IsAlgClosed.lift
  exact
    { lift.toRingHom with
      commutes' := fun c => by
        change lift (algebraMap E B (algebraMap ℂ E c)) = algebraMap ℂ AC c
        rw [lift.commutes]
        exact phiAC.commutes c }

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- The extended full-state branch embedding still sends every actual state to its prescribed
ramified Hahn coordinate. -/
theorem finiteCascadeFullHahnBranchAlgebraicClosureEmbedding_apply_state
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (i : Fin (N + 1)) :
    finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeStateInBranchField hfan N i) =
      algebraMap (HahnFraction (mgDeg (N + 1)) ℂ)
        (AlgebraicClosure (HahnFraction (mgDeg (N + 1)) ℂ))
        (hahnFractionRamCoordinate r i) := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let B := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  let H := HahnFraction (mgDeg (N + 1)) ℂ
  let AC := AlgebraicClosure H
  let phi : E →ₐ[ℂ] H := finiteCascadeFullHahnStateEmbedding hfan hall r hr
  let phiAC : E →ₐ[ℂ] AC := (IsScalarTower.toAlgHom ℂ H AC).comp phi
  letI : Algebra E AC := phiAC.toAlgebra
  letI : FiniteDimensional E B :=
    finiteDimensional_nonautonomousFiniteCascadeBranchFieldOverState hfan hall h1
  let lift : B →ₐ[E] AC := IsAlgClosed.lift
  change lift (nonautonomousFiniteCascadeStateInBranchField hfan N i) = _
  have hstate : nonautonomousFiniteCascadeStateInBranchField hfan N i =
      algebraMap E B (nonautonomousCascadeStateFamilyInStateField hfan N i) := by
    apply Subtype.ext
    rfl
  rw [hstate, lift.commutes]
  change phiAC (nonautonomousCascadeStateFamilyInStateField hfan N i) = _
  rw [show phiAC = (IsScalarTower.toAlgHom ℂ H AC).comp phi by rfl,
    AlgHom.comp_apply, finiteCascadeFullHahnStateEmbedding_apply_generator]
  rfl

/-! ## Exact local components after the full-state embedding -/

/-- Adjacent rational-state evaluation transported to the algebraic closure of the full-state Hahn
field. -/
noncomputable def finiteCascadeFullHahnLocalRationalStateEval
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (k : Fin N) :
    FirstOrderRationalStateField →ₐ[ℂ]
      AlgebraicClosure (HahnFraction (mgDeg (N + 1)) ℂ) :=
  (finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr).comp
    (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k)

/-- The first local state coordinate is the corresponding full Hahn coordinate. -/
theorem finiteCascadeFullHahnLocalRationalStateEval_first
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (k : Fin N) :
    finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeLocalJet hfan k 0) =
      algebraMap (HahnFraction (mgDeg (N + 1)) ℂ)
        (AlgebraicClosure (HahnFraction (mgDeg (N + 1)) ℂ))
        (hahnFractionRamCoordinate r k.castSucc) := by
  change finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
      (nonautonomousFiniteCascadeStateInBranchField hfan N k.castSucc) = _
  exact finiteCascadeFullHahnBranchAlgebraicClosureEmbedding_apply_state
    hfan hall h1 r hr k.castSucc

/-- The second local state coordinate is the next full Hahn coordinate. -/
theorem finiteCascadeFullHahnLocalRationalStateEval_second
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (k : Fin N) :
    finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeLocalJet hfan k 1) =
      algebraMap (HahnFraction (mgDeg (N + 1)) ℂ)
        (AlgebraicClosure (HahnFraction (mgDeg (N + 1)) ℂ))
        (hahnFractionRamCoordinate r k.succ) := by
  change finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
      (nonautonomousFiniteCascadeStateInBranchField hfan N k.succ) = _
  exact finiteCascadeFullHahnBranchAlgebraicClosureEmbedding_apply_state
    hfan hall h1 r hr k.succ

/-- Every embedded actual velocity remains a root of the exact chosen irreducible Wiman component,
now with both adjacent states realized as genuine Hahn coordinates. -/
theorem finiteCascadeFullHahnVelocity_chosen_component_root
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin (N + 1) → ℕ) (hr : ∀ i, 0 < r i) (k : Fin N) :
    ((firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 k).P).map
      (finiteCascadeFullHahnLocalRationalStateEval
        hfan hall h1 r hr k).toRingHom).IsRoot
      (finiteCascadeFullHahnBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeLocalJet hfan k 2)) := by
  have hroot := Polynomial.IsRoot.map
    (f := (finiteCascadeFullHahnBranchAlgebraicClosureEmbedding
      hfan hall h1 r hr).toRingHom)
    (nonautonomousFiniteCascadeVelocity_chosen_component_root hfan hall h1 k)
  rw [Polynomial.map_map] at hroot
  exact hroot

end

end GaloisForLFunctions.HTGeometry
