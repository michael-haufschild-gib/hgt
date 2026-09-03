import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxBranchField

/-!
# Algebraic embedding of the finite nonautonomous branch field

The actual clock and `N` cascade states form a free rational function field of rank `N + 1`
over `ℂ`.  The rational Hahn clock and the `N` ramified coordinate monomials form another such
family.  This identifies the two state fields generator by generator.

The finitely many actual derivative branches are algebraic over the actual state field, so the
state embedding extends unconditionally to the algebraic closure of the Hahn fraction field.
This is the exact algebraic part of common branch selection.  It does not assert that the extended
branch values lie in the Hahn field itself, nor that the arbitrary algebraic extension preserves
the Hahn valuation or any prescribed leading coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-! ## Free Hahn coordinate frame -/

/-- The ramified Hahn coordinate monomials are algebraically independent over their coefficient
field.  Positivity of each ramification index makes their partial-derivative Jacobian a nonzero
diagonal matrix. -/
theorem algebraicIndependent_hahnFractionRamCoordinateBase
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) :
    AlgebraicIndependent K (hahnFractionRamCoordinateBase K r) := by
  apply algebraicIndependent_of_hahnFractionRamGradientMatrixBase_det_ne_zero r
  have hmatrix : hahnFractionRamGradientMatrixBase K r
      (hahnFractionRamCoordinateBase K r) =
      Matrix.diagonal (fun _ : Fin N =>
        algebraMap K (HahnFraction (mgDeg N) K) (-1)) := by
    ext i j
    rw [hahnFractionRamGradientMatrixBase,
      hahnFractionRamPartialBase_coordinate K r hr]
    by_cases hji : i = j
    · subst i
      simp
    · simp [hji]
  rw [hmatrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    (map_ne_zero (algebraMap K (HahnFraction (mgDeg N) K))).mpr (by simp)

/-- Clock followed by positive cascade-state coordinates in their natural source order.  The Hahn
coordinates are reversed because the nonautonomous cascade vector field numbers coordinate zero
from the terminal output. -/
noncomputable def nonautonomousHahnClockCoordinateFamily
    {C : Type*} [Field C] [CharZero C] {N : ℕ}
    (r : Fin N → ℕ) : Fin (N + 1) → HahnFraction (mgDeg N) (RatFunc C) :=
  fun i => Fin.cases
    (algebraMap (RatFunc C) (HahnFraction (mgDeg N) (RatFunc C)) RatFunc.X)
    (fun k => hahnFractionRamCoordinateBase (RatFunc C) r (Fin.rev k)) i

@[simp] theorem nonautonomousHahnClockCoordinateFamily_zero
    {C : Type*} [Field C] [CharZero C] {N : ℕ} (r : Fin N → ℕ) :
    nonautonomousHahnClockCoordinateFamily (C := C) r 0 =
      algebraMap (RatFunc C) (HahnFraction (mgDeg N) (RatFunc C)) RatFunc.X := rfl

@[simp] theorem nonautonomousHahnClockCoordinateFamily_succ
    {C : Type*} [Field C] [CharZero C] {N : ℕ} (r : Fin N → ℕ) (k : Fin N) :
    nonautonomousHahnClockCoordinateFamily (C := C) r k.succ =
      hahnFractionRamCoordinateBase (RatFunc C) r (Fin.rev k) := rfl

/-- The rational Hahn clock and all ramified state coordinates are jointly algebraically
independent over the constant field. -/
theorem algebraicIndependent_nonautonomousHahnClockCoordinateFamily
    {C : Type*} [Field C] [CharZero C] {N : ℕ}
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) :
    AlgebraicIndependent C (nonautonomousHahnClockCoordinateFamily (C := C) r) := by
  let H := HahnFraction (mgDeg N) (RatFunc C)
  let g : Fin (N + 1) → H := nonautonomousHahnClockCoordinateFamily (C := C) r
  let D : Fin (N + 1) → H → H := fun i =>
    Fin.cases
      (hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C) : H → H)
      (fun k => (hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k) : H → H)) i
  let d : Fin (N + 1) → H := fun i => Fin.cases 1 (fun _ => -1) i
  let M : Matrix (Fin (N + 1)) (Fin (N + 1)) H := Matrix.diagonal d
  change AlgebraicIndependent C g
  refine algebraicIndependent_of_domain_jacobian g D ?_ ?_ ?_ M ?_ ?_
  · intro i a b
    refine Fin.cases ?_ (fun k => ?_) i
    · change hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C) (a + b) = _
      exact map_add _ a b
    · change hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k) (a + b) = _
      exact map_add _ a b
  · intro i a b
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [D, Fin.cases_zero, smul_eq_mul, mul_comm] using
        (hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C)).leibniz a b
    · simpa only [D, Fin.cases_succ, smul_eq_mul, mul_comm] using
        (hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)).leibniz a b
  · intro i c
    refine Fin.cases ?_ (fun k => ?_) i
    · change (hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C) :
        Derivation C H H) (algebraMap C H c) = 0
      exact (hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C) :
        Derivation C H H).map_algebraMap c
    · change hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)
        (algebraMap C H c) = 0
      calc
        _ = hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)
            (algebraMap (RatFunc C) H (algebraMap C (RatFunc C) c)) := by rfl
        _ = 0 := (hahnFractionRamPartialBase (RatFunc C) r
          (Fin.rev k)).map_algebraMap (algebraMap C (RatFunc C) c)
  · rw [show M = Matrix.diagonal d by rfl, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [d]
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j
      · change hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C)
          (algebraMap (RatFunc C) H RatFunc.X) = _
        rw [hahnFractionCoefficientDerivation_coeffAlgebraMap,
          show RatFunc.X = algebraMap (Polynomial C) (RatFunc C) Polynomial.X by
            rw [RatFunc.algebraMap_X],
          ratFuncCoordinateDerivation_algebraMap]
        simp [M, d]
      · change hahnFractionCoefficientDerivation (ratFuncCoordinateDerivation C)
          (hahnFractionRamCoordinateBase (RatFunc C) r (Fin.rev l)) = _
        rw [hahnFractionCoefficientDerivation_coordinateBase]
        change 0 = Matrix.diagonal d 0 l.succ
        rw [Matrix.diagonal_apply_ne d (by
          intro h
          have hv := congrArg Fin.val h
          simp at hv)]
    · refine Fin.cases ?_ (fun l => ?_) j
      · change hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)
          (algebraMap (RatFunc C) H RatFunc.X) = _
        rw [(hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)).map_algebraMap]
        simp [M]
      · change hahnFractionRamPartialBase (RatFunc C) r (Fin.rev k)
          (hahnFractionRamCoordinateBase (RatFunc C) r (Fin.rev l)) = _
        rw [hahnFractionRamPartialBase_coordinate (RatFunc C) r hr]
        by_cases hlk : l = k
        · subst l
          simp [M, d]
        · have hrev : Fin.rev l ≠ Fin.rev k := fun h => hlk (Fin.rev_injective h)
          have hsucc : k.succ ≠ l.succ := by
            intro h
            apply hlk
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa using hv.symm
          change _ = Matrix.diagonal d k.succ l.succ
          rw [Matrix.diagonal_apply_ne d hsucc]
          simp [hrev]

/-! ## Actual state field -/

/-- Actual clock and states, corestricted to their generated state field. -/
noncomputable def nonautonomousCascadeStateFamilyInStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : Fin (N + 1) → NonautonomousRamifiedCascadeStateField hfan N :=
  fun i => ⟨cascadeMero hfan i,
    IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩

/-- Corestricting the free actual state family to its own field preserves algebraic
independence. -/
theorem algebraicIndependent_nonautonomousCascadeStateFamilyInStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    AlgebraicIndependent ℂ (nonautonomousCascadeStateFamilyInStateField hfan N) := by
  have hambient := algebraicIndependent_cascadeMero_over_complex hfan hall N
  rw [algebraicIndependent_iff_injective_aeval] at hambient ⊢
  intro p q hpq
  apply hambient
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let M := meroField (Set.univ : Set ℂ)
  let incl : E →ₐ[ℂ] M := IsScalarTower.toAlgHom ℂ E M
  have hnatural : incl.comp
      (MvPolynomial.aeval (nonautonomousCascadeStateFamilyInStateField hfan N)) =
      MvPolynomial.aeval (fun i : Fin (N + 1) => cascadeMero hfan i) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change ((nonautonomousCascadeStateFamilyInStateField hfan N i : E) : M) =
      cascadeMero hfan i
    rfl
  have hmap := congrArg incl hpq
  change (incl.comp
      (MvPolynomial.aeval (nonautonomousCascadeStateFamilyInStateField hfan N))) p =
    (incl.comp
      (MvPolynomial.aeval (nonautonomousCascadeStateFamilyInStateField hfan N))) q at hmap
  rw [hnatural] at hmap
  exact hmap

/-- The corestricted actual family generates its whole state field. -/
theorem adjoin_range_nonautonomousCascadeStateFamilyInStateField_eq_top
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    IntermediateField.adjoin ℂ
      (Set.range (nonautonomousCascadeStateFamilyInStateField hfan N)) = ⊤ := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let J := IntermediateField.adjoin ℂ
    (Set.range (nonautonomousCascadeStateFamilyInStateField hfan N))
  apply top_unique
  intro a ha
  change a ∈ J
  have haE : (a : meroField (Set.univ : Set ℂ)) ∈ E := a.property
  let p : ∀ z, z ∈ E → Prop := fun z hz => (⟨z, hz⟩ : E) ∈ J
  change p (a : meroField (Set.univ : Set ℂ)) haE
  refine IntermediateField.adjoin_induction ℂ (p := p) ?_ ?_ ?_ ?_ ?_ haE
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    simpa [p, J, E, nonautonomousCascadeStateFamilyInStateField] using
      (IntermediateField.subset_adjoin ℂ
        (Set.range (nonautonomousCascadeStateFamilyInStateField hfan N))
        (Set.mem_range_self i))
  · intro z
    simp [p, J, E]
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using! J.add_mem hzJ hwJ
  · intro z hz hzJ
    simpa only [p, Subtype.coe_eta] using! J.inv_mem hzJ
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using! J.mul_mem hzJ hwJ

/-! ## Generator-preserving state and branch embeddings -/

/-- Generator-preserving embedding of actual cascade state field into generic rational Hahn
field. -/
noncomputable def nonautonomousRamifiedCascadeStateEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) :
    NonautonomousRamifiedCascadeStateField hfan N →ₐ[ℂ]
      HahnFraction (mgDeg N) (RatFunc ℂ) := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let H := HahnFraction (mgDeg N) (RatFunc ℂ)
  let xE : Fin (N + 1) → E := nonautonomousCascadeStateFamilyInStateField hfan N
  let xH : Fin (N + 1) → H := nonautonomousHahnClockCoordinateFamily (C := ℂ) r
  have hxE : AlgebraicIndependent ℂ xE :=
    algebraicIndependent_nonautonomousCascadeStateFamilyInStateField hfan hall N
  have hxH : AlgebraicIndependent ℂ xH :=
    algebraicIndependent_nonautonomousHahnClockCoordinateFamily r hr
  have htop : IntermediateField.adjoin ℂ (Set.range xE) = ⊤ :=
    adjoin_range_nonautonomousCascadeStateFamilyInStateField_eq_top hfan N
  let sourceEquiv : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) ≃ₐ[ℂ] E :=
    (hxE.aevalEquivField.trans (IntermediateField.equivOfEq htop)).trans
      IntermediateField.topEquiv
  let targetLift : FractionRing (MvPolynomial (Fin (N + 1)) ℂ) →ₐ[ℂ] H :=
    IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.mp hxH)
  exact targetLift.comp sourceEquiv.symm.toAlgHom

set_option maxHeartbeats 1000000 in
theorem nonautonomousRamifiedCascadeStateEmbedding_apply_generator
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) (i : Fin (N + 1)) :
    nonautonomousRamifiedCascadeStateEmbedding hfan hall r hr
        (nonautonomousCascadeStateFamilyInStateField hfan N i) =
      nonautonomousHahnClockCoordinateFamily (C := ℂ) r i := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let H := HahnFraction (mgDeg N) (RatFunc ℂ)
  let xE : Fin (N + 1) → E := nonautonomousCascadeStateFamilyInStateField hfan N
  let xH : Fin (N + 1) → H := nonautonomousHahnClockCoordinateFamily (C := ℂ) r
  have hxE : AlgebraicIndependent ℂ xE :=
    algebraicIndependent_nonautonomousCascadeStateFamilyInStateField hfan hall N
  have hxH : AlgebraicIndependent ℂ xH :=
    algebraicIndependent_nonautonomousHahnClockCoordinateFamily r hr
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
/-- The finite actual derivative-branch field embeds in the algebraic closure of the generic Hahn
field, extending the generator-preserving state embedding.  No branch-selection hypothesis is
used. -/
noncomputable def nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) :
    NonautonomousFiniteCascadeBranchField hfan N →ₐ[ℂ]
      AlgebraicClosure (HahnFraction (mgDeg N) (RatFunc ℂ)) := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let B := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  let H := HahnFraction (mgDeg N) (RatFunc ℂ)
  let AC := AlgebraicClosure H
  let phi : E →ₐ[ℂ] H := nonautonomousRamifiedCascadeStateEmbedding hfan hall r hr
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
/-- The extended finite-branch embedding sends every actual clock/state generator to its prescribed
generic Hahn clock/state coordinate. -/
theorem nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding_apply_state
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeStateInBranchField hfan N i) =
      algebraMap (HahnFraction (mgDeg N) (RatFunc ℂ))
          (AlgebraicClosure (HahnFraction (mgDeg N) (RatFunc ℂ)))
        (nonautonomousHahnClockCoordinateFamily (C := ℂ) r i) := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let B := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  let H := HahnFraction (mgDeg N) (RatFunc ℂ)
  let AC := AlgebraicClosure H
  let phi : E →ₐ[ℂ] H := nonautonomousRamifiedCascadeStateEmbedding hfan hall r hr
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
    AlgHom.comp_apply, nonautonomousRamifiedCascadeStateEmbedding_apply_generator]
  rfl

end

end GaloisForLFunctions.HTGeometry
