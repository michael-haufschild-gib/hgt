import GaloisForLFunctions.HTGeometry.RamifiedPuiseuxCoordinateSpecialization
import GaloisForLFunctions.HTGeometry.CascadeRationalBaseIndependence
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic
import GaloisForLFunctions.HTGeometry.CascadeExactOrder
import GaloisForLFunctions.HTGeometry.FiniteOrderCascadeCompositionDepth

/-!
# Actual autonomous cascades from selected ramified Puiseux branches

This module realizes the selected output-linear autonomous branch inside the actual meromorphic
cascade.  The relative algebraic closure of the positive state field carries the ordinary time
derivation and a coordinate frame.  Agreement on state-field generators forces the selected Hahn
embedding to intertwine these derivations on the entire algebraic branch field.  The resulting
output-jet independence is transferred to the actual meromorphic field and descended from
constants `ℂ` to the rational clock field `ℂ(z)`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher HahnSeries

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

private theorem autonomousActual_deriv_complexConst (c : ℂ) :
    (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := by
  change (algebraMap (RatFunc ℂ) (meroField Set.univ)
    (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  change (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  rw [meroField_deriv_ratfuncToMero]
  have hzero : ratFuncCoordinateDerivation ℂ (algebraMap ℂ (RatFunc ℂ) c) = 0 :=
    (ratFuncCoordinateDerivation_eq_zero_iff
      (algebraMap ℂ (RatFunc ℂ) c)).mpr ⟨c, rfl⟩
  rw [hzero, map_zero]

private theorem autonomousActual_deriv_smul (c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) : (c • x)′ = c • x′ := by
  rw [Algebra.smul_def c x, differential_deriv_mul,
    autonomousActual_deriv_complexConst, zero_mul, zero_add, Algebra.smul_def]

private theorem autonomousActual_deriv_one :
    (1 : meroField (Set.univ : Set ℂ))′ = 0 := by
  have h := autonomousActual_deriv_complexConst (1 : ℂ)
  rwa [map_one] at h

private theorem autonomousActual_deriv_leibniz
    (a b : meroField (Set.univ : Set ℂ)) : (a * b)′ = a • b′ + b • a′ := by
  rw [differential_deriv_mul]
  simp only [smul_eq_mul]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
private noncomputable def autonomousActualComplexDerivation :
    Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) where
  toLinearMap :=
    { toAddHom := { toFun := fun x => x′, map_add' := fun x y => map_add _ x y }
      map_smul' := autonomousActual_deriv_smul }
  map_one_eq_zero' := autonomousActual_deriv_one
  leibniz' := autonomousActual_deriv_leibniz

@[simp] private theorem autonomousActualComplexDerivation_apply
    (x : meroField (Set.univ : Set ℂ)) : autonomousActualComplexDerivation x = x′ := rfl

/-- Reversed positive cascade states: coordinate zero is terminal output. -/
def autonomousRamifiedCascadeState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) : meroField (Set.univ : Set ℂ) :=
  cascadeMero hfan ((Fin.rev k : Fin N).1 + 1)

/-- Field generated over constants by positive cascade states, excluding clock. -/
abbrev AutonomousRamifiedCascadeStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  IntermediateField.adjoin ℂ (Set.range (autonomousRamifiedCascadeState hfan :
    Fin N → meroField (Set.univ : Set ℂ)))

/-- Relative algebraic field containing all autonomous algebraic velocity branches. -/
abbrev AutonomousRamifiedCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :=
  algebraicClosure (AutonomousRamifiedCascadeStateField hfan N)
    (meroField (Set.univ : Set ℂ))

noncomputable def autonomousRamifiedCascadeStateInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) : AutonomousRamifiedCascadeBranchField hfan N :=
  ⟨autonomousRamifiedCascadeState hfan k,
    mem_algebraicClosure_restrictScalars_of_mem _
      (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self k))⟩

@[simp] theorem autonomousRamifiedCascadeStateInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) :
    ((autonomousRamifiedCascadeStateInBranchField hfan k :
      AutonomousRamifiedCascadeBranchField hfan N) : meroField (Set.univ : Set ℂ)) =
      autonomousRamifiedCascadeState hfan k := rfl

/-- Exact data selected by output-linear autonomous branches along an actual cascade. -/
structure AutonomousRamifiedPuiseuxBranchSelection
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) where
  r : Fin N → ℕ
  ramification_pos : ∀ j, 0 < r j
  A : Fin N → HahnFraction (mgDeg N) ℂ
  lambda : Fin N → ℂ
  lambda_ne_zero : ∀ j, lambda j ≠ 0
  hasLead : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)
  velocity : Fin N → AutonomousRamifiedCascadeBranchField hfan N
  state_derivative : ∀ k : Fin N,
    (((∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)), velocity j) :
      AutonomousRamifiedCascadeBranchField hfan N) : meroField (Set.univ : Set ℂ)) =
        cascadeMeroDeriv hfan ((Fin.rev k : Fin N).1 + 1)
  branchMap : AutonomousRamifiedCascadeBranchField hfan N →ₐ[ℂ]
    HahnFraction (mgDeg N) ℂ
  branchMap_state : ∀ k,
    branchMap (autonomousRamifiedCascadeStateInBranchField hfan k) =
      hahnFractionRamCoordinate r k
  branchMap_velocity : ∀ j, branchMap (velocity j) = A j

theorem algebraicIndependent_autonomousRamifiedCascadeState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    AlgebraicIndependent ℂ
      (autonomousRamifiedCascadeState hfan : Fin N → meroField (Set.univ : Set ℂ)) := by
  have hfull := algebraicIndependent_cascadeMero_over_complex hfan hall N
  let e : Fin N → Fin (N + 1) := fun k => ⟨(Fin.rev k : Fin N).1 + 1, by omega⟩
  have he : Function.Injective e := by
    intro a b hab
    have hval : (Fin.rev a : Fin N).1 + 1 = (Fin.rev b : Fin N).1 + 1 :=
      congrArg Fin.val hab
    have hv : (Fin.rev a : Fin N).1 = (Fin.rev b : Fin N).1 :=
      Nat.add_right_cancel hval
    exact Fin.rev_injective (Fin.ext hv)
  have hsub := hfull.comp e he
  convert hsub using 1
  funext k
  rfl

@[simp] theorem autonomousRamifiedCascadeState_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (m : ℕ) :
    autonomousRamifiedCascadeState hfan (0 : Fin (m + 1)) = cascadeMero hfan (m + 1) := by
  simp [autonomousRamifiedCascadeState, Fin.rev]

set_option maxHeartbeats 1000000 in
theorem exists_autonomousRamifiedCascade_lawCoordinateFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (sel : AutonomousRamifiedPuiseuxBranchSelection hfan N) :
    ∃ D : Derivation ℂ (AutonomousRamifiedCascadeBranchField hfan N)
        (AutonomousRamifiedCascadeBranchField hfan N),
      ∃ P : Fin N → Derivation ℂ (AutonomousRamifiedCascadeBranchField hfan N)
        (AutonomousRamifiedCascadeBranchField hfan N),
        (∀ y, ((D y : AutonomousRamifiedCascadeBranchField hfan N) :
          meroField (Set.univ : Set ℂ)) =
            ((y : AutonomousRamifiedCascadeBranchField hfan N) :
              meroField (Set.univ : Set ℂ))′) ∧
        (∀ k, D (autonomousRamifiedCascadeStateInBranchField hfan k) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
            sel.velocity j) ∧
        ∀ j k, P j (autonomousRamifiedCascadeStateInBranchField hfan k) =
          algebraMap ℂ (AutonomousRamifiedCascadeBranchField hfan N)
            (if k = j then -1 else 0) := by
  classical
  let M := meroField (Set.univ : Set ℂ)
  let x : Fin N → M := autonomousRamifiedCascadeState hfan
  let E := AutonomousRamifiedCascadeStateField hfan N
  let B := AutonomousRamifiedCascadeBranchField hfan N
  let xE : Fin N → E := fun k =>
    ⟨x k, IntermediateField.subset_adjoin ℂ (Set.range x) (Set.mem_range_self k)⟩
  letI : CharZero E := (algebraMap E M).charZero
  letI : CharZero B := (algebraMap B M).charZero
  have hstateDeriv : ∀ a : E, autonomousActualComplexDerivation (a : M) ∈ B := by
    intro a
    exact (derivationBase_mem_of_mem_adjoin autonomousActualComplexDerivation
      (M := B.restrictScalars ℂ)
      (fun y hy => by
        rcases hy with ⟨k, rfl⟩
        constructor
        · exact mem_algebraicClosure_restrictScalars_of_mem E
            (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self k))
        · change (autonomousRamifiedCascadeState hfan k)′ ∈ B.restrictScalars ℂ
          have hderiv : (cascadeMero hfan ((Fin.rev k : Fin N).1 + 1))′ =
              cascadeMeroDeriv hfan ((Fin.rev k : Fin N).1 + 1) := by
            have h := differentialJet_one_cascadeMero hfan ((Fin.rev k : Fin N).1 + 1)
            rw [differentialJet_succ, differentialJet_zero] at h
            exact h
          rw [autonomousRamifiedCascadeState, hderiv]
          rw [← sel.state_derivative k]
          exact (∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
            sel.velocity j).property) a.2).2
  have hBstable : ∀ y : M, y ∈ B → autonomousActualComplexDerivation y ∈ B := by
    intro y hy
    apply derivationInt_mem_algebraicClosure E
      (toIntDerivation autonomousActualComplexDerivation) ?_ hy
    intro z hz
    rw [IntermediateField.mem_bot] at hz
    obtain ⟨a, rfl⟩ := hz
    exact hstateDeriv a
  let D : Derivation ℂ B B :=
    restrictDerivation autonomousActualComplexDerivation (B.restrictScalars ℂ) hBstable
  obtain ⟨P₀, hP₀, hcomm₀⟩ :=
    exists_commuting_coordinate_derivations_adjoin x
      (algebraicIndependent_autonomousRamifiedCascadeState hfan hall N)
  obtain ⟨Pplus, hPres, _⟩ :=
    exists_commuting_derivation_extension_family_tower (L := B) P₀ hcomm₀
  let P : Fin N → Derivation ℂ B B := fun j => -(Pplus j)
  refine ⟨D, P, fun _ => rfl, ?_, ?_⟩
  · intro k
    apply Subtype.ext
    change (autonomousRamifiedCascadeState hfan k)′ =
      (((∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
        sel.velocity j) : B) : M)
    have hderiv : (cascadeMero hfan ((Fin.rev k : Fin N).1 + 1))′ =
        cascadeMeroDeriv hfan ((Fin.rev k : Fin N).1 + 1) := by
      have h := differentialJet_one_cascadeMero hfan ((Fin.rev k : Fin N).1 + 1)
      rw [differentialJet_succ, differentialJet_zero] at h
      exact h
    rw [autonomousRamifiedCascadeState, hderiv]
    exact (sel.state_derivative k).symm
  · intro j k
    have hxE : algebraMap E B (xE k) =
        autonomousRamifiedCascadeStateInBranchField hfan k := by
      apply Subtype.ext
      rfl
    rw [← hxE]
    change -(Pplus j (algebraMap E B (xE k))) = _
    rw [hPres, hP₀]
    split_ifs with h
    · subst k
      simp
    · simp

set_option maxHeartbeats 1000000 in
theorem transcendental_clock_over_autonomousRamifiedCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    Transcendental (AutonomousRamifiedCascadeBranchField hfan N)
      (cascadeMero hfan 0) := by
  let M := meroField (Set.univ : Set ℂ)
  let x : Fin N → M := autonomousRamifiedCascadeState hfan
  let E := AutonomousRamifiedCascadeStateField hfan N
  let B := AutonomousRamifiedCascadeBranchField hfan N
  let e : Option (Fin N) → Fin (N + 1) := fun o =>
    o.elim 0 (fun k => ⟨(Fin.rev k : Fin N).1 + 1, by omega⟩)
  have he : Function.Injective e := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · have hval := congrArg Fin.val hab
      dsimp [e] at hval
      omega
    · have hval := congrArg Fin.val hab
      dsimp [e] at hval
      omega
    · congr 1
      have hval : (Fin.rev a : Fin N).1 + 1 = (Fin.rev b : Fin N).1 + 1 :=
        congrArg Fin.val hab
      exact Fin.rev_injective (Fin.ext (Nat.add_right_cancel hval))
  have hfull := algebraicIndependent_cascadeMero_over_complex hfan hall N
  have hoption : AlgebraicIndependent ℂ
      (fun o : Option (Fin N) => o.elim (cascadeMero hfan 0) x) := by
    have hsub := hfull.comp e he
    convert hsub using 1
    funext o
    rcases o with _ | k
    · rfl
    · rfl
  have hx := algebraicIndependent_autonomousRamifiedCascadeState hfan hall N
  have hzAlg : Transcendental (Algebra.adjoin ℂ (Set.range x))
      (cascadeMero hfan 0) := (hx.option_iff_transcendental _).mp hoption
  have hzE : Transcendental E (cascadeMero hfan 0) :=
    (GaloisForLFunctions.transcendental_algebraAdjoin_iff
      (Set.range x) (cascadeMero hfan 0)).mp hzAlg
  intro hzB
  exact hzE (hzB.restrictScalars E)

set_option maxHeartbeats 1000000 in
theorem algebraicIndependent_autonomousRamifiedCascadeOutputJets
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (sel : AutonomousRamifiedPuiseuxBranchSelection hfan (n + 1)) :
    AlgebraicIndependent ℂ (fun i : Fin (n + 1) =>
      differentialJet (i : ℕ) (cascadeMero hfan (n + 1))) := by
  let B := AutonomousRamifiedCascadeBranchField hfan (n + 1)
  let x : Fin (n + 1) → B := autonomousRamifiedCascadeStateInBranchField hfan
  let M := meroField (Set.univ : Set ℂ)
  let xM : Fin (n + 1) → M := autonomousRamifiedCascadeState hfan
  let E := AutonomousRamifiedCascadeStateField hfan (n + 1)
  let xE : Fin (n + 1) → E := fun k =>
    ⟨xM k, IntermediateField.subset_adjoin ℂ (Set.range xM) (Set.mem_range_self k)⟩
  letI : CharZero E := (algebraMap E M).charZero
  letI : CharZero B := (algebraMap B M).charZero
  have hxTop : IntermediateField.adjoin ℂ (Set.range xE) = ⊤ := by
    exact adjoin_range_lift_eq_top xM xM rfl
  obtain ⟨D, P, hDcoe, hDstate, hP⟩ :=
    exists_autonomousRamifiedCascade_lawCoordinateFrame hfan hall sel
  have hmodel : IsRamifiedPuiseuxCascadeSpecialization sel.r sel.A sel.branchMap
      D P (x 0) := by
    refine ⟨sel.branchMap_state 0, ?_, ?_⟩
    · apply derivation_map_eq_of_isAlgebraic_tower_adjoin xE hxTop
      intro k
      have hxEB : algebraMap E B (xE k) = x k := by
        apply Subtype.ext
        rfl
      rw [hxEB, hDstate, map_prod]
      simp only [sel.branchMap_velocity]
      rw [sel.branchMap_state,
        hahnFractionRamCascadeDerivation_coordinate sel.r sel.ramification_pos]
      rfl
    · intro j
      apply derivation_map_eq_of_isAlgebraic_tower_adjoin xE hxTop
      intro k
      have hxEB : algebraMap E B (xE k) = x k := by
        apply Subtype.ext
        rfl
      rw [hxEB, hP, sel.branchMap.commutes, sel.branchMap_state,
        hahnFractionRamPartial_coordinate sel.r sel.ramification_pos]
  have hsource : AlgebraicIndependent ℂ (fun i : Fin (n + 1) =>
      ((D : B → B)^[(i : ℕ)]) (x 0)) :=
    algebraicIndependent_cascadeOutputJets_of_ramifiedPuiseuxSpecialization
      sel.r sel.ramification_pos sel.A sel.lambda sel.lambda_ne_zero sel.hasLead
      sel.branchMap D P (x 0) hmodel
  have hiterate : ∀ (q : ℕ) (y : B),
      ((((D : B → B)^[q]) y : B) : meroField (Set.univ : Set ℂ)) =
        differentialJet q ((y : B) : meroField (Set.univ : Set ℂ)) := by
    intro q
    induction q with
    | zero =>
        intro y
        simp [differentialJet_zero]
    | succ q ih =>
        intro y
        rw [Function.iterate_succ_apply', differentialJet_succ, hDcoe, ih]
  have hmapped := hsource.map'
    (f := (B.restrictScalars ℂ).toSubalgebra.val) Subtype.val_injective
  convert hmapped using 1
  funext i
  symm
  change ((((D : B → B)^[(i : ℕ)]) (x 0) : B) :
      meroField (Set.univ : Set ℂ)) = _
  rw [hiterate]
  congr 1

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem algebraicIndependent_ratFunc_autonomousRamifiedCascadeOutputJets
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (sel : AutonomousRamifiedPuiseuxBranchSelection hfan (n + 1)) :
    AlgebraicIndependent (RatFunc ℂ) (fun i : Fin (n + 1) =>
      differentialJet (i : ℕ) (cascadeMero hfan (n + 1))) := by
  let M := meroField (Set.univ : Set ℂ)
  let B := AutonomousRamifiedCascadeBranchField hfan (n + 1)
  let jets : Fin (n + 1) → M := fun i =>
    differentialJet (i : ℕ) (cascadeMero hfan (n + 1))
  have hjets : AlgebraicIndependent ℂ jets :=
    algebraicIndependent_autonomousRamifiedCascadeOutputJets hfan hall sel
  obtain ⟨D, P, hDcoe, _, _⟩ :=
    exists_autonomousRamifiedCascade_lawCoordinateFrame hfan hall sel
  let x : Fin (n + 1) → B := autonomousRamifiedCascadeStateInBranchField hfan
  have hiterate : ∀ (q : ℕ) (y : B),
      ((((D : B → B)^[q]) y : B) : M) = differentialJet q ((y : B) : M) := by
    intro q
    induction q with
    | zero =>
        intro y
        simp [differentialJet_zero]
    | succ q ih =>
        intro y
        rw [Function.iterate_succ_apply', differentialJet_succ, hDcoe, ih]
  let J : IntermediateField ℂ M := IntermediateField.adjoin ℂ (Set.range jets)
  have hJle : J ≤ B.restrictScalars ℂ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    change jets i ∈ B.restrictScalars ℂ
    rw [show jets i = ((((D : B → B)^[(i : ℕ)]) (x 0) : B) : M) by
      rw [hiterate]
      congr 1]
    exact ((((D : B → B)^[(i : ℕ)]) (x 0) : B).property)
  letI : Algebra J B := (IntermediateField.inclusion hJle).toAlgebra
  letI : IsScalarTower J B M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hclockB :=
    transcendental_clock_over_autonomousRamifiedCascadeBranchField hfan hall (n + 1)
  have hclockJ : Transcendental J (cascadeMero hfan 0) :=
    hclockB.restrictScalars (algebraMap J B).injective
  have hclockAlg : Transcendental (Algebra.adjoin ℂ (Set.range jets))
      (cascadeMero hfan 0) :=
    (GaloisForLFunctions.transcendental_algebraAdjoin_iff
      (Set.range jets) (cascadeMero hfan 0)).mpr hclockJ
  have hjoint : AlgebraicIndependent ℂ
      (fun o : Option (Fin (n + 1)) => o.elim (cascadeMero hfan 0) jets) :=
    (hjets.option_iff_transcendental (cascadeMero hfan 0)).mpr hclockAlg
  exact algebraicIndependent_over_ratFunc_of_clock_option hfan jets hjoint

/-- **Exact autonomous unit differential-order cost.**  Selecting the card's stated output-linear
ramified Puiseux branch along every analytic cascade state forces exact order equal to depth. -/
theorem exactDifferentialOrder_entireCascade_of_autonomousRamifiedPuiseuxBranchSelection
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (sel : AutonomousRamifiedPuiseuxBranchSelection hfan (n + 1)) :
    ExactDifferentialOrder (entireCascade f (n + 1)) (n + 1) := by
  apply exactDifferentialOrder_entireCascade_of_transcendental hfan hall h1
  exact algebraicIndependent_ratFunc_autonomousRamifiedCascadeOutputJets hfan hall sel

/-- **Complete selected-branch autonomous unit-cost law.**  Under the card's finite positive-lower
order assumptions, differential order and positive composition depth both equal displayed cascade
length. -/
theorem exactOrder_and_compositionDepth_autonomousRamifiedPuiseuxCascade
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hfin : ∀ k, k < n + 1 → FiniteOrderEnvelope (f k))
    (hpos : ∀ k, k < n + 1 → PositiveLowerOrder (f k))
    (sel : AutonomousRamifiedPuiseuxBranchSelection hfan (n + 1)) :
    ExactDifferentialOrder (entireCascade f (n + 1)) (n + 1) ∧
      CompositionDepthAtLeast (entireCascade f (n + 1)) (n + 1) ∧
      ¬ CompositionDepthAtLeast (entireCascade f (n + 1)) (n + 2) := by
  refine ⟨exactDifferentialOrder_entireCascade_of_autonomousRamifiedPuiseuxBranchSelection
    hfan hall h1 sel, ?_⟩
  simpa [Nat.add_assoc] using compositionDepth_finiteOrder_positiveCascade (n + 1)
    (fun k hk => (hall k).1)
    (fun k hk => exists_ne_of_transcendentalEntire (hall k)) hfin hpos

end

end GaloisForLFunctions.HTGeometry
