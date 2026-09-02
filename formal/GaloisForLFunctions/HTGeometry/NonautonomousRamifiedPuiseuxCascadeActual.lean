import GaloisForLFunctions.HTGeometry.RamifiedMultiGradedNewtonModelBase
import GaloisForLFunctions.HTGeometry.UniversalFirstOrderEntireCascadeUnitCost
import GaloisForLFunctions.HTGeometry.CascadeExactOrder
import GaloisForLFunctions.HTGeometry.FiniteOrderCascadeCompositionDepth

/-!
# Actual nonautonomous cascades from selected ramified Puiseux branches

This module realizes the differential-coefficient Hahn observability theorem in the actual global
meromorphic field.  The Puiseux expansion map is part of the card's stated analytic branch-selection
condition.  Its compatibility with time differentiation is derived from its values on the clock,
states, and selected velocity branches; it is not assumed.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher HahnSeries

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

private theorem nonautonomousActual_deriv_complexConst (c : ℂ) :
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

private theorem nonautonomousActual_deriv_smul (c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) : (c • x)′ = c • x′ := by
  rw [Algebra.smul_def c x, differential_deriv_mul,
    nonautonomousActual_deriv_complexConst, zero_mul, zero_add, Algebra.smul_def]

private theorem nonautonomousActual_deriv_one :
    (1 : meroField (Set.univ : Set ℂ))′ = 0 := by
  have h := nonautonomousActual_deriv_complexConst (1 : ℂ)
  rwa [map_one] at h

private theorem nonautonomousActual_deriv_leibniz
    (a b : meroField (Set.univ : Set ℂ)) : (a * b)′ = a • b′ + b • a′ := by
  rw [differential_deriv_mul]
  simp only [smul_eq_mul]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
private noncomputable def nonautonomousActualComplexDerivation :
    Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) where
  toLinearMap :=
    { toAddHom := { toFun := fun x => x′, map_add' := fun x y => map_add _ x y }
      map_smul' := nonautonomousActual_deriv_smul }
  map_one_eq_zero' := nonautonomousActual_deriv_one
  leibniz' := nonautonomousActual_deriv_leibniz

@[simp] private theorem nonautonomousActualComplexDerivation_apply
    (x : meroField (Set.univ : Set ℂ)) : nonautonomousActualComplexDerivation x = x′ := rfl

/-- Full actual state field: clock together with every positive state through level `N`. -/
abbrev NonautonomousRamifiedCascadeStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (N : ℕ) :=
  IntermediateField.adjoin ℂ
    (Set.range (fun i : Fin (N + 1) => cascadeMero hfan i))

/-- Relative algebraic field containing all actual selected derivative branches. -/
abbrev NonautonomousRamifiedCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (N : ℕ) :=
  algebraicClosure (NonautonomousRamifiedCascadeStateField hfan N)
    (meroField (Set.univ : Set ℂ))

/-- Reversed positive cascade states, so coordinate zero is the terminal output. -/
def nonautonomousRamifiedCascadeState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) : meroField (Set.univ : Set ℂ) :=
  cascadeMero hfan ((Fin.rev k : Fin N).1 + 1)

/-- Actual clock as an element of the algebraic branch field. -/
noncomputable def nonautonomousRamifiedClockInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousRamifiedCascadeBranchField hfan N :=
  ⟨cascadeMero hfan 0, mem_algebraicClosure_restrictScalars_of_mem _
    (IntermediateField.subset_adjoin ℂ _
      (Set.mem_range_self (⟨0, by omega⟩ : Fin (N + 1))))⟩

/-- Reversed positive state inside the actual algebraic branch field. -/
noncomputable def nonautonomousRamifiedCascadeStateInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) : NonautonomousRamifiedCascadeBranchField hfan N :=
  ⟨nonautonomousRamifiedCascadeState hfan k,
    mem_algebraicClosure_restrictScalars_of_mem _
      (IntermediateField.subset_adjoin ℂ _
        (Set.mem_range_self
          (⟨(Fin.rev k : Fin N).1 + 1, by omega⟩ : Fin (N + 1))))⟩

@[simp] theorem nonautonomousRamifiedClockInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    ((nonautonomousRamifiedClockInBranchField hfan N :
      NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ) =
      cascadeMero hfan 0 := rfl

@[simp] theorem nonautonomousRamifiedCascadeStateInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (k : Fin N) :
    ((nonautonomousRamifiedCascadeStateInBranchField hfan k :
      NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ) =
      nonautonomousRamifiedCascadeState hfan k := rfl

/-- The rational clock field maps into the full actual branch field. -/
noncomputable def nonautonomousRamifiedRatFuncToBranch
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : RatFunc ℂ →+* NonautonomousRamifiedCascadeBranchField hfan N :=
  (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).codRestrict
    (NonautonomousRamifiedCascadeBranchField hfan N) (fun q =>
      mem_algebraicClosure_restrictScalars_of_mem _ (by
        have hle : IntermediateField.adjoin ℂ {cascadeMero hfan 0} ≤
            NonautonomousRamifiedCascadeStateField hfan N := by
          rw [IntermediateField.adjoin_le_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact IntermediateField.subset_adjoin ℂ _
            (Set.mem_range_self (⟨0, by omega⟩ : Fin (N + 1)))
        exact hle (algebraMap_ratFunc_mem_adjoin_cascadeMero_zero hfan q)))

/-- Canonical rational-clock algebra on the actual branch field. -/
noncomputable instance nonautonomousRamifiedBranchRatFuncAlgebra
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : Algebra (RatFunc ℂ) (NonautonomousRamifiedCascadeBranchField hfan N) :=
  (nonautonomousRamifiedRatFuncToBranch hfan N).toAlgebra

noncomputable instance nonautonomousRamifiedBranchScalarTower
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : IsScalarTower ℂ (RatFunc ℂ)
      (NonautonomousRamifiedCascadeBranchField hfan N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[simp] theorem nonautonomousRamifiedBranch_algebraMap_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (q : RatFunc ℂ) :
    ((algebraMap (RatFunc ℂ) (NonautonomousRamifiedCascadeBranchField hfan N) q :
      NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ) =
      algebraMap (RatFunc ℂ) (meroField Set.univ) q := rfl

/-- The rational-function coordinate is the actual clock in the branch field. -/
theorem nonautonomousRamifiedBranch_algebraMap_X
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    algebraMap (RatFunc ℂ) (NonautonomousRamifiedCascadeBranchField hfan N) RatFunc.X =
      nonautonomousRamifiedClockInBranchField hfan N := by
  apply Subtype.ext
  rw [nonautonomousRamifiedBranch_algebraMap_coe,
    nonautonomousRamifiedClockInBranchField_coe, cascadeMero_zero]

/-- Exact data supplied by analytic selection of output-linear nonautonomous branches.  Velocity
elements live in the actual relative algebraic state field, while `branchMap` is their common
Puiseux expansion at the nested infinity corner. -/
structure NonautonomousRamifiedPuiseuxBranchSelection
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) where
  r : Fin N → ℕ
  ramification_pos : ∀ j, 0 < r j
  A : Fin N → HahnFraction (mgDeg N) (RatFunc ℂ)
  lambda : Fin N → RatFunc ℂ
  lambda_ne_zero : ∀ j, lambda j ≠ 0
  hasLead : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)
  velocity : Fin N → NonautonomousRamifiedCascadeBranchField hfan N
  state_derivative : ∀ k : Fin N,
    (((∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)), velocity j) :
      NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ) =
        cascadeMeroDeriv hfan ((Fin.rev k : Fin N).1 + 1)
  branchMap : NonautonomousRamifiedCascadeBranchField hfan N →ₐ[RatFunc ℂ]
    HahnFraction (mgDeg N) (RatFunc ℂ)
  branchMap_state : ∀ k,
    branchMap (nonautonomousRamifiedCascadeStateInBranchField hfan k) =
      hahnFractionRamCoordinateBase (RatFunc ℂ) r k
  branchMap_velocity : ∀ j, branchMap (velocity j) = A j

/-- The total differential-coefficient Hahn derivation sends the rational clock to one. -/
theorem hahnFractionRamCascadeDifferentialDerivation_algebraMap_X
    {N : ℕ} (r : Fin N → ℕ)
    (A : Fin N → HahnFraction (mgDeg N) (RatFunc ℂ)) :
    hahnFractionRamCascadeDifferentialDerivation ℂ (RatFunc ℂ)
        (ratFuncCoordinateDerivation ℂ) r A
        (algebraMap (RatFunc ℂ) (HahnFraction (mgDeg N) (RatFunc ℂ)) RatFunc.X) = 1 := by
  rw [hahnFractionRamCascadeDifferentialDerivation_coeffAlgebraMap,
    show RatFunc.X = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X by
      rw [RatFunc.algebraMap_X],
    ratFuncCoordinateDerivation_algebraMap]
  simp

/-- Ordinary meromorphic differentiation preserves the actual relative algebraic branch field. -/
theorem nonautonomousActualComplexDerivation_mem_branchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ NonautonomousRamifiedCascadeBranchField hfan N) :
    nonautonomousActualComplexDerivation y ∈
      NonautonomousRamifiedCascadeBranchField hfan N := by
  let M := meroField (Set.univ : Set ℂ)
  let x : Fin (N + 1) → M := fun i => cascadeMero hfan i
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let xE : Fin (N + 1) → E := fun i =>
    ⟨x i, IntermediateField.subset_adjoin ℂ (Set.range x) (Set.mem_range_self i)⟩
  let B := NonautonomousRamifiedCascadeBranchField hfan N
  letI : CharZero E := (algebraMap E M).charZero
  letI : CharZero B := (algebraMap B M).charZero
  have hstate : ∀ a : E, nonautonomousActualComplexDerivation (a : M) ∈ B := by
    intro a
    exact (derivationBase_mem_of_mem_adjoin nonautonomousActualComplexDerivation
      (M := B.restrictScalars ℂ)
      (fun z hz => by
        rcases hz with ⟨i, rfl⟩
        constructor
        · exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (xE i))
        · change (cascadeMero hfan i)′ ∈ B.restrictScalars ℂ
          rw [← differentialJet_zero (cascadeMero hfan i), ← differentialJet_succ,
            differentialJet_one_cascadeMero]
          exact cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure
            hfan hall h1 i)
      a.2).2
  apply derivationInt_mem_algebraicClosure E
    (toIntDerivation nonautonomousActualComplexDerivation) ?_ hy
  intro z hz
  rw [IntermediateField.mem_bot] at hz
  obtain ⟨a, rfl⟩ := hz
  exact hstate a

/-- Ordinary time derivation restricted to the actual algebraic branch field. -/
noncomputable def nonautonomousRamifiedCascadeDerivation
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Derivation ℂ (NonautonomousRamifiedCascadeBranchField hfan N)
      (NonautonomousRamifiedCascadeBranchField hfan N) :=
  restrictDerivation nonautonomousActualComplexDerivation
    ((NonautonomousRamifiedCascadeBranchField hfan N).restrictScalars ℂ)
    (fun _ hy => nonautonomousActualComplexDerivation_mem_branchField hfan hall h1 hy)

@[simp] theorem nonautonomousRamifiedCascadeDerivation_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (y : NonautonomousRamifiedCascadeBranchField hfan N) :
    ((nonautonomousRamifiedCascadeDerivation hfan hall h1 y :
      NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ) =
      ((y : NonautonomousRamifiedCascadeBranchField hfan N) : meroField Set.univ)′ := rfl

/-- Restricted actual derivation sends the clock to one. -/
theorem nonautonomousRamifiedCascadeDerivation_clock
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousRamifiedCascadeDerivation hfan hall h1
        (nonautonomousRamifiedClockInBranchField hfan N) = 1 := by
  apply Subtype.ext
  rw [nonautonomousRamifiedCascadeDerivation_coe]
  change (cascadeMero hfan 0)′ = (1 : meroField Set.univ)
  rw [← differentialJet_zero (cascadeMero hfan 0), ← differentialJet_succ,
    differentialJet_one_cascadeMero, cascadeMeroDeriv_zero]

/-- Restricted actual derivation obeys the selected suffix-product cascade law. -/
theorem nonautonomousRamifiedCascadeDerivation_state
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (sel : NonautonomousRamifiedPuiseuxBranchSelection hfan N) (k : Fin N) :
    nonautonomousRamifiedCascadeDerivation hfan hall h1
        (nonautonomousRamifiedCascadeStateInBranchField hfan k) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)), sel.velocity j := by
  apply Subtype.ext
  rw [nonautonomousRamifiedCascadeDerivation_coe]
  change (cascadeMero hfan ((Fin.rev k : Fin N).1 + 1))′ = _
  rw [← differentialJet_zero (cascadeMero hfan ((Fin.rev k : Fin N).1 + 1)),
    ← differentialJet_succ, differentialJet_one_cascadeMero]
  exact (sel.state_derivative k).symm

end

end GaloisForLFunctions.HTGeometry
