import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeBranchTower
import GaloisForLFunctions.HTGeometry.ValuationSubringExtension

/-!
# Algebraic retention in the terminal cascade valuation tower

A terminal valuation is first constructed to be trivial on the lower rational state field.  The
whole lower actual branch field is algebraic over that state field.  Integrally closedness of a
valuation ring therefore forces every lower branch element into the valuation ring.  In
particular the lower actual component, not merely its rational state coordinates, injects into the
residue field for the next inward refinement.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- Canonical map from a depth-`N` rational state field into the depth-`N` finite actual branch
field, with the latter regarded over complex constants. -/
noncomputable def nonautonomousFiniteCascadeStateToBranch
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    NonautonomousRamifiedCascadeStateField hfan N →+*
      NonautonomousFiniteCascadeBranchField hfan N :=
  (algebraMap (NonautonomousRamifiedCascadeStateField hfan N)
      (meroField (Set.univ : Set ℂ))).codRestrict
    (NonautonomousFiniteCascadeBranchField hfan N) (fun x =>
      IntermediateField.algebraMap_mem
        (NonautonomousFiniteCascadeBranchFieldOverState hfan N) x)

/-- Canonical map from the lower rational state field directly into the successor finite branch
field. -/
noncomputable def nonautonomousFiniteCascadeLowerStateInclusionSucc
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    NonautonomousRamifiedCascadeStateField hfan N →+*
      NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
  (nonautonomousFiniteCascadeBranchInclusionSucc hfan N).toRingHom.comp
    (nonautonomousFiniteCascadeStateToBranch hfan N)

/-- If a valuation on a successor branch field is trivial on the lower rational state field, it
contains the entire lower actual branch field. -/
theorem nonautonomousFiniteCascadeBranchInclusionSucc_mem_of_lowerState_mem
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    {N : ℕ} (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (A : ValuationSubring (NonautonomousFiniteCascadeBranchField hfan (N + 1)))
    (hstate : ∀ x : NonautonomousRamifiedCascadeStateField hfan N,
      nonautonomousFiniteCascadeLowerStateInclusionSucc hfan N x ∈ A) :
    ∀ y : NonautonomousFiniteCascadeBranchField hfan N,
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N y ∈ A := by
  let F := NonautonomousRamifiedCascadeStateField hfan N
  let L := NonautonomousFiniteCascadeBranchField hfan N
  let K := NonautonomousFiniteCascadeBranchField hfan (N + 1)
  let e : F →+* L := nonautonomousFiniteCascadeStateToBranch hfan N
  let g : L →+* K :=
    (nonautonomousFiniteCascadeBranchInclusionSucc hfan N).toRingHom
  let q : F →+* K := g.comp e
  letI : Algebra F L := e.toAlgebra
  letI : Algebra L K := g.toAlgebra
  letI : Algebra F K := q.toAlgebra
  letI : IsScalarTower F L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional F L :=
    finiteDimensional_nonautonomousFiniteCascadeBranchFieldOverState hfan hall h1
  apply valuationSubring_contains_algebraic_tower (F := F) (L := L) (K := K) A
  · exact hstate
  · infer_instance

/-- The lower actual branch field therefore embeds faithfully in the residue field of every
successor valuation trivial on the lower state field. -/
noncomputable def nonautonomousFiniteCascadeLowerBranchResidueEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    {N : ℕ} (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (A : ValuationSubring (NonautonomousFiniteCascadeBranchField hfan (N + 1)))
    (hstate : ∀ x : NonautonomousRamifiedCascadeStateField hfan N,
      nonautonomousFiniteCascadeLowerStateInclusionSucc hfan N x ∈ A) :
    NonautonomousFiniteCascadeBranchField hfan N →+*
      IsLocalRing.ResidueField A :=
  valuationSubringResidueEmbedding A
    (nonautonomousFiniteCascadeBranchInclusionSucc hfan N).toRingHom
    (nonautonomousFiniteCascadeBranchInclusionSucc_mem_of_lowerState_mem
      hfan hall h1 A hstate)

/-- The residue embedding of the entire lower actual branch field is injective. -/
theorem nonautonomousFiniteCascadeLowerBranchResidueEmbedding_injective
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    {N : ℕ} (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (A : ValuationSubring (NonautonomousFiniteCascadeBranchField hfan (N + 1)))
    (hstate : ∀ x : NonautonomousRamifiedCascadeStateField hfan N,
      nonautonomousFiniteCascadeLowerStateInclusionSucc hfan N x ∈ A) :
    Function.Injective
      (nonautonomousFiniteCascadeLowerBranchResidueEmbedding
        hfan hall h1 A hstate) :=
  RingHom.injective _

end

end GaloisForLFunctions.HTGeometry
