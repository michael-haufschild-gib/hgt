import GaloisForLFunctions.RHTower.CCMRationalAdelicRealStructure
import Mathlib.Topology.Order

/-!
# LF and finite-support direct-sum topology on the rational CCM source

The finite-adelic Bruhat factor is an algebraic inductive limit of finite-dimensional coefficient
spaces.  After tensoring with the archimedean Schwartz space, its canonical LF topology is the
final topology of all finite families of finite Bruhat coefficients.  The crossed product then
receives the final finite-support direct-sum topology, and the minimal unitization receives the
transported product topology.

Reflection preserves each system after reflecting its finite coefficients.  This proves
continuity of the exact rational CCM source involution without a discrete or indiscrete topology.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- A finite Bruhat-coefficient stage: a finite direct sum of archimedean Schwartz spaces. -/
def ccmRationalAdelicBruhatLFStage (n : ℕ) (φ : Fin n → FinBruhat)
    (f : Fin n → Arch) : Core :=
  ∑ i, f i ⊗ₜ[ℂ] φ i

/-- Canonical final LF topology of the algebraic rational adelic Bruhat--Schwartz tensor. -/
@[reducible]
def ccmRationalAdelicBruhatLFTopology : TopologicalSpace Core :=
  ⨆ (n : ℕ) (φ : Fin n → FinBruhat),
    TopologicalSpace.coinduced (ccmRationalAdelicBruhatLFStage n φ) inferInstance

theorem ccmRationalAdelicBruhatLFStage_continuous
    (n : ℕ) (φ : Fin n → FinBruhat) :
    @Continuous (Fin n → Arch) Core inferInstance
      ccmRationalAdelicBruhatLFTopology
      (ccmRationalAdelicBruhatLFStage n φ) := by
  exact continuous_iSup_rng (continuous_iSup_rng continuous_coinduced_rng)

/-- Universal property of the rational adelic Bruhat LF topology. -/
theorem ccmRationalAdelicBruhatLF_continuous_iff
    {Y : Type*} (tY : TopologicalSpace Y) (g : Core → Y) :
    @Continuous Core Y ccmRationalAdelicBruhatLFTopology tY g ↔
      ∀ (n : ℕ) (φ : Fin n → FinBruhat),
        @Continuous (Fin n → Arch) Y inferInstance tY
          (g ∘ ccmRationalAdelicBruhatLFStage n φ) := by
  rw [ccmRationalAdelicBruhatLFTopology, continuous_iSup_dom]
  apply forall_congr'
  intro n
  rw [continuous_iSup_dom]
  apply forall_congr'
  intro φ
  exact continuous_coinduced_dom

theorem ccmRationalAdelicBruhatLFStage_reflection
    (n : ℕ) (φ : Fin n → FinBruhat) (f : Fin n → Arch) :
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
        (ccmRationalAdelicBruhatLFStage n φ f) =
      ccmRationalAdelicBruhatLFStage n
        (fun i => ccmRationalFiniteBruhatReflection (φ i))
        (fun i => ccmRationalArchimedeanSchwartzReflection (f i)) := by
  simp [ccmRationalAdelicBruhatLFStage,
    ccmRationalAdelicBruhatSimpleTensor_sigma_tmul]

/-- Bruhat reflection is continuous for the exact LF topology. -/
theorem ccmRationalAdelicBruhatReflection_continuous :
    @Continuous Core Core ccmRationalAdelicBruhatLFTopology
      ccmRationalAdelicBruhatLFTopology
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  rw [ccmRationalAdelicBruhatLF_continuous_iff]
  intro n φ
  rw [show ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma ∘
      ccmRationalAdelicBruhatLFStage n φ =
    ccmRationalAdelicBruhatLFStage n
      (fun i => ccmRationalFiniteBruhatReflection (φ i)) ∘
      (fun f i => ccmRationalArchimedeanSchwartzReflection (f i)) by
        funext f
        exact ccmRationalAdelicBruhatLFStage_reflection n φ f]
  exact (ccmRationalAdelicBruhatLFStage_continuous n _).comp
    (continuous_pi fun i =>
      ccmRationalArchimedeanSchwartzReflection_continuous.comp
        (continuous_apply i))

theorem ccmRationalAdelicBruhatLFStage_smul
    (z : ℂ) (n : ℕ) (φ : Fin n → FinBruhat) (f : Fin n → Arch) :
    z • ccmRationalAdelicBruhatLFStage n φ f =
      ccmRationalAdelicBruhatLFStage n φ (fun i => z • f i) := by
  rw [ccmRationalAdelicBruhatLFStage, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact TensorProduct.smul_tmul' z (f i) (φ i)

theorem ccmRationalAdelicBruhat_smul_continuous (z : ℂ) :
    @Continuous Core Core ccmRationalAdelicBruhatLFTopology
      ccmRationalAdelicBruhatLFTopology (fun x => z • x) := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  rw [ccmRationalAdelicBruhatLF_continuous_iff]
  intro n φ
  rw [show (fun x : Core => z • x) ∘
      ccmRationalAdelicBruhatLFStage n φ =
    ccmRationalAdelicBruhatLFStage n φ ∘
      (fun f i => z • f i) by
        funext f
        exact ccmRationalAdelicBruhatLFStage_smul z n φ f]
  exact (ccmRationalAdelicBruhatLFStage_continuous n φ).comp
    (continuous_pi fun i => (continuous_apply i).const_smul z)

theorem ccmRationalAdelicMonomialRealTwist_continuous (k : Scale) :
    @Continuous Core Core ccmRationalAdelicBruhatLFTopology
      ccmRationalAdelicBruhatLFTopology
      (ccmRationalAdelicMonomialRealTwist k) := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  change @Continuous Core Core ccmRationalAdelicBruhatLFTopology
    ccmRationalAdelicBruhatLFTopology
    ((fun x => ccmRationalUnitSign k.val • x) ∘
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma)
  exact (ccmRationalAdelicBruhat_smul_continuous _).comp
    ccmRationalAdelicBruhatReflection_continuous

/-- Finite-support direct-sum stage of the algebraic crossed product. -/
def ccmRationalAdelicCrossedDirectSumStage
    (n : ℕ) (label : Fin n → Scale) (a : Fin n → Core) : Crossed :=
  ∑ i, Finsupp.single (label i) (a i)

/-- Final finite-support direct-sum topology of the rational crossed product. -/
@[reducible]
def ccmRationalAdelicCrossedDirectSumTopology : TopologicalSpace Crossed := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  exact ⨆ (n : ℕ) (label : Fin n → Scale),
    TopologicalSpace.coinduced
      (ccmRationalAdelicCrossedDirectSumStage n label) inferInstance

theorem ccmRationalAdelicCrossedDirectSumStage_continuous
    (n : ℕ) (label : Fin n → Scale) :
    @Continuous (Fin n → Core) Crossed
      (by letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
          exact inferInstance)
      ccmRationalAdelicCrossedDirectSumTopology
      (ccmRationalAdelicCrossedDirectSumStage n label) := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  exact continuous_iSup_rng (continuous_iSup_rng continuous_coinduced_rng)

/-- Universal property of the finite-support direct-sum topology. -/
theorem ccmRationalAdelicCrossedDirectSum_continuous_iff
    {Y : Type*} (tY : TopologicalSpace Y) (g : Crossed → Y) :
    @Continuous Crossed Y ccmRationalAdelicCrossedDirectSumTopology tY g ↔
      ∀ (n : ℕ) (label : Fin n → Scale),
        @Continuous (Fin n → Core) Y
          (by letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
              exact inferInstance)
          tY (g ∘ ccmRationalAdelicCrossedDirectSumStage n label) := by
  rw [ccmRationalAdelicCrossedDirectSumTopology, continuous_iSup_dom]
  apply forall_congr'
  intro n
  rw [continuous_iSup_dom]
  apply forall_congr'
  intro label
  exact continuous_coinduced_dom

theorem ccmRationalAdelicCrossedDirectSumStage_real
    (n : ℕ) (label : Fin n → Scale) (a : Fin n → Core) :
    ccmRationalAdelicCrossedProductRealStructure
        (ccmRationalAdelicCrossedDirectSumStage n label a) =
      ccmRationalAdelicCrossedDirectSumStage n label
        (fun i => ccmRationalAdelicMonomialRealTwist (label i) (a i)) := by
  change ccmRationalAdelicCrossedProductRealStructureₛₗ
      (∑ i, Finsupp.single (label i) (a i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ccmRationalAdelicCrossedProductRealStructure_single (label i) (a i)

/-- Crossed-product Real involution is continuous in the finite-support direct-sum topology. -/
theorem ccmRationalAdelicCrossedProductRealStructure_continuous :
    @Continuous Crossed Crossed ccmRationalAdelicCrossedDirectSumTopology
      ccmRationalAdelicCrossedDirectSumTopology
      ccmRationalAdelicCrossedProductRealStructure := by
  letI : TopologicalSpace Core := ccmRationalAdelicBruhatLFTopology
  letI : TopologicalSpace Crossed := ccmRationalAdelicCrossedDirectSumTopology
  rw [ccmRationalAdelicCrossedDirectSum_continuous_iff]
  intro n label
  rw [show ccmRationalAdelicCrossedProductRealStructure ∘
      ccmRationalAdelicCrossedDirectSumStage n label =
    ccmRationalAdelicCrossedDirectSumStage n label ∘
      (fun a i => ccmRationalAdelicMonomialRealTwist (label i) (a i)) by
        funext a
        exact ccmRationalAdelicCrossedDirectSumStage_real n label a]
  exact (ccmRationalAdelicCrossedDirectSumStage_continuous n label).comp
    (continuous_pi fun i =>
      (ccmRationalAdelicMonomialRealTwist_continuous (label i)).comp
        (continuous_apply i))

/-- Transported product topology on the exact minimal unitization. -/
@[reducible]
def ccmRationalAdelicSourceLFTopology : TopologicalSpace Source := by
  letI : TopologicalSpace Crossed := ccmRationalAdelicCrossedDirectSumTopology
  exact TopologicalSpace.induced (fun x : Source => (x.fst, x.snd)) inferInstance

/-- Exact rational CCM source Real involution is LF-continuous. -/
theorem ccmRationalAdelicSourceRealStructure_continuous :
    @Continuous Source Source ccmRationalAdelicSourceLFTopology
      ccmRationalAdelicSourceLFTopology
      ccmRationalAdelicSourceRealStructure := by
  letI : TopologicalSpace Crossed := ccmRationalAdelicCrossedDirectSumTopology
  letI : TopologicalSpace Source := ccmRationalAdelicSourceLFTopology
  apply continuous_induced_rng.mpr
  change Continuous fun x : Source =>
    (star x.fst, ccmRationalAdelicCrossedProductRealStructure x.snd)
  have htoProd : Continuous (fun x : Source => (x.fst, x.snd)) :=
    continuous_induced_dom
  have hfst : Continuous (fun x : Source => x.fst) :=
    continuous_fst.comp htoProd
  have hsnd : Continuous (fun x : Source => x.snd) :=
    continuous_snd.comp htoProd
  exact (continuous_star.comp hfst).prodMk
    (ccmRationalAdelicCrossedProductRealStructure_continuous.comp hsnd)

end GaloisForLFunctions.RHTower
