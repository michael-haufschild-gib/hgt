import GaloisForLFunctions.HTGeometry.DomainJetRelationLocus
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# The compact-open Fréchet space of holomorphic functions on a domain

For an open `Ω ⊆ ℂ` the holomorphic functions on `Ω` form a closed complex subspace of the
compact-open space `C(↥Ω, ℂ)`.  Since `↥Ω` is locally compact and second countable, the ambient
space is completely metrizable, so the subspace is a Fréchet — in particular Baire — space.

Every fixed jet is a continuous functional there: compact-open convergence of holomorphic functions
is locally uniform convergence, which passes to every iterated derivative.

This is the ambient space of the DA/HT topological interlacing law.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology

noncomputable section

open Classical in
/-- Canonical extension by zero of a function on a subtype. -/
def holoExtend (Ω : Set ℂ) (F : ↥Ω → ℂ) : ℂ → ℂ :=
  fun z => if h : z ∈ Ω then F ⟨z, h⟩ else 0

@[simp] theorem holoExtend_coe {Ω : Set ℂ} (F : ↥Ω → ℂ) (z : ↥Ω) :
    holoExtend Ω F (z : ℂ) = F z := by
  classical
  simp only [holoExtend, dif_pos z.2]

theorem holoExtend_of_mem {Ω : Set ℂ} (F : ↥Ω → ℂ) {z : ℂ} (hz : z ∈ Ω) :
    holoExtend Ω F z = F ⟨z, hz⟩ := by
  classical
  simp only [holoExtend, dif_pos hz]

theorem holoExtend_add {Ω : Set ℂ} (F G : ↥Ω → ℂ) :
    holoExtend Ω (F + G) = holoExtend Ω F + holoExtend Ω G := by
  classical
  funext z
  by_cases hz : z ∈ Ω <;> simp [holoExtend, hz]

theorem holoExtend_smul {Ω : Set ℂ} (c : ℂ) (F : ↥Ω → ℂ) :
    holoExtend Ω (c • F) = c • holoExtend Ω F := by
  classical
  funext z
  by_cases hz : z ∈ Ω <;> simp [holoExtend, hz]

theorem holoExtend_zero (Ω : Set ℂ) : holoExtend Ω (0 : ↥Ω → ℂ) = 0 := by
  classical
  funext z
  by_cases hz : z ∈ Ω <;> simp [holoExtend, hz]

/-- Holomorphic functions on `Ω` as a complex submodule of the compact-open space. -/
def holoCompactOpenSubmodule (Ω : Set ℂ) : Submodule ℂ C(↥Ω, ℂ) where
  carrier := {F | DifferentiableOn ℂ (holoExtend Ω (F : ↥Ω → ℂ)) Ω}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have h0 : holoExtend Ω ((0 : C(↥Ω, ℂ)) : ↥Ω → ℂ) = 0 := holoExtend_zero Ω
    rw [h0]
    exact differentiableOn_const 0
  add_mem' := by
    intro F G hF hG
    simp only [Set.mem_setOf_eq] at hF hG ⊢
    have hadd : holoExtend Ω ((F + G : C(↥Ω, ℂ)) : ↥Ω → ℂ)
        = holoExtend Ω (F : ↥Ω → ℂ) + holoExtend Ω (G : ↥Ω → ℂ) := holoExtend_add _ _
    rw [hadd]
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    simp only [Set.mem_setOf_eq] at hF ⊢
    have hsmul : holoExtend Ω ((c • F : C(↥Ω, ℂ)) : ↥Ω → ℂ)
        = c • holoExtend Ω (F : ↥Ω → ℂ) := holoExtend_smul c _
    rw [hsmul]
    exact hF.const_smul c

/-- The compact-open Fréchet model of `O(Ω)`. -/
abbrev HoloCO (Ω : Set ℂ) := holoCompactOpenSubmodule Ω

instance holoCOCoeFun (Ω : Set ℂ) : CoeFun (HoloCO Ω) (fun _ => ↥Ω → ℂ) :=
  ⟨fun F => F.1.1⟩

instance holoCOContinuousAdd (Ω : Set ℂ) : ContinuousAdd (HoloCO Ω) :=
  continuousAdd_induced (holoCompactOpenSubmodule Ω).subtype

instance holoCOContinuousSMul (Ω : Set ℂ) : ContinuousSMul ℂ (HoloCO Ω) :=
  continuousSMul_induced (holoCompactOpenSubmodule Ω).subtype

/-- The plane function attached to an element of the compact-open holomorphic space. -/
def holoCOFun {Ω : Set ℂ} (F : HoloCO Ω) : ℂ → ℂ := holoExtend Ω (F : ↥Ω → ℂ)

theorem differentiableOn_holoCOFun {Ω : Set ℂ} (F : HoloCO Ω) :
    DifferentiableOn ℂ (holoCOFun F) Ω := F.2

theorem analyticOnNhd_holoCOFun {Ω : Set ℂ} (hΩ : IsOpen Ω) (F : HoloCO Ω) :
    AnalyticOnNhd ℂ (holoCOFun F) Ω :=
  (Complex.analyticOnNhd_iff_differentiableOn hΩ).2 (differentiableOn_holoCOFun F)

/-! ## Topology -/

section Topology

variable {Ω : Set ℂ} (hΩ : IsOpen Ω)

theorem tendstoLocallyUniformlyOn_of_tendsto {u : ℕ → HoloCO Ω} {F : HoloCO Ω}
    (hΩ : IsOpen Ω) (hu : Tendsto u atTop (𝓝 F)) :
    TendstoLocallyUniformlyOn (fun n z => holoCOFun (u n) z) (holoCOFun F) atTop Ω := by
  haveI := hΩ.locallyCompactSpace
  have huC : Tendsto (fun n => (u n).1) atTop (𝓝 F.1) := (continuous_subtype_val.tendsto F).comp hu
  have hloc : TendstoLocallyUniformly (fun n (z : ↥Ω) => (u n).1 z) (F.1) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp huC
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  refine (hloc.congr (fun n z => by simp [holoCOFun])).congr_right (fun z => by
    simp [holoCOFun, Function.comp])

theorem isSeqClosed_holoCompactOpen (hΩ : IsOpen Ω) :
    IsSeqClosed {F : C(↥Ω, ℂ) | DifferentiableOn ℂ (holoExtend Ω (F : ↥Ω → ℂ)) Ω} := by
  haveI := hΩ.locallyCompactSpace
  intro u F hu huF
  have hloc : TendstoLocallyUniformly (fun n (z : ↥Ω) => (u n) z) (F) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp huF
  have hlocOn : TendstoLocallyUniformlyOn
      (fun n z => holoExtend Ω ((u n : C(↥Ω, ℂ)) : ↥Ω → ℂ) z)
      (holoExtend Ω (F : ↥Ω → ℂ)) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    refine (hloc.congr (fun n z => by simp)).congr_right (fun z => by simp [Function.comp])
  refine hlocOn.differentiableOn ?_ hΩ
  filter_upwards with n using hu n

theorem isClosed_holoCompactOpen (hΩ : IsOpen Ω) :
    IsClosed {F : C(↥Ω, ℂ) | DifferentiableOn ℂ (holoExtend Ω (F : ↥Ω → ℂ)) Ω} := by
  haveI := hΩ.locallyCompactSpace
  exact (isSeqClosed_holoCompactOpen hΩ).isClosed

theorem completeSpace_holoCO (hΩ : IsOpen Ω) : CompleteSpace (HoloCO Ω) := by
  haveI := hΩ.locallyCompactSpace
  haveI hcl : IsClosed {F : C(↥Ω, ℂ) | DifferentiableOn ℂ (holoExtend Ω (F : ↥Ω → ℂ)) Ω} :=
    isClosed_holoCompactOpen hΩ
  exact IsClosed.completeSpace_coe (s := {F : C(↥Ω, ℂ) |
    DifferentiableOn ℂ (holoExtend Ω (F : ↥Ω → ℂ)) Ω})

theorem isCompletelyMetrizableSpace_holoCO (hΩ : IsOpen Ω) :
    TopologicalSpace.IsCompletelyMetrizableSpace (HoloCO Ω) := by
  haveI := hΩ.locallyCompactSpace
  exact IsClosed.isCompletelyMetrizableSpace (isClosed_holoCompactOpen hΩ)

theorem baireSpace_holoCO (hΩ : IsOpen Ω) : BaireSpace (HoloCO Ω) := by
  haveI := hΩ.locallyCompactSpace
  haveI := isCompletelyMetrizableSpace_holoCO hΩ
  infer_instance

/-! ## Continuity of the jets -/

theorem tendstoLocallyUniformlyOn_iteratedDeriv_holoCOFun (hΩ : IsOpen Ω) {u : ℕ → HoloCO Ω}
    {F : HoloCO Ω} (hu : Tendsto u atTop (𝓝 F)) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n z => iteratedDeriv k (holoCOFun (u n)) z)
      (iteratedDeriv k (holoCOFun F)) atTop Ω := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using tendstoLocallyUniformlyOn_of_tendsto hΩ hu
  | succ k hk =>
      have hdiff : ∀ᶠ n in atTop,
          DifferentiableOn ℂ (iteratedDeriv k (holoCOFun (u n))) Ω := by
        filter_upwards with n
        exact ((analyticOnNhd_iteratedDeriv (analyticOnNhd_holoCOFun hΩ (u n)) k)).differentiableOn
      have hnext := hk.deriv hdiff hΩ
      simpa only [Function.comp_def, iteratedDeriv_succ] using hnext

theorem continuous_holoCOJet (hΩ : IsOpen Ω) (a : ℂ) (ha : a ∈ Ω) (k : ℕ) :
    Continuous (fun F : HoloCO Ω => iteratedDeriv k (holoCOFun F) a) := by
  haveI := hΩ.locallyCompactSpace
  haveI := isCompletelyMetrizableSpace_holoCO hΩ
  rw [continuous_iff_seqContinuous]
  intro u F hu
  exact (tendstoLocallyUniformlyOn_iteratedDeriv_holoCOFun hΩ hu k).tendsto_at ha

end Topology

end

end GaloisForLFunctions.HTGeometry
