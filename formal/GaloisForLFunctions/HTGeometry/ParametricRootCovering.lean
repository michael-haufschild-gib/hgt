import GaloisForLFunctions.U0.HolomorphicIFT
import GaloisForLFunctions.Bottcher.BranchContinuation

/-!
# Local covering charts for parametric simple roots

A scalar analytic relation over an arbitrary complete complex Banach parameter space has a
locally homeomorphic root projection wherever its vertical derivative is nonzero.  This isolates
the topology-independent implicit-function chart used by polynomial and spectral root covers.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Set
open scoped ContDiff

noncomputable section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

/-- Zero locus of a scalar holomorphic relation over a Banach parameter space. -/
def ParametricRootLocus (f : P × ℂ → ℂ) : Set (P × ℂ) := {q | f q = 0}

/-- Projection of a parametric root locus to its parameter. -/
def parametricRootProj {f : P × ℂ → ℂ} (q : ParametricRootLocus f) : P := q.1.1

/-- Implicit-function data at a simple root of an analytic scalar relation. -/
noncomputable def parametricRootIFTData {f : P × ℂ → ℂ}
    (q : ParametricRootLocus f) (hf : AnalyticAt ℂ f q.1)
    (hvertical : (fderiv ℂ f q.1) (0, 1) ≠ 0) :
    ImplicitFunctionData ℂ (P × ℂ) ℂ P := by
  have cdf : ContDiffAt ℂ ω f q.1 := hf.contDiffAt
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  have if₂ : (fderiv ℂ f q.1 ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hvertical)
  exact cdf.hasStrictFDerivAt hω |>.implicitFunctionDataOfProdDomain if₂

theorem parametricRootIFTData_apply {f : P × ℂ → ℂ}
    (q : ParametricRootLocus f) (hf : AnalyticAt ℂ f q.1)
    (hvertical : (fderiv ℂ f q.1) (0, 1) ≠ 0) (v : P × ℂ) :
    (parametricRootIFTData q hf hvertical).toOpenPartialHomeomorph v = (f v, v.1) := rfl

theorem parametricRootIFTData_mem_source {f : P × ℂ → ℂ}
    (q : ParametricRootLocus f) (hf : AnalyticAt ℂ f q.1)
    (hvertical : (fderiv ℂ f q.1) (0, 1) ≠ 0) :
    (q : P × ℂ) ∈ (parametricRootIFTData q hf hvertical).toOpenPartialHomeomorph.source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

/-- A local chart of the root projection at any simple analytic root. -/
theorem exists_chart_parametricRootProj {f : P × ℂ → ℂ}
    (e : ParametricRootLocus f) (hf : AnalyticAt ℂ f e.1)
    (hvertical : (fderiv ℂ f e.1) (0, 1) ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (ParametricRootLocus f) P,
      e ∈ φ.source ∧ parametricRootProj (f := f) = φ := by
  classical
  let ψ := (parametricRootIFTData e hf hvertical).toOpenPartialHomeomorph
  let baseTarget : P → ℂ × P := fun p => (0, p)
  have hbaseTarget : Continuous baseTarget := continuous_const.prodMk continuous_id
  have hambient : Continuous (fun q : ParametricRootLocus f => (q : P × ℂ)) :=
    continuous_subtype_val
  let targetPred : P → Prop := fun p => baseTarget p ∈ ψ.target
  have hsymm_spec : ∀ p (hp : targetPred p),
      f (ψ.symm (baseTarget p)) = 0 ∧ (ψ.symm (baseTarget p)).1 = p := by
    intro p hp
    have hright := ψ.right_inv hp
    have h1 := congrArg Prod.fst hright
    have h2 := congrArg Prod.snd hright
    rw [show ψ (ψ.symm (baseTarget p)) =
        (f (ψ.symm (baseTarget p)), (ψ.symm (baseTarget p)).1) from
      parametricRootIFTData_apply e hf hvertical _] at h1 h2
    exact ⟨h1, h2⟩
  let liftRoot : ∀ p, targetPred p → ParametricRootLocus f :=
    fun p hp => ⟨ψ.symm (baseTarget p), (hsymm_spec p hp).1⟩
  let invRoot : P → ParametricRootLocus f :=
    fun p => if hp : targetPred p then liftRoot p hp else e
  let source : Set (ParametricRootLocus f) :=
    (fun q : ParametricRootLocus f => (q : P × ℂ)) ⁻¹' ψ.source
  let target : Set P := baseTarget ⁻¹' ψ.target
  have hpsi_eq : ∀ q : ParametricRootLocus f,
      ψ (q : P × ℂ) = baseTarget (parametricRootProj q) := by
    intro q
    rw [parametricRootIFTData_apply e hf hvertical]
    exact Prod.ext q.2 rfl
  have hmapSource : ∀ q ∈ source, parametricRootProj q ∈ target := by
    intro q hq
    show baseTarget (parametricRootProj q) ∈ ψ.target
    rw [← hpsi_eq q]
    exact ψ.map_source hq
  have hmapTarget : ∀ p ∈ target, invRoot p ∈ source := by
    intro p hp
    have hp' : targetPred p := hp
    rw [show invRoot p = liftRoot p hp' by
      dsimp only [invRoot]; rw [dif_pos hp']]
    exact ψ.map_target hp'
  have hleft : ∀ q ∈ source, invRoot (parametricRootProj q) = q := by
    intro q hq
    have hp' : targetPred (parametricRootProj q) := hmapSource q hq
    rw [show invRoot (parametricRootProj q) = liftRoot (parametricRootProj q) hp' by
      dsimp only [invRoot]; rw [dif_pos hp']]
    apply Subtype.ext
    show ψ.symm (baseTarget (parametricRootProj q)) = (q : P × ℂ)
    rw [← hpsi_eq q]
    exact ψ.left_inv hq
  have hright : ∀ p ∈ target, parametricRootProj (invRoot p) = p := by
    intro p hp
    have hp' : targetPred p := hp
    rw [show invRoot p = liftRoot p hp' by dsimp only [invRoot]; rw [dif_pos hp']]
    exact (hsymm_spec p hp').2
  have hcontInv : ContinuousOn invRoot target := by
    have hψsymm : ContinuousOn (fun p => ψ.symm (baseTarget p)) target :=
      ψ.continuousOn_symm.comp hbaseTarget.continuousOn (fun p hp => hp)
    rw [continuousOn_iff_continuous_restrict]
    apply Continuous.subtype_mk
    have hrestr : Continuous fun p : target => ψ.symm (baseTarget p.1) :=
      continuousOn_iff_continuous_restrict.mp hψsymm
    convert hrestr using 1
    funext p
    have hp' : targetPred p.1 := p.2
    change ((invRoot p.1 : ParametricRootLocus f) : P × ℂ) =
      ψ.symm (baseTarget p.1)
    rw [show invRoot p.1 = liftRoot p.1 hp' by
      dsimp only [invRoot]; rw [dif_pos hp']]
  let chart : OpenPartialHomeomorph (ParametricRootLocus f) P :=
    { toFun := parametricRootProj
      invFun := invRoot
      source := source
      target := target
      map_source' := hmapSource
      map_target' := hmapTarget
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := hcontInv
      open_source := ψ.open_source.preimage hambient
      open_target := ψ.open_target.preimage hbaseTarget }
  exact ⟨chart, parametricRootIFTData_mem_source e hf hvertical, rfl⟩

/-- Projection from a simple analytic root locus is a local homeomorphism. -/
theorem isLocalHomeomorph_parametricRootProj {f : P × ℂ → ℂ}
    (hf : ∀ q : ParametricRootLocus f, AnalyticAt ℂ f q.1)
    (hvertical : ∀ q : ParametricRootLocus f,
      (fderiv ℂ f q.1) (0, 1) ≠ 0) :
    IsLocalHomeomorph (parametricRootProj (f := f)) :=
  fun q => exists_chart_parametricRootProj q (hf q) (hvertical q)

end

end GaloisForLFunctions.HTGeometry
