import Mathlib.Topology.IsLocalHomeomorph

/-!
# Pullback stability of local homeomorphisms

This module constructs the local chart on a topological fibre product explicitly.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Set

noncomputable section

variable {B E X : Type*} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace X]

/-- Topological pullback of `p : E → B` along `g : X → B`. -/
def LocalHomeomorphPullback (p : E → B) (g : X → B) : Set (X × E) :=
  {q | g q.1 = p q.2}

/-- Projection from a topological pullback to the new base. -/
def localHomeomorphPullbackProj {p : E → B} {g : X → B}
    (q : LocalHomeomorphPullback p g) : X := q.1.1

/-- A pullback chart induced by a local-homeomorphism chart. -/
theorem exists_chart_localHomeomorphPullbackProj_of_chart {p : E → B} {g : X → B}
    (q : LocalHomeomorphPullback p g) (e : OpenPartialHomeomorph E B)
    (hqe : q.1.2 ∈ e.source) (hpe : p = e) (hg : Continuous g) :
    ∃ φ : OpenPartialHomeomorph (LocalHomeomorphPullback p g) X,
      q ∈ φ.source ∧ localHomeomorphPullbackProj = φ := by
  classical
  have hpe_apply : ∀ y : E, p y = e y := fun y => congrFun hpe y
  let targetPred : X → Prop := fun x => g x ∈ e.target
  have hlift_mem : ∀ x (hx : targetPred x),
      g x = p (e.symm (g x)) := by
    intro x hx
    rw [hpe]
    exact (e.right_inv hx).symm
  let lift : ∀ x, targetPred x → LocalHomeomorphPullback p g :=
    fun x hx => ⟨(x, e.symm (g x)), hlift_mem x hx⟩
  let inv : X → LocalHomeomorphPullback p g :=
    fun x => if hx : targetPred x then lift x hx else q
  let source : Set (LocalHomeomorphPullback p g) :=
    (fun r : LocalHomeomorphPullback p g => r.1.2) ⁻¹' e.source
  let target : Set X := g ⁻¹' e.target
  have hmapSource : ∀ r ∈ source, localHomeomorphPullbackProj r ∈ target := by
    intro r hr
    show g r.1.1 ∈ e.target
    rw [r.2, hpe_apply]
    exact e.map_source hr
  have hmapTarget : ∀ x ∈ target, inv x ∈ source := by
    intro x hx
    have hx' : targetPred x := hx
    rw [show inv x = lift x hx' by dsimp only [inv]; rw [dif_pos hx']]
    exact e.map_target hx'
  have hleft : ∀ r ∈ source, inv (localHomeomorphPullbackProj r) = r := by
    intro r hr
    have hx' : targetPred (localHomeomorphPullbackProj r) := hmapSource r hr
    rw [show inv (localHomeomorphPullbackProj r) =
        lift (localHomeomorphPullbackProj r) hx' by
      dsimp only [inv]; rw [dif_pos hx']]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change e.symm (g r.1.1) = r.1.2
      rw [r.2, hpe_apply]
      exact e.left_inv hr
  have hright : ∀ x ∈ target, localHomeomorphPullbackProj (inv x) = x := by
    intro x hx
    have hx' : targetPred x := hx
    rw [show inv x = lift x hx' by dsimp only [inv]; rw [dif_pos hx']]
    rfl
  have hcontInv : ContinuousOn inv target := by
    rw [continuousOn_iff_continuous_restrict]
    apply Continuous.subtype_mk
    have hsecond : Continuous fun x : target => e.symm (g x.1) :=
      continuousOn_iff_continuous_restrict.mp
        (e.continuousOn_symm.comp hg.continuousOn (fun x hx => hx))
    have hpair : Continuous fun x : target => (x.1, e.symm (g x.1)) :=
      continuous_subtype_val.prodMk hsecond
    convert hpair using 1
    funext x
    have hx' : targetPred x.1 := x.2
    change ((inv x.1 : LocalHomeomorphPullback p g) : X × E) =
      (x.1, e.symm (g x.1))
    rw [show inv x.1 = lift x.1 hx' by dsimp only [inv]; rw [dif_pos hx']]
  let chart : OpenPartialHomeomorph (LocalHomeomorphPullback p g) X :=
    { toFun := localHomeomorphPullbackProj
      invFun := inv
      source := source
      target := target
      map_source' := hmapSource
      map_target' := hmapTarget
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := hcontInv
      open_source := e.open_source.preimage
        (continuous_snd.comp continuous_subtype_val)
      open_target := e.open_target.preimage hg }
  exact ⟨chart, hqe, rfl⟩

/-- A local-homeomorphism chart pulls back along every continuous base map. -/
theorem exists_chart_localHomeomorphPullbackProj {p : E → B} {g : X → B}
    (hp : IsLocalHomeomorph p) (hg : Continuous g) (q : LocalHomeomorphPullback p g) :
    ∃ φ : OpenPartialHomeomorph (LocalHomeomorphPullback p g) X,
      q ∈ φ.source ∧ localHomeomorphPullbackProj = φ := by
  obtain ⟨e, hqe, hpe⟩ := hp q.1.2
  exact exists_chart_localHomeomorphPullbackProj_of_chart q e hqe hpe hg

/-- Local homeomorphisms are stable under arbitrary continuous base change. -/
theorem isLocalHomeomorph_localHomeomorphPullbackProj {p : E → B} {g : X → B}
    (hp : IsLocalHomeomorph p) (hg : Continuous g) :
    IsLocalHomeomorph (localHomeomorphPullbackProj (p := p) (g := g)) :=
  fun q => exists_chart_localHomeomorphPullbackProj hp hg q

end


end GaloisForLFunctions.HTGeometry
