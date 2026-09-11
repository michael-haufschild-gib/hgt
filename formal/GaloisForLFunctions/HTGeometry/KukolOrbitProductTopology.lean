import GaloisForLFunctions.HTGeometry.KukolGlobalOrbitSlice

/-!
# Topology of the global unipotent orbit decomposition

The regular point space carries the ordinary minus/plus/transverse product
topology. Kukol's action and its canonical gauge are continuous. The global
orbit/slice equivalence is a homeomorphism, for arbitrary simultaneous families.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Topology
variable {κ : Type*}

/-- The raw minus/plus/transverse chart fixes the ordinary product topology on regular points. -/
def kukolRegularRawEquiv : KukolRegularPoint κ ≃ ℂˣ × ℂ × (κ → ℂ) where
  toFun x := (x.minus,x.plus,x.transverse)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : TopologicalSpace (KukolRegularPoint κ) :=
  TopologicalSpace.induced (kukolRegularRawEquiv (κ := κ)) inferInstance

/-- This is the raw coordinate topology, before changing to invariant coordinates. -/
def kukolRegularRawHomeomorph : KukolRegularPoint κ ≃ₜ ℂˣ × ℂ × (κ → ℂ) :=
  kukolRegularRawEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

@[fun_prop] theorem continuous_kukolRegularMinus :
    Continuous (fun x : KukolRegularPoint κ => x.minus) :=
  kukolRegularRawHomeomorph.continuous.fst

@[fun_prop] theorem continuous_kukolRegularPlus :
    Continuous (fun x : KukolRegularPoint κ => x.plus) :=
  kukolRegularRawHomeomorph.continuous.snd.fst

@[fun_prop] theorem continuous_kukolRegularTransverse :
    Continuous (fun x : KukolRegularPoint κ => x.transverse) :=
  kukolRegularRawHomeomorph.continuous.snd.snd

variable [Fintype κ]

/-- The Lorentz invariant is continuous in the original complex coordinates. -/
@[fun_prop] theorem continuous_kukolRegularQuadratic : Continuous (kukolRegularQuadratic (κ := κ)) := by
  unfold kukolRegularQuadratic
  fun_prop

/-- The complex unipotent action is jointly continuous in the parameter and the point. -/
@[fun_prop] theorem continuous_kukolRegularAction :
    Continuous (fun p : (κ → ℂ) × KukolRegularPoint κ => kukolRegularAction p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : (κ → ℂ) × KukolRegularPoint κ =>
    ((p.2).minus,(p.2).plus+2*(∑ k,(p.2).transverse k*p.1 k)+
      ((p.2).minus : ℂ)*(∑ k,p.1 k^2),fun k => (p.2).transverse k+((p.2).minus : ℂ)*p.1 k))
  fun_prop

variable {ι : Type*}

omit [Fintype κ] in
/-- The anchored group coordinate varies continuously for arbitrary simultaneous families. -/
@[fun_prop] theorem continuous_kukolDiagonalGauge (anchor : ι) :
    Continuous (kukolDiagonalGauge (κ := κ) anchor) := by
  apply continuous_pi
  intro k
  exact ((continuous_apply k).comp (continuous_kukolRegularTransverse.comp (continuous_apply anchor))).div
    (Units.continuous_val.comp (continuous_kukolRegularMinus.comp (continuous_apply anchor)))
    (fun x => (x anchor).minus.ne_zero)

/-- The canonical representative map is continuous, including its dependence on all family members. -/
@[fun_prop] theorem continuous_kukolDiagonalNormalize (anchor : ι) :
    Continuous (kukolDiagonalNormalize (κ := κ) anchor) := by
  apply continuous_pi
  intro j
  exact continuous_kukolRegularAction.comp
    ((continuous_kukolDiagonalGauge anchor).neg.prodMk (continuous_apply j))

/-- The global orbit decomposition is a genuine homeomorphism for the ordinary coordinate topology. -/
def kukolDiagonalOrbitHomeomorph (anchor : ι) :
    (ι → KukolRegularPoint κ) ≃ₜ (κ → ℂ) × KukolDiagonalSlice (κ := κ) anchor where
  toEquiv := kukolDiagonalOrbitEquiv anchor
  continuous_toFun := (continuous_kukolDiagonalGauge anchor).prodMk
    ((continuous_kukolDiagonalNormalize anchor).subtype_mk (kukolDiagonalNormalize_anchor anchor))
  continuous_invFun := by
    apply continuous_pi
    intro j
    exact continuous_kukolRegularAction.comp
      (continuous_fst.prodMk ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))

end GaloisForLFunctions.HTGeometry
