import GaloisForLFunctions.RHTower.ConsolidatedBridges

/-!
# Realizations of the abstract bridge interfaces

The bridge interfaces are pure logic: confinement holds when nothing is source carrying or when
everything is on the seam, and detection holds when every zero is already on line.  Each bridge is
therefore consistent, and the contrapositive form records exactly what the bridge forbids: no model
can simultaneously detect an off-line zero and confine every source-carrying defect to the seam.
-/

namespace GaloisForLFunctions

section Defects

variable {Zero Defect : Type*}

theorem allSourceDefectsOnSeam_of_onSeam (SourceCarrying : Defect → Prop) :
    allSourceDefectsOnSeam (fun _ => True) SourceCarrying := fun _ _ => trivial

theorem allSourceDefectsOnSeam_of_no_source (OnSeam : Defect → Prop) :
    allSourceDefectsOnSeam OnSeam (fun _ => False) := fun _ h => h.elim

theorem detectsOffSeamDefect_of_allZerosOnLine {OnLine : Zero → Prop}
    (OnSeam SourceCarrying : Defect → Prop) (h : allZerosOnLine OnLine) :
    detectsOffSeamDefect OnLine OnSeam SourceCarrying := fun ρ hρ => absurd (h ρ) hρ

theorem offSeamSourceDefectFor_of_link {Link : Zero → Defect → Prop}
    {OnSeam SourceCarrying : Defect → Prop} {ρ : Zero} {d : Defect}
    (hsource : SourceCarrying d) (hlink : Link ρ d) (hoff : ¬ OnSeam d) :
    offSeamSourceDefectFor Link OnSeam SourceCarrying ρ :=
  ⟨d, hsource, hlink, hoff⟩

/-- **What the defect bridge forbids.**  No model detects an off-line zero while confining every
source-carrying defect to the seam. -/
theorem not_detects_and_confine_of_offLine {OnLine : Zero → Prop}
    {OnSeam SourceCarrying : Defect → Prop} {ρ : Zero} (hoff : ¬ OnLine ρ) :
    ¬ (detectsOffSeamDefect OnLine OnSeam SourceCarrying ∧
        allSourceDefectsOnSeam OnSeam SourceCarrying) := by
  rintro ⟨hDetect, hConfine⟩
  exact hoff (twoLemmaBridge_forces_onLine hDetect hConfine ρ)

end Defects

section Support

variable {Zero SupportPoint : Type*}

theorem supportConfinedToSeam_of_onSeam (InSupport : SupportPoint → Prop) :
    supportConfinedToSeam InSupport (fun _ => True) := fun _ _ => trivial

theorem supportConfinedToSeam_of_empty_support (OnSeamSupport : SupportPoint → Prop) :
    supportConfinedToSeam (fun _ => False) OnSeamSupport := fun _ h => h.elim

theorem offLineProducesOffSeamSupport_of_allZerosOnLine {OnLine : Zero → Prop}
    (InSupport OnSeamSupport : SupportPoint → Prop) (h : allZerosOnLine OnLine) :
    offLineProducesOffSeamSupport OnLine InSupport OnSeamSupport :=
  fun ρ hρ => absurd (h ρ) hρ

/-- **What the support bridge forbids.** -/
theorem not_support_detects_and_confine_of_offLine {OnLine : Zero → Prop}
    {InSupport OnSeamSupport : SupportPoint → Prop} {ρ : Zero} (hoff : ¬ OnLine ρ) :
    ¬ (offLineProducesOffSeamSupport OnLine InSupport OnSeamSupport ∧
        supportConfinedToSeam InSupport OnSeamSupport) := by
  rintro ⟨hDetect, hConfine⟩
  exact hoff (supportBridge_forces_onLine hDetect hConfine ρ)

end Support

end GaloisForLFunctions
