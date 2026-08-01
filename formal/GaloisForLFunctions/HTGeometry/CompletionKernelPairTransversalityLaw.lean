import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge

/-!
# Completion kernel-pair transversality

Information discarded by a completion map cannot be recreated by downstream
postprocessing.  An auxiliary transverse channel repairs a target exactly when
its joint kernel with the completion kernel refines the target kernel.

For reflection problems this gives an orientation-before-completion law: a
reflection-odd real charge cannot descend through a reflection-invariant
completion except on its zero locus.  Every sufficient transverse channel must
separate each nonzero reflected pair.  If completion fibres are dense, even
one-point continuity of a separated downstream reporter forces constancy.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Kernel pair of a map, viewed as the information it discards. -/
def MapKernelPair {X Y : Type*} (f : X → Y) (x y : X) : Prop :=
  f x = f y

/-- A target is a downstream function of a completion map. -/
def FactorsThrough
    {X Q C : Type*} (π : X → Q) (χ : X → C) : Prop :=
  ∃ d : Q → C, χ = d ∘ π

/-- Exact factorization through the attained range of an observation.  This
avoids imposing any arbitrary extension on points of the codomain which are
not observed. -/
def FactorsThroughRange
    {X Q C : Type*} (π : X → Q) (χ : X → C) : Prop :=
  ∃ d : Set.range π → C,
    ∀ x, d ⟨π x, ⟨x, rfl⟩⟩ = χ x

/-- Kernel refinement: every distinction erased by `π` is also erased by
`χ`. -/
def KernelRefines
    {X Q C : Type*} (π : X → Q) (χ : X → C) : Prop :=
  ∀ x y, MapKernelPair π x y → MapKernelPair χ x y

/-- A transverse channel repairs completion for target `χ` when equality in
both observed coordinates forces equality of the target. -/
def JointlyRecovers
    {X Q T C : Type*} (π : X → Q) (τ : X → T) (χ : X → C) : Prop :=
  ∀ x y, MapKernelPair π x y → MapKernelPair τ x y → MapKernelPair χ x y

/-- Postprocessing can only enlarge a kernel pair. -/
theorem mapKernelPair_mono_of_factorsThrough
    {X Q C : Type*} {π : X → Q} {χ : X → C}
    (hχ : FactorsThrough π χ) {x y : X}
    (hπ : MapKernelPair π x y) :
    MapKernelPair χ x y := by
  obtain ⟨d, rfl⟩ := hχ
  exact congrArg d hπ

/-- One collapsed target-distinguishing pair forbids every downstream
factorization through the completion. -/
theorem no_factorization_of_kernelPair_collision
    {X Q C : Type*} {π : X → Q} {χ : X → C} {x y : X}
    (hπ : MapKernelPair π x y) (hχ : ¬ MapKernelPair χ x y) :
    ¬ FactorsThrough π χ := by
  intro hfactor
  exact hχ (mapKernelPair_mono_of_factorsThrough hfactor hπ)

/-- Universal factorization law for an arbitrary observation: a target is
recoverable on the attained observation range exactly when its kernel pair
contains the observation kernel pair. -/
theorem factorsThroughRange_iff_kernelRefines
    {X Q C : Type*} (π : X → Q) (χ : X → C) :
    FactorsThroughRange π χ ↔ KernelRefines π χ := by
  constructor
  · rintro ⟨d, hd⟩ x y hπ
    have hrange :
        (⟨π x, ⟨x, rfl⟩⟩ : Set.range π) =
          ⟨π y, ⟨y, rfl⟩⟩ :=
      Subtype.ext hπ
    calc
      χ x = d ⟨π x, ⟨x, rfl⟩⟩ := (hd x).symm
      _ = d ⟨π y, ⟨y, rfl⟩⟩ := congrArg d hrange
      _ = χ y := hd y
  · intro hrefine
    let d : Set.range π → C :=
      fun q => χ (Classical.choose q.property)
    refine ⟨d, ?_⟩
    intro x
    apply hrefine (Classical.choose (show π x ∈ Set.range π from ⟨x, rfl⟩)) x
    exact Classical.choose_spec
      (show π x ∈ Set.range π from ⟨x, rfl⟩)

/-- Heterogeneous record of an arbitrary family of observation channels. -/
def observationRecord
    {J X : Type*} {Y : J → Type*}
    (obs : ∀ j, X → Y j) (x : X) : ∀ j, Y j :=
  fun j => obs j x

/-- A family of channels jointly recovers a target when equality in every
channel forces equality of the target. -/
def ObservationFamilyRecovers
    {J X C : Type*} {Y : J → Type*}
    (obs : ∀ j, X → Y j) (χ : X → C) : Prop :=
  ∀ x y, (∀ j, obs j x = obs j y) → χ x = χ y

/-- Arbitrarily many heterogeneous channels obey the same kernel law: their
joint record recovers a target exactly when the intersection of all channel
kernels refines the target kernel. -/
theorem observationFamilyRecovers_iff_recordKernelRefines
    {J X C : Type*} {Y : J → Type*}
    (obs : ∀ j, X → Y j) (χ : X → C) :
    ObservationFamilyRecovers obs χ ↔
      KernelRefines (observationRecord obs) χ := by
  constructor
  · intro h x y hrecord
    apply h x y
    intro j
    exact congrFun hrecord j
  · intro h x y hobs
    apply h x y
    funext j
    exact hobs j

/-- Exact arbitrary-family recovery theorem.  No topology, linearity,
boundedness, finiteness, or common channel codomain is assumed. -/
theorem observationFamilyRecovers_iff_factorsThroughRecordRange
    {J X C : Type*} {Y : J → Type*}
    (obs : ∀ j, X → Y j) (χ : X → C) :
    ObservationFamilyRecovers obs χ ↔
      FactorsThroughRange (observationRecord obs) χ := by
  rw [observationFamilyRecovers_iff_recordKernelRefines,
    factorsThroughRange_iff_kernelRefines]

/-- Exact repair criterion in kernel-pair form. -/
theorem jointlyRecovers_iff_kernelPair_inter_refines
    {X Q T C : Type*} (π : X → Q) (τ : X → T) (χ : X → C) :
    JointlyRecovers π τ χ ↔
      ∀ x y, MapKernelPair π x y → MapKernelPair τ x y →
        MapKernelPair χ x y :=
  Iff.rfl

/-- Every repair must separate each completion collision which the target
distinguishes. -/
theorem transverseChannel_separates_targetCollision
    {X Q T C : Type*} {π : X → Q} {τ : X → T} {χ : X → C}
    (hrepair : JointlyRecovers π τ χ) {x y : X}
    (hπ : MapKernelPair π x y) (hχ : ¬ MapKernelPair χ x y) :
    ¬ MapKernelPair τ x y := by
  intro hτ
  exact hχ (hrepair x y hπ hτ)

/-- Joint observation map. -/
def jointObservation
    {X Q T : Type*} (π : X → Q) (τ : X → T) (x : X) : Q × T :=
  (π x, τ x)

/-- The canonical target recovered on the actual range of a sufficient joint
observation. -/
noncomputable def recoveredTargetOnJointRange
    {X Q T C : Type*} (π : X → Q) (τ : X → T) (χ : X → C)
    (_hrepair : JointlyRecovers π τ χ)
    (z : Set.range (jointObservation π τ)) : C :=
  χ (Classical.choose z.property)

/-- A sufficient transverse channel reconstructs the target exactly on every
observed record; no arbitrary extension outside the observed range is needed. -/
theorem recoveredTargetOnJointRange_apply
    {X Q T C : Type*} (π : X → Q) (τ : X → T) (χ : X → C)
    (hrepair : JointlyRecovers π τ χ) (x : X) :
    recoveredTargetOnJointRange π τ χ hrepair
      ⟨jointObservation π τ x, ⟨x, rfl⟩⟩ = χ x := by
  unfold recoveredTargetOnJointRange
  let y : X := Classical.choose
    (show (jointObservation π τ x) ∈ Set.range (jointObservation π τ) from ⟨x, rfl⟩)
  have hy : jointObservation π τ y = jointObservation π τ x :=
    Classical.choose_spec
      (show (jointObservation π τ x) ∈ Set.range (jointObservation π τ) from ⟨x, rfl⟩)
  apply hrepair y x
  · exact congrArg Prod.fst hy
  · exact congrArg Prod.snd hy

/-- A completion coordinate is reflection invariant. -/
def InvariantUnder
    {X Q : Type*} (σ : X → X) (π : X → Q) : Prop :=
  ∀ x, π (σ x) = π x

/-- A real target charge is reflection odd. -/
def OddUnder (X : Type*) (σ : X → X) (χ : X → ℝ) : Prop :=
  ∀ x, χ (σ x) = -χ x

/-- **Orientation-before-completion law.** A reflection-odd real charge which
factors through a reflection-invariant completion vanishes identically. -/
theorem oddTarget_eq_zero_of_factorsThrough_invariantCompletion
    {X Q : Type*} {σ : X → X} {π : X → Q} {χ : X → ℝ}
    (hπ : InvariantUnder σ π) (hχ : OddUnder X σ χ)
    (hfactor : FactorsThrough π χ) :
    ∀ x, χ x = 0 := by
  intro x
  have hsame : χ (σ x) = χ x :=
    mapKernelPair_mono_of_factorsThrough hfactor (hπ x)
  linarith [hχ x]

/-- Every sufficient transverse channel separates a reflected pair carrying
nonzero odd charge. -/
theorem transverseChannel_separates_reflection_of_oddCharge_ne_zero
    {X Q T : Type*} {σ : X → X} {π : X → Q} {τ : X → T}
    {χ : X → ℝ}
    (hπ : InvariantUnder σ π) (hχ : OddUnder X σ χ)
    (hrepair : JointlyRecovers π τ χ) {x : X} (hx : χ x ≠ 0) :
    τ (σ x) ≠ τ x := by
  apply transverseChannel_separates_targetCollision hrepair (hπ x)
  intro heq
  change χ (σ x) = χ x at heq
  apply hx
  linarith [hχ x]

/-- Reflection-odd part of a scalar transverse channel. -/
noncomputable def reflectionOddPart
    {X : Type*} (σ : X → X) (τ : X → ℝ) (x : X) : ℝ :=
  (τ x - τ (σ x)) / 2

/-- Every sufficient scalar repair has nonzero odd part at every nonzero
orientation charge. -/
theorem reflectionOddPart_ne_zero_of_jointlyRecovers
    {X Q : Type*} {σ : X → X} {π : X → Q} {τ χ : X → ℝ}
    (hπ : InvariantUnder σ π) (hχ : OddUnder X σ χ)
    (hrepair : JointlyRecovers π τ χ) {x : X} (hx : χ x ≠ 0) :
    reflectionOddPart σ τ x ≠ 0 := by
  have hsep :=
    transverseChannel_separates_reflection_of_oddCharge_ne_zero
      hπ hχ hrepair hx
  intro hzero
  have hnum : τ x - τ (σ x) = 0 := by
    unfold reflectionOddPart at hzero
    linarith
  exact hsep (sub_eq_zero.mp hnum).symm

/-- The target charge itself is the canonical sufficient transverse channel. -/
theorem targetChannel_jointlyRecovers
    {X Q C : Type*} (π : X → Q) (χ : X → C) :
    JointlyRecovers π χ χ := by
  intro x y _ hχ
  exact hχ

/-- Dense completion fibres make every separated downstream reporter singular:
if its source pullback is continuous at even one point, it is constant. -/
theorem downstreamReporter_constant_of_dense_completionFibers
    {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (π : X → Q) (hπsurj : Function.Surjective π)
    (F : Q → Y) (x : X) (hF : ContinuousAt (F ∘ π) x)
    (hdense : ∀ z : X, Dense (π ⁻¹' {π z})) :
    ∀ q₁ q₂, F q₁ = F q₂ := by
  have hconstant :=
    GaloisForLFunctions.continuousAt_constant_of_dense_fibers
      π (F ∘ π) x hF hdense
      (fun y z hyz => congrArg F hyz)
  intro q₁ q₂
  obtain ⟨y, rfl⟩ := hπsurj q₁
  obtain ⟨z, rfl⟩ := hπsurj q₂
  exact (hconstant y).trans (hconstant z).symm

end GaloisForLFunctions.HTGeometry
