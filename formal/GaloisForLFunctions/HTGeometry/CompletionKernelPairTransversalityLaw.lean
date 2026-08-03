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

universe u

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

/-! ## Reflection-grade conservation -/

/-- `Bool`-valued reflection grade: `false` is even and `true` is odd. -/
def ReflectionParity {X R : Type*} [Neg R]
    (odd : Bool) (σ : X → X) (f : X → R) : Prop :=
  ∀ x, f (σ x) = if odd then -f x else f x

theorem reflectionParity_false_iff_invariantUnder
    {X R : Type*} [Neg R] (σ : X → X) (f : X → R) :
    ReflectionParity false σ f ↔ InvariantUnder σ f := by
  rfl

theorem reflectionParity_true_iff_oddUnder
    {X : Type*} (σ : X → X) (f : X → ℝ) :
    ReflectionParity true σ f ↔ OddUnder X σ f := by
  rfl

/-- **Reflection-grade product law.**  Multiplication adds the two
`Z/2`-grades.  In particular, the product of two odd source factors is
reflection-even. -/
theorem reflectionParity_mul
    {X R : Type*} [CommRing R]
    {a b : Bool} {σ : X → X} {f g : X → R}
    (hf : ReflectionParity a σ f)
    (hg : ReflectionParity b σ g) :
    ReflectionParity (Bool.xor a b) σ (fun x => f x * g x) := by
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    simp_all [ReflectionParity, Bool.xor]

/-- Equivariant additive transport preserves reflection grade. -/
theorem reflectionParity_addHom
    {X A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {odd : Bool} {σ : X → X} {f : X → A}
    (hf : ReflectionParity odd σ f) (T : A →+ B) :
    ReflectionParity odd σ (T ∘ f) := by
  intro x
  rw [Function.comp_apply, Function.comp_apply, hf x]
  by_cases hodd : odd
  · simp [hodd]
  · simp [hodd]

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

/-- Characteristic-zero field-valued form of odd-target descent. -/
theorem target_eq_zero_of_reflectionParity_factorsThrough_invariantCompletion
    {X Q R : Type*} [Field R] [CharZero R]
    {σ : X → X} {π : X → Q} {χ : X → R}
    (hπ : InvariantUnder σ π)
    (hχ : ReflectionParity true σ χ)
    (hfactor : FactorsThrough π χ) :
    ∀ x, χ x = 0 := by
  intro x
  have hsame : χ (σ x) = χ x :=
    mapKernelPair_mono_of_factorsThrough hfactor (hπ x)
  have hodd : χ (σ x) = -χ x := by
    simpa [ReflectionParity] using hχ x
  rw [hsame] at hodd
  have htwo : (2 : R) * χ x = 0 := by
    linear_combination hodd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- **Odd-multiplier selector law.**  Let `g` be a reflection-even defect.
If a reflection-odd source multiplier `a`, nonzero everywhere `g` is
nonzero, makes `a * g` factor through a reflection-invariant observation,
then `g` vanishes.  Thus an extra odd source grade can restore the
orientation consumed by a double-odd contraction without requiring a
nonzero odd value at reflection-fixed points. -/
theorem evenTarget_eq_zero_of_supportNonzero_oddMultiplier_factorsThrough_invariantCompletion
    {X Q R : Type*} [Field R] [CharZero R]
    {σ : X → X} {π : X → Q} {a g : X → R}
    (hπ : InvariantUnder σ π)
    (ha : ReflectionParity true σ a)
    (hg : ReflectionParity false σ g)
    (ha0 : ∀ x, g x ≠ 0 → a x ≠ 0)
    (hfactor : FactorsThrough π (fun x => a x * g x)) :
    ∀ x, g x = 0 := by
  have hproductParity :
      ReflectionParity true σ (fun x => a x * g x) := by
    simpa using reflectionParity_mul ha hg
  have hzero :=
    target_eq_zero_of_reflectionParity_factorsThrough_invariantCompletion
      hπ hproductParity hfactor
  intro x
  by_contra hg0
  exact (ha0 x hg0) ((mul_eq_zero.mp (hzero x)).resolve_right hg0)

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

/-! ## The observation preorder

The kernel-pair law is most economical when observations are ordered by the
distinctions they retain.  In this order serial postprocessing moves upward
(towards less information), while a parallel record is the meet of its
channels.  Recoverability of a target is exactly comparison with that target
in the same order. -/

/-- `π` refines `ψ` when every distinction retained by `ψ` is already
retained by `π`.  Equivalently, the kernel pair of `π` is contained in the
kernel pair of `ψ`. -/
def ObservationRefines
    {X Q R : Type*} (π : X → Q) (ψ : X → R) : Prop :=
  KernelRefines π ψ

theorem observationRefines_refl
    {X Q : Type*} (π : X → Q) :
    ObservationRefines π π := by
  intro x y hxy
  exact hxy

theorem observationRefines_trans
    {X Q R C : Type*} {π : X → Q} {ψ : X → R} {χ : X → C}
    (hπψ : ObservationRefines π ψ)
    (hψχ : ObservationRefines ψ χ) :
    ObservationRefines π χ := by
  intro x y hπ
  exact hψχ x y (hπψ x y hπ)

/-- Every serial consumer is above its input in the observation order: it can
only identify more source pairs. -/
theorem observationRefines_postprocess
    {X Q R : Type*} (π : X → Q) (f : Q → R) :
    ObservationRefines π (f ∘ π) := by
  intro x y hπ
  exact congrArg f hπ

/-- Injective postprocessing preserves the complete kernel pair of an
observation.  It changes representation but no retained distinction. -/
theorem mapKernelPair_comp_iff_of_injective
    {X Q R : Type*} (π : X → Q) (f : Q → R)
    (hf : Function.Injective f) (x y : X) :
    MapKernelPair (f ∘ π) x y ↔ MapKernelPair π x y := by
  constructor
  · exact fun h => hf h
  · exact fun h => congrArg f h

/-- **Injective-transport neutrality.**  An injective change of carrier is an
isomorphism in the observation preorder: it neither creates nor destroys
recoverability of any target. -/
theorem factorsThroughRange_comp_iff_of_injective
    {X Q R C : Type*} (π : X → Q) (f : Q → R)
    (hf : Function.Injective f) (χ : X → C) :
    FactorsThroughRange (f ∘ π) χ ↔ FactorsThroughRange π χ := by
  rw [factorsThroughRange_iff_kernelRefines,
    factorsThroughRange_iff_kernelRefines]
  constructor
  · intro h x y hπ
    exact h x y (congrArg f hπ)
  · intro h x y hpost
    exact h x y (hf hpost)

/-- Recoverability is downward closed in the observation order.  A more
informative observation retains every target recoverable from a coarser one. -/
theorem factorsThroughRange_of_refines_of_factorsThroughRange
    {X Q R C : Type*} {π : X → Q} {ψ : X → R} {χ : X → C}
    (hπψ : ObservationRefines π ψ)
    (hψχ : FactorsThroughRange ψ χ) :
    FactorsThroughRange π χ := by
  rw [factorsThroughRange_iff_kernelRefines] at hψχ ⊢
  exact observationRefines_trans hπψ hψχ

/-- Serial postprocessing cannot create recovery of a target which was not
already recoverable from the unprocessed observation. -/
theorem not_factorsThroughRange_postprocess_of_not_factorsThroughRange
    {X Q R C : Type*} (π : X → Q) (f : Q → R) (χ : X → C)
    (hπχ : ¬ FactorsThroughRange π χ) :
    ¬ FactorsThroughRange (f ∘ π) χ := by
  intro hpost
  exact hπχ
    (factorsThroughRange_of_refines_of_factorsThroughRange
      (observationRefines_postprocess π f) hpost)

/-- The heterogeneous parallel record is the meet of its component
observations in the observation preorder. -/
theorem observationRefines_record_iff
    {J X Q : Type*} {Y : J → Type*}
    (π : X → Q) (obs : ∀ j, X → Y j) :
    ObservationRefines π (observationRecord obs) ↔
      ∀ j, ObservationRefines π (obs j) := by
  constructor
  · intro h j x y hπ
    exact congrFun (h x y hπ) j
  · intro h x y hπ
    funext j
    exact h j x y hπ

/-! ## The complete observation lattice

Modulo equality of kernel pairs, observations on a fixed source realize the
complete lattice of equivalence relations on that source.  Parallel records
are meets.  The quotient by the join of two kernel relations is their least
common coarsening. -/

/-- Kernel pair of an observation, packaged as a source equivalence relation. -/
def ObservationKernelSetoid {X Q : Type*} (π : X → Q) : Setoid X where
  r := MapKernelPair π
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Canonical observation realizing a prescribed source equivalence relation. -/
def quotientObservation {X : Type*} (r : Setoid X) : X → Quotient r :=
  Quotient.mk'

theorem mapKernelPair_quotientObservation_iff
    {X : Type*} (r : Setoid X) (x y : X) :
    MapKernelPair (quotientObservation r) x y ↔ r x y :=
  Quotient.eq'

@[simp]
theorem observationKernelSetoid_quotientObservation
    {X : Type*} (r : Setoid X) :
    ObservationKernelSetoid (quotientObservation r) = r := by
  apply Setoid.ext
  intro x y
  exact mapKernelPair_quotientObservation_iff r x y

/-- Every equivalence relation on a source is the kernel pair of an
observation.  Hence observations modulo kernel-pair equality realize the
entire complete lattice of source equivalence relations. -/
theorem every_setoid_is_observationKernel
    {X : Type u} (r : Setoid X) :
    ∃ (Q : Type u) (π : X → Q), ObservationKernelSetoid π = r := by
  exact
    ⟨Quotient r, quotientObservation r,
      observationKernelSetoid_quotientObservation r⟩

theorem observationKernelSetoid_le_iff
    {X Q R : Type*} (π : X → Q) (ψ : X → R) :
    ObservationKernelSetoid π ≤ ObservationKernelSetoid ψ ↔
      ObservationRefines π ψ := by
  rfl

/-- An arbitrary heterogeneous record realizes the infimum of its channel
kernel relations. -/
theorem observationKernelSetoid_record
    {J X : Type*} {Y : J → Type*}
    (obs : ∀ j, X → Y j) :
    ObservationKernelSetoid (observationRecord obs) =
      ⨅ j, ObservationKernelSetoid (obs j) := by
  apply le_antisymm
  · apply le_iInf
    intro j
    rw [observationKernelSetoid_le_iff]
    intro x y hxy
    exact congrFun hxy j
  · let q := quotientObservation (⨅ j, ObservationKernelSetoid (obs j))
    have hq : ObservationRefines q (observationRecord obs) :=
      (observationRefines_record_iff q obs).2 (fun j => by
        rw [← observationKernelSetoid_le_iff]
        simpa [q] using
          (iInf_le (fun j => ObservationKernelSetoid (obs j)) j))
    rw [← observationKernelSetoid_le_iff] at hq
    simpa [q] using hq

/-- Canonical least common coarsening of two observations. -/
def observationJoin
    {X Q R : Type*} (π : X → Q) (ψ : X → R) :
    X → Quotient (ObservationKernelSetoid π ⊔ ObservationKernelSetoid ψ) :=
  quotientObservation (ObservationKernelSetoid π ⊔ ObservationKernelSetoid ψ)

/-- **Observation-lattice join law.**  The join is above both inputs and
below every common coarsening. -/
theorem observationJoin_law
    {X Q R : Type*} (π : X → Q) (ψ : X → R) :
    ObservationRefines π (observationJoin π ψ) ∧
      ObservationRefines ψ (observationJoin π ψ) ∧
      ∀ {C : Type*} (χ : X → C),
        ObservationRefines π χ → ObservationRefines ψ χ →
          ObservationRefines (observationJoin π ψ) χ := by
  constructor
  · rw [← observationKernelSetoid_le_iff]
    simp [observationJoin]
  constructor
  · rw [← observationKernelSetoid_le_iff]
    simp [observationJoin]
  · intro C χ hπ hψ
    rw [← observationKernelSetoid_le_iff] at hπ hψ ⊢
    simpa [observationJoin] using (sup_le hπ hψ)

theorem observationJoin_refines_iff
    {X Q R C : Type*} (π : X → Q) (ψ : X → R) (χ : X → C) :
    ObservationRefines (observationJoin π ψ) χ ↔
      ObservationRefines π χ ∧ ObservationRefines ψ χ := by
  rw [← observationKernelSetoid_le_iff,
    ← observationKernelSetoid_le_iff,
    ← observationKernelSetoid_le_iff]
  simp [observationJoin]

/-- The complete observation-order law.  A target is recoverable precisely
when it lies above the observation; serial consumers move upward, and
parallel resolution takes meets. -/
theorem observationOrder_recovery_iff
    {X Q C : Type*} (π : X → Q) (χ : X → C) :
    FactorsThroughRange π χ ↔ ObservationRefines π χ :=
  factorsThroughRange_iff_kernelRefines π χ

end GaloisForLFunctions.HTGeometry
