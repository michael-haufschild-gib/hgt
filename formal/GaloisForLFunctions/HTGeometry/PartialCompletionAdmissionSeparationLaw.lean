import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw

/-!
# Admission--separation law for partial completions

Singular, unbounded, and rigged completions are not total maps on their source spaces.  They first
select an admissible domain and only then identify points through an observation map.  Exact global
recovery therefore has two logically independent gates:

1. every relevant source point must enter the admissible domain;
2. the observation kernel on that domain must refine the target kernel.

Postprocessing changes neither the admission predicate nor any distinction already erased by the
observation.  For a reflection-stable domain, an invariant observation cannot recover a nonzero
reflection-odd charge.  A completion which does recover that charge must separate every admitted
reflected pair carrying nonzero charge.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A partial completion consists of an admission predicate and an observation on admitted source
points. -/
structure PartialCompletion (X Q : Type*) where
  admissible : X → Prop
  observe : {x : X // admissible x} → Q

/-- Restriction of a source target to the admitted domain. -/
def PartialCompletion.restrictedTarget
    {X Q C : Type*} (P : PartialCompletion X Q) (χ : X → C) :
    {x : X // P.admissible x} → C := fun x => χ x.1

/-- Exact recovery on the attained observation range of the admitted domain. -/
def PartialCompletion.RecoversOnAdmitted
    {X Q C : Type*} (P : PartialCompletion X Q) (χ : X → C) : Prop :=
  FactorsThroughRange P.observe (P.restrictedTarget χ)

/-- Global recovery requires both universal admission and recovery on the admitted domain. -/
def PartialCompletion.GloballyRecovers
    {X Q C : Type*} (P : PartialCompletion X Q) (χ : X → C) : Prop :=
  (∀ x, P.admissible x) ∧ P.RecoversOnAdmitted χ

/-- The separation gate: recovery on the admitted domain is exactly kernel refinement there. -/
theorem partialCompletion_recoversOnAdmitted_iff_kernelRefines
    {X Q C : Type*} (P : PartialCompletion X Q) (χ : X → C) :
    P.RecoversOnAdmitted χ ↔
      KernelRefines P.observe (P.restrictedTarget χ) := by
  exact factorsThroughRange_iff_kernelRefines _ _

/-- **Admission--separation law.**  Exact global recovery is equivalent to universal source
admission together with kernel separation on the admitted domain. -/
theorem partialCompletion_globallyRecovers_iff_admission_and_kernelRefines
    {X Q C : Type*} (P : PartialCompletion X Q) (χ : X → C) :
    P.GloballyRecovers χ ↔
      (∀ x, P.admissible x) ∧
        KernelRefines P.observe (P.restrictedTarget χ) := by
  rw [PartialCompletion.GloballyRecovers,
    partialCompletion_recoversOnAdmitted_iff_kernelRefines]

/-- Downstream postprocessing preserves the admission predicate. -/
def PartialCompletion.postprocess
    {X Q Y : Type*} (P : PartialCompletion X Q) (g : Q → Y) :
    PartialCompletion X Y where
  admissible := P.admissible
  observe := g ∘ P.observe

@[simp] theorem partialCompletion_postprocess_admissible
    {X Q Y : Type*} (P : PartialCompletion X Q) (g : Q → Y) (x : X) :
    (P.postprocess g).admissible x ↔ P.admissible x := Iff.rfl

/-- Postprocessing cannot split a collision of the admitted observation. -/
theorem partialCompletion_kernelPair_mono_postprocess
    {X Q Y : Type*} (P : PartialCompletion X Q) (g : Q → Y)
    {x y : {x : X // P.admissible x}}
    (h : MapKernelPair P.observe x y) :
    MapKernelPair (P.postprocess g).observe x y := by
  exact congrArg g h

/-- The admission domain is stable under a source reflection. -/
def PartialCompletion.ReflectionStable
    {X Q : Type*} (P : PartialCompletion X Q) (σ : X → X) : Prop :=
  ∀ x, P.admissible x → P.admissible (σ x)

/-- An admitted observation is reflection invariant, with the domain-stability witness made
explicit. -/
def PartialCompletion.ReflectionInvariantOnStable
    {X Q : Type*} (P : PartialCompletion X Q) (σ : X → X)
    (hstable : P.ReflectionStable σ) : Prop :=
  ∀ (x : X) (hx : P.admissible x),
    P.observe ⟨σ x, hstable x hx⟩ = P.observe ⟨x, hx⟩

/-- A reflection-invariant partial completion can recover a reflection-odd real charge only on
its zero locus. -/
theorem oddTarget_eq_zero_on_admitted_of_invariantPartialCompletion
    {X Q : Type*} (P : PartialCompletion X Q) {σ : X → X}
    (hstable : P.ReflectionStable σ)
    (hinv : P.ReflectionInvariantOnStable σ hstable)
    {χ : X → ℝ} (hχ : OddUnder X σ χ)
    (hrec : P.RecoversOnAdmitted χ) :
    ∀ x, P.admissible x → χ x = 0 := by
  intro x hx
  have href :=
    (partialCompletion_recoversOnAdmitted_iff_kernelRefines P χ).1 hrec
  have heq := href ⟨σ x, hstable x hx⟩ ⟨x, hx⟩ (hinv x hx)
  change χ (σ x) = χ x at heq
  linarith [hχ x]

/-- The separation arm of the reflection trilemma: every admitted nonzero odd pair must remain
distinct in any recovering completion. -/
theorem partialCompletion_separates_reflection_of_oddCharge_ne_zero
    {X Q : Type*} (P : PartialCompletion X Q) {σ : X → X}
    (hstable : P.ReflectionStable σ)
    {χ : X → ℝ} (hχ : OddUnder X σ χ)
    (hrec : P.RecoversOnAdmitted χ) {x : X}
    (hxadm : P.admissible x) (hx : χ x ≠ 0) :
    P.observe ⟨σ x, hstable x hxadm⟩ ≠ P.observe ⟨x, hxadm⟩ := by
  intro hsame
  have href :=
    (partialCompletion_recoversOnAdmitted_iff_kernelRefines P χ).1 hrec
  have heq := href ⟨σ x, hstable x hxadm⟩ ⟨x, hxadm⟩ hsame
  change χ (σ x) = χ x at heq
  apply hx
  linarith [hχ x]

end GaloisForLFunctions.HTGeometry
