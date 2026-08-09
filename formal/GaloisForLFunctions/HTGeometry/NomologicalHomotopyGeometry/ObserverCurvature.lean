import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Real.Basic

/-!
# Observer curvature, false flatness, and serial irreversibility

An obstruction layer packages exactly the output of one stage of the partial-flattening recursion:
partial branches, next-stage branches, their cohomology target, and the proved extension criterion.
This lets the observer theorem be stated once, independently of a presentation of the underlying
`L∞` algebra, while retaining every datum used in the paper proof.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.ObserverCurvature

open Function Set

noncomputable section

universe u v w z

/-- One dependency-closed layer of a curvature obstruction tower. -/
structure ObstructionLayer (k : Type u) [Field k] where
  Partial : Type v
  Next : Type v
  Cohomology : Type v
  cohomologyAdd : AddCommGroup Cohomology
  cohomologyModule : Module k Cohomology
  obstruction : Partial → Cohomology
  extension_iff : Nonempty Next ↔ ∃ β : Partial, obstruction β = 0

attribute [instance] ObstructionLayer.cohomologyAdd ObstructionLayer.cohomologyModule

variable {k : Type u} [Field k]

namespace ObstructionLayer

/-- Obstruction spectrum at this layer. -/
def spectrum (A : ObstructionLayer k) : Set A.Cohomology :=
  Set.range A.obstruction

/-- Span of the represented obstruction spectrum. -/
def spectrumSpan (A : ObstructionLayer k) : Submodule k A.Cohomology :=
  Submodule.span k A.spectrum

/-- Extendibility through the next curvature layer. -/
abbrev Extendible (A : ObstructionLayer k) : Prop := Nonempty A.Next

theorem extendible_iff_zero_mem_spectrum (A : ObstructionLayer k) :
    A.Extendible ↔ 0 ∈ A.spectrum := by
  simpa [spectrum] using A.extension_iff

/-- If the next cohomology degree vanishes (as differential forms do above finite base dimension),
every represented partial flattening extends through this layer. -/
theorem extendible_of_subsingleton_cohomology (A : ObstructionLayer k)
    [Subsingleton A.Cohomology] (b : A.Partial) : A.Extendible := by
  apply A.extension_iff.mpr
  exact ⟨b, Subsingleton.elim _ _⟩

end ObstructionLayer

/-- Strict represented observer at one obstruction layer.  Partial branches and cohomology classes
are transported, and the next obstruction is natural. -/
structure Observer (A : ObstructionLayer k) (B : ObstructionLayer k) where
  push : A.Partial → B.Partial
  cohomologyMap : A.Cohomology →ₗ[k] B.Cohomology
  obstruction_natural : ∀ β, B.obstruction (push β) = cohomologyMap (A.obstruction β)

namespace Observer

variable {A B C : ObstructionLayer k}

/-- Identity observer. -/
def id (A : ObstructionLayer k) : Observer A A where
  push := fun β ↦ β
  cohomologyMap := LinearMap.id
  obstruction_natural := fun _ ↦ rfl

/-- Serial composition of represented observers. -/
def comp (Ψ : Observer B C) (Φ : Observer A B) : Observer A C where
  push := Ψ.push ∘ Φ.push
  cohomologyMap := Ψ.cohomologyMap.comp Φ.cohomologyMap
  obstruction_natural β := by
    rw [Function.comp_apply, Ψ.obstruction_natural, LinearMap.comp_apply,
      ← Φ.obstruction_natural]

/-- Full obstruction-tower functoriality: represented spectra map into target spectra. -/
theorem image_spectrum_subset (Φ : Observer A B) :
    Φ.cohomologyMap '' A.spectrum ⊆ B.spectrum := by
  rintro _ ⟨_, ⟨β, rfl⟩, rfl⟩
  exact ⟨Φ.push β, Φ.obstruction_natural β⟩

/-- Pointwise naturality in the paper's orientation. -/
theorem obstruction_push (Φ : Observer A B) (β : A.Partial) :
    B.obstruction (Φ.push β) = Φ.cohomologyMap (A.obstruction β) :=
  Φ.obstruction_natural β

/-- Class erasure at a represented source branch. -/
def ClassErasure (Φ : Observer A B) : Prop :=
  ∃ β : A.Partial, A.obstruction β ≠ 0 ∧ Φ.cohomologyMap (A.obstruction β) = 0

/-- Every represented zero in the target reflects to a source zero. -/
def ReflectsRepresentedZero (Φ : Observer A B) : Prop :=
  ∀ β : A.Partial, Φ.cohomologyMap (A.obstruction β) = 0 → A.obstruction β = 0

/-- Effective lifting of every zero-obstruction target branch.  Branch types may already be
homotopy quotients, so equality here includes the declared homotopy identification. -/
def EffectiveZeroBranchLifting (Φ : Observer A B) : Prop :=
  ∀ β' : B.Partial, B.obstruction β' = 0 → ∃ β : A.Partial, Φ.push β = β'

/-- Target is extendible through the next layer but source is not: represented false flatness. -/
def FalseFlatness (_Φ : Observer A B) : Prop :=
  B.Extendible ∧ ¬ A.Extendible

/-- Class erasure makes the pushed source branch falsely unobstructed. -/
theorem classErasure_false_extension (Φ : Observer A B) (h : Φ.ClassErasure) :
    ∃ β : A.Partial,
      A.obstruction β ≠ 0 ∧ B.obstruction (Φ.push β) = 0 := by
  obtain ⟨β, hβ, hmap⟩ := h
  exact ⟨β, hβ, (Φ.obstruction_natural β).trans hmap⟩

/-- With zero reflection and effective branch lifting, target extendibility descends to source
extendibility. -/
theorem extendible_of_reflects_of_effective (Φ : Observer A B)
    (hreflect : Φ.ReflectsRepresentedZero)
    (hlift : Φ.EffectiveZeroBranchLifting) (hB : B.Extendible) : A.Extendible := by
  obtain ⟨β', hβ'⟩ := B.extension_iff.mp hB
  obtain ⟨β, hpush⟩ := hlift β' hβ'
  apply A.extension_iff.mpr
  refine ⟨β, hreflect β ?_⟩
  rw [← Φ.obstruction_natural, hpush, hβ']

/-- Exact two-mechanism classification: represented false flatness forces either class erasure or
failure of effective zero-branch lifting. -/
theorem falseFlatness_classification (Φ : Observer A B) (hfalse : Φ.FalseFlatness) :
    Φ.ClassErasure ∨ ¬ Φ.EffectiveZeroBranchLifting := by
  by_cases hreflect : Φ.ReflectsRepresentedZero
  · by_cases hlift : Φ.EffectiveZeroBranchLifting
    · exact False.elim (hfalse.2 (extendible_of_reflects_of_effective Φ hreflect hlift hfalse.1))
    · exact Or.inr hlift
  · left
    rw [ReflectsRepresentedZero] at hreflect
    obtain ⟨β, hβbad⟩ := not_forall.mp hreflect
    obtain ⟨hmap, hβ⟩ := Classical.not_imp.mp hβbad
    exact ⟨β, hβ, hmap⟩

/-- Serial postprocessing cannot reconstruct a class already sent to zero. -/
theorem serial_erasure (Φ : Observer A B) (Ψ : Observer B C) {o : A.Cohomology}
    (h : Φ.cohomologyMap o = 0) :
    (Ψ.comp Φ).cohomologyMap o = 0 := by
  simp [comp, h]

/-- A source branch cannot appear from serial composition unless it was already supplied to the
first observer. -/
theorem serial_push_range_subset (Φ : Observer A B) (Ψ : Observer B C) :
    Set.range (Ψ.comp Φ).push ⊆ Ψ.push '' Set.range Φ.push := by
  rintro _ ⟨β, rfl⟩
  exact ⟨Φ.push β, ⟨β, rfl⟩, rfl⟩

end Observer

/-! ## Parallel observers and curvature horizon -/

namespace Parallel

variable {H : Type v} [AddCommGroup H] [Module k H]
  {ι : Type w} {Hι : ι → Type z}
  [∀ i, AddCommGroup (Hι i)] [∀ i, Module k (Hι i)]

/-- Joint cohomology observer. -/
def joint (Φ : ∀ i, H →ₗ[k] Hι i) : H →ₗ[k] (∀ i, Hι i) :=
  LinearMap.pi Φ

/-- Joint erasure is exactly membership in the intersection of component kernels. -/
theorem ker_joint (Φ : ∀ i, H →ₗ[k] Hι i) :
    LinearMap.ker (joint Φ) = ⨅ i, LinearMap.ker (Φ i) :=
  LinearMap.ker_pi Φ

theorem joint_eq_zero_iff (Φ : ∀ i, H →ₗ[k] Hι i) (o : H) :
    joint Φ o = 0 ↔ ∀ i, Φ i o = 0 := by
  simp [joint, funext_iff]

/-- Parallel observers detect every class in `W` exactly when `W` meets their joint kernel only
at zero. -/
theorem detectsOn_iff_inf_ker_eq_bot (Φ : ∀ i, H →ₗ[k] Hι i) (W : Submodule k H) :
    (∀ o ∈ W, joint Φ o = 0 → o = 0) ↔
      W ⊓ LinearMap.ker (joint Φ) = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · intro o ho
      have hoW : o ∈ W := ho.1
      have hoker : joint Φ o = 0 := ho.2
      simpa only [Submodule.mem_bot] using h o hoW hoker
    · exact bot_le
  · intro h o hoW hzero
    have : o ∈ W ⊓ LinearMap.ker (joint Φ) := ⟨hoW, hzero⟩
    rw [h] at this
    exact this

/-- Finite observer curvature horizon in witness form. -/
theorem finite_curvature_horizon [Fintype ι] [FiniteDimensional k H]
    [∀ i, FiniteDimensional k (Hι i)] (Φ : ∀ i, H →ₗ[k] Hι i)
    (h : (∑ i, Module.finrank k (Hι i)) < Module.finrank k H) :
    ∃ o : H, o ≠ 0 ∧ ∀ i, Φ i o = 0 := by
  have hdim : Module.finrank k (∀ i, Hι i) < Module.finrank k H := by
    simpa only [Module.finrank_pi_fintype] using h
  obtain ⟨o, ho, ho0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := joint Φ) hdim)
  exact ⟨o, ho0, (joint_eq_zero_iff Φ o).mp ho⟩

/-- If curvature-span dimensions tend to infinity while total observer rank has one fixed finite
bound, every sufficiently high curvature layer contains a nonzero jointly erased class. -/
theorem eventually_curvature_horizon {ι : Type w} [Fintype ι]
    (Hn : ℕ → Type v) (Hnι : ℕ → ι → Type z)
    [∀ n, AddCommGroup (Hn n)] [∀ n, Module k (Hn n)]
    [∀ n i, AddCommGroup (Hnι n i)] [∀ n i, Module k (Hnι n i)]
    [∀ n, FiniteDimensional k (Hn n)] [∀ n i, FiniteDimensional k (Hnι n i)]
    (Φ : ∀ n i, Hn n →ₗ[k] Hnι n i) (D : ℕ)
    (hbound : ∀ n, (∑ i, Module.finrank k (Hnι n i)) ≤ D)
    (hgrowth : Filter.Tendsto (fun n ↦ Module.finrank k (Hn n)) Filter.atTop Filter.atTop) :
    ∀ᶠ n in Filter.atTop, ∃ o : Hn n, o ≠ 0 ∧ ∀ i, Φ n i o = 0 := by
  filter_upwards [Filter.tendsto_atTop.1 hgrowth (D + 1)] with n hn
  apply finite_curvature_horizon (Φ n)
  exact (hbound n).trans_lt (Nat.lt_of_succ_le hn)

end Parallel

/-! ## Secondary curvature and nullhomotopy independence -/

namespace Secondary

/-- Chain-level presentation of a secondary curvature representative.  Different nullhomotopies
may change the raw representative, but only by a declared twisted coboundary. -/
structure Presentation (k : Type u) [Field k] where
  Nullhomotopy : Type v
  Representative : Type v
  representativeAdd : AddCommGroup Representative
  representativeModule : Module k Representative
  boundaries : Submodule k Representative
  raw : Nullhomotopy → Representative
  change_exact : ∀ b b', raw b' - raw b ∈ boundaries

attribute [instance] Presentation.representativeAdd Presentation.representativeModule

variable {k : Type u} [Field k]

/-- Twisted cohomology target of the secondary representative. -/
abbrev Presentation.Cohomology (A : Presentation k) :=
  A.Representative ⧸ A.boundaries

/-- Secondary cohomology class represented by one nullhomotopy. -/
def Presentation.obstructionClass (A : Presentation k) (b : A.Nullhomotopy) : A.Cohomology :=
  A.boundaries.mkQ (A.raw b)

/-- The secondary cohomology class is independent of the chosen nullhomotopy. -/
theorem Presentation.obstructionClass_independent (A : Presentation k)
    (b b' : A.Nullhomotopy) : A.obstructionClass b' = A.obstructionClass b := by
  apply (Submodule.Quotient.eq A.boundaries).2
  exact A.change_exact b b'

set_option linter.checkUnivs false in
/-- One secondary obstruction layer, including possible next flattenings and the exact extension
criterion before choice independence is used. -/
structure Layer (k : Type u) [Field k] extends Presentation k where
  Next : Type v
  extension_iff : Nonempty Next ↔
    ∃ b : toPresentation.Nullhomotopy, toPresentation.obstructionClass b = 0

namespace Layer

/-- Once one nullhomotopy is fixed, extendibility is equivalent to vanishing of its canonical
secondary class. -/
theorem extendible_iff_class_eq_zero (A : Layer k) (b : A.toPresentation.Nullhomotopy) :
    Nonempty A.Next ↔ A.toPresentation.obstructionClass b = 0 := by
  constructor
  · intro h
    obtain ⟨b', hb'⟩ := A.extension_iff.mp h
    rw [A.toPresentation.obstructionClass_independent b b'] at hb'
    exact hb'
  · intro hb
    exact A.extension_iff.mpr ⟨b, hb⟩

/-- The first secondary obstruction spectrum is a singleton, despite raw representative
dependence. -/
theorem obstructionClass_range_eq_singleton (A : Layer k)
    (b : A.toPresentation.Nullhomotopy) :
    Set.range A.toPresentation.obstructionClass = {A.toPresentation.obstructionClass b} := by
  ext o
  constructor
  · rintro ⟨b', rfl⟩
    simpa using A.toPresentation.obstructionClass_independent b b'
  · intro ho
    have ho' : o = A.toPresentation.obstructionClass b := by simpa using ho
    exact ⟨b, ho'.symm⟩

end Layer

/-! ### Exact nonzero-secondary model -/

/-- A one-dimensional cohomology model with vanishing primary layer but secondary class `1`. -/
def nonzeroSecondaryLayer : Layer ℝ where
  Nullhomotopy := Unit
  Representative := ℝ
  representativeAdd := inferInstance
  representativeModule := inferInstance
  boundaries := ⊥
  raw := fun _ ↦ 1
  change_exact := by intro b b'; simp
  Next := Empty
  extension_iff := by
    constructor
    · rintro ⟨h⟩
      exact Empty.elim h
    · rintro ⟨b, hb⟩
      change (⊥ : Submodule ℝ ℝ).mkQ (1 : ℝ) = 0 at hb
      have hmem : (1 : ℝ) ∈ LinearMap.ker (⊥ : Submodule ℝ ℝ).mkQ := hb
      rw [Submodule.ker_mkQ] at hmem
      norm_num at hmem

theorem nonzeroSecondaryLayer_class_ne_zero :
    nonzeroSecondaryLayer.toPresentation.obstructionClass () ≠ 0 := by
  intro h
  change (⊥ : Submodule ℝ ℝ).mkQ (1 : ℝ) = 0 at h
  have hmem : (1 : ℝ) ∈ LinearMap.ker (⊥ : Submodule ℝ ℝ).mkQ := h
  rw [Submodule.ker_mkQ] at hmem
  norm_num at hmem

theorem nonzeroSecondaryLayer_not_extendible : ¬ Nonempty nonzeroSecondaryLayer.Next :=
  not_nonempty_empty

end Secondary

/-! ## Exact two-step class-erasure model -/

namespace Countermodel

/-! ### Layer-level exact false-flatness model -/

/-- One represented source branch carrying obstruction `1`, hence no next flattening. -/
def obstructedLayer : ObstructionLayer ℝ where
  Partial := PUnit
  Next := PEmpty
  Cohomology := ℝ
  cohomologyAdd := inferInstance
  cohomologyModule := inferInstance
  obstruction := fun _ ↦ 1
  extension_iff := by
    constructor
    · rintro ⟨h⟩
      exact PEmpty.elim h
    · rintro ⟨_, h⟩
      norm_num at h

/-- One target branch with zero obstruction and an actual next flattening. -/
def flatLayer : ObstructionLayer ℝ where
  Partial := PUnit
  Next := PUnit
  Cohomology := ℝ
  cohomologyAdd := inferInstance
  cohomologyModule := inferInstance
  obstruction := fun _ ↦ 0
  extension_iff := by
    constructor
    · intro _
      exact ⟨PUnit.unit, rfl⟩
    · intro _
      exact ⟨PUnit.unit⟩

/-- Strict observer killing the source obstruction class. -/
def erasingObserver : Observer obstructedLayer flatLayer where
  push := fun β ↦ β
  cohomologyMap := (0 : ℝ →ₗ[ℝ] ℝ)
  obstruction_natural := fun _ ↦ rfl

theorem erasingObserver_is_classErasure : erasingObserver.ClassErasure := by
  refine ⟨PUnit.unit, ?_, ?_⟩
  · change (1 : ℝ) ≠ 0
    norm_num
  · rfl

theorem erasingObserver_is_falseFlat : erasingObserver.FalseFlatness := by
  constructor
  · exact ⟨PUnit.unit⟩
  · exact not_nonempty_pempty

/-! ### Spectrum inclusion can be strict -/

def zeroSpectrumLayer : ObstructionLayer ℝ where
  Partial := PUnit
  Next := PUnit
  Cohomology := ℝ
  cohomologyAdd := inferInstance
  cohomologyModule := inferInstance
  obstruction := fun _ ↦ 0
  extension_iff := by
    constructor
    · intro _
      exact ⟨PUnit.unit, rfl⟩
    · intro _
      exact ⟨PUnit.unit⟩

def extraBranchLayer : ObstructionLayer ℝ where
  Partial := Bool
  Next := PUnit
  Cohomology := ℝ
  cohomologyAdd := inferInstance
  cohomologyModule := inferInstance
  obstruction := fun β ↦ if β then 1 else 0
  extension_iff := by
    constructor
    · intro _
      exact ⟨false, by simp⟩
    · intro _
      exact ⟨PUnit.unit⟩

def strictSpectrumObserver : Observer zeroSpectrumLayer extraBranchLayer where
  push := fun _ ↦ false
  cohomologyMap := LinearMap.id (R := ℝ) (M := ℝ)
  obstruction_natural := fun _ ↦ rfl

/-- Exact Massey-indeterminacy model: one obstruction spectrum contains both zero and a nonzero
class. -/
theorem extraBranchLayer_spectrum_multivalued :
    (0 : ℝ) ∈ extraBranchLayer.spectrum ∧
      (1 : ℝ) ∈ extraBranchLayer.spectrum ∧ (0 : ℝ) ≠ 1 := by
  exact ⟨⟨false, by simp [extraBranchLayer]⟩,
    ⟨true, by simp [extraBranchLayer]⟩, by norm_num⟩

theorem spectrum_inclusion_is_strict :
    strictSpectrumObserver.cohomologyMap '' zeroSpectrumLayer.spectrum ⊂
      extraBranchLayer.spectrum := by
  constructor
  · exact strictSpectrumObserver.image_spectrum_subset
  · intro h
    have hone : (1 : ℝ) ∈ extraBranchLayer.spectrum := by
      exact ⟨true, by simp [extraBranchLayer]⟩
    have himage := h hone
    obtain ⟨o, ⟨β, hβ⟩, ho⟩ := himage
    simp [zeroSpectrumLayer] at hβ
    subst o
    change (0 : ℝ) = 1 at ho
    norm_num at ho

/-- Coefficient space with basis `(x,v)`. -/
abbrev TwoStep := ℝ × ℝ

def x : TwoStep := (1, 0)
def v : TwoStep := (0, 1)

/-- Only nonzero graded bracket: `[x,x]=v`. -/
def bracket (a b : TwoStep) : TwoStep := (0, a.1 * b.1)

/-- Quotient by the central curvature generator `v`. -/
def quotientObserver : TwoStep →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ

@[simp] theorem bracket_x_x : bracket x x = v := by
  norm_num [bracket, x, v]

@[simp] theorem quotientObserver_v : quotientObserver v = 0 := by
  rfl

theorem v_ne_zero : v ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  norm_num [v] at this

/-- The exact source obstruction is nonzero and its strict quotient observer is flat. -/
theorem exact_class_erasure :
    v ≠ 0 ∧ quotientObserver v = 0 ∧ quotientObserver (bracket x x) = 0 :=
  ⟨v_ne_zero, quotientObserver_v, by simp⟩

/-- Quotient observer kills every bracket value, so the target algebra is abelian. -/
theorem quotient_bracket_zero (a b : TwoStep) : quotientObserver (bracket a b) = 0 :=
  rfl

end Countermodel

end

end HTGeometry.NomologicalHomotopyGeometry.ObserverCurvature
