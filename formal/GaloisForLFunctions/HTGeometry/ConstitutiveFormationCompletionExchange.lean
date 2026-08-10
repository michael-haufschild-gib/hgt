import GaloisForLFunctions.HTGeometry.ConstitutiveFinitaryFormation
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-!
# Finite formation depth and completion exchange

A finite family of continuous self-maps on a compact Hausdorff space commutes with topological
closure at every bounded word depth.  Consequently every point born only after completing the
full finite-word saturation is approached by realizations of unbounded word depth.  Finite changes
of generators preserve this divergence up to multiplicative constants, while an equivariant
observer can erase but cannot create a completion boundary.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- A point map acts on law sets by direct image. -/
def imageFormation {X : Type u} {ι : Type v} (φ : ι → X → X)
    (i : ι) (A : Set X) : Set X :=
  φ i '' A

/-- Laws reachable by formation words of length at most `d`. -/
def boundedFormationReach {X : Type u} {ι : Type v} (φ : ι → X → X)
    (d : ℕ) (A : Set X) : Set X :=
  ⋃ w ∈ {w : List ι | w.length ≤ d}, runFormations (imageFormation φ) w A

/-- Laws reachable by arbitrary finite formation words. -/
def formationSaturation {X : Type u} {ι : Type v} (φ : ι → X → X)
    (A : Set X) : Set X :=
  wordSaturation (imageFormation φ) A

/-- Laws present after completing finite-word saturation but absent from the finite-word
saturation of the completed input. -/
def formationCompletionBoundary {X : Type u} {ι : Type v} [TopologicalSpace X]
    (φ : ι → X → X) (A : Set X) : Set X :=
  closure (formationSaturation φ A) \ formationSaturation φ (closure A)

@[simp] theorem mem_boundedFormationReach {X : Type u} {ι : Type v}
    {φ : ι → X → X} {d : ℕ} {A : Set X} {x : X} :
    x ∈ boundedFormationReach φ d A ↔
      ∃ w : List ι, w.length ≤ d ∧ x ∈ runFormations (imageFormation φ) w A := by
  simp [boundedFormationReach]

@[simp] theorem mem_formationSaturation {X : Type u} {ι : Type v}
    {φ : ι → X → X} {A : Set X} {x : X} :
    x ∈ formationSaturation φ A ↔
      ∃ w : List ι, x ∈ runFormations (imageFormation φ) w A := by
  rfl

theorem boundedFormationReach_subset_saturation {X : Type u} {ι : Type v}
    (φ : ι → X → X) (d : ℕ) (A : Set X) :
    boundedFormationReach φ d A ⊆ formationSaturation φ A := by
  intro x hx
  obtain ⟨w, _hw, hxw⟩ := mem_boundedFormationReach.mp hx
  exact mem_formationSaturation.mpr ⟨w, hxw⟩

theorem formationSaturation_eq_iUnion_bounded {X : Type u} {ι : Type v}
    (φ : ι → X → X) (A : Set X) :
    formationSaturation φ A = ⋃ d : ℕ, boundedFormationReach φ d A := by
  ext x
  constructor
  · rintro ⟨w, hxw⟩
    exact mem_iUnion.mpr ⟨w.length, mem_boundedFormationReach.mpr ⟨w, le_rfl, hxw⟩⟩
  · intro hx
    obtain ⟨d, hxd⟩ := mem_iUnion.mp hx
    exact boundedFormationReach_subset_saturation φ d A hxd

theorem runImageFormations_closure {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i))
    (w : List ι) (A : Set X) :
    closure (runFormations (imageFormation φ) w A) =
      runFormations (imageFormation φ) w (closure A) := by
  induction w generalizing A with
  | nil => rfl
  | cons i w ih =>
      rw [runFormations_cons, ih]
      change runFormations (imageFormation φ) w (closure (φ i '' A)) =
        runFormations (imageFormation φ) w (φ i '' closure A)
      rw [(hφ i).isClosedMap.closure_image_eq_of_continuous (hφ i)]

/-- **Finite-depth formation/completion exchange.** -/
theorem boundedFormationReach_closure {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Finite ι]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i))
    (d : ℕ) (A : Set X) :
    closure (boundedFormationReach φ d A) = boundedFormationReach φ d (closure A) := by
  rw [boundedFormationReach,
    (List.finite_length_le ι d).closure_biUnion]
  simp_rw [runImageFormations_closure φ hφ]
  rfl

theorem runImageFormations_subset_of_invariant {X : Type u} {ι : Type v}
    (φ : ι → X → X) {A C : Set X} (hAC : A ⊆ C)
    (hC : ∀ i, imageFormation φ i C ⊆ C) (w : List ι) :
    runFormations (imageFormation φ) w A ⊆ C := by
  induction w generalizing A with
  | nil => exact hAC
  | cons i w ih =>
      exact ih ((image_mono hAC).trans (hC i))

theorem formationSaturation_subset_of_invariant {X : Type u} {ι : Type v}
    (φ : ι → X → X) {A C : Set X} (hAC : A ⊆ C)
    (hC : ∀ i, imageFormation φ i C ⊆ C) :
    formationSaturation φ A ⊆ C := by
  rintro x ⟨w, hxw⟩
  exact runImageFormations_subset_of_invariant φ hAC hC w hxw

theorem imageFormation_saturation_subset {X : Type u} {ι : Type v}
    (φ : ι → X → X) (i : ι) (A : Set X) :
    imageFormation φ i (formationSaturation φ A) ⊆ formationSaturation φ A := by
  rintro x ⟨y, ⟨w, hyw⟩, rfl⟩
  refine mem_formationSaturation.mpr ⟨w ++ [i], ?_⟩
  rw [runFormations_append]
  exact ⟨y, hyw, rfl⟩

/-- The closure of finite-word saturation is the least closed invariant law space. -/
theorem closure_formationSaturation_least {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (φ : ι → X → X)
    {A C : Set X} (hAC : A ⊆ C) (hCclosed : IsClosed C)
    (hC : ∀ i, imageFormation φ i C ⊆ C) :
    closure (formationSaturation φ A) ⊆ C := by
  apply closure_minimal
  · exact formationSaturation_subset_of_invariant φ hAC hC
  · exact hCclosed

theorem imageFormation_closure_saturation_subset {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i))
    (i : ι) (A : Set X) :
    imageFormation φ i (closure (formationSaturation φ A)) ⊆
      closure (formationSaturation φ A) := by
  change φ i '' closure (formationSaturation φ A) ⊆ _
  rw [← (hφ i).isClosedMap.closure_image_eq_of_continuous (hφ i)]
  exact closure_mono (imageFormation_saturation_subset φ i A)

theorem formationSaturation_closure_subset_closure_saturation {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i)) (A : Set X) :
    formationSaturation φ (closure A) ⊆ closure (formationSaturation φ A) := by
  apply formationSaturation_subset_of_invariant φ
  · exact closure_mono (wordSaturation_extensive (imageFormation φ) A)
  · exact fun i => imageFormation_closure_saturation_subset φ hφ i A

theorem formationSaturation_closure_eq_iUnion_stageClosure {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Finite ι]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i)) (A : Set X) :
    formationSaturation φ (closure A) =
      ⋃ d : ℕ, closure (boundedFormationReach φ d A) := by
  rw [formationSaturation_eq_iUnion_bounded]
  simp_rw [boundedFormationReach_closure φ hφ]

/-- The completion boundary is exactly closure of the filtered union minus union of stage
closures. -/
theorem formationCompletionBoundary_eq_limitExchange {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Finite ι]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i)) (A : Set X) :
    formationCompletionBoundary φ A =
      closure (⋃ d : ℕ, boundedFormationReach φ d A) \
        ⋃ d : ℕ, closure (boundedFormationReach φ d A) := by
  rw [formationCompletionBoundary, formationSaturation_eq_iUnion_bounded,
    formationSaturation_closure_eq_iUnion_stageClosure φ hφ]

/-- Every neighbourhood of a completion-born law contains an effective realization beyond every
fixed formation depth. -/
theorem completionBoundary_nhds_exists_beyond {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Finite ι]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i))
    {A : Set X} {x : X} (hx : x ∈ formationCompletionBoundary φ A)
    {U : Set X} (hU : U ∈ 𝓝 x) (d : ℕ) :
    ∃ y, y ∈ U ∧ y ∈ formationSaturation φ A ∧ y ∉ boundedFormationReach φ d A := by
  rcases hx with ⟨hxClosure, hxNotCompleted⟩
  by_contra h
  push Not at h
  have hxStageClosure : x ∈ closure (boundedFormationReach φ d A) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    have hUV : U ∩ V ∈ 𝓝 x := Filter.inter_mem hU hV
    obtain ⟨y, hyUV, hySat⟩ := (mem_closure_iff_nhds.mp hxClosure) (U ∩ V) hUV
    exact ⟨y, hyUV.2, h y hyUV.1 hySat⟩
  have hxStageCompleted : x ∈ boundedFormationReach φ d (closure A) := by
    rw [← boundedFormationReach_closure φ hφ]
    exact hxStageClosure
  exact hxNotCompleted (boundedFormationReach_subset_saturation φ d (closure A) hxStageCompleted)

/-- Uniformly bounded formation depth forbids completed-law birth. -/
theorem formationCompletionBoundary_eq_empty_of_bounded_saturation {X : Type u} {ι : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Finite ι]
    (φ : ι → X → X) (hφ : ∀ i, Continuous (φ i))
    (A : Set X) (D : ℕ) (hD : formationSaturation φ A = boundedFormationReach φ D A) :
    formationCompletionBoundary φ A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hx with ⟨hxClosure, hxNotCompleted⟩
  rw [hD, boundedFormationReach_closure φ hφ] at hxClosure
  exact hxNotCompleted (boundedFormationReach_subset_saturation φ D (closure A) hxClosure)

/-! ## Bounded changes of generators -/

/-- Expand each letter using a finite dictionary in another formation family. -/
def expandFormationWord {ι : Type v} {κ : Type w}
    (code : ι → List κ) (w : List ι) : List κ :=
  w.flatMap code

theorem runFormations_expandFormationWord {X : Type u} {ι : Type v} {κ : Type w}
    (φ : ι → Set X → Set X) (ψ : κ → Set X → Set X)
    (code : ι → List κ)
    (hcode : ∀ i A, runFormations ψ (code i) A = φ i A)
    (w : List ι) (A : Set X) :
    runFormations ψ (expandFormationWord code w) A = runFormations φ w A := by
  induction w generalizing A with
  | nil => rfl
  | cons i w ih =>
      rw [expandFormationWord, List.flatMap_cons, runFormations_append,
        hcode i A, runFormations_cons]
      simpa only [expandFormationWord] using ih (φ i A)

theorem length_expandFormationWord_le {ι : Type v} {κ : Type w}
    (code : ι → List κ) (a : ℕ) (hcode : ∀ i, (code i).length ≤ a)
    (w : List ι) :
    (expandFormationWord code w).length ≤ a * w.length := by
  induction w with
  | nil => simp [expandFormationWord]
  | cons i w ih =>
      simp only [expandFormationWord, List.flatMap_cons, List.length_append, List.length_cons]
      calc
        (code i).length + (List.flatMap code w).length ≤ a + a * w.length :=
          Nat.add_le_add (hcode i) ih
        _ = a * (w.length + 1) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- A dictionary of generator words with maximum length `a` multiplies reach depth by at most
`a`. -/
theorem boundedFormationReach_subset_of_dictionary {X : Type u} {ι : Type v} {κ : Type w}
    (φ : ι → X → X) (ψ : κ → X → X) (code : ι → List κ)
    (a d : ℕ) (hcodeLen : ∀ i, (code i).length ≤ a)
    (hcode : ∀ i A,
      runFormations (imageFormation ψ) (code i) A = imageFormation φ i A)
    (A : Set X) :
    boundedFormationReach φ d A ⊆ boundedFormationReach ψ (a * d) A := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_boundedFormationReach.mp hx
  refine mem_boundedFormationReach.mpr ⟨expandFormationWord code w, ?_, ?_⟩
  · exact (length_expandFormationWord_le code a hcodeLen w).trans
      (Nat.mul_le_mul_left a hw)
  · rwa [runFormations_expandFormationWord (imageFormation φ) (imageFormation ψ) code hcode]

theorem formationSaturation_subset_of_dictionary {X : Type u} {ι : Type v} {κ : Type w}
    (φ : ι → X → X) (ψ : κ → X → X) (code : ι → List κ)
    (hcode : ∀ i A,
      runFormations (imageFormation ψ) (code i) A = imageFormation φ i A)
    (A : Set X) :
    formationSaturation φ A ⊆ formationSaturation ψ A := by
  rintro x ⟨w, hxw⟩
  refine mem_formationSaturation.mpr ⟨expandFormationWord code w, ?_⟩
  rwa [runFormations_expandFormationWord (imageFormation φ) (imageFormation ψ) code hcode]

/-- Mutually bounded dictionaries give the same generated law space and the same completion
boundary. -/
theorem formationCompletionBoundary_eq_of_mutual_dictionaries
    {X : Type u} {ι : Type v} {κ : Type w} [TopologicalSpace X]
    (φ : ι → X → X) (ψ : κ → X → X)
    (codeφ : ι → List κ) (codeψ : κ → List ι)
    (hφ : ∀ i A,
      runFormations (imageFormation ψ) (codeφ i) A = imageFormation φ i A)
    (hψ : ∀ j A,
      runFormations (imageFormation φ) (codeψ j) A = imageFormation ψ j A)
    (A : Set X) :
    formationCompletionBoundary φ A = formationCompletionBoundary ψ A := by
  have hsat : formationSaturation φ A = formationSaturation ψ A :=
    Set.Subset.antisymm
      (formationSaturation_subset_of_dictionary φ ψ codeφ hφ A)
      (formationSaturation_subset_of_dictionary ψ φ codeψ hψ A)
  have hsatClosure : formationSaturation φ (closure A) =
      formationSaturation ψ (closure A) :=
    Set.Subset.antisymm
      (formationSaturation_subset_of_dictionary φ ψ codeφ hφ (closure A))
      (formationSaturation_subset_of_dictionary ψ φ codeψ hψ (closure A))
  simp only [formationCompletionBoundary, hsat, hsatClosure]

/-! ## Equivariant observers -/

theorem observer_runFormations_image {X : Type u} {Y : Type v} {ι : Type w}
    (φ : ι → X → X) (ψ : ι → Y → Y) (q : X → Y)
    (hq : ∀ i x, q (φ i x) = ψ i (q x))
    (w : List ι) (A : Set X) :
    q '' runFormations (imageFormation φ) w A =
      runFormations (imageFormation ψ) w (q '' A) := by
  induction w generalizing A with
  | nil => rfl
  | cons i w ih =>
      rw [runFormations_cons, runFormations_cons, ih]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨q a, ⟨a, ha, rfl⟩, (hq i a).symm⟩
      · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨φ i a, ⟨a, ha, rfl⟩, hq i a⟩

theorem observer_boundedFormationReach {X : Type u} {Y : Type v} {ι : Type w}
    (φ : ι → X → X) (ψ : ι → Y → Y) (q : X → Y)
    (hq : ∀ i x, q (φ i x) = ψ i (q x))
    (d : ℕ) (A : Set X) :
    q '' boundedFormationReach φ d A = boundedFormationReach ψ d (q '' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hxw⟩ := mem_boundedFormationReach.mp hx
    refine mem_boundedFormationReach.mpr ⟨w, hw, ?_⟩
    rw [← observer_runFormations_image φ ψ q hq w A]
    exact ⟨x, hxw, rfl⟩
  · intro hy
    obtain ⟨w, hw, hyw⟩ := mem_boundedFormationReach.mp hy
    rw [← observer_runFormations_image φ ψ q hq w A] at hyw
    obtain ⟨x, hxw, rfl⟩ := hyw
    exact ⟨x, mem_boundedFormationReach.mpr ⟨w, hw, hxw⟩, rfl⟩

theorem observer_formationSaturation {X : Type u} {Y : Type v} {ι : Type w}
    (φ : ι → X → X) (ψ : ι → Y → Y) (q : X → Y)
    (hq : ∀ i x, q (φ i x) = ψ i (q x)) (A : Set X) :
    q '' formationSaturation φ A = formationSaturation ψ (q '' A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, hxw⟩, rfl⟩
    refine mem_formationSaturation.mpr ⟨w, ?_⟩
    rw [← observer_runFormations_image φ ψ q hq w A]
    exact ⟨x, hxw, rfl⟩
  · rintro ⟨w, hyw⟩
    rw [← observer_runFormations_image φ ψ q hq w A] at hyw
    obtain ⟨x, hxw, rfl⟩ := hyw
    exact ⟨x, mem_formationSaturation.mpr ⟨w, hxw⟩, rfl⟩

theorem image_diff_superset_diff_image {X : Type u} {Y : Type v}
    (q : X → Y) (C D : Set X) :
    q '' C \ q '' D ⊆ q '' (C \ D) := by
  intro y hy
  obtain ⟨x, hxC, rfl⟩ := hy.1
  exact ⟨x, ⟨hxC, fun hxD => hy.2 ⟨x, hxD, rfl⟩⟩, rfl⟩

/-- An equivariant observer can erase but cannot create a formation-completion boundary. -/
theorem observer_completionBoundary_subset {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : ι → X → X) (ψ : ι → Y → Y) (q : X → Y)
    (hqcont : Continuous q) (hq : ∀ i x, q (φ i x) = ψ i (q x))
    (A : Set X) :
    formationCompletionBoundary ψ (q '' A) ⊆
      q '' formationCompletionBoundary φ A := by
  have hqClosure (S : Set X) : q '' closure S = closure (q '' S) := by
    rw [← hqcont.isClosedMap.closure_image_eq_of_continuous hqcont]
  rw [formationCompletionBoundary, formationCompletionBoundary,
    ← observer_formationSaturation φ ψ q hq A,
    ← hqClosure (formationSaturation φ A),
    ← hqClosure A,
    ← observer_formationSaturation φ ψ q hq (closure A)]
  exact image_diff_superset_diff_image q _ _

/-- An injective equivariant observer preserves the completion boundary exactly. -/
theorem observer_completionBoundary_eq_of_injective {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : ι → X → X) (ψ : ι → Y → Y) (q : X → Y)
    (hqcont : Continuous q) (hqinj : Function.Injective q)
    (hq : ∀ i x, q (φ i x) = ψ i (q x)) (A : Set X) :
    formationCompletionBoundary ψ (q '' A) =
      q '' formationCompletionBoundary φ A := by
  have hqClosure (S : Set X) : q '' closure S = closure (q '' S) := by
    rw [← hqcont.isClosedMap.closure_image_eq_of_continuous hqcont]
  rw [formationCompletionBoundary, formationCompletionBoundary,
    ← observer_formationSaturation φ ψ q hq A,
    ← hqClosure (formationSaturation φ A),
    ← hqClosure A,
    ← observer_formationSaturation φ ψ q hq (closure A),
    ← Set.image_sdiff hqinj]

/-! ## Sharp finite-signature countermodel -/

/-- An infinite family of continuous constant formations on the one-point compactification of
`ℕ`. -/
def infiniteConstantFormationFamily (n : ℕ) (_x : OnePoint ℕ) : OnePoint ℕ :=
  OnePoint.some n

theorem infiniteConstantFormationFamily_reach_one :
    boundedFormationReach infiniteConstantFormationFamily 1
      ({OnePoint.some 0} : Set (OnePoint ℕ)) =
      Set.range ((↑) : ℕ → OnePoint ℕ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, hxw⟩ := mem_boundedFormationReach.mp hx
    cases w with
    | nil =>
        change x = OnePoint.some 0 at hxw
        exact ⟨0, hxw.symm⟩
    | cons i w =>
        have hw0 : w = [] := by
          simpa using hw
        subst w
        have hxi : x = OnePoint.some i := by
          simpa [imageFormation, infiniteConstantFormationFamily] using hxw
        exact ⟨i, hxi.symm⟩
  · rintro ⟨n, rfl⟩
    exact mem_boundedFormationReach.mpr
      ⟨[n], by simp, by simp [imageFormation, infiniteConstantFormationFamily]⟩

/-- Finiteness of the formation signature is load-bearing: with infinitely many continuous
constant generators, completion already fails to exchange with depth one. -/
theorem infiniteSignature_depthOne_completionExchange_fails :
    closure (boundedFormationReach infiniteConstantFormationFamily 1
      ({OnePoint.some 0} : Set (OnePoint ℕ))) ≠
      boundedFormationReach infiniteConstantFormationFamily 1
        (closure ({OnePoint.some 0} : Set (OnePoint ℕ))) := by
  intro h
  have hinLeft : OnePoint.infty ∈
      closure (boundedFormationReach infiniteConstantFormationFamily 1
        ({OnePoint.some 0} : Set (OnePoint ℕ))) := by
    rw [infiniteConstantFormationFamily_reach_one]
    exact (OnePoint.denseRange_coe (X := ℕ)).closure_eq ▸ mem_univ OnePoint.infty
  have hinRight : OnePoint.infty ∈
      boundedFormationReach infiniteConstantFormationFamily 1
        (closure ({OnePoint.some 0} : Set (OnePoint ℕ))) := h ▸ hinLeft
  rw [isClosed_singleton.closure_eq, infiniteConstantFormationFamily_reach_one] at hinRight
  exact OnePoint.infty_notMem_range_coe hinRight

end GaloisForLFunctions.HTGeometry
