import GaloisForLFunctions.RHTower.DeningerFinestClosed
import GaloisForLFunctions.RHTower.DeningerPlaceSpace

/-!
# The test space is the strict inductive limit of its finite-dimensional steps

On a discrete space the step of an exhaustion is the space of test functions supported in a fixed
set.  For a finite set that space is finite dimensional, because evaluation at the points of the
set is injective on it, and the steps of an increasing exhaustion are directed and exhaust the
whole test space, because every test function has finite support.

Every subspace of the test space is closed for the finest locally convex topology, so these
inclusions have closed image: the test space is a strict countable inductive limit of finite
dimensional spaces.  Any two exhaustions give the same limit, since both give the whole space, so
the description does not depend on the chosen exhaustion.

* `deningerTestStep` : the test functions supported in a set.
* `deningerTestStep_finiteDimensional` : **a step over a finite set is finite dimensional.**
* `deningerTestStep_iSup_eq_top` : **the steps of an exhaustion exhaust the test space.**
* `deningerTestStep_exhaustion_independent` : the limit is independent of the exhaustion.
* `deningerTest_indLim` : the four properties, bundled.
* `deningerPlaceTest_indLim` : the inductive limit description over the places of a number field.
-/

namespace RHTower

open NumberField

section Step

variable {Y : Type*} [TopologicalSpace Y]

/-- The step of an exhaustion: the test functions supported in `S`. -/
def deningerTestStep (S : Set Y) : Submodule ℝ (DeningerTestSpace Y) where
  carrier := {f | Function.support ((f : DeningerTestSpace Y) : Y → ℝ) ⊆ S}
  add_mem' := by
    intro f g hf hg y hy
    by_cases hfy : ((f : DeningerTestSpace Y) : Y → ℝ) y = 0
    · refine hg ?_
      intro hzero
      apply hy
      show ((f : DeningerTestSpace Y) : Y → ℝ) y + ((g : DeningerTestSpace Y) : Y → ℝ) y = 0
      rw [hfy, hzero, add_zero]
    · exact hf hfy
  zero_mem' := by
    intro y hy
    exact absurd rfl hy
  smul_mem' := by
    intro c f hf y hy
    refine hf ?_
    intro hzero
    apply hy
    show c * ((f : DeningerTestSpace Y) : Y → ℝ) y = 0
    rw [hzero, mul_zero]

theorem deningerTestStep_mem {S : Set Y} {f : DeningerTestSpace Y} :
    f ∈ deningerTestStep S ↔ Function.support ((f : DeningerTestSpace Y) : Y → ℝ) ⊆ S :=
  Iff.rfl

/-- The steps grow with the set. -/
theorem deningerTestStep_mono {S T : Set Y} (hST : S ⊆ T) :
    deningerTestStep S ≤ deningerTestStep T :=
  fun _ hf => hf.trans hST

/-- Evaluation at the points of `S`, on the step of `S`. -/
def deningerStepEval (S : Set Y) : deningerTestStep S →ₗ[ℝ] (S → ℝ) where
  toFun f := fun s => ((f : DeningerTestSpace Y) : Y → ℝ) (s : Y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deningerStepEval_injective (S : Set Y) :
    Function.Injective (deningerStepEval S) := by
  intro f g hfg
  refine Subtype.ext (Subtype.ext (funext fun y => ?_))
  by_cases hy : y ∈ S
  · exact congrFun hfg ⟨y, hy⟩
  · have hf : ((f : DeningerTestSpace Y) : Y → ℝ) y = 0 := by
      by_contra hne
      exact hy (f.2 hne)
    have hg : ((g : DeningerTestSpace Y) : Y → ℝ) y = 0 := by
      by_contra hne
      exact hy (g.2 hne)
    rw [hf, hg]

/-- **A step over a finite set is finite dimensional**: evaluation at the points of the set is an
injection into a finite product of lines. -/
theorem deningerTestStep_finiteDimensional {S : Set Y} (hS : S.Finite) :
    FiniteDimensional ℝ (deningerTestStep S) := by
  haveI : Fintype S := hS.fintype
  exact Module.Finite.of_injective (deningerStepEval S) (deningerStepEval_injective S)

end Step

section Exhaustion

variable {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]

/-- **The steps of an increasing exhaustion exhaust the test space**: a test function has finite
support, and a finite set already lies in one step. -/
theorem deningerTestStep_iSup_eq_top (S : ℕ → Set Y) (hmono : Monotone S)
    (hcover : ∀ y, ∃ m, y ∈ S m) :
    ⨆ m, deningerTestStep (S m) = (⊤ : Submodule ℝ (DeningerTestSpace Y)) := by
  classical
  choose g hg using hcover
  refine eq_top_iff.mpr fun f _ => ?_
  have hfin : (Function.support ((f : DeningerTestSpace Y) : Y → ℝ)).Finite :=
    f.2.2.finite_of_discrete
  set N : ℕ := hfin.toFinset.sup g with hN
  have hmem : f ∈ deningerTestStep (S N) := by
    intro y hy
    have hle : g y ≤ N := Finset.le_sup (hfin.mem_toFinset.mpr hy)
    exact hmono hle (hg y)
  exact Submodule.mem_iSup_of_mem N hmem

/-- **The inductive limit does not depend on the exhaustion**: any two increasing exhaustions give
the whole test space. -/
theorem deningerTestStep_exhaustion_independent (S T : ℕ → Set Y) (hS : Monotone S)
    (hT : Monotone T) (hScover : ∀ y, ∃ m, y ∈ S m) (hTcover : ∀ y, ∃ m, y ∈ T m) :
    ⨆ m, deningerTestStep (S m) = ⨆ m, deningerTestStep (T m) := by
  rw [deningerTestStep_iSup_eq_top S hS hScover, deningerTestStep_iSup_eq_top T hT hTcover]

/-- **The test space is a strict countable inductive limit of finite dimensional spaces**: the
steps of an increasing exhaustion by finite sets are finite dimensional, directed, closed for the
finest locally convex topology, and their supremum is the whole space. -/
theorem deningerTest_indLim (S : ℕ → Set Y) (hmono : Monotone S) (hfin : ∀ m, (S m).Finite)
    (hcover : ∀ y, ∃ m, y ∈ S m) :
    (∀ m, FiniteDimensional ℝ (deningerTestStep (S m)))
      ∧ Monotone (fun m => deningerTestStep (S m))
      ∧ Directed (· ≤ ·) (fun m => deningerTestStep (S m))
      ∧ (∀ (m : ℕ) (g : DeningerTestSpace Y), g ∉ deningerTestStep (S m) →
          ∃ (p : Seminorm ℝ (DeningerTestSpace Y)) (c : ℝ), 0 < c ∧
            ∀ v ∈ deningerTestStep (S m), c ≤ p (g - v))
      ∧ ⨆ m, deningerTestStep (S m) = ⊤ := by
  have hstepmono : Monotone fun m => deningerTestStep (S m) :=
    fun _ _ h => deningerTestStep_mono (hmono h)
  exact ⟨fun m => deningerTestStep_finiteDimensional (hfin m), hstepmono,
    hstepmono.directed_le,
    fun m g hg => deningerTestSubspace_closed (deningerTestStep (S m)) hg,
    deningerTestStep_iSup_eq_top S hmono hcover⟩

/-- A countable discrete space has an increasing exhaustion by finite sets. -/
theorem deningerExists_exhaustion (Y : Type*) [Countable Y] [Nonempty Y] :
    ∃ S : ℕ → Set Y, Monotone S ∧ (∀ m, (S m).Finite) ∧ ∀ y, ∃ m, y ∈ S m := by
  obtain ⟨e, he⟩ := exists_surjective_nat Y
  refine ⟨fun m => e '' Set.Iic m, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Set.image_mono (Set.Iic_subset_Iic.mpr hmn)
  · intro m
    exact (Set.finite_Iic m).image e
  · intro y
    obtain ⟨n, rfl⟩ := he y
    exact ⟨n, ⟨n, le_refl n, rfl⟩⟩

end Exhaustion

section PlaceModel

variable (K : Type*) [Field K] [NumberField K]

instance : Nonempty (DeningerPlace K) := ⟨Sum.inl (Classical.arbitrary (InfinitePlace K))⟩

/-- **The inductive limit description over the places of a number field.**  There is an increasing
exhaustion of the place space by finite sets whose steps are finite dimensional, directed, closed,
and exhaust the test space of the place space. -/
theorem deningerPlaceTest_indLim :
    ∃ S : ℕ → Set (DeningerPlace K), Monotone S ∧ (∀ m, (S m).Finite) ∧
      (∀ m, FiniteDimensional ℝ (deningerTestStep (S m)))
        ∧ Directed (· ≤ ·) (fun m => deningerTestStep (S m))
        ∧ ⨆ m, deningerTestStep (S m) = ⊤ := by
  obtain ⟨S, hmono, hfin, hcover⟩ := deningerExists_exhaustion (DeningerPlace K)
  obtain ⟨hdim, _, hdir, _, htop⟩ := deningerTest_indLim S hmono hfin hcover
  exact ⟨S, hmono, hfin, hdim, hdir, htop⟩

end PlaceModel

end RHTower
