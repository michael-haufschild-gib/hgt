import GaloisForLFunctions.HTGeometry.ExactnessFlagProvenanceTopology
import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# Completion defects as provenance-exactness flags

An exactness defect is not merely a nonzero scalar in a quotient.  It records two logically
different facts: a vector remains an admissible cycle, but it has ceased to be a boundary after a
change of presentation or completion.  The mixed lower--Scott topology on exactness flags retains
both facts.

This file connects that topology to the algebraic completion defects already used in the corpus.

* `boundaryExactnessFlag J` has boundary space `J` and full cycle space.
* `boundaryEscapeClass` is the class of one source boundary whose image may escape the target
  boundary space.
* `boundaryEscapeClass_ne_zero_iff_survival` identifies nonzero escape with membership in the open
  framed-survival locus of the target flag.
* `escapeFree_iff_no_boundary_survival` says a boundary migration is exact precisely when no source
  boundary survives as a target defect.
* `derivedLimitExactnessFlag` turns the Roos presentation of `lim^(1 : ℕ)` into the same topological
  object; a surviving vector is exactly a nonzero derived-limit class.

No vanishing or exactness premise is introduced.  The constructions expose failures of completion
rather than declaring them absent.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {k : Type u} [Field k]
variable {V W : Type v}
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Exactness flag whose boundaries are `J` and whose admissible cycles are all vectors. -/
def boundaryExactnessFlag (J : Submodule k W) : ExFlag k W :=
  ⟨J, ⊤, le_top⟩

@[simp] theorem boundaryExactnessFlag_boundary (J : Submodule k W) :
    (boundaryExactnessFlag J).boundary = J := rfl

@[simp] theorem boundaryExactnessFlag_cycle (J : Submodule k W) :
    (boundaryExactnessFlag J).cycle = ⊤ := rfl

/-- One source boundary, regarded inside the image of the full source boundary space. -/
def mappedBoundaryVector (f : V →ₗ[k] W) (Jsource : Submodule k V)
    (x : V) (hx : x ∈ Jsource) : Jsource.map f :=
  ⟨f x, Submodule.mem_map_of_mem hx⟩

/-- Quotient class of one source boundary that may fail to remain a boundary in the target. -/
def boundaryEscapeClass (f : V →ₗ[k] W) (Jsource : Submodule k V)
    (Jtarget : Submodule k W) (x : V) (hx : x ∈ Jsource) :
    EscapeDefect f Jsource Jtarget :=
  Submodule.Quotient.mk (mappedBoundaryVector f Jsource x hx)

/-- A source-boundary class vanishes exactly when its image is a target boundary. -/
theorem boundaryEscapeClass_eq_zero_iff
    (f : V →ₗ[k] W) (Jsource : Submodule k V)
    (Jtarget : Submodule k W) (x : V) (hx : x ∈ Jsource) :
    boundaryEscapeClass f Jsource Jtarget x hx = 0 ↔ f x ∈ Jtarget := by
  rw [boundaryEscapeClass, Submodule.Quotient.mk_eq_zero]
  rfl

/-- A nonzero boundary-escape class is exactly a surviving defect in the target exactness flag. -/
theorem boundaryEscapeClass_ne_zero_iff_survival
    (f : V →ₗ[k] W) (Jsource : Submodule k V)
    (Jtarget : Submodule k W) (x : V) (hx : x ∈ Jsource) :
    boundaryEscapeClass f Jsource Jtarget x hx ≠ 0 ↔
      boundaryExactnessFlag Jtarget ∈ ExFlag.survival (f x) := by
  rw [ne_eq, boundaryEscapeClass_eq_zero_iff]
  simp [ExFlag.mem_survival_iff, boundaryExactnessFlag]

/-- Boundary migration is exact precisely when no source boundary survives in the target flag. -/
theorem escapeFree_iff_no_boundary_survival
    (f : V →ₗ[k] W) (Jsource : Submodule k V)
    (Jtarget : Submodule k W) :
    EscapeFree f Jsource Jtarget ↔
      ∀ x : V, x ∈ Jsource →
        boundaryExactnessFlag Jtarget ∉ ExFlag.survival (f x) := by
  rw [EscapeFree]
  constructor
  · intro h x hx hsurv
    exact hsurv.2 (h (Submodule.mem_map_of_mem hx))
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    by_contra htarget
    exact h x hx ⟨Submodule.mem_top, htarget⟩

/-! ## Closed exactness and provenance-continuous completion -/

/-- Flags at which one framed vector does not survive as a homological defect. -/
def exactAtLocus (v : W) : Set (ExFlag k W) :=
  (ExFlag.survival (R := k) (M := W) v)ᶜ

/-- Exactness at a fixed frame is closed in the mixed lower--Scott provenance topology. -/
theorem isClosed_exactAtLocus (v : W) :
    IsClosed (exactAtLocus (k := k) v) :=
  (ExFlag.isOpen_survival (R := k) (M := W) v).isClosed_compl

/-- The locus of fully exact flags: every admissible cycle is a boundary. -/
def exactFlagLocus : Set (ExFlag k W) :=
  ⋂ v : W, exactAtLocus (k := k) v

/-- A flag lies in the fully exact locus exactly when its boundary and cycle spaces agree. -/
theorem mem_exactFlagLocus_iff (p : ExFlag k W) :
    p ∈ exactFlagLocus ↔ p.boundary = p.cycle := by
  constructor
  · intro hp
    apply le_antisymm p.boundary_le_cycle
    intro v hv
    by_contra hvB
    have hvExact : p ∈ exactAtLocus (k := k) v :=
      Set.mem_iInter.mp hp v
    exact hvExact ⟨hv, hvB⟩
  · intro h
    rw [exactFlagLocus, Set.mem_iInter]
    intro v
    show p ∈ (ExFlag.survival (R := k) (M := W) v)ᶜ
    intro hsurv
    exact hsurv.2 (by rw [h]; exact hsurv.1)

/-- Full exactness is a closed condition in provenance-exactness geometry. -/
theorem isClosed_exactFlagLocus : IsClosed (exactFlagLocus : Set (ExFlag k W)) :=
  isClosed_iInter fun v => isClosed_exactAtLocus (k := k) v

/-- A provenance limit cannot acquire a new fixed framed defect absent eventually in the system. -/
theorem not_mem_survival_of_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {p : ι → ExFlag k W} {pLim : ExFlag k W} {v : W}
    (hp : Filter.Tendsto p l (nhds pLim))
    (hexact : ∀ᶠ i in l, p i ∉ ExFlag.survival v) :
    pLim ∉ ExFlag.survival v :=
  (isClosed_exactAtLocus v).mem_of_tendsto hp hexact

/-- A provenance limit of eventually fully exact flags is fully exact. -/
theorem mem_exactFlagLocus_of_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {p : ι → ExFlag k W} {pLim : ExFlag k W}
    (hp : Filter.Tendsto p l (nhds pLim))
    (hexact : ∀ᶠ i in l, p i ∈ exactFlagLocus) :
    pLim ∈ exactFlagLocus :=
  isClosed_exactFlagLocus.mem_of_tendsto hp hexact

section DerivedLimit

variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)]

/-- The Roos boundary range together with the full sequence space of possible derived cycles. -/
def derivedLimitExactnessFlag
    (bond : ∀ n, A (n + 1) →ₗ[k] A n) : ExFlag k (∀ n, A n) :=
  boundaryExactnessFlag (LinearMap.range (inverseDifference A bond))

/-- A sequence survives in the Roos exactness flag exactly when its `lim¹` class is nonzero. -/
theorem derivedLimitClass_ne_zero_iff_survival
    (bond : ∀ n, A (n + 1) →ₗ[k] A n) (x : ∀ n, A n) :
    (Submodule.Quotient.mk x : DerivedLimitOne A bond) ≠ 0 ↔
      derivedLimitExactnessFlag A bond ∈ ExFlag.survival x := by
  rw [ne_eq, Submodule.Quotient.mk_eq_zero]
  simp [derivedLimitExactnessFlag, ExFlag.mem_survival_iff,
    boundaryExactnessFlag]

/-- Failure to survive is constructive Roos exactness: the sequence has a global primitive. -/
theorem not_mem_derivedLimit_survival_iff_exists_primitive
    (bond : ∀ n, A (n + 1) →ₗ[k] A n) (x : ∀ n, A n) :
    derivedLimitExactnessFlag A bond ∉ ExFlag.survival x ↔
      ∃ y : ∀ n, A n, inverseDifference A bond y = x := by
  rw [derivedLimitExactnessFlag, ExFlag.mem_survival_iff]
  simp only [boundaryExactnessFlag_cycle, Submodule.mem_top, true_and,
    boundaryExactnessFlag_boundary, not_not]
  exact LinearMap.mem_range

end DerivedLimit

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
