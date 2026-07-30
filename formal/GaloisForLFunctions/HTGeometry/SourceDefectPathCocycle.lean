import GaloisForLFunctions.HTGeometry.ProjectiveSourceVisibilityParity

/-!
# Source-defect path cocycle and reporter-index no-go

The defect `1 - A` of a linear source change is an exact path cocycle:

`D(A ∘ B) = D(A) + A ∘ D(B)`.

Consequently every word defect telescopes from the defects of its generators. For a binary
source square, the identity report is zero and the composite report is determined by the two
generator reports. The four-label square report is injective exactly when the paired generator
report is injective; adding identity and composite labels creates no new visibility index.

This is elementary linear and group-cohomological algebra. It does not derive physical states,
weak isospin, colour, spacetime, gravity, or any other force.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The identity source change has zero defect. -/
theorem sourceChangeDefect_id :
    sourceChangeDefect (LinearMap.id : V →ₗ[K] V) = 0 := by
  ext v
  simp [sourceChangeDefect]

/-- **Exact source-defect path cocycle.** Composite change has the first defect plus the
transported second defect. -/
theorem sourceChangeDefect_comp (A B : V →ₗ[K] V) :
    sourceChangeDefect (A.comp B) =
      sourceChangeDefect A + A.comp (sourceChangeDefect B) := by
  ext v
  simp [sourceChangeDefect]

/-- Ordered composition of a word of source changes. -/
def sourceChangeWord : List (V →ₗ[K] V) → V →ₗ[K] V
  | [] => LinearMap.id
  | A :: rest => A.comp (sourceChangeWord rest)

/-- Transported telescoping sum of the generator defects in a source-change word. -/
def sourceChangeWordDefect : List (V →ₗ[K] V) → V →ₗ[K] V
  | [] => 0
  | A :: rest => sourceChangeDefect A + A.comp (sourceChangeWordDefect rest)

/-- Every finite path defect is determined by transported generator defects. -/
theorem sourceChangeDefect_word (word : List (V →ₗ[K] V)) :
    sourceChangeDefect (sourceChangeWord word) = sourceChangeWordDefect word := by
  induction word with
  | nil =>
      exact sourceChangeDefect_id
  | cons A rest ih =>
      rw [sourceChangeWord, sourceChangeDefect_comp, ih]
      rfl

/-- Defects of the four square labels `1`, `A`, `B`, and `A ∘ B`. -/
def sourceSquareDefectReport (A B : V →ₗ[K] V) :
    V →ₗ[K] (V × V) × (V × V) :=
  ((sourceChangeDefect (LinearMap.id : V →ₗ[K] V)).prod (sourceChangeDefect A)).prod
    ((sourceChangeDefect B).prod (sourceChangeDefect (A.comp B)))

/-- The deterministic lift from two generator defects to all four square-label defects. -/
def sourceSquareDefectLift (A : V →ₗ[K] V) :
    (V × V) →ₗ[K] (V × V) × (V × V) where
  toFun p := ((0, p.1), (p.2, p.1 + A p.2))
  map_add' p q := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    ext <;> simp [smul_add]

/-- The square-label lift retains both generator defects and is therefore injective. -/
theorem sourceSquareDefectLift_injective (A : V →ₗ[K] V) :
    Function.Injective (sourceSquareDefectLift A) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun z => z.1.2) h
  · exact congrArg (fun z => z.2.1) h

/-- **Reporter-index factorization.** All four square-label defects factor through the paired
generator report. -/
theorem sourceSquareDefectReport_factorization (A B : V →ₗ[K] V) :
    sourceSquareDefectReport A B =
      (sourceSquareDefectLift A).comp (projectiveSourceJointDefect A B) := by
  apply LinearMap.ext
  intro v
  change
    ((sourceChangeDefect (LinearMap.id : V →ₗ[K] V) v, sourceChangeDefect A v),
      (sourceChangeDefect B v, sourceChangeDefect (A.comp B) v)) =
    ((0, sourceChangeDefect A v),
      (sourceChangeDefect B v, sourceChangeDefect A v + A (sourceChangeDefect B v)))
  rw [sourceChangeDefect_id, sourceChangeDefect_comp]
  rfl

/-- Adding the identity and composite square labels neither gains nor loses injectivity. -/
theorem sourceSquareDefectReport_injective_iff (A B : V →ₗ[K] V) :
    Function.Injective (sourceSquareDefectReport A B) ↔
      Function.Injective (projectiveSourceJointDefect A B) := by
  constructor
  · intro hfull x y hpair
    apply hfull
    rw [sourceSquareDefectReport_factorization]
    simp only [LinearMap.comp_apply]
    rw [hpair]
  · intro hpair
    rw [sourceSquareDefectReport_factorization]
    exact (sourceSquareDefectLift_injective A).comp hpair

/-- A nontrivial projective commutator makes the full square-label report injective, but only
through the already-injective paired generator report. -/
theorem sourceSquareDefectReport_injective_of_projective
    (A B : V →ₗ[K] V) (ζ : K)
    (hcomm : A.comp B = ζ • (B.comp A))
    (hζ : ζ ≠ 1) :
    Function.Injective (sourceSquareDefectReport A B) :=
  (sourceSquareDefectReport_injective_iff A B).2
    (projectiveSourceJointDefect_injective A B ζ hcomm hζ)

end

end GaloisForLFunctions.HTGeometry
