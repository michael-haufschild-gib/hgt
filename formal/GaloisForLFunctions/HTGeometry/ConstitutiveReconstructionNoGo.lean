import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Reconstruction-radius no-go and serial survivor

Serial coarsening does not monotonically increase the optimal internal-centre reconstruction radius:
a newly merged fibre may contain a better centre.  A closed three-point metric counterexample is
given below.  What is monotone is the set of indistinguishable source pairs, hence fibre diameter
and every pairwise separation obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- Three source points on a path. -/
inductive ConstitutiveThreePoint where
  | left
  | center
  | right
  deriving DecidableEq

/-- Isometric coordinate in the real line. -/
def ConstitutiveThreePoint.coordinate : ConstitutiveThreePoint → ℝ
  | .left => -1
  | .center => 0
  | .right => 1

theorem ConstitutiveThreePoint.coordinate_injective :
    Function.Injective ConstitutiveThreePoint.coordinate := by
  intro x y h
  cases x with
  | left =>
      cases y with
      | left => rfl
      | center => norm_num [ConstitutiveThreePoint.coordinate] at h
      | right => norm_num [ConstitutiveThreePoint.coordinate] at h
  | center =>
      cases y with
      | left => norm_num [ConstitutiveThreePoint.coordinate] at h
      | center => rfl
      | right => norm_num [ConstitutiveThreePoint.coordinate] at h
  | right =>
      cases y with
      | left => norm_num [ConstitutiveThreePoint.coordinate] at h
      | center => norm_num [ConstitutiveThreePoint.coordinate] at h
      | right => rfl

instance : MetricSpace ConstitutiveThreePoint :=
  MetricSpace.induced ConstitutiveThreePoint.coordinate
    ConstitutiveThreePoint.coordinate_injective inferInstance

@[simp]
theorem ConstitutiveThreePoint.dist_left_center :
    dist ConstitutiveThreePoint.left ConstitutiveThreePoint.center = 1 := by
  change dist (-1 : ℝ) 0 = 1
  norm_num

@[simp]
theorem ConstitutiveThreePoint.dist_right_center :
    dist ConstitutiveThreePoint.right ConstitutiveThreePoint.center = 1 := by
  change dist (1 : ℝ) 0 = 1
  norm_num

@[simp]
theorem ConstitutiveThreePoint.dist_left_right :
    dist ConstitutiveThreePoint.left ConstitutiveThreePoint.right = 2 := by
  change dist (-1 : ℝ) 1 = 2
  norm_num [Real.dist_eq]

/-- Fine observer: endpoints share a fibre, centre is separate. -/
def constitutiveThreePointFine : ConstitutiveThreePoint → Bool
  | .left => false
  | .center => true
  | .right => false

/-- Coarse observer, obtained by forgetting the fine Boolean output. -/
def constitutiveThreePointCoarse (_ : ConstitutiveThreePoint) : Unit :=
  ()

/-- A section of the fine observer. -/
structure ConstitutiveThreePointFineSection where
  lift : Bool → ConstitutiveThreePoint
  rightInverse : ∀ y, constitutiveThreePointFine (lift y) = y

/-- Every fine section has worst-case reconstruction error exactly at least two. -/
theorem constitutiveThreePoint_fine_error_two
    (s : ConstitutiveThreePointFineSection) :
    ∃ x, dist x (s.lift (constitutiveThreePointFine x)) = 2 := by
  cases h : s.lift false with
  | left =>
      exact ⟨.right, by simp [constitutiveThreePointFine, h, dist_comm]⟩
  | center =>
      have hfalse : true = false := by
        simpa [constitutiveThreePointFine, h] using s.rightInverse false
      exact False.elim (Bool.false_ne_true hfalse.symm)
  | right =>
      exact ⟨.left, by simp [constitutiveThreePointFine, h]⟩

/-- Coarse section selecting the newly available midpoint. -/
def constitutiveThreePointCoarseSection : Unit → ConstitutiveThreePoint :=
  fun _ ↦ .center

/-- The coarser observer has uniform reconstruction error at most one. -/
theorem constitutiveThreePoint_coarse_error_one :
    ∀ x,
      dist x (constitutiveThreePointCoarseSection (constitutiveThreePointCoarse x)) ≤ 1 := by
  intro x
  cases x <;> simp [constitutiveThreePointCoarseSection]

/-- The coarse observer is a serial postprocessing of the fine observer. -/
theorem constitutiveThreePoint_coarse_factors_through_fine :
    constitutiveThreePointCoarse = (fun _ : Bool ↦ ()) ∘ constitutiveThreePointFine := by
  rfl

/-- **Closed counterexample.** Every section of the finer observer incurs error two somewhere,
while a section after serial coarsening has error at most one everywhere. -/
theorem constitutiveThreePoint_serial_radius_can_decrease :
    (∀ s : ConstitutiveThreePointFineSection,
        ∃ x, dist x (s.lift (constitutiveThreePointFine x)) = 2) ∧
      (∀ x,
        dist x (constitutiveThreePointCoarseSection (constitutiveThreePointCoarse x)) ≤ 1) := by
  exact ⟨constitutiveThreePoint_fine_error_two, constitutiveThreePoint_coarse_error_one⟩

/-! ## Correct serial invariant -/

/-- A marked pair lying in one observer fibre. -/
structure ConstitutiveObserverFiberPair {X : Type u} {Y : Type v} (q : X → Y) where
  left : X
  right : X
  sameObservation : q left = q right

/-- Serial postprocessing preserves every indistinguishable source pair. -/
def ConstitutiveObserverFiberPair.postprocess {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (r : Y → Z) (p : ConstitutiveObserverFiberPair q) :
    ConstitutiveObserverFiberPair (r ∘ q) where
  left := p.left
  right := p.right
  sameObservation := congrArg r p.sameObservation

/-- Postprocessing preserves the source distance of every hidden pair exactly. -/
theorem constitutiveObserverFiberPair_postprocess_distance
    {X : Type u} [PseudoMetricSpace X] {Y : Type v} {Z : Type w}
    (q : X → Y) (r : Y → Z) (p : ConstitutiveObserverFiberPair q) :
    dist (p.postprocess q r).left (p.postprocess q r).right = dist p.left p.right := by
  rfl

/-- A uniform reconstructor, with its legality and bound carried inside the object. -/
structure ConstitutiveUniformReconstructor
    {X : Type u} [PseudoMetricSpace X] {Y : Type v} (q : X → Y) where
  bound : ℝ
  lift : Y → X
  rightInverse : ∀ y, q (lift y) = y
  error_le : ∀ x, dist x (lift (q x)) ≤ bound

/-- Every uniformly reconstructed fibre pair has separation at most twice the declared error. -/
theorem constitutiveUniformReconstructor_pair_distance_le
    {X : Type u} [PseudoMetricSpace X] {Y : Type v} (q : X → Y)
    (s : ConstitutiveUniformReconstructor q) (p : ConstitutiveObserverFiberPair q) :
    dist p.left p.right ≤ 2 * s.bound := by
  calc
    dist p.left p.right ≤
        dist p.left (s.lift (q p.left)) + dist (s.lift (q p.left)) p.right :=
      dist_triangle _ _ _
    _ = dist p.left (s.lift (q p.left)) + dist p.right (s.lift (q p.right)) := by
      rw [p.sameObservation]
      rw [dist_comm (s.lift (q p.right)) p.right]
    _ ≤ s.bound + s.bound := add_le_add (s.error_le p.left) (s.error_le p.right)
    _ = 2 * s.bound := by ring

end GaloisForLFunctions.HTGeometry
