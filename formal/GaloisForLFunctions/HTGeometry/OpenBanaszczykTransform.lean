import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Open Banaszczyk transforms

The open transform retains midpoints whose two unit translates lie in a convex target, then
extends every retained fibre by two steps in each direction.  Its translate containment is the
deterministic mechanism behind finite sign recovery: every transformed point can be pulled back
to the preceding target after adding one of the two signs of the step vector.
-/

open Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Midpoints whose positive and negative `v`-translates both lie in `K`. -/
def banaszczykCore (K : Set E) (v : E) : Set E :=
  (K - {v}) ∩ (K + {v})

/-- Open scalar sweep through the step vector, with the paper's cutoff two. -/
def banaszczykSweep (v : E) : Set E :=
  (fun t : ℝ => t • v) '' Ioo (-2) 2

/-- Open-set Banaszczyk transform. -/
def openBanaszczykTransform (K : Set E) (v : E) : Set E :=
  banaszczykCore K v + banaszczykSweep v

omit [NormedSpace ℝ E] in
theorem mem_banaszczykCore {K : Set E} {v z : E} :
    z ∈ banaszczykCore K v ↔ z + v ∈ K ∧ z - v ∈ K := by
  constructor
  · rintro ⟨⟨a, ha, b, hb, hab⟩, ⟨c, hc, d, hd, hcd⟩⟩
    simp only [mem_singleton_iff] at hb hd
    subst b
    subst d
    constructor
    · rw [← hab]
      simpa only [sub_add_cancel] using ha
    · rw [← hcd]
      simpa only [add_sub_cancel_right] using hc
  · rintro ⟨hplus, hminus⟩
    constructor
    · exact ⟨z + v, hplus, v, mem_singleton v, by module⟩
    · exact ⟨z - v, hminus, v, mem_singleton v, by module⟩

theorem mem_banaszczykSweep {v x : E} :
    x ∈ banaszczykSweep v ↔ ∃ t ∈ Ioo (-2 : ℝ) 2, t • v = x := by
  simp only [banaszczykSweep, mem_image]

theorem mem_openBanaszczykTransform {K : Set E} {v x : E} :
    x ∈ openBanaszczykTransform K v ↔
      ∃ z : E, z + v ∈ K ∧ z - v ∈ K ∧
        ∃ t ∈ Ioo (-2 : ℝ) 2, z + t • v = x := by
  rw [openBanaszczykTransform, Set.mem_add]
  constructor
  · rintro ⟨z, hz, w, hw, hzw⟩
    obtain ⟨t, ht, rfl⟩ := mem_banaszczykSweep.mp hw
    exact ⟨z, (mem_banaszczykCore.mp hz).1, (mem_banaszczykCore.mp hz).2,
      t, ht, hzw⟩
  · rintro ⟨z, hzplus, hzminus, t, ht, hzt⟩
    exact ⟨z, mem_banaszczykCore.mpr ⟨hzplus, hzminus⟩,
      t • v, mem_banaszczykSweep.mpr ⟨t, ht, rfl⟩, hzt⟩

theorem banaszczykSweep_zero : banaszczykSweep (0 : E) = {0} := by
  ext x
  constructor
  · rintro ⟨t, _ht, rfl⟩
    simp
  · intro hx
    rw [mem_singleton_iff] at hx
    subst x
    exact ⟨0, by constructor <;> linarith, by simp⟩

theorem zero_mem_banaszczykSweep (v : E) : 0 ∈ banaszczykSweep v :=
  mem_banaszczykSweep.mpr ⟨0, by constructor <;> linarith, by simp⟩

theorem convex_banaszczykSweep (v : E) : Convex ℝ (banaszczykSweep v) := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ a b ha hb hab
  refine ⟨a * s + b * t, ?_, ?_⟩
  · simpa only [smul_eq_mul] using (convex_Ioo (-2 : ℝ) 2 hs ht ha hb hab)
  · module

theorem isBounded_banaszczykSweep (v : E) : Bornology.IsBounded (banaszczykSweep v) := by
  apply (Metric.isBounded_closedBall :
    Bornology.IsBounded (Metric.closedBall (0 : E) (2 * ‖v‖))).subset
  rintro x ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
  have habs : |t| ≤ 2 := (abs_lt.mpr ht).le
  exact mul_le_mul_of_nonneg_right habs (norm_nonneg v)

theorem convex_banaszczykCore {K : Set E} (hK : Convex ℝ K) (v : E) :
    Convex ℝ (banaszczykCore K v) :=
  (hK.sub (convex_singleton v)).inter (hK.add (convex_singleton v))

omit [NormedSpace ℝ E] in
theorem isOpen_banaszczykCore {K : Set E} (hK : IsOpen K) (v : E) :
    IsOpen (banaszczykCore K v) := by
  rw [banaszczykCore, Set.sub_singleton, Set.add_singleton]
  exact (isOpenMap_sub_right v K hK).inter (isOpenMap_add_right v K hK)

omit [NormedSpace ℝ E] in
theorem isBounded_banaszczykCore {K : Set E} (hK : Bornology.IsBounded K) (v : E) :
    Bornology.IsBounded (banaszczykCore K v) :=
  (isBounded_sub hK Bornology.isBounded_singleton).subset inter_subset_left

theorem openBanaszczykTransform_mono {K L : Set E} (hKL : K ⊆ L) (v : E) :
    openBanaszczykTransform K v ⊆ openBanaszczykTransform L v := by
  intro x hx
  rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, t, ht, hzt⟩
  exact mem_openBanaszczykTransform.mpr
    ⟨z, hKL hzplus, hKL hzminus, t, ht, hzt⟩

@[simp] theorem openBanaszczykTransform_zero (K : Set E) :
    openBanaszczykTransform K 0 = K := by
  ext x
  constructor
  · intro hx
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hz, _hz, _t, _ht, hzx⟩
    have hzx' : z = x := by simpa using hzx
    have hz' : z ∈ K := by simpa using hz
    exact hzx' ▸ hz'
  · intro hx
    exact mem_openBanaszczykTransform.mpr
      ⟨x, by simpa, by simpa, 0, by constructor <;> linarith, by simp⟩

theorem convex_openBanaszczykTransform {K : Set E} (hK : Convex ℝ K) (v : E) :
    Convex ℝ (openBanaszczykTransform K v) :=
  (convex_banaszczykCore hK v).add (convex_banaszczykSweep v)

theorem isOpen_openBanaszczykTransform {K : Set E} (hK : IsOpen K) (v : E) :
    IsOpen (openBanaszczykTransform K v) :=
  (isOpen_banaszczykCore hK v).add_right

theorem isBounded_openBanaszczykTransform {K : Set E}
    (hK : Bornology.IsBounded K) (v : E) :
    Bornology.IsBounded (openBanaszczykTransform K v) :=
  isBounded_add (isBounded_banaszczykCore hK v) (isBounded_banaszczykSweep v)

/- Reversing the direction vector does not change the transform. -/
omit [NormedSpace ℝ E] in
theorem banaszczykCore_neg (K : Set E) (v : E) :
    banaszczykCore K (-v) = banaszczykCore K v := by
  ext z
  simp only [mem_banaszczykCore]
  constructor
  · rintro ⟨hplus, hminus⟩
    constructor
    · convert hminus using 1
      module
    · convert hplus using 1
      module
  · rintro ⟨hplus, hminus⟩
    constructor
    · convert hminus using 1
      module
    · convert hplus using 1
      module

theorem banaszczykSweep_neg (v : E) : banaszczykSweep (-v) = banaszczykSweep v := by
  ext x
  simp only [mem_banaszczykSweep]
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [← htx]
    module
  · rintro ⟨t, ht, htx⟩
    refine ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [← htx]
    module

theorem openBanaszczykTransform_neg (K : Set E) (v : E) :
    openBanaszczykTransform K (-v) = openBanaszczykTransform K v := by
  rw [openBanaszczykTransform, openBanaszczykTransform, banaszczykCore_neg,
    banaszczykSweep_neg]

/-- Every transformed point can be pulled back into the target by one of the two signs of `v`. -/
theorem openBanaszczykTransform_subset_translate_union {K : Set E}
    (hK : Convex ℝ K) (v : E) :
    openBanaszczykTransform K v ⊆ (K - {v}) ∪ (K + {v}) := by
  intro x hx
  rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, t, ht, hzt⟩
  by_cases ht0 : 0 ≤ t
  · right
    have hhalf0 : 0 ≤ t / 2 := by linarith
    have hhalf1 : 0 ≤ 1 - t / 2 := by linarith [ht.2]
    have hmem := hK hzminus hzplus hhalf1 hhalf0 (by ring)
    have hback : x - v = (1 - t / 2) • (z - v) + (t / 2) • (z + v) := by
      rw [← hzt]
      module
    rw [← hback] at hmem
    exact ⟨x - v, hmem, v, mem_singleton v, by module⟩
  · left
    have ht0' : t ≤ 0 := le_of_not_ge ht0
    have hhalf0 : 0 ≤ -t / 2 := by linarith
    have hhalf1 : 0 ≤ (t + 2) / 2 := by linarith [ht.1]
    have hmem := hK hzminus hzplus hhalf0 hhalf1 (by ring)
    have hback : x + v = (-t / 2) • (z - v) + ((t + 2) / 2) • (z + v) := by
      rw [← hzt]
      module
    rw [← hback] at hmem
    exact ⟨x + v, hmem, v, mem_singleton v, by module⟩

/-- Boolean form of the one-step pullback used by finite sign recovery. -/
theorem exists_bool_add_mem_of_mem_openBanaszczykTransform {K : Set E}
    (hK : Convex ℝ K) {x : E} (v : E) (hx : x ∈ openBanaszczykTransform K v) :
    ∃ sign : Bool, x + (if sign then v else -v) ∈ K := by
  rcases openBanaszczykTransform_subset_translate_union hK v hx with hminus | hplus
  · rcases hminus with ⟨k, hk, w, hw, hkw⟩
    rw [mem_singleton_iff] at hw
    subst w
    refine ⟨true, ?_⟩
    simp only [if_true]
    have hxk : x + v = k := by
      rw [← hkw]
      module
    rwa [hxk]
  · rcases hplus with ⟨k, hk, w, hw, hkw⟩
    rw [mem_singleton_iff] at hw
    subst w
    refine ⟨false, ?_⟩
    have hxk : x + -v = k := by
      rw [← hkw]
      module
    simpa [hxk] using hk

/-- Central symmetry is preserved by the open transform. -/
theorem neg_openBanaszczykTransform_eq {K : Set E} (hK : -K = K) (v : E) :
    -(openBanaszczykTransform K v) = openBanaszczykTransform K v := by
  have hneg : ∀ {a : E}, a ∈ K → -a ∈ K := by
    intro a ha
    rw [← hK]
    exact Set.neg_mem_neg.mpr ha
  have htransform : ∀ {x : E}, x ∈ openBanaszczykTransform K v →
      -x ∈ openBanaszczykTransform K v := by
    intro x hx
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, t, ht, hzt⟩
    refine mem_openBanaszczykTransform.mpr
      ⟨-z, ?_, ?_, -t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    · convert hneg hzminus using 1
      module
    · convert hneg hzplus using 1
      module
    · rw [← hzt]
      module
  ext x
  rw [Set.mem_neg]
  constructor
  · intro hx
    simpa only [neg_neg] using htransform hx
  · exact htransform

/-! ## Closed canonical applications -/

omit [NormedSpace ℝ E] in
theorem neg_ball_zero_eq (r : ℝ) : -(Metric.ball (0 : E) r) = Metric.ball 0 r := by
  ext x
  simp [Metric.mem_ball, dist_eq_norm]

/-- Every origin-centered norm ball has all geometric invariants needed by the transform. -/
theorem openBanaszczykTransform_ball_geometry (r : ℝ) (v : E) :
    Convex ℝ (openBanaszczykTransform (Metric.ball (0 : E) r) v) ∧
      IsOpen (openBanaszczykTransform (Metric.ball (0 : E) r) v) ∧
      Bornology.IsBounded (openBanaszczykTransform (Metric.ball (0 : E) r) v) ∧
      -(openBanaszczykTransform (Metric.ball (0 : E) r) v) =
        openBanaszczykTransform (Metric.ball (0 : E) r) v := by
  exact ⟨convex_openBanaszczykTransform (convex_ball 0 r) v,
    isOpen_openBanaszczykTransform Metric.isOpen_ball v,
    isBounded_openBanaszczykTransform Metric.isBounded_ball v,
    neg_openBanaszczykTransform_eq (neg_ball_zero_eq r) v⟩

/-- Closed norm-ball application of one-step translate containment. -/
theorem exists_bool_norm_add_lt_of_mem_openBanaszczykTransform_ball (r : ℝ)
    {x : E} (v : E) (hx : x ∈ openBanaszczykTransform (Metric.ball (0 : E) r) v) :
    ∃ sign : Bool, ‖x + (if sign then v else -v)‖ < r := by
  obtain ⟨sign, hsign⟩ :=
    exists_bool_add_mem_of_mem_openBanaszczykTransform (convex_ball 0 r) v hx
  refine ⟨sign, ?_⟩
  simpa [Metric.mem_ball] using hsign

/-- Open coordinate cube in a finite real product. -/
def openCoordinateCube (ι : Type*) (C : ℝ) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ => Ioo (-C) C)

@[simp] theorem mem_openCoordinateCube {ι : Type*} {C : ℝ} {x : ι → ℝ} :
    x ∈ openCoordinateCube ι C ↔ ∀ i, |x i| < C := by
  simp [openCoordinateCube, abs_lt]

theorem convex_openCoordinateCube (ι : Type*) (C : ℝ) :
    Convex ℝ (openCoordinateCube ι C) :=
  convex_pi fun _ _ => convex_Ioo _ _

/-- Closed coordinate-cube application of one-step translate containment. -/
theorem exists_bool_forall_abs_add_lt_of_mem_openBanaszczykTransform_cube
    {ι : Type*} [Fintype ι] (C : ℝ) {x : ι → ℝ} (v : ι → ℝ)
    (hx : x ∈ openBanaszczykTransform (openCoordinateCube ι C) v) :
    ∃ sign : Bool, ∀ i, |x i + (if sign then v i else -v i)| < C := by
  obtain ⟨sign, hsign⟩ :=
    exists_bool_add_mem_of_mem_openBanaszczykTransform
      (convex_openCoordinateCube ι C) v hx
  refine ⟨sign, ?_⟩
  cases sign <;> simpa using (mem_openCoordinateCube.mp hsign)

theorem isOpen_openCoordinateCube (ι : Type*) [Finite ι] (C : ℝ) :
    IsOpen (openCoordinateCube ι C) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isBounded_openCoordinateCube (ι : Type*) [Fintype ι] (C : ℝ) :
    Bornology.IsBounded (openCoordinateCube ι C) := by
  exact Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

theorem neg_openCoordinateCube_eq (ι : Type*) (C : ℝ) :
    -(openCoordinateCube ι C) = openCoordinateCube ι C := by
  ext x
  rw [Set.mem_neg]
  simp only [mem_openCoordinateCube, Pi.neg_apply, abs_neg]

/-- Dimension-free cube radius in the vector-balancing theorem. -/
noncomputable def komlosCubeRadius : ℝ := 3 * Real.sqrt (2 * Real.pi)

theorem komlosCubeRadius_pos : 0 < komlosCubeRadius := by
  unfold komlosCubeRadius
  positivity

/-- Target cube used for the dimension-free signing bound. -/
noncomputable def komlosCube (d : ℕ) : Set (Fin d → ℝ) :=
  openCoordinateCube (Fin d) komlosCubeRadius

theorem komlosCube_nonempty (d : ℕ) : (komlosCube d).Nonempty := by
  refine ⟨0, ?_⟩
  simp [komlosCube, komlosCubeRadius_pos]

/-- Every Komlós cube has the complete geometric package, with no dimension restriction. -/
theorem komlosCube_geometry (d : ℕ) :
    Convex ℝ (komlosCube d) ∧ IsOpen (komlosCube d) ∧
      Bornology.IsBounded (komlosCube d) ∧
      -(komlosCube d) = komlosCube d := by
  exact ⟨convex_openCoordinateCube _ _, isOpen_openCoordinateCube _ _,
    isBounded_openCoordinateCube _ _, neg_openCoordinateCube_eq _ _⟩

/-- The open convention deletes a fibre exactly at the unit-interval threshold. -/
theorem openBanaszczykTransform_unitInterval_one :
    openBanaszczykTransform (Ioo (-1 : ℝ) 1) 1 = ∅ := by
  ext x
  constructor
  · intro hx
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, _t, _ht, _hzt⟩
    simp only [mem_Ioo] at hzplus hzminus
    exfalso
    linarith
  · simp

end GaloisForLFunctions.HTGeometry
