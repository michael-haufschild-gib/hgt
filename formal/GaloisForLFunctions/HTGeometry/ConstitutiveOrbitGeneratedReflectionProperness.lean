import Mathlib

/-!
# Orbit-generated reflection properness

This module certifies the finite cyclic core of ULF-OGRPM-1.  A coordinate reflection fixes one
source sector and negates its complement.  The complete source orbit of those reflections has an
exact tight defect identity.  Repeating the closed observer cycle accumulates linearly open work.
-/

namespace HTGeometry

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reflection fixing coordinate `k` and negating every other coordinate. -/
def coordinateReflection (k : ι) (x : ι → ℝ) : ι → ℝ := fun j =>
  if j = k then x j else -x j

/-- Additive defect of the `k`-th reflection from the odd condition. -/
def coordinateReflectionDefect (k : ι) (x : ι → ℝ) : ι → ℝ := fun j =>
  x j + coordinateReflection k x j

/-- Squared Euclidean work of all reflection defects in one complete observer cycle. -/
def orbitReflectionCycleWork (x : ι → ℝ) : ℝ :=
  ∑ k, ∑ j, coordinateReflectionDefect k x j ^ (2 : ℕ)

/-- Squared Euclidean source energy. -/
def coordinateEnergy (x : ι → ℝ) : ℝ := ∑ j, x j ^ (2 : ℕ)

/-- Work after `q` completed observer cycles. -/
def repeatedOrbitReflectionWork (q : ℕ) (x : ι → ℝ) : ℝ :=
  q * orbitReflectionCycleWork x

omit [Fintype ι] in
@[simp] theorem coordinateReflection_apply_same (k : ι) (x : ι → ℝ) :
    coordinateReflection k x k = x k := by
  simp [coordinateReflection]

omit [Fintype ι] in
theorem coordinateReflection_apply_ne {j k : ι} (h : j ≠ k) (x : ι → ℝ) :
    coordinateReflection k x j = -x j := by
  simp [coordinateReflection, h]

omit [Fintype ι] in
/-- Every generated coordinate reflection is an involution. -/
theorem coordinateReflection_involutive (k : ι) (x : ι → ℝ) :
    coordinateReflection k (coordinateReflection k x) = x := by
  funext j
  by_cases h : j = k
  · subst h
    simp
  · simp [coordinateReflection, h]

/-- Coordinate reflections preserve squared Euclidean energy. -/
theorem coordinateEnergy_coordinateReflection (k : ι) (x : ι → ℝ) :
    coordinateEnergy (coordinateReflection k x) = coordinateEnergy x := by
  unfold coordinateEnergy
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = k
  · simp [coordinateReflection, h]
  · simp [coordinateReflection, h]

omit [Fintype ι] in
/-- A reflection defect is supported exactly on its fixed coordinate. -/
theorem coordinateReflectionDefect_apply (k : ι) (x : ι → ℝ) (j : ι) :
    coordinateReflectionDefect k x j = if j = k then 2 * x j else 0 := by
  by_cases h : j = k
  · simp [coordinateReflectionDefect, coordinateReflection, h, two_mul]
  · simp [coordinateReflectionDefect, coordinateReflection, h]

/-- Exact tight-frame identity for one complete generated reflection orbit. -/
theorem orbitReflectionCycleWork_eq_four_energy (x : ι → ℝ) :
    orbitReflectionCycleWork x = 4 * coordinateEnergy x := by
  unfold orbitReflectionCycleWork coordinateEnergy
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [coordinateReflectionDefect_apply, eq_comm]
  ring

omit [Fintype ι] in
/-- The complete reflection orbit has zero common odd sector. -/
theorem coordinateReflection_joint_odd_iff (x : ι → ℝ) :
    (∀ k, coordinateReflection k x = -x) ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj := congrFun (h j) j
    simp at hj
    have hx : x j = 0 := by linarith [hj]
    simpa using hx
  · rintro rfl
    intro k
    funext j
    simp [coordinateReflection]

/-- One complete cycle has zero work exactly at the neutral state. -/
theorem orbitReflectionCycleWork_eq_zero_iff (x : ι → ℝ) :
    orbitReflectionCycleWork x = 0 ↔ x = 0 := by
  rw [orbitReflectionCycleWork_eq_four_energy]
  constructor
  · intro h
    have henergy : coordinateEnergy x = 0 := by linarith
    funext j
    have hterm : x j ^ (2 : ℕ) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp henergy j
        (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hterm
  · rintro rfl
    simp [coordinateEnergy]

/-- Closed observer cycles accumulate exactly linear marked work. -/
theorem repeatedOrbitReflectionWork_eq (q : ℕ) (x : ι → ℝ) :
    repeatedOrbitReflectionWork q x = 4 * q * coordinateEnergy x := by
  rw [repeatedOrbitReflectionWork, orbitReflectionCycleWork_eq_four_energy]
  ring

/-- If every number of completed cycles has zero work, the source state is neutral. -/
theorem repeatedOrbitReflectionWork_all_zero_iff (x : ι → ℝ) :
    (∀ q : ℕ, repeatedOrbitReflectionWork q x = 0) ↔ x = 0 := by
  constructor
  · intro h
    have hcycle : orbitReflectionCycleWork x = 0 := by
      simpa [repeatedOrbitReflectionWork] using h 1
    exact (orbitReflectionCycleWork_eq_zero_iff x).mp hcycle
  · rintro rfl
    simp [repeatedOrbitReflectionWork, orbitReflectionCycleWork, coordinateReflectionDefect,
      coordinateReflection]

/-- Capstone: a recurrent coordinate-reflection observer is exactly proper on its marked cycle. -/
theorem orbitGeneratedReflectionProperness_capstone (x : ι → ℝ) :
    orbitReflectionCycleWork x = 4 * coordinateEnergy x ∧
      (orbitReflectionCycleWork x = 0 ↔ x = 0) ∧
      (∀ q : ℕ, repeatedOrbitReflectionWork q x = 4 * q * coordinateEnergy x) := by
  exact ⟨orbitReflectionCycleWork_eq_four_energy x,
    orbitReflectionCycleWork_eq_zero_iff x,
    fun q => repeatedOrbitReflectionWork_eq q x⟩

end HTGeometry
