import Mathlib

/-!
# Finite positivity and critical-line selectors

This module isolates the finite selector mechanism that an RH proof would need:
a positive quadratic defect energy is faithful.  It vanishes exactly when every
finite defect vanishes, and in the critical-line specialization this is exactly
zero off-line index.

The last lemmas record the anti-theatre point: the functional-equation mirror
`s ↦ 1 - conj(s)` preserves squared distance from the critical line.  Symmetry
alone is not a positivity selector.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHProofLab

noncomputable section

section FiniteBadIndex

variable {ι : Type*}

/-- The finite count of elements selected by a bad/off-line predicate. -/
def finiteBadCount (S : Finset ι) (Bad : ι → Prop) [DecidablePred Bad] : ℕ :=
  (S.filter Bad).card

/-- A finite carrier has no bad/off-line elements. -/
def finiteNoBad (S : Finset ι) (Bad : ι → Prop) : Prop :=
  ∀ i ∈ S, ¬ Bad i

/-- A finite carrier has no bad elements exactly when its bad index is zero. -/
@[aesop norm simp]
theorem finiteNoBad_iff_badCount_eq_zero
    (S : Finset ι) (Bad : ι → Prop) [DecidablePred Bad] :
    finiteNoBad S Bad ↔ finiteBadCount S Bad = 0 := by
  constructor
  · intro hNoBad
    rw [finiteBadCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    exact hNoBad i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  · intro hCount i hi hBad
    have hmem : i ∈ S.filter Bad := Finset.mem_filter.mpr ⟨hi, hBad⟩
    have hpos : 0 < (S.filter Bad).card := Finset.card_pos.mpr ⟨i, hmem⟩
    rw [finiteBadCount] at hCount
    omega

end FiniteBadIndex

section EnergySelector

variable {ι : Type*} [Fintype ι]

/-- A finite weighted quadratic defect energy. -/
def defectEnergy (w d : ι → ℝ) : ℝ :=
  ∑ i, w i * d i ^ 2

/-- The unweighted positive selector: sum of squares vanishes iff every defect vanishes. -/
@[aesop norm simp]
theorem sum_sq_eq_zero_iff_all_zero (d : ι → ℝ) :
    (∑ i, d i ^ 2 = 0) ↔ ∀ i, d i = 0 := by
  constructor
  · intro h i
    have hnonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ d j ^ 2 := by
      intro j _hj
      exact sq_nonneg _
    have hall : ∀ j ∈ (Finset.univ : Finset ι), d j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h
    exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))
  · intro h
    simp [h]

/--
The weighted positive selector: if all weights are strictly positive, the energy
vanishes exactly when every defect vanishes.
-/
@[aesop norm simp]
theorem defectEnergy_eq_zero_iff_all_zero
    (w d : ι → ℝ) (hw : ∀ i, 0 < w i) :
    defectEnergy w d = 0 ↔ ∀ i, d i = 0 := by
  constructor
  · intro h i
    have hnonneg :
        ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ w j * d j ^ 2 := by
      intro j _hj
      exact mul_nonneg (le_of_lt (hw j)) (sq_nonneg _)
    have hall : ∀ j ∈ (Finset.univ : Finset ι), w j * d j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h
    have hi : w i * d i ^ 2 = 0 := hall i (Finset.mem_univ i)
    have hwi : w i ≠ 0 := ne_of_gt (hw i)
    have hdi : d i ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left hwi
    exact sq_eq_zero_iff.mp hdi
  · intro h
    simp [defectEnergy, h]

end EnergySelector

section CriticalLine

variable {ι : Type*} [Fintype ι]

/-- Signed real-part defect from the critical line `Re(s)=1/2`. -/
def criticalLineDefect (z : ℂ) : ℝ :=
  z.re - (1 / 2 : ℝ)

/-- All points in a finite carrier lie on the critical line. -/
def allOnCriticalLine (z : ι → ℂ) : Prop :=
  ∀ i, criticalLineDefect (z i) = 0

/-- Weighted critical-line defect energy for a finite carrier. -/
def criticalLineEnergy (w : ι → ℝ) (z : ι → ℂ) : ℝ :=
  defectEnergy w (fun i => criticalLineDefect (z i))

/-- Unweighted critical-line defect energy for a finite carrier. -/
def unweightedCriticalLineEnergy (z : ι → ℂ) : ℝ :=
  ∑ i, criticalLineDefect (z i) ^ 2

/-- Unweighted critical-line energy vanishes exactly when every point is on the line. -/
@[aesop norm simp]
theorem unweightedCriticalLineEnergy_eq_zero_iff_all_on_line
    (z : ι → ℂ) :
    unweightedCriticalLineEnergy z = 0 ↔ allOnCriticalLine z := by
  simpa [unweightedCriticalLineEnergy, allOnCriticalLine] using
    (sum_sq_eq_zero_iff_all_zero (fun i => criticalLineDefect (z i)))

/-- Positive critical-line energy vanishes exactly when every point is on the line. -/
@[aesop norm simp]
theorem criticalLineEnergy_eq_zero_iff_all_on_line
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i, 0 < w i) :
    criticalLineEnergy w z = 0 ↔ allOnCriticalLine z := by
  simpa [criticalLineEnergy, allOnCriticalLine] using
    (defectEnergy_eq_zero_iff_all_zero w (fun i => criticalLineDefect (z i)) hw)

/--
Positive critical-line energy is a faithful off-line index: it vanishes exactly
when the finite off-line count is zero.
-/
@[aesop norm simp]
theorem criticalLineEnergy_eq_zero_iff_badCount_eq_zero
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i, 0 < w i) :
    criticalLineEnergy w z = 0 ↔
      finiteBadCount (Finset.univ : Finset ι)
        (fun i => criticalLineDefect (z i) ≠ 0) = 0 := by
  classical
  rw [criticalLineEnergy_eq_zero_iff_all_on_line w z hw]
  simpa [allOnCriticalLine, finiteNoBad] using
    (finiteNoBad_iff_badCount_eq_zero
      (S := (Finset.univ : Finset ι))
      (Bad := fun i => criticalLineDefect (z i) ≠ 0))

/--
Unweighted critical-line energy is already a faithful off-line index: it
vanishes exactly when the finite off-line count is zero.
-/
@[aesop norm simp]
theorem unweightedCriticalLineEnergy_eq_zero_iff_badCount_eq_zero
    (z : ι → ℂ) :
    unweightedCriticalLineEnergy z = 0 ↔
      finiteBadCount (Finset.univ : Finset ι)
        (fun i => criticalLineDefect (z i) ≠ 0) = 0 := by
  classical
  rw [unweightedCriticalLineEnergy_eq_zero_iff_all_on_line]
  simpa [allOnCriticalLine, finiteNoBad] using
    (finiteNoBad_iff_badCount_eq_zero
      (S := (Finset.univ : Finset ι))
      (Bad := fun i => criticalLineDefect (z i) ≠ 0))

/-- The functional-equation mirror across the critical line. -/
def criticalMirror (z : ℂ) : ℂ :=
  1 - star z

/-- Mirroring changes the signed critical-line defect by a sign. -/
@[aesop safe]
theorem criticalLineDefect_mirror (z : ℂ) :
    criticalLineDefect (criticalMirror z) = - criticalLineDefect z := by
  simp [criticalLineDefect, criticalMirror]
  ring

/-- Mirroring preserves squared distance from the critical line. -/
@[aesop safe]
theorem criticalLineDefect_sq_mirror (z : ℂ) :
    criticalLineDefect (criticalMirror z) ^ 2 = criticalLineDefect z ^ 2 := by
  rw [criticalLineDefect_mirror]
  ring

/--
Functional-equation mirror symmetry preserves the whole finite critical-line
energy.  It therefore cannot by itself force that energy to vanish.
-/
@[aesop safe]
theorem criticalLineEnergy_mirror_invariant
    (w : ι → ℝ) (z : ι → ℂ) :
    criticalLineEnergy w (fun i => criticalMirror (z i)) =
      criticalLineEnergy w z := by
  unfold criticalLineEnergy defectEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  rw [criticalLineDefect_sq_mirror]

/-- Unweighted critical-line energy is also invariant under the mirror. -/
@[aesop safe]
theorem unweightedCriticalLineEnergy_mirror_invariant
    (z : ι → ℂ) :
    unweightedCriticalLineEnergy (fun i => criticalMirror (z i)) =
      unweightedCriticalLineEnergy z := by
  unfold unweightedCriticalLineEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  rw [criticalLineDefect_sq_mirror]

end CriticalLine

end

end GaloisForLFunctions.RHProofLab
