import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Small sections of a metrized rational lattice

On a lattice with positive generator `d`, an integer `z` indexes the section `dz`.
Its archimedean bound is `exp A`. The logarithmic count differs from the
positive part of the degree `A - log d` by a universal constant, including
when the zero section is the only section.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- Integer coordinates of the small sections in the basis of the lattice. -/
def smallSections (d A : ℝ) : Finset ℤ :=
  let r := ⌊Real.exp A / d⌋₊
  Icc (-(r : ℤ)) r

theorem mem_smallSections {d A : ℝ} (hd : 0 < d) (z : ℤ) :
    z ∈ smallSections d A ↔ |d * (z : ℝ)| ≤ Real.exp A := by
  rw [abs_mul, abs_of_pos hd, mul_comm, ← le_div_iff₀ hd]
  change z ∈ Icc _ _ ↔ _
  rw [mem_Icc, ← abs_le, ← Int.natCast_natAbs, Nat.cast_le, Nat.le_floor_iff
    (div_nonneg (Real.exp_pos _).le hd.le)]
  simp

/-- A nonzero small section exists exactly when the generator fits inside the ball. -/
theorem exists_nonzero_smallSection {d A : ℝ} (hd : 0 < d) :
    (∃ z ∈ smallSections d A, z ≠ 0) ↔ Real.log d ≤ A := by
  rw [Real.log_le_iff_le_exp hd]
  constructor
  · rintro ⟨z, hz, hne⟩
    have h1 : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hne; omega
    have hr : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast h1
    have hz' := (mem_smallSections hd z).mp hz
    rw [abs_mul, abs_of_pos hd] at hz'
    exact (le_mul_of_one_le_right hd.le hr).trans hz'
  · intro h
    exact ⟨1, (mem_smallSections hd 1).mpr (by simpa [abs_of_pos hd] using h), one_ne_zero⟩

/-- The natural-valued height is the integer part of the logarithm of the section count. -/
def sectionHeight (d A : ℝ) : ℕ := ⌊Real.log (smallSections d A).card⌋₊

theorem card_smallSections (d A : ℝ) :
    (smallSections d A).card = 2 * ⌊Real.exp A / d⌋₊ + 1 := by
  simp only [smallSections, Int.card_Icc]
  omega

/-- Both sides of degree zero have the same absolute error bound. -/
theorem sectionHeight_bounds {d A : ℝ} (hd : 0 < d) :
    max (A - Real.log d) 0 - 1 ≤ sectionHeight d A ∧
      (sectionHeight d A : ℝ) ≤ max (A - Real.log d) 0 + Real.log 3 := by
  let x := A - Real.log d
  have he : Real.exp A / d = Real.exp x := by simp only [x, Real.exp_sub, Real.exp_log hd]
  let r := ⌊Real.exp x⌋₊
  have hfloor : (r : ℝ) ≤ Real.exp x := Nat.floor_le (Real.exp_pos _).le
  have hnext : Real.exp x < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hc : ((smallSections d A).card : ℝ) = 2 * (r : ℝ) + 1 := by
    rw [card_smallSections, he]
    push_cast
    rfl
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hlow : Real.exp (max x 0) ≤ 2 * (r : ℝ) + 1 := by
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, Real.exp_zero]; linarith
    · rw [max_eq_left h]; linarith
  have hupp : 2 * (r : ℝ) + 1 ≤ 3 * Real.exp (max x 0) := by
    have h₁ := Real.exp_le_exp.mpr (le_max_left x 0)
    have h₂ := Real.exp_le_exp.mpr (le_max_right x 0)
    rw [Real.exp_zero] at h₂
    linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hlow
  rw [Real.log_exp] at hlog
  have hlog' := Real.log_le_log (by positivity) hupp
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog'
  rw [sectionHeight, hc]
  change max x 0 - 1 ≤ _ ∧ _ ≤ max x 0 + _
  exact ⟨by linarith [Nat.lt_floor_add_one (Real.log (2 * (r : ℝ) + 1))],
    (Nat.floor_le (by linarith [le_max_right x 0])).trans (by linarith)⟩

end GaloisForLFunctions.CountingHolography.Sections
