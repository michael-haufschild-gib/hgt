import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth even bump supported strictly inside an annulus

The Sonin wavepacket construction needs a fixed even, nonnegative, smooth, compactly supported
profile living strictly between two positive radii.  A single `ContDiffBump` centred at the
midpoint of `[b, c]` with outer radius a third of the width sits strictly inside `(b, c)`; adding
its reflection makes it even without creating overlap, because the interval is on one side of the
origin.
-/

noncomputable section

namespace RHTower

open Metric Set

/-- The one-sided smooth bump concentrated strictly inside `(b, c)`. -/
def soninAnnulusBumpData (b c : ℝ) (hbc : b < c) : ContDiffBump ((b + c) / 2) where
  rIn := (c - b) / 6
  rOut := (c - b) / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- An even, nonnegative, smooth profile supported strictly inside the annulus `b < |x| < c`. -/
def soninAnnulusBump (b c : ℝ) (hbc : b < c) : ℝ → ℝ := fun x =>
  soninAnnulusBumpData b c hbc x + soninAnnulusBumpData b c hbc (-x)

theorem soninAnnulusBump_even (b c : ℝ) (hbc : b < c) (x : ℝ) :
    soninAnnulusBump b c hbc (-x) = soninAnnulusBump b c hbc x := by
  simp only [soninAnnulusBump, neg_neg]
  ring

theorem soninAnnulusBump_nonneg (b c : ℝ) (hbc : b < c) (x : ℝ) :
    0 ≤ soninAnnulusBump b c hbc x :=
  add_nonneg (soninAnnulusBumpData b c hbc).nonneg (soninAnnulusBumpData b c hbc).nonneg

theorem contDiff_soninAnnulusBump (b c : ℝ) (hbc : b < c) :
    ContDiff ℝ (⊤ : ℕ∞) (soninAnnulusBump b c hbc) :=
  (soninAnnulusBumpData b c hbc).contDiff.add
    ((soninAnnulusBumpData b c hbc).contDiff.comp contDiff_neg)

theorem continuous_soninAnnulusBump (b c : ℝ) (hbc : b < c) :
    Continuous (soninAnnulusBump b c hbc) :=
  (contDiff_soninAnnulusBump b c hbc).continuous

/-- The one-sided bump lives in the open interval `(b, c)`. -/
theorem soninAnnulusBumpData_support_subset (b c : ℝ) (hbc : b < c) {x : ℝ}
    (hx : soninAnnulusBumpData b c hbc x ≠ 0) : b < x ∧ x < c := by
  have hmem : x ∈ ball ((b + c) / 2) ((c - b) / 3) := by
    have := (soninAnnulusBumpData b c hbc).support_eq
    have hx' : x ∈ Function.support (soninAnnulusBumpData b c hbc) := hx
    rwa [this] at hx'
  rw [mem_ball, Real.dist_eq, abs_lt] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

/-- The even profile is supported strictly inside the annulus. -/
theorem soninAnnulusBump_support_subset (b c : ℝ) (hb : 0 < b) (hbc : b < c) {x : ℝ}
    (hx : soninAnnulusBump b c hbc x ≠ 0) : b < |x| ∧ |x| < c := by
  have hor : soninAnnulusBumpData b c hbc x ≠ 0 ∨
      soninAnnulusBumpData b c hbc (-x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (by simp only [soninAnnulusBump, hcon.1, hcon.2, add_zero])
  rcases hor with h | h
  · obtain ⟨h1, h2⟩ := soninAnnulusBumpData_support_subset b c hbc h
    have hxpos : 0 < x := hb.trans h1
    rw [abs_of_pos hxpos]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := soninAnnulusBumpData_support_subset b c hbc h
    have hxneg : x < 0 := by linarith
    rw [abs_of_neg hxneg]
    exact ⟨h1, h2⟩

/-- The even profile is not identically zero: it equals one at the midpoint. -/
theorem soninAnnulusBump_midpoint (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    soninAnnulusBump b c hbc ((b + c) / 2) = 1 := by
  have h1 : soninAnnulusBumpData b c hbc ((b + c) / 2) = 1 := by
    refine (soninAnnulusBumpData b c hbc).one_of_mem_closedBall ?_
    simp only [mem_closedBall, dist_self, soninAnnulusBumpData]
    linarith
  have h2 : soninAnnulusBumpData b c hbc (-((b + c) / 2)) = 0 := by
    by_contra hne
    obtain ⟨hlt, _⟩ := soninAnnulusBumpData_support_subset b c hbc hne
    linarith
  simp only [soninAnnulusBump, h1, h2, add_zero]

theorem soninAnnulusBump_ne_zero (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    soninAnnulusBump b c hbc ≠ 0 := by
  intro hzero
  have := soninAnnulusBump_midpoint b c hb hbc
  rw [hzero] at this
  exact one_ne_zero this.symm

/-- The even profile vanishes outside a fixed compact interval. -/
theorem soninAnnulusBump_eq_zero_of_abs_le (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {x : ℝ} (hx : |x| ≤ b) : soninAnnulusBump b c hbc x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (soninAnnulusBump_support_subset b c hb hbc hne).1)

theorem soninAnnulusBump_eq_zero_of_le_abs (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {x : ℝ} (hx : c ≤ |x|) : soninAnnulusBump b c hbc x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (soninAnnulusBump_support_subset b c hb hbc hne).2)

theorem hasCompactSupport_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    HasCompactSupport (soninAnnulusBump b c hbc) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -c) (b := c))
  intro x hx
  have := soninAnnulusBump_support_subset b c hb hbc hx
  rw [abs_lt] at this
  exact ⟨this.2.1.le, this.2.2.le⟩

end RHTower
