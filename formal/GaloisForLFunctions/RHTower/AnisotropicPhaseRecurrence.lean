import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Anisotropic finite phase recurrence

The usual simultaneous Dirichlet theorem uses one common resolution in all
coordinates.  Weighted phase coherence requires a separate integer resolution
in each coordinate.  The exact cost is the product of those resolutions.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- **Anisotropic simultaneous Dirichlet approximation.**  Positive integer
resolutions `Q i` cost exactly `∏ i, Q i` product boxes. -/
theorem exists_fin_simultaneous_integer_approximation_anisotropic
    {d : ℕ} (α : Fin d → ℝ) (Q : Fin d → ℕ)
    (hQ : ∀ i, 0 < Q i) :
    ∃ n : ℕ, 0 < n ∧ n ≤ ∏ i, Q i ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ 1 / (Q i : ℝ) := by
  let P : ℕ := ∏ i, Q i
  let Cell : Fin d → Type := fun i =>
    {z : ℤ // z ∈ Finset.Ico (0 : ℤ) (Q i)}
  let box : Fin (P + 1) → ((i : Fin d) → Cell i) := fun j i =>
    ⟨⌊Int.fract (α i * (j : ℕ)) * Q i⌋, by
      rw [Finset.mem_Ico]
      constructor
      · exact Int.floor_nonneg.mpr
          (mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg (Q i)))
      · exact Int.floor_lt.mpr
          (mul_lt_of_lt_one_left (Nat.cast_pos.mpr (hQ i))
            (Int.fract_lt_one _))⟩
  have hCellCard (i : Fin d) : Fintype.card (Cell i) = Q i := by
    simp [Cell]
  have hcard :
      Fintype.card ((i : Fin d) → Cell i) <
        Fintype.card (Fin (P + 1)) := by
    rw [Fintype.card_pi, Fintype.card_fin]
    simp_rw [hCellCard]
    simp only [P]
    omega
  obtain ⟨x, y, hxy, hbox⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt box hcard
  have hordered : (x : ℕ) < (y : ℕ) ∨ (y : ℕ) < (x : ℕ) :=
    Nat.lt_or_gt_of_ne (fun h => hxy (Fin.ext h))
  rcases hordered with hlt | hlt
  · let n : ℕ := (y : ℕ) - (x : ℕ)
    let r : Fin d → ℤ := fun i =>
      ⌊α i * (y : ℕ)⌋ - ⌊α i * (x : ℕ)⌋
    refine ⟨n, Nat.sub_pos_of_lt hlt, ?_, r, ?_⟩
    · have hy : (y : ℕ) ≤ P := Nat.lt_succ_iff.mp y.isLt
      exact (Nat.sub_le (y : ℕ) (x : ℕ)).trans hy
    · intro i
      have hfloor :
          ⌊Int.fract (α i * (x : ℕ)) * Q i⌋ =
            ⌊Int.fract (α i * (y : ℕ)) * Q i⌋ := by
        exact congrArg Subtype.val (congrFun hbox i)
      have hunit :
          |Int.fract (α i * (y : ℕ)) * Q i -
              Int.fract (α i * (x : ℕ)) * Q i| ≤ 1 :=
        (Int.abs_sub_lt_one_of_floor_eq_floor hfloor.symm).le
      apply (le_div_iff₀ (Nat.cast_pos.mpr (hQ i))).2
      have hinside :
          ((n : ℝ) * α i - r i) * (Q i : ℝ) =
            Int.fract (α i * (y : ℕ)) * Q i -
              Int.fract (α i * (x : ℕ)) * Q i := by
        simp only [n, r, Int.fract, Nat.cast_sub hlt.le, Int.cast_sub]
        ring
      calc
        |(n : ℝ) * α i - r i| * (Q i : ℝ) =
            |(n : ℝ) * α i - r i| * |(Q i : ℝ)| := by
          exact congrArg (fun q : ℝ => |(n : ℝ) * α i - r i| * q)
            (abs_of_nonneg (Nat.cast_nonneg (Q i))).symm
        _ = |((n : ℝ) * α i - r i) * (Q i : ℝ)| := (abs_mul _ _).symm
        _ = |Int.fract (α i * (y : ℕ)) * Q i -
              Int.fract (α i * (x : ℕ)) * Q i| := congrArg abs hinside
        _ ≤ 1 := hunit
  · let n : ℕ := (x : ℕ) - (y : ℕ)
    let r : Fin d → ℤ := fun i =>
      ⌊α i * (x : ℕ)⌋ - ⌊α i * (y : ℕ)⌋
    refine ⟨n, Nat.sub_pos_of_lt hlt, ?_, r, ?_⟩
    · have hx : (x : ℕ) ≤ P := Nat.lt_succ_iff.mp x.isLt
      exact (Nat.sub_le (x : ℕ) (y : ℕ)).trans hx
    · intro i
      have hfloor :
          ⌊Int.fract (α i * (y : ℕ)) * Q i⌋ =
            ⌊Int.fract (α i * (x : ℕ)) * Q i⌋ := by
        exact congrArg Subtype.val (congrFun hbox.symm i)
      have hunit :
          |Int.fract (α i * (x : ℕ)) * Q i -
              Int.fract (α i * (y : ℕ)) * Q i| ≤ 1 :=
        (Int.abs_sub_lt_one_of_floor_eq_floor hfloor.symm).le
      apply (le_div_iff₀ (Nat.cast_pos.mpr (hQ i))).2
      have hinside :
          ((n : ℝ) * α i - r i) * (Q i : ℝ) =
            Int.fract (α i * (x : ℕ)) * Q i -
              Int.fract (α i * (y : ℕ)) * Q i := by
        simp only [n, r, Int.fract, Nat.cast_sub hlt.le, Int.cast_sub]
        ring
      calc
        |(n : ℝ) * α i - r i| * (Q i : ℝ) =
            |(n : ℝ) * α i - r i| * |(Q i : ℝ)| := by
          exact congrArg (fun q : ℝ => |(n : ℝ) * α i - r i| * q)
            (abs_of_nonneg (Nat.cast_nonneg (Q i))).symm
        _ = |((n : ℝ) * α i - r i) * (Q i : ℝ)| := (abs_mul _ _).symm
        _ = |Int.fract (α i * (x : ℕ)) * Q i -
              Int.fract (α i * (y : ℕ)) * Q i| := congrArg abs hinside
        _ ≤ 1 := hunit

/-- Anisotropic angular recurrence with coordinate error `2π / Q i`. -/
theorem exists_fin_simultaneous_two_pi_phase_approximation_anisotropic
    {d : ℕ} (ω : Fin d → ℝ) (Q : Fin d → ℕ)
    (hQ : ∀ i, 0 < Q i) :
    ∃ n : ℕ, 0 < n ∧ n ≤ ∏ i, Q i ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q i : ℝ) := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_integer_approximation_anisotropic
      (fun i => ω i / (2 * Real.pi)) Q hQ
  refine ⟨n, hn, hnQ, r, ?_⟩
  intro i
  have hscale := mul_le_mul_of_nonneg_left (hr i)
    (show 0 ≤ 2 * Real.pi by positivity)
  have hleft :
      (2 * Real.pi) *
          |(n : ℝ) * (ω i / (2 * Real.pi)) - r i| =
        |(n : ℝ) * ω i - 2 * Real.pi * r i| := by
    have hinside :
        (2 * Real.pi) *
            ((n : ℝ) * (ω i / (2 * Real.pi)) - r i) =
          (n : ℝ) * ω i - 2 * Real.pi * r i := by
      field_simp [Real.pi_ne_zero]
    calc
      (2 * Real.pi) *
          |(n : ℝ) * (ω i / (2 * Real.pi)) - r i| =
          |2 * Real.pi| *
            |(n : ℝ) * (ω i / (2 * Real.pi)) - r i| := by
        rw [abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)]
      _ = |(2 * Real.pi) *
          ((n : ℝ) * (ω i / (2 * Real.pi)) - r i)| :=
        (abs_mul _ _).symm
      _ = |(n : ℝ) * ω i - 2 * Real.pi * r i| := congrArg abs hinside
  have hright :
      (2 * Real.pi) * (1 / (Q i : ℝ)) =
        2 * Real.pi / (Q i : ℝ) := by ring
  rwa [hleft, hright] at hscale

end RHTower
