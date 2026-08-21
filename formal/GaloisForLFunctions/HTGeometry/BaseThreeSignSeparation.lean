/-
# Base-three weights separate sign patterns

Weighting the sites of a qubit register by powers of three makes the classical onsite energy
injective on computational configurations: the difference of two sign patterns has entries in
`{-2,0,2}`, and at the largest differing site the weight `2·3^S` already exceeds the total
`3^S - 1` that all smaller sites can contribute.  The separation is quantitative -- at least two
units -- so it survives a bounded perturbation of the remaining coefficients.

Main results:
* `sum_lt_three_pow` — the geometric bound on the lower sites.
* `two_le_abs_sum_signDiff` — **the base-three separation**.
-/
import Mathlib

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `±1` sign a configuration assigns to a site. -/
def siteSign (x : Fin m → Bool) (s : Fin m) : ℝ := if x s then (-1 : ℝ) else 1

theorem abs_siteSign (x : Fin m → Bool) (s : Fin m) : |siteSign x s| = 1 := by
  by_cases h : x s <;> norm_num [siteSign, h]

theorem siteSign_sub_eq_zero_iff {x y : Fin m → Bool} (s : Fin m) :
    siteSign x s - siteSign y s = 0 ↔ x s = y s := by
  by_cases hx : x s <;> by_cases hy : y s <;> norm_num [siteSign, hx, hy]

theorem abs_siteSign_sub_of_ne {x y : Fin m → Bool} {s : Fin m} (h : x s ≠ y s) :
    |siteSign x s - siteSign y s| = 2 := by
  by_cases hx : x s <;> by_cases hy : y s <;> simp_all [siteSign] <;> norm_num

theorem abs_siteSign_sub_le (x y : Fin m → Bool) (s : Fin m) :
    |siteSign x s - siteSign y s| ≤ 2 := by
  by_cases hx : x s <;> by_cases hy : y s <;> norm_num [siteSign, hx, hy]

/-- The lower sites contribute strictly less than the largest one. -/
theorem sum_lt_three_pow (S : ℕ) :
    ∑ k ∈ Finset.range S, (2 : ℝ) * 3 ^ k = 3 ^ S - 1 := by
  induction S with
  | zero => simp
  | succ S ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- **Base-three separation.**  Two distinct configurations differ by at least two units in the
base-three weighted sign sum. -/
theorem two_le_abs_sum_signDiff {m : ℕ} {x y : Fin m → Bool} (hxy : x ≠ y) :
    2 ≤ |∑ s : Fin m, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)| := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (Fin m), D = Finset.univ.filter fun s => x s ≠ y s := ⟨_, rfl⟩
  have hmemD : ∀ s, s ∈ D ↔ x s ≠ y s := by
    intro s
    rw [hDdef]
    simp
  have hDne : D.Nonempty := by
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hxy
    exact ⟨s, (hmemD s).mpr hs⟩
  obtain ⟨S, hSmem⟩ : ∃ S, S ∈ D ∧ ∀ s ∈ D, s ≤ S :=
    ⟨D.max' hDne, D.max'_mem hDne, fun s hs => D.le_max' s hs⟩
  obtain ⟨hSD, hSmax⟩ := hSmem
  have hzero : ∀ s ∉ D, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) = 0 := by
    intro s hs
    have : x s = y s := by
      by_contra h
      exact hs ((hmemD s).mpr h)
    rw [(siteSign_sub_eq_zero_iff s).mpr this, mul_zero]
  have hsupp : ∑ s : Fin m, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)
      = ∑ s ∈ D, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) :=
    (Finset.sum_subset (Finset.subset_univ D) fun s _ hs => hzero s hs).symm
  have hsplit : ∑ s ∈ D, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)
      = (3 : ℝ) ^ (S : ℕ) * (siteSign x S - siteSign y S)
        + ∑ s ∈ D.erase S, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) :=
    (Finset.add_sum_erase D _ hSD).symm
  have hbig : |(3 : ℝ) ^ (S : ℕ) * (siteSign x S - siteSign y S)| = 2 * 3 ^ (S : ℕ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ (S : ℕ)),
      abs_siteSign_sub_of_ne ((hmemD S).mp hSD)]
    ring
  have hsmall : |∑ s ∈ D.erase S, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)|
      ≤ 3 ^ (S : ℕ) - 1 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ s ∈ D.erase S,
        |(3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)| ≤ 2 * 3 ^ (s : ℕ) := by
      intro s _
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ (s : ℕ))]
      have := abs_siteSign_sub_le x y s
      nlinarith [abs_nonneg (siteSign x s - siteSign y s), pow_pos (by norm_num : (0:ℝ) < 3) (s:ℕ)]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have himg : ((D.erase S).image (fun s : Fin m => (s : ℕ))) ⊆ Finset.range (S : ℕ) := by
      intro k hk
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
      have hne : s ≠ S := Finset.ne_of_mem_erase hs
      have hle : s ≤ S := hSmax s (Finset.mem_of_mem_erase hs)
      have hlt : s < S := lt_of_le_of_ne hle hne
      exact Finset.mem_range.mpr (Fin.lt_def.mp hlt)
    calc ∑ s ∈ D.erase S, (2 : ℝ) * 3 ^ (s : ℕ)
        = ∑ k ∈ (D.erase S).image (fun s : Fin m => (s : ℕ)), (2 : ℝ) * 3 ^ k := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact Fin.val_injective h
      _ ≤ ∑ k ∈ Finset.range (S : ℕ), (2 : ℝ) * 3 ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun k _ _ => by positivity
      _ = 3 ^ (S : ℕ) - 1 := sum_lt_three_pow _
  rw [hsupp, hsplit]
  have htri := abs_sub_abs_le_abs_sub
    ((3 : ℝ) ^ (S : ℕ) * (siteSign x S - siteSign y S))
    (-(∑ s ∈ D.erase S, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)))
  have habs : |(-(∑ s ∈ D.erase S, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)))|
      = |∑ s ∈ D.erase S, (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)| := abs_neg _
  have hone : (1 : ℝ) ≤ 3 ^ (S : ℕ) := one_le_pow₀ (by norm_num)
  rw [habs, sub_neg_eq_add, hbig] at htri
  linarith [htri, hsmall, hone]

end GaloisForLFunctions.HTGeometry

end
