import GaloisForLFunctions.RHTower.Sieve.InverseSquareTail
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealFinsetHalaszMontgomery

namespace RHTower.Sieve

open Finset

noncomputable section

/-! # Reciprocal tails on separated Menon frequencies

Menon's long-factor branch gives a pointwise bound consisting of a power-saving term and a
reciprocal-height term.  This file supplies the exact summation interface needed on a finite
one-separated frequency set.  The reciprocal part costs `O(T₀⁻¹)`, independently of cardinality.
-/

/-- Iterating consecutive spacing gives a linear lower bound along the certified timeline. -/
theorem cglFiniteSeparatedOrdinatesTimeline_lower_linear
    {R : ℕ} (P : RHTower.CGLFiniteSeparatedOrdinates R) (i : ℕ) :
    RHTower.cglFiniteSeparatedOrdinatesTimeline P 0 + (i : ℝ) * P.spacing ≤
      RHTower.cglFiniteSeparatedOrdinatesTimeline P i := by
  induction i with
  | zero => simp
  | succ i hi =>
      calc
        RHTower.cglFiniteSeparatedOrdinatesTimeline P 0 + ((i + 1 : ℕ) : ℝ) * P.spacing =
            (RHTower.cglFiniteSeparatedOrdinatesTimeline P 0 + (i : ℝ) * P.spacing) +
              P.spacing := by push_cast; ring
        _ ≤ RHTower.cglFiniteSeparatedOrdinatesTimeline P i + P.spacing := by
          linarith
        _ ≤ RHTower.cglFiniteSeparatedOrdinatesTimeline P (i + 1) :=
          RHTower.cglFiniteSeparatedOrdinatesTimeline_step P i

/-- A nonnegative one-separated packet above `T₀` has reciprocal-square mass at most `2 / T₀`. -/
theorem sum_inv_one_add_sq_le_of_oneSeparated_nonneg
    {S : Finset ℝ} {T0 : ℝ} (hT0 : 2 ≤ T0)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hlower : ∀ t ∈ S, T0 ≤ t) :
    ∑ t ∈ S, 1 / (1 + t) ^ (2 : ℕ) ≤ 2 / T0 := by
  classical
  by_cases hS : S = ∅
  · simp [hS, div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ T0)]
  let P := matomakiTeravainenFiniteSeparatedOrdinates S 1 one_pos hsep
  let R : ℕ := ⌊T0⌋₊
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    exact Nat.le_floor (by norm_num; linarith)
  have hRle : (R : ℝ) ≤ T0 := by
    dsimp only [R]
    exact Nat.floor_le (by linarith)
  have hRhalf : T0 / 2 ≤ (R : ℝ) := by
    have hfloorLt : T0 < (R : ℝ) + 1 := by
      dsimp only [R]
      exact Nat.lt_floor_add_one T0
    linarith
  have hcard : 0 < S.card := Finset.card_pos.mpr (by simpa [Finset.nonempty_iff_ne_empty])
  have hzeroMem : RHTower.cglFiniteSeparatedOrdinatesTimeline P 0 ∈ S := by
    exact matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      S 1 one_pos hsep (by omega)
  have htimeline0 : T0 ≤ RHTower.cglFiniteSeparatedOrdinatesTimeline P 0 :=
    hlower _ hzeroMem
  have hterm : ∀ i ∈ Finset.range S.card,
      1 / (1 + RHTower.cglFiniteSeparatedOrdinatesTimeline P i) ^ (2 : ℕ) ≤
        1 / ((i : ℝ) + R + 1) ^ (2 : ℕ) := by
    intro i hi
    have hlinear := cglFiniteSeparatedOrdinatesTimeline_lower_linear P i
    have hspacing : P.spacing = 1 := by rfl
    rw [hspacing] at hlinear
    have hden : (i : ℝ) + R + 1 ≤
        1 + RHTower.cglFiniteSeparatedOrdinatesTimeline P i := by
      have hi0 : (0 : ℝ) ≤ i := by positivity
      linarith
    have hleft : 0 ≤ (i : ℝ) + R + 1 := by positivity
    have hsq := pow_le_pow_left₀ hleft hden 2
    exact one_div_le_one_div_of_le (by positivity) hsq
  rw [sum_finset_eq_sum_matomakiTeravainenFiniteSeparatedOrdinates_timeline
    S 1 one_pos hsep]
  calc
    ∑ i ∈ Finset.range S.card,
        1 / (1 + RHTower.cglFiniteSeparatedOrdinatesTimeline P i) ^ (2 : ℕ) ≤
      ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + R + 1) ^ (2 : ℕ) :=
        Finset.sum_le_sum hterm
    _ ≤ 1 / (R : ℝ) - 1 / ((S.card : ℝ) + R) :=
      sum_range_inv_sq_shift_le R S.card hR1
    _ ≤ 1 / (R : ℝ) := by
      have hnonneg : 0 ≤ 1 / ((S.card : ℝ) + R) := by positivity
      linarith
    _ ≤ 2 / T0 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ)) (by linarith : 0 < T0)]
      nlinarith

/-- A two-sided one-separated packet outside `[-T₀,T₀]` has reciprocal-square mass at most
`4 / T₀`. -/
theorem sum_inv_one_add_abs_sq_le_of_oneSeparated
    {S : Finset ℝ} {T0 : ℝ} (hT0 : 2 ≤ T0)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hlower : ∀ t ∈ S, T0 ≤ |t|) :
    ∑ t ∈ S, 1 / (1 + |t|) ^ (2 : ℕ) ≤ 4 / T0 := by
  classical
  let Spos := S.filter (fun t => 0 ≤ t)
  let Sneg := S.filter (fun t => ¬ 0 ≤ t)
  let Sneg' := Sneg.image (fun t : ℝ => -t)
  have hsplit : ∑ t ∈ S, 1 / (1 + |t|) ^ (2 : ℕ) =
      (∑ t ∈ Spos, 1 / (1 + t) ^ (2 : ℕ)) +
        ∑ t ∈ Sneg', 1 / (1 + t) ^ (2 : ℕ) := by
    dsimp only [Spos, Sneg, Sneg']
    rw [← Finset.sum_filter_add_sum_filter_not S (fun t => 0 ≤ t)
      (fun t => 1 / (1 + |t|) ^ (2 : ℕ))]
    congr 1
    · apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [abs_of_nonneg ht.2]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_filter] at ht
        have htneg : t < 0 := lt_of_not_ge ht.2
        rw [abs_of_neg htneg]
      · intro x hx y hy hxy
        exact neg_injective hxy
  have hposSep : ∀ x ∈ Spos, ∀ y ∈ Spos, x ≠ y → (1 : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hposLower : ∀ t ∈ Spos, T0 ≤ t := by
    intro t ht
    have hnonneg := (Finset.mem_filter.mp ht).2
    simpa [abs_of_nonneg hnonneg] using hlower t (Finset.mem_filter.mp ht).1
  have hnegSep : ∀ x ∈ Sneg', ∀ y ∈ Sneg', x ≠ y → (1 : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    dsimp only [Sneg'] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.mp hy
    have hxy0 : x0 ≠ y0 := fun h => hxy (by rw [h])
    simpa only [neg_sub_neg, abs_neg] using
      hsep y0 (Finset.mem_filter.mp hy0).1 x0 (Finset.mem_filter.mp hx0).1 hxy0.symm
  have hnegLower : ∀ t ∈ Sneg', T0 ≤ t := by
    intro t ht
    dsimp only [Sneg'] at ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    have huneg : u < 0 := by
      dsimp only [Sneg] at hu
      exact lt_of_not_ge (Finset.mem_filter.mp hu).2
    simpa [abs_of_neg huneg] using
      hlower u (by dsimp only [Sneg] at hu; exact (Finset.mem_filter.mp hu).1)
  rw [hsplit]
  calc
    (∑ t ∈ Spos, 1 / (1 + t) ^ (2 : ℕ)) + ∑ t ∈ Sneg', 1 / (1 + t) ^ (2 : ℕ) ≤
        2 / T0 + 2 / T0 := add_le_add
          (sum_inv_one_add_sq_le_of_oneSeparated_nonneg hT0 hposSep hposLower)
          (sum_inv_one_add_sq_le_of_oneSeparated_nonneg hT0 hnegSep hnegLower)
    _ = 4 / T0 := by ring

/-- Menon's IIb summation rule: power saving costs cardinality, while reciprocal-height decay costs
only `T₀⁻¹` on a one-separated packet. -/
theorem sum_sq_le_of_pointwise_power_add_reciprocal
    {S : Finset ℝ} {T0 A B : ℝ} (hT0 : 2 ≤ T0) (hB : 0 ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hlower : ∀ t ∈ S, T0 ≤ |t|)
    (F : ℝ → ℝ) (hF : ∀ t ∈ S, 0 ≤ F t ∧ F t ≤ A + B / (1 + |t|)) :
    ∑ t ∈ S, (F t) ^ (2 : ℕ) ≤ 2 * (S.card : ℝ) * A ^ (2 : ℕ) + 8 * B ^ (2 : ℕ) / T0 := by
  have hpoint : ∀ t ∈ S, (F t) ^ (2 : ℕ) ≤
      2 * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) * (1 / (1 + |t|) ^ (2 : ℕ)) := by
    intro t ht
    have hrecip : 0 ≤ B / (1 + |t|) := by positivity
    have hsq := pow_le_pow_left₀ (hF t ht).1 (hF t ht).2 2
    calc
      (F t) ^ (2 : ℕ) ≤ (A + B / (1 + |t|)) ^ (2 : ℕ) := hsq
      _ ≤ 2 * A ^ (2 : ℕ) + 2 * (B / (1 + |t|)) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (A - B / (1 + |t|))]
      _ = 2 * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) * (1 / (1 + |t|) ^ (2 : ℕ)) := by
        simp only [div_eq_mul_inv, mul_pow, inv_pow]
        ring
  calc
    ∑ t ∈ S, (F t) ^ (2 : ℕ) ≤
        ∑ t ∈ S, (2 * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) * (1 / (1 + |t|) ^ (2 : ℕ))) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (S.card : ℝ) * A ^ (2 : ℕ) +
        2 * B ^ (2 : ℕ) * (∑ t ∈ S, 1 / (1 + |t|) ^ (2 : ℕ)) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * (S.card : ℝ) * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) * (4 / T0) := by
      gcongr
      exact sum_inv_one_add_abs_sq_le_of_oneSeparated hT0 hsep hlower
    _ = 2 * (S.card : ℝ) * A ^ (2 : ℕ) + 8 * B ^ (2 : ℕ) / T0 := by ring

end

end RHTower.Sieve
