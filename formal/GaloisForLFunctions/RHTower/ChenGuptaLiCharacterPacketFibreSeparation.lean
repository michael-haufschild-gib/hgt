/-
# Chen--Gupta--Li fibrewise separated character packets

The separation clause in Chen--Gupta--Li's large-value theorem is fibrewise:
two distinct rows either carry different characters or their ordinates are
separated.  This module formalizes that exact finite geometry.  A fibre rank
and its separated extension are certified finite data, allowing each character
fibre to be handled by the existing harmonic Gram-row argument without
incorrectly imposing separation on different-character rows.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketOffDiagonal

noncomputable section

namespace RHTower

/-- A finite CGL character packet with a separated ordering inside each
character fibre.  `fibreTime` is an infinite extension of each finite fibre;
the rank certificate records the actual packet rows in its first `R` slots.
This is the finite data behind the source condition that equal-character rows
have separated ordinates. -/
structure CGLFibreSeparatedPacket (q R : ℕ) where
  ordinate : Fin R → ℝ
  character : Fin R → DirichletCharacter ℂ (q + 1)
  spacing : ℝ
  spacing_pos : 0 < spacing
  fibreRank : Fin R → ℕ
  fibreRank_lt : ∀ r, fibreRank r < R
  fibreTime : DirichletCharacter ℂ (q + 1) → ℕ → ℝ
  fibreTime_step : ∀ χ i, fibreTime χ i + spacing ≤ fibreTime χ (i + 1)
  ordinate_eq_fibreTime : ∀ r, ordinate r = fibreTime (character r) (fibreRank r)
  fibreRank_injective : ∀ {r s}, character r = character s → fibreRank r = fibreRank s → r = s

/-- The reciprocal kernel row after different character labels have been
removed. -/
def cglFibreSeparatedPacketSameCharacterReciprocalRow {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (r : Fin R) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
    if P.character r = P.character s then
      2 / |P.ordinate s - P.ordinate r| else 0

/-- The rank certificate yields the source's fibrewise separation statement. -/
theorem cglFibreSeparatedPacket_sameCharacter_separation {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (r s : Fin R) (hrs : r ≠ s)
    (hchar : P.character r = P.character s) :
    P.spacing ≤ |P.ordinate r - P.ordinate s| := by
  have hrank : P.fibreRank r ≠ P.fibreRank s :=
    fun heq => hrs (P.fibreRank_injective hchar heq)
  rcases lt_or_gt_of_ne hrank with hlt | hgt
  · have hspread := RHTower.Sieve.le_of_gap (P.fibreTime_step (P.character r))
      (P.fibreRank r) (P.fibreRank s) (le_of_lt hlt)
    have hunit : (1 : ℝ) ≤ (P.fibreRank s : ℝ) - P.fibreRank r := by
      have : (P.fibreRank r : ℝ) + 1 ≤ P.fibreRank s := by exact_mod_cast hlt
      linarith
    have hmul : P.spacing ≤ ((P.fibreRank s : ℝ) - P.fibreRank r) * P.spacing := by
      simpa using mul_le_mul_of_nonneg_right hunit (le_of_lt P.spacing_pos)
    have hstep : P.fibreTime (P.character r) (P.fibreRank r) + P.spacing ≤
        P.fibreTime (P.character r) (P.fibreRank s) := by
      linarith
    rw [P.ordinate_eq_fibreTime r, P.ordinate_eq_fibreTime s, ← hchar]
    rw [abs_of_nonpos (by linarith [P.spacing_pos])]
    linarith
  · have hspread := RHTower.Sieve.le_of_gap (P.fibreTime_step (P.character s))
      (P.fibreRank s) (P.fibreRank r) (le_of_lt hgt)
    have hunit : (1 : ℝ) ≤ (P.fibreRank r : ℝ) - P.fibreRank s := by
      have : (P.fibreRank s : ℝ) + 1 ≤ P.fibreRank r := by exact_mod_cast hgt
      linarith
    have hmul : P.spacing ≤ ((P.fibreRank r : ℝ) - P.fibreRank s) * P.spacing := by
      simpa using mul_le_mul_of_nonneg_right hunit (le_of_lt P.spacing_pos)
    have hstep : P.fibreTime (P.character s) (P.fibreRank s) + P.spacing ≤
        P.fibreTime (P.character s) (P.fibreRank r) := by
      linarith
    have hstep' : P.fibreTime (P.character r) (P.fibreRank s) + P.spacing ≤
        P.fibreTime (P.character r) (P.fibreRank r) := by
      simpa only [hchar] using hstep
    rw [P.ordinate_eq_fibreTime r, P.ordinate_eq_fibreTime s, ← hchar]
    rw [abs_of_nonneg (by linarith [hstep', P.spacing_pos])]
    linarith [hstep']

/-- Different equal-character rows have distinct ordinates. -/
theorem cglFibreSeparatedPacket_ordinate_ne {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (r s : Fin R) (hrs : r ≠ s)
    (hchar : P.character r = P.character s) : P.ordinate r ≠ P.ordinate s := by
  intro heq
  have hsep := cglFibreSeparatedPacket_sameCharacter_separation P r s hrs hchar
  rw [heq] at hsep
  simp only [sub_self, abs_zero] at hsep
  linarith [P.spacing_pos]

/-- The same-character off-diagonal interval-kernel row of a fibrewise
separated packet. -/
def cglFibreSeparatedPacketSameCharacterKernelRow {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) (r : Fin R) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
    if P.character r = P.character s then
      ‖cglCharacterPacketIntervalKernel A B (P.ordinate r) (P.ordinate s)‖ else 0

/-- The same-character reciprocal row has the exact harmonic bound.  Its proof
reindexes the finite character fibre into the range of its certified separated
extension, then applies the existing separated-row theorem. -/
theorem cglFibreSeparatedPacket_sameCharacterReciprocalRow_le {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (r : Fin R) :
    cglFibreSeparatedPacketSameCharacterReciprocalRow P r ≤
      (4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
  let S : Finset (Fin R) := ((Finset.univ : Finset (Fin R)).erase r).filter
    (fun s => P.character r = P.character s)
  let f : ℕ → ℝ := fun k => 2 / |P.fibreTime (P.character r) k -
    P.fibreTime (P.character r) (P.fibreRank r)|
  have hS : cglFibreSeparatedPacketSameCharacterReciprocalRow P r = ∑ s ∈ S, f (P.fibreRank s) := by
    unfold cglFibreSeparatedPacketSameCharacterReciprocalRow
    unfold S
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hchar : P.character r = P.character s
    · rw [if_pos hchar]
      rw [P.ordinate_eq_fibreTime s, P.ordinate_eq_fibreTime r]
      rw [← hchar]
      simp [f, abs_sub_comm]
    · rw [if_neg hchar]
      simp [hchar]
  rw [hS]
  have hinj : Set.InjOn P.fibreRank S := by
    intro s hs t ht heq
    have hschar : P.character r = P.character s := (Finset.mem_filter.mp hs).2
    have htchar : P.character r = P.character t := (Finset.mem_filter.mp ht).2
    exact P.fibreRank_injective (hschar.symm.trans htchar) heq
  calc
    ∑ s ∈ S, f (P.fibreRank s) = ∑ k ∈ S.image P.fibreRank, f k :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ (Finset.range R).erase (P.fibreRank r), f k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨s, hs, hks⟩
        subst k
        apply Finset.mem_erase.mpr
        constructor
        · intro heq
          have hchar : P.character r = P.character s := (Finset.mem_filter.mp hs).2
          have hsr : s = r := P.fibreRank_injective hchar.symm heq
          exact (Finset.mem_erase.mp (Finset.mem_filter.mp hs).1).1 hsr
        · exact Finset.mem_range.mpr (P.fibreRank_lt s)
      · intro k hk hks
        exact div_nonneg (by norm_num) (abs_nonneg _)
    _ ≤ _ := by
      have hbase := RHTower.Sieve.sum_inv_abs_dist_le P.spacing_pos
        (P.fibreTime_step (P.character r)) (P.fibreRank_lt r)
      change (∑ s ∈ (Finset.range R).erase (P.fibreRank r), f s) ≤ _
      calc
        ∑ s ∈ (Finset.range R).erase (P.fibreRank r), f s =
            2 * ∑ s ∈ (Finset.range R).erase (P.fibreRank r),
              1 / |P.fibreTime (P.character r) s - P.fibreTime (P.character r) (P.fibreRank r)| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          dsimp [f]
          ring
        _ ≤ 2 * ((2 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hbase (by norm_num)
        _ = _ := by ring

/-- Interval kernels are bounded by their fibrewise reciprocal row. -/
theorem cglFibreSeparatedPacket_sameCharacterKernelRow_le_reciprocal {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) (r : Fin R) :
    cglFibreSeparatedPacketSameCharacterKernelRow P A B r ≤
      cglFibreSeparatedPacketSameCharacterReciprocalRow P r := by
  unfold cglFibreSeparatedPacketSameCharacterKernelRow
    cglFibreSeparatedPacketSameCharacterReciprocalRow
  apply Finset.sum_le_sum
  intro s hs
  have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
  by_cases hchar : P.character r = P.character s
  · rw [if_pos hchar, if_pos hchar]
    have htime : P.ordinate r ≠ P.ordinate s :=
      cglFibreSeparatedPacket_ordinate_ne P r s (Ne.symm hsr) hchar
    let p : CGLDistinctOrdinatePair := ⟨(P.ordinate r, P.ordinate s), htime⟩
    simpa only [p, abs_sub_comm] using norm_cglCharacterPacketIntervalKernel_le A B p
  · rw [if_neg hchar, if_neg hchar]

/-- Fibrewise separation gives the source-correct CGL harmonic interval-kernel
bound, without introducing separation between different characters. -/
theorem cglFibreSeparatedPacket_sameCharacterKernelRow_le {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (A B : ℝ) (r : Fin R) :
    cglFibreSeparatedPacketSameCharacterKernelRow P A B r ≤
      (4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) :=
  le_trans (cglFibreSeparatedPacket_sameCharacterKernelRow_le_reciprocal P A B r)
    (cglFibreSeparatedPacket_sameCharacterReciprocalRow_le P r)

end RHTower
