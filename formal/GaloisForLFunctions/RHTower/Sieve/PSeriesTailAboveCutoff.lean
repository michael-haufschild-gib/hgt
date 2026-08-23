import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# The tail of a `p`-series above a cutoff

For an exponent above one the reciprocal powers beyond `R` sum to at most `c/(c−1)·R^{1−c}`: the
first term is kept and the rest compared with the integral, which the antitone comparison supplies.
-/

namespace RHTower.Sieve

open Real MeasureTheory

noncomputable section

/-- The integral of a reciprocal power above one. -/
theorem integral_rpow_neg_Icc_le {c R N : ℝ} (hc : 1 < c) (hR : 0 < R) (hRN : R ≤ N) :
    (∫ t in R..N, t ^ (-c)) ≤ R ^ (1 - c) / (c - 1) := by
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hne : (-c : ℝ) ≠ -1 := by intro h; linarith [neg_injective h]
  have hzero : (0 : ℝ) ∉ Set.uIcc R N := by
    rw [Set.uIcc_of_le hRN, Set.mem_Icc]
    intro h
    linarith [h.1]
  have hint : (∫ t in R..N, t ^ (-c)) = (N ^ (-c + 1) - R ^ (-c + 1)) / (-c + 1) :=
    integral_rpow (Or.inr ⟨hne, hzero⟩)
  rw [hint]
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hR hRN
  have hid : (N ^ (-c + 1) - R ^ (-c + 1)) / (-c + 1)
      = (R ^ (1 - c) - N ^ (1 - c)) / (c - 1) := by
    rw [show (-c + 1 : ℝ) = 1 - c by ring]
    have h1 : (1 - c : ℝ) ≠ 0 := by intro h; linarith
    field_simp
    ring
  rw [hid]
  have hNnn : (0 : ℝ) ≤ N ^ (1 - c) := Real.rpow_nonneg hN.le _
  rw [div_le_div_iff_of_pos_right hc1]
  linarith

/-- **The `p`-series tail.**  For `c > 1` and `R ≥ 1`, the reciprocal powers from `R` on sum to at
most `c/(c−1)·R^{1−c}`. -/
theorem sum_rpow_neg_tail_le {c : ℝ} (hc : 1 < c) {R N : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc R N, ((r : ℝ)) ^ (-c) ≤ (c / (c - 1)) * ((R : ℝ)) ^ (1 - c) := by
  classical
  have hc0 : (0 : ℝ) < c := by linarith
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hRnn : (0 : ℝ) ≤ ((R : ℝ)) ^ (1 - c) := Real.rpow_nonneg hR0.le _
  rcases lt_or_ge N R with hNR | hNR
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hRN : (R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNR
    have hmap : Finset.Icc (R + 1) N = (Finset.Ico R N).map (addRightEmbedding 1) := by
      rw [Finset.map_add_right_Ico]
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hsplit : ∑ r ∈ Finset.Icc R N, ((r : ℝ)) ^ (-c)
        = ((R : ℝ)) ^ (-c) + ∑ i ∈ Finset.Ico R N, ((((i + 1 : ℕ)) : ℝ)) ^ (-c) := by
      have hIcc : Finset.Icc R N = insert R (Finset.Icc (R + 1) N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), hmap, Finset.sum_map]
      rfl
    rw [hsplit]
    have hcomp := (antitoneOn_rpow_neg (σ := c) hc0.le R N hR).sum_le_integral_Ico hNR
    have hint := integral_rpow_neg_Icc_le hc hR0 hRN
    have hhead : ((R : ℝ)) ^ (-c) ≤ ((R : ℝ)) ^ (1 - c) := by
      have hone : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      exact Real.rpow_le_rpow_of_exponent_le hone (by linarith)
    have hid : (c / (c - 1)) * ((R : ℝ)) ^ (1 - c)
        = ((R : ℝ)) ^ (1 - c) + ((R : ℝ)) ^ (1 - c) / (c - 1) := by
      field_simp
      ring
    rw [hid]
    linarith [hcomp, hint, hhead]

end

end RHTower.Sieve
