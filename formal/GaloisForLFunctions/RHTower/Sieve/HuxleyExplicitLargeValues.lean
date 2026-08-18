import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues

/-!
# Huxley's large-values count with an explicit logarithm
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- A `delta`-separated finite set confined to a range of length `Ttot` has at most
`Ttot/delta + 1` points. -/
theorem card_le_of_separated {delta Ttot : ℝ} (hdelta : 0 < delta) (hTtot : 0 ≤ Ttot)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot) :
    ((S.card : ℝ)) ≤ Ttot / delta + 1 := by
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    have : (0 : ℝ) ≤ Ttot / delta := div_nonneg hTtot hdelta.le
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hpos : 0 < S.card := Finset.card_pos.2 hne
    obtain ⟨R, hcard⟩ : ∃ R, S.card = R + 1 := ⟨S.card - 1, by omega⟩
    have hgrow : ∀ n : ℕ,
        sepEnum S hcard delta 0 + (n : ℝ) * delta ≤ sepEnum S hcard delta n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hg := sepEnum_gap hcard hsep k
        push_cast
        linarith
    have hspR := hspread (sepEnum S hcard delta R) (sepEnum_mem hcard delta (le_refl R))
      (sepEnum S hcard delta 0) (sepEnum_mem hcard delta (Nat.zero_le R))
    have hle : sepEnum S hcard delta R - sepEnum S hcard delta 0 ≤ Ttot :=
      le_trans (le_abs_self _) hspR
    have hR : (R : ℝ) * delta ≤ Ttot := by linarith [hgrow R]
    have hRle : (R : ℝ) ≤ Ttot / delta := by
      rw [le_div_iff₀ hdelta]
      exact hR
    rw [hcard]
    push_cast
    linarith

/-- **Huxley's large-values theorem with the logarithm made explicit.**  Since a `delta`-separated
set inside a range of length `Ttot` has at most `Ttot/delta + 1` points, the implicit `log |S|` of
`huxley_block_large_values` can be replaced by `log (Ttot/delta + 1)`. -/
theorem huxley_block_large_values_explicit {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    {delta Ttot V D : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot) (hD : 0 ≤ D)
    (hc : ∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖blockPoly N c 1 x‖)
    (hthresh : (D ^ 2 / (N : ℝ)) * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)))
      ≤ V ^ 2 / 3) :
    ((S.card : ℝ)) * V ^ 2
      ≤ (1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) + 1)
        * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta)) := by
  have hbase := huxley_block_large_values hN c hdelta hV hTtot hD hc S hsep hspread hbig hthresh
  refine le_trans hbase ?_
  have hcnt := card_le_of_separated hdelta hTtot S hsep hspread
  have hone : (1 : ℝ) ≤ Ttot / delta + 1 := by
    have : (0 : ℝ) ≤ Ttot / delta := div_nonneg hTtot hdelta.le
    linarith
  have hlog : Real.log (S.card : ℝ) ≤ Real.log (Ttot / delta + 1) := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hp
    · rw [h0]
      simpa using Real.log_nonneg hone
    · exact Real.log_le_log (by exact_mod_cast hp) hcnt
  have hnum : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) hTtot) (by positivity)
  have hpos1 : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) + 1 := by
    have hq : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) :=
      div_nonneg hnum (by positivity)
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hpos1
  have hstep : 12 * Real.pi * (1 + Real.log (S.card : ℝ)) / delta
      ≤ 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hdelta.le
  have hD2 : (0 : ℝ) ≤ 2 * D ^ 2 := by positivity
  nlinarith [hstep, hD2]

end RHTower.Sieve
