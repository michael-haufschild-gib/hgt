import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityHypothesis

/-!
# Discharging the largeness hypotheses of the density bound
-/

namespace RHTower.Sieve

open Finset

/-- The three largeness hypotheses of `lemma41_huxley` hold for all large `T`, with an explicit
threshold. -/
theorem exists_lemma41_largeness {eps D : ℝ} (heps : 0 < eps) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((6594624 : ℝ) ≤ T ^ (eps ^ 2)
        ∧ 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) ≤ T ^ (eps ^ 2)
        ∧ D ^ 6 ≤ T ^ (eps ^ 2)) := by
  set z : ℝ := eps ^ 2 / 2 with hzdef
  have hz : (0 : ℝ) < z := by rw [hzdef]; positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := 6594624 + D ^ 6 + 1 + 12 * Real.pi + 12 * Real.pi * (3 : ℝ) ^ z / z with hCdef
  have hC1 : (1 : ℝ) ≤ C := by
    have h1 : (0 : ℝ) ≤ D ^ 6 := by positivity
    have h2 : (0 : ℝ) ≤ 12 * Real.pi * (3 : ℝ) ^ z / z := by
      have : (0 : ℝ) < (3 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    rw [hCdef]; linarith
  have hC0 : (0 : ℝ) < C := by linarith
  refine ⟨max 1 (C ^ (1 / z)), le_max_left _ _, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hTz : C ≤ T ^ z := by
    have hle : C ^ (1 / z) ≤ T := le_trans (le_max_right _ _) hT
    have h0 : (0 : ℝ) ≤ C ^ (1 / z) := (Real.rpow_pos_of_pos hC0 _).le
    have hmono := Real.rpow_le_rpow h0 hle hz.le
    rwa [← Real.rpow_mul hC0.le, one_div, inv_mul_cancel₀ (ne_of_gt hz), Real.rpow_one] at hmono
  have hTz1 : (1 : ℝ) ≤ T ^ z := le_trans hC1 hTz
  have hsplit : T ^ (eps ^ 2) = T ^ z * T ^ z := by
    rw [← Real.rpow_add hT0, hzdef]
    congr 1
    ring
  have hbig : C ≤ T ^ (eps ^ 2) := by
    rw [hsplit]
    nlinarith [hTz, hTz1, hC1]
  have hD6 : D ^ 6 ≤ C := by
    have h2 : (0 : ℝ) ≤ 12 * Real.pi * (3 : ℝ) ^ z / z := by
      have : (0 : ℝ) < (3 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    rw [hCdef]; linarith
  have h6594 : (6594624 : ℝ) ≤ C := by
    have h1 : (0 : ℝ) ≤ D ^ 6 := by positivity
    have h2 : (0 : ℝ) ≤ 12 * Real.pi * (3 : ℝ) ^ z / z := by
      have h3 : (0 : ℝ) < (3 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    rw [hCdef]; linarith
  refine ⟨by linarith [hbig, h6594], ?_, le_trans hD6 hbig⟩
  -- the logarithmic term
  have hlog : Real.log (2 * T + 1) ≤ (3 : ℝ) ^ z * T ^ z / z := by
    have h1 : Real.log (2 * T + 1) ≤ (2 * T + 1) ^ z / z :=
      Real.log_le_rpow_div (by linarith) hz
    have h2 : (2 * T + 1) ^ z ≤ (3 * T) ^ z :=
      Real.rpow_le_rpow (by linarith) (by linarith) hz.le
    have h3 : (3 * T : ℝ) ^ z = (3 : ℝ) ^ z * T ^ z :=
      Real.mul_rpow (by norm_num) hT0.le
    rw [h3] at h2
    calc Real.log (2 * T + 1) ≤ (2 * T + 1) ^ z / z := h1
      _ ≤ (3 : ℝ) ^ z * T ^ z / z := by
        exact div_le_div_of_nonneg_right h2 hz.le
  have hstep : 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) ≤ C * T ^ z := by
    have hcoef : (0 : ℝ) ≤ 12 * Real.pi := by positivity
    have h1 : 12 * Real.pi * Real.log (2 * T + 1)
        ≤ 12 * Real.pi * ((3 : ℝ) ^ z * T ^ z / z) := by
      exact mul_le_mul_of_nonneg_left hlog hcoef
    have hCterm : 12 * Real.pi * ((3 : ℝ) ^ z * T ^ z / z)
        = (12 * Real.pi * (3 : ℝ) ^ z / z) * T ^ z := by
      field_simp
    have hrest : (1 : ℝ) + 12 * Real.pi ≤ (1 + 12 * Real.pi) * T ^ z := by
      nlinarith [hTz1, hpi]
    have hCsplit : C * T ^ z
        = (6594624 + D ^ 6) * T ^ z + (1 + 12 * Real.pi) * T ^ z
          + (12 * Real.pi * (3 : ℝ) ^ z / z) * T ^ z := by
      rw [hCdef]; ring
    have hfirst : (0 : ℝ) ≤ (6594624 + D ^ 6) * T ^ z := by positivity
    rw [hCsplit]
    rw [hCterm] at h1
    linarith
  have hfin : C * T ^ z ≤ T ^ (eps ^ 2) := by
    rw [hsplit]
    have hz0 : (0 : ℝ) < T ^ z := by linarith
    exact mul_le_mul_of_nonneg_right hTz hz0.le
  linarith

/-- **Matomäki–Teräväinen's Lemma 4.1, Huxley form, with the largeness threshold supplied.**
For every small `ε > 0` and every coefficient bound `D` there is a `T₀` beyond which: for a dyadic
Dirichlet block of length `N ∈ [T^{9/11}, T^{1−ε}]` with `‖c n‖ ≤ D`, and every
`σ ∈ [5ε, 7/32 − 5ε]`, a one-separated set of ordinates inside a range of length `2T` on which the
block reaches `N^{−σ}` has at most `T^{2σ−ε²/5}` members.  The only side condition is the Huxley
threshold `2400 D² ≤ N^{1/2−2σ}`, which the divisor bound supplies. -/
theorem exists_lemma41_huxley {eps D : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hD1 : 1 ≤ D) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (N : ℕ) (sigma : ℝ) (c : ℕ → ℂ) (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ N →
      T ^ ((9 : ℝ) / 11) ≤ (N : ℝ) → (N : ℝ) ≤ T ^ (1 - eps) →
      5 * eps ≤ sigma → sigma ≤ 7 / 32 - 5 * eps →
      2400 * D ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma) →
      (∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖blockPoly N c 1 x‖) →
      (S.card : ℝ) ≤ T ^ (2 * sigma - eps ^ 2 / 5) := by
  obtain ⟨T₀, hT₀1, hT₀⟩ := exists_lemma41_largeness (eps := eps) (D := D) heps
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N sigma c S hT hN hNlo hNhi hsl hsh hthr hc hsep hspread hbig
  obtain ⟨hE, hL, hD6⟩ := hT₀ T hT
  exact lemma41_huxley c S hN heps hepss (le_trans hT₀1 hT) hE hL hD1 hD6 hNlo hNhi hsl hsh
    hthr hc hsep hspread hbig

end RHTower.Sieve
