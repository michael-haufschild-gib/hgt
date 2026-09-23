import GaloisForLFunctions.RHTower.Sieve.HuxleySubdivision
import GaloisForLFunctions.RHTower.Sieve.DyadicSecondEnvelopeClosed

/-!
# Huxley's large-values theorem in closed form
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem norm_dyadicDirRow (N : ℕ) (t : ℝ) :
    ‖dyadicDirRow N t‖ = Real.sqrt (N : ℝ) := by
  have h := norm_dyadicDirRow_sq N t
  have h0 : (0 : ℝ) ≤ ‖dyadicDirRow N t‖ := norm_nonneg _
  rw [← h, Real.sqrt_sq h0]

theorem sq_le_of_large_value {N : ℕ} (a : EuclideanSpace ℂ (Fin N)) {t V G : ℝ}
    (hmass : ‖a‖ ^ (2 : ℕ) ≤ G) (hbig : V ≤ ‖⟪dyadicDirRow N t, a⟫_ℂ‖) (hV : 0 ≤ V) :
    V ^ (2 : ℕ) ≤ (N : ℝ) * G := by
  have hcs : ‖⟪dyadicDirRow N t, a⟫_ℂ‖ ≤ ‖dyadicDirRow N t‖ * ‖a‖ :=
    norm_inner_le_norm _ _
  have hVle : V ≤ Real.sqrt (N : ℝ) * ‖a‖ := by
    rw [← norm_dyadicDirRow N t]
    exact le_trans hbig hcs
  have hsq : V ^ (2 : ℕ) ≤ (Real.sqrt (N : ℝ) * ‖a‖) ^ (2 : ℕ) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) * ‖a‖ := by positivity
    exact pow_le_pow_left₀ hV hVle 2
  have hexp : (Real.sqrt (N : ℝ) * ‖a‖) ^ (2 : ℕ) = (N : ℝ) * ‖a‖ ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [hsq, hexp, mul_le_mul_of_nonneg_left hmass hNR]

/-- **Huxley's large-values theorem, closed form.** -/
theorem huxley_large_values_closed {N : ℕ} (hN : 1 ≤ N)
    (a : EuclideanSpace ℂ (Fin N)) {lam : ℕ → ℝ}
    {delta Ttot V G : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot)
    (hmass : ‖a‖ ^ (2 : ℕ) ≤ G)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (R : ℕ)
    (hspread : ∀ r, r ≤ R → lam r - lam 0 ≤ Ttot)
    (hbig : ∀ r, r ≤ R → V ≤ ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖)
    (hthresh : G * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤ V ^ (2 : ℕ) / 3) :
    ((R : ℝ) + 1) * V ^ (2 : ℕ)
      ≤ (Ttot * (1284 * G) ^ (2 : ℕ) / V ^ (4 : ℕ) + 1) *
        (2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
          * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hVG : V ^ (2 : ℕ) ≤ (N : ℝ) * G := sq_le_of_large_value a hmass (hbig 0 (Nat.zero_le R)) hV.le
  have hV2 : (0 : ℝ) < V ^ (2 : ℕ) := by positivity
  have hG0 : (0 : ℝ) < G := by nlinarith [hVG, hN0, hV2]
  -- the resonance threshold
  set U : ℝ := 4 * Real.pi * (N : ℝ) / 3 with hUdef
  have hU : (0 : ℝ) < U := by rw [hUdef]; positivity
  have hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ) := le_of_eq (by rw [hUdef]; ring)
  have hUeq : (N : ℝ) / Real.sqrt U = Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)) := by
    have hsq : ((N : ℝ) / Real.sqrt U) ^ (2 : ℕ) = 3 * (N : ℝ) / (4 * Real.pi) := by
      rw [div_pow, Real.sq_sqrt hU.le, hUdef]
      field_simp
    rw [← hsq, Real.sqrt_sq (by positivity)]
  -- the window
  set w0 : ℝ := V ^ (2 : ℕ) / (1284 * G) with hw0def
  have hw0 : (0 : ℝ) < w0 := by rw [hw0def]; positivity
  set W : ℝ := w0 ^ (2 : ℕ) with hWdef
  have hW : (0 : ℝ) < W := by rw [hWdef]; positivity
  have hsqW : Real.sqrt W = w0 := by rw [hWdef, Real.sqrt_sq hw0.le]
  -- the window is short enough for the phase test
  have hWsmall : W ≤ (N : ℝ) ^ (2 : ℕ) := by
    have h1 : w0 ≤ (N : ℝ) := by
      rw [hw0def, div_le_iff₀ (by positivity)]
      nlinarith [hVG, hG0, hN0]
    have h2 : (0 : ℝ) ≤ w0 := hw0.le
    rw [hWdef]
    nlinarith [h1, h2, hN0]
  have hlamW : logDyadicLambda N W ≤ 1 := by
    rw [logDyadicLambda_eq_dyadicSecondEnvelopeClosed, div_le_one (by positivity)]
    nlinarith [hWsmall, hN0, hpi, Real.pi_gt_three]
  -- the envelope and its absorption
  set B : ℝ := 1 + 214 * Real.sqrt W + 1536 * ((N : ℝ) / Real.sqrt U) with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ Real.sqrt W := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt U := by positivity
    linarith
  have hB : logDyadicSecondEnvelope N U W ≤ B := by
    have h := logDyadicSecondEnvelope_le hN hU hW.le
    rw [hBdef]
    linarith
  have habsorb : G * B ≤ V ^ (2 : ℕ) / 2 := by
    have hkey : G * (214 * Real.sqrt W) = V ^ (2 : ℕ) / 6 := by
      rw [hsqW, hw0def]
      field_simp
      ring
    have hrest : G * (1 + 1536 * ((N : ℝ) / Real.sqrt U)) ≤ V ^ (2 : ℕ) / 3 := by
      rw [hUeq]; exact hthresh
    rw [hBdef]
    nlinarith [hkey, hrest]
  -- apply the subdivision theorem
  have hmain := huxley_global_large_values hN a hdelta hU hV hW hmass hgap hnear hlamW hB hB1
    R hspread hbig habsorb
  refine le_trans hmain ?_
  have hCpos : (0 : ℝ) ≤ 2 * G * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta)
      * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1)) := by
    have hharm : (0 : ℝ) ≤ ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1) := by positivity
    have : (0 : ℝ) ≤ (12 * Real.pi * (N : ℝ) / delta)
        * ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1) := by positivity
    nlinarith [hG0, hN0]
  refine mul_le_mul_of_nonneg_right ?_ hCpos
  have hfl : ((⌊Ttot / W⌋₊ : ℝ)) ≤ Ttot / W := Nat.floor_le (by positivity)
  have hWval : Ttot / W = Ttot * (1284 * G) ^ (2 : ℕ) / V ^ (4 : ℕ) := by
    rw [hWdef, hw0def]
    field_simp
  rw [← hWval]
  linarith [hfl]

end RHTower.Sieve
