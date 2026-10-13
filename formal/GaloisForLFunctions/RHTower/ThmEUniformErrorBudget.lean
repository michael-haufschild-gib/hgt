import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The error budget of the rank–trace seam

A purely real-variable lemma: the error of the rank–trace certificate,

`4R₁ + R₂ + 3N_II + B(4 + 2√(c N + R₂) + B)`,   `R₂ = c(((1+E)/a² − 1)N + (1+E)R_N/a²)`,

is at most `ε N` as soon as each of its ingredients is below its share of `ε N_low`, where `N_low ≤ N`
(`seam_error_le`).  The shares are `ε/8` for `4R₁`, `3N_II`, `5ρ_B`, the relative taper and Frobenius
errors and the Riemann–von Mangoldt error, and `ε/8 · √N_low` for the square-root tail term.
-/

open Real

namespace RHTower

/-- **The error budget.** -/
theorem seam_error_le {N Nl a c C E ρE RN R₁ R₂ NII B ρB L ε : ℝ}
    (hNl : 0 < Nl) (hN : Nl ≤ N) (ha2 : 1 / 2 ≤ a) (ha1 : a ≤ 1) (hL2 : 2 ≤ L)
    (haL : 1 - 2 / L ≤ a) (hc0 : 0 < c) (hc : c ≤ C) (hE0 : 0 ≤ E) (hE : E ≤ ρE) (hρE1 : ρE ≤ 1)
    (hr2 : 4 * C * (ρE + 4 / L) ≤ ε / 8) (hRN0 : 0 ≤ RN) (hr3 : 8 * C * RN ≤ ε / 8 * Nl)
    (hR₂ : R₂ = c * (((1 + 1 * E) / a ^ 2 - 1) * N + (1 + 1 * E) / a ^ 2 * RN))
    (hR₁ : 4 * R₁ ≤ ε / 8 * Nl) (hNII : 3 * NII ≤ ε / 8 * Nl) (hB0 : 0 ≤ B) (hB : B ≤ ρB)
    (hρB1 : ρB ≤ 1) (hr5 : 5 * ρB ≤ ε / 8 * Nl)
    (hr6 : 2 * ρB * Real.sqrt (C + 1) ≤ ε / 8 * Real.sqrt Nl) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    4 * R₁ + R₂ + 3 * NII + B * (4 + 2 * Real.sqrt (c * N + R₂) + B) ≤ ε * N := by
  have hN0 : 0 < N := lt_of_lt_of_le hNl hN
  have ha0 : 0 < a := by linarith
  have ha2' : 1 / 4 ≤ a ^ 2 := by nlinarith
  have haL2 : 1 - 4 / L ≤ a ^ 2 := by
    have h1 : 0 ≤ 1 - 2 / L := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h2 : (1 - 2 / L) * (1 - 2 / L) ≤ a * a := mul_le_mul haL haL h1 ha0.le
    have h3 : (1 - 2 / L) * (1 - 2 / L) = 1 - 4 / L + (2 / L) ^ 2 := by ring
    rw [h3] at h2
    rw [sq]
    linarith [sq_nonneg (2 / L)]
  have hinv : 1 / a ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  -- the Frobenius share
  have hK1 : (1 + 1 * E) / a ^ 2 - 1 ≤ 4 * (ρE + 4 / L) := by
    have e : (1 + 1 * E) / a ^ 2 - 1 = (1 + E - a ^ 2) * (1 / a ^ 2) := by
      field_simp
    have h1 : 0 ≤ 1 + E - a ^ 2 := by nlinarith
    rw [e]
    calc (1 + E - a ^ 2) * (1 / a ^ 2) ≤ (1 + E - a ^ 2) * 4 := mul_le_mul_of_nonneg_left hinv h1
      _ ≤ 4 * (ρE + 4 / L) := by nlinarith
  have hK10 : 0 ≤ (1 + 1 * E) / a ^ 2 - 1 := by
    rw [sub_nonneg, le_div_iff₀ (by positivity)]; nlinarith
  have hK : (1 + 1 * E) / a ^ 2 ≤ 8 := by
    calc (1 + 1 * E) / a ^ 2 = (1 + E) * (1 / a ^ 2) := by ring
      _ ≤ 2 * 4 := mul_le_mul (by linarith) hinv (by positivity) (by norm_num)
      _ = 8 := by norm_num
  have hR₂le : R₂ ≤ ε / 4 * N := by
    rw [hR₂]
    have h1 : c * ((((1 + 1 * E) / a ^ 2 - 1) * N)) ≤ C * (4 * (ρE + 4 / L)) * N := by
      calc c * ((((1 + 1 * E) / a ^ 2 - 1) * N)) = c * ((1 + 1 * E) / a ^ 2 - 1) * N := by ring
        _ ≤ C * (4 * (ρE + 4 / L)) * N :=
            mul_le_mul_of_nonneg_right (mul_le_mul hc hK1 hK10 (by linarith)) hN0.le
    have h2 : c * ((1 + 1 * E) / a ^ 2 * RN) ≤ 8 * C * RN := by
      calc c * ((1 + 1 * E) / a ^ 2 * RN) = c * ((1 + 1 * E) / a ^ 2) * RN := by ring
        _ ≤ C * 8 * RN := mul_le_mul_of_nonneg_right
            (mul_le_mul hc hK (by positivity) (by linarith)) hRN0
        _ = 8 * C * RN := by ring
    have h3 : C * (4 * (ρE + 4 / L)) * N ≤ ε / 8 * N := by
      have : C * (4 * (ρE + 4 / L)) = 4 * C * (ρE + 4 / L) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hr2 hN0.le
    have h4 : ε / 8 * Nl ≤ ε / 8 * N := mul_le_mul_of_nonneg_left hN (by positivity)
    rw [mul_add]
    linarith
  have hR₂0 : 0 ≤ R₂ := by
    rw [hR₂]
    have : 0 ≤ (1 + 1 * E) / a ^ 2 := by positivity
    positivity
  -- the square-root share
  have hsq : Real.sqrt (c * N + R₂) ≤ Real.sqrt (C + 1) * Real.sqrt N := by
    rw [← Real.sqrt_mul (by linarith)]
    apply Real.sqrt_le_sqrt
    have h1 : ε / 4 * N ≤ N := by
      have : ε / 4 ≤ 1 := by linarith
      calc ε / 4 * N ≤ 1 * N := mul_le_mul_of_nonneg_right this hN0.le
        _ = N := one_mul N
    have h2 : c * N ≤ C * N := mul_le_mul_of_nonneg_right hc hN0.le
    have h3 : (C + 1) * N = C * N + N := by ring
    linarith
  have hsqN : Real.sqrt Nl * Real.sqrt N ≤ N := by
    calc Real.sqrt Nl * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN) (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0.le
  have hBterm : B * (4 + 2 * Real.sqrt (c * N + R₂) + B) ≤ ε / 4 * N := by
    have hs0 : 0 ≤ Real.sqrt (c * N + R₂) := Real.sqrt_nonneg _
    have hρB0 : 0 ≤ ρB := hB0.trans hB
    have hBs : B * Real.sqrt (c * N + R₂) ≤ ρB * (Real.sqrt (C + 1) * Real.sqrt N) :=
      mul_le_mul hB hsq hs0 hρB0
    have hBB : B * B ≤ ρB := by
      calc B * B ≤ ρB * 1 := mul_le_mul hB (hB.trans hρB1) hB0 hρB0
        _ = ρB := mul_one _
    have h3 : 2 * ρB * Real.sqrt (C + 1) * Real.sqrt N ≤ ε / 8 * Real.sqrt Nl * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hr6 (Real.sqrt_nonneg _)
    have h4 : ε / 8 * Real.sqrt Nl * Real.sqrt N ≤ ε / 8 * N := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsqN (by positivity)
    have h5 : 5 * ρB ≤ ε / 8 * N := hr5.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have e : B * (4 + 2 * Real.sqrt (c * N + R₂) + B)
        = 4 * B + 2 * (B * Real.sqrt (c * N + R₂)) + B * B := by ring
    have e2 : 2 * (ρB * (Real.sqrt (C + 1) * Real.sqrt N))
        = 2 * ρB * Real.sqrt (C + 1) * Real.sqrt N := by ring
    rw [e]
    linarith
  have h6 : ε / 8 * Nl ≤ ε / 8 * N := mul_le_mul_of_nonneg_left hN (by positivity)
  linarith

end RHTower
