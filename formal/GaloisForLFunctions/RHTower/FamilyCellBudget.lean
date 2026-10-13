import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Frobenius share of the family error budget

A real-variable lemma.  With `m` nontrivial characters (`φ(q) = m + 1`), the summed Frobenius bound

`Fr = (1+η)(m+1)(c N_m L² + K M) + m(1+1/η) P`,

normalised by `(aL)²`, is at most `c N + (ε/8) m N_low` as soon as `1/a²`, `η` and `1/m` are at most
`1 + δ`, `δ`, `δ`, the Riemann–von Mangoldt error `R_N = N_m − N_low` is small, and the majorants
`K M` and `(1 + 1/η) P` are small against `N_low L²` (`family_phi_budget`).  The main term uses the identity
`(TL/2π)(ℓ² + L²/3) = (ℓ/L + L/3ℓ)(Tℓ/2π) L²` (`main_frob_eq`).
-/

open Real

namespace RHTower

/-- `(TL/2π)(ℓ² + L²/3) = (ℓ/L + L/(3ℓ)) (Tℓ/2π) L²`. -/
theorem main_frob_eq {T L ell : ℝ} (hL : 0 < L) (hell : 0 < ell) :
    T * L / (2 * π) * (ell ^ 2 + L ^ 2 / 3) = (ell / L + L / (3 * ell)) * (T / (2 * π) * ell) * L ^ 2 := by
  field_simp

/-- `(1+δ)³ ≤ 1 + 7δ` for `0 ≤ δ ≤ 1`, in the form used below. -/
theorem three_factor_le {x y z δ : ℝ} (hx : x ≤ 1 + δ) (hy0 : 0 ≤ y) (hy : y ≤ 1 + δ)
    (hz0 : 0 ≤ z) (hz : z ≤ 1 + δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : x * y * z ≤ 1 + 7 * δ := by
  have h1 : x * y ≤ (1 + δ) * (1 + δ) := mul_le_mul hx hy hy0 (by linarith)
  have h2 : x * y * z ≤ (1 + δ) * (1 + δ) * (1 + δ) := mul_le_mul h1 hz hz0 (by positivity)
  have hd2 : δ * δ ≤ δ := by nlinarith
  have hd3 : δ * δ * δ ≤ δ := by nlinarith
  linarith

/-- **The Frobenius share.** -/
theorem family_phi_budget {a L η m c C Nm Nl RN K Mj P δ ε N : ℝ}
    (ha : 1 / 2 ≤ a) (haδ : 1 / a ^ 2 ≤ 1 + δ) (hη0 : 0 < η) (hη : η ≤ δ) (hm : 1 ≤ m) (hmδ : 1 / m ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc0 : 0 ≤ c) (hc : c ≤ C) (hNl : Nm - RN ≤ Nl) (hNm : Nm ≤ 2 * Nl)
    (hRN0 : 0 ≤ RN) (hRN : C * RN ≤ ε / 64 * Nl) (hδC : 14 * δ * C ≤ ε / 32) (hL : 0 < L)
    (hK : 0 ≤ K) (hMj0 : 0 ≤ Mj) (hP0 : 0 ≤ P) (hMj : 16 * (K * Mj) ≤ ε / 64 * Nl * L ^ 2)
    (hP : 4 * ((1 + 1 / η) * P) ≤ ε / 64 * Nl * L ^ 2) (hN : m * Nl ≤ N) (hNl0 : 0 ≤ Nl)
    (hNm0 : 0 ≤ Nm) (hε : 0 ≤ ε) :
    ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * L ^ 2 + K * Mj)) + m * ((1 + 1 / η) * P))
      ≤ c * N + ε / 8 * (m * Nl) := by
  have ha0 : 0 < a := by linarith
  have hm0 : 0 < m := by linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have hinv : ((a * L)⁻¹) ^ 2 = 1 / a ^ 2 * (1 / L ^ 2) := by field_simp
  have ha4 : 1 / a ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hia0 : 0 ≤ 1 / a ^ 2 := by positivity
  -- the main term
  have hmain : 1 / a ^ 2 * (1 + η) * (1 + 1 / m) ≤ 1 + 7 * δ :=
    three_factor_le haδ (by linarith) (by linarith) (by positivity) (by linarith) hδ0 hδ1
  have hT1 : ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * L ^ 2)))
      = (1 / a ^ 2 * (1 + η) * (1 + 1 / m)) * (c * m * Nm) := by
    rw [hinv]; field_simp
  have hcmN : 0 ≤ c * m * Nm := by positivity
  have hT1le : ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * L ^ 2)))
      ≤ (1 + 7 * δ) * (c * m * Nm) := by
    rw [hT1]; exact mul_le_mul_of_nonneg_right hmain hcmN
  have hcN : c * (m * Nl) ≤ c * N := mul_le_mul_of_nonneg_left hN hc0
  have hrest1 : (1 + 7 * δ) * (c * m * Nm) ≤ c * (m * Nl) + ε / 16 * (m * Nl) := by
    have h1 : c * Nm ≤ c * Nl + C * RN := by
      have : c * Nm ≤ c * (Nl + RN) := mul_le_mul_of_nonneg_left (by linarith) hc0
      have h2 : c * RN ≤ C * RN := mul_le_mul_of_nonneg_right hc hRN0
      linarith
    have h3 : 7 * δ * (c * Nm) ≤ ε / 32 * Nl := by
      have h4 : c * Nm ≤ C * (2 * Nl) := mul_le_mul hc hNm hNm0 (by linarith)
      have h5 : 7 * δ * (c * Nm) ≤ 7 * δ * (C * (2 * Nl)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : 7 * δ * (C * (2 * Nl)) = 14 * δ * C * Nl := by ring
      have h7 : 14 * δ * C * Nl ≤ ε / 32 * Nl := mul_le_mul_of_nonneg_right hδC hNl0
      linarith
    have e : (1 + 7 * δ) * (c * m * Nm) = m * (c * Nm + 7 * δ * (c * Nm)) := by ring
    rw [e]
    have hεN : 0 ≤ ε * Nl := mul_nonneg hε hNl0
    have h8 : c * Nm + 7 * δ * (c * Nm) ≤ c * Nl + ε / 16 * Nl := by linarith
    calc m * (c * Nm + 7 * δ * (c * Nm)) ≤ m * (c * Nl + ε / 16 * Nl) :=
          mul_le_mul_of_nonneg_left h8 hm0.le
      _ = c * (m * Nl) + ε / 16 * (m * Nl) := by ring
  -- the majorant term
  have hT2 : ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (K * Mj))) ≤ ε / 64 * (m * Nl) := by
    have h1 : ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (K * Mj)))
        = 1 / a ^ 2 * (1 + η) * ((m + 1) / m) * (m * (K * Mj) / L ^ 2) := by
      rw [hinv]; field_simp
    have h2 : 1 / a ^ 2 * (1 + η) * ((m + 1) / m) ≤ 4 * 2 * 2 := by
      have hm1 : (m + 1) / m ≤ 2 := by rw [div_le_iff₀ hm0]; linarith
      have hη2 : 1 + η ≤ 2 := by linarith
      apply mul_le_mul _ hm1 (by positivity) (by norm_num)
      exact mul_le_mul ha4 hη2 (by linarith) (by norm_num)
    have h3 : 0 ≤ m * (K * Mj) / L ^ 2 := by positivity
    rw [h1]
    calc 1 / a ^ 2 * (1 + η) * ((m + 1) / m) * (m * (K * Mj) / L ^ 2)
        ≤ 4 * 2 * 2 * (m * (K * Mj) / L ^ 2) := mul_le_mul_of_nonneg_right h2 h3
      _ = m * (16 * (K * Mj) / L ^ 2) := by ring
      _ ≤ m * (ε / 64 * Nl) := by
          apply mul_le_mul_of_nonneg_left _ hm0.le
          rw [div_le_iff₀ hL2]; exact hMj
      _ = ε / 64 * (m * Nl) := by ring
  -- the parity term
  have hT3 : ((a * L)⁻¹) ^ 2 * (m * ((1 + 1 / η) * P)) ≤ ε / 64 * (m * Nl) := by
    have h1 : ((a * L)⁻¹) ^ 2 * (m * ((1 + 1 / η) * P)) = 1 / a ^ 2 * (m * ((1 + 1 / η) * P) / L ^ 2) := by
      rw [hinv]; ring
    have h3 : 0 ≤ m * ((1 + 1 / η) * P) / L ^ 2 := by positivity
    rw [h1]
    calc 1 / a ^ 2 * (m * ((1 + 1 / η) * P) / L ^ 2) ≤ 4 * (m * ((1 + 1 / η) * P) / L ^ 2) :=
          mul_le_mul_of_nonneg_right ha4 h3
      _ = m * (4 * ((1 + 1 / η) * P) / L ^ 2) := by ring
      _ ≤ m * (ε / 64 * Nl) := by
          apply mul_le_mul_of_nonneg_left _ hm0.le
          rw [div_le_iff₀ hL2]; exact hP
      _ = ε / 64 * (m * Nl) := by ring
  have e : ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * L ^ 2 + K * Mj)) + m * ((1 + 1 / η) * P))
      = ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * L ^ 2)))
        + ((a * L)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (K * Mj)))
        + ((a * L)⁻¹) ^ 2 * (m * ((1 + 1 / η) * P)) := by ring
  rw [e]
  have hmNl : 0 ≤ m * Nl := by positivity
  have hεmN : 0 ≤ ε * (m * Nl) := mul_nonneg hε hmNl
  linarith

end RHTower
