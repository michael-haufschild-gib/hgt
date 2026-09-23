import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The polynomial coherence horizon

Two ridge normalizations and one triangle inequality give the horizon.  Both block energies are at
least the ridge mass times the squared coefficient norm, so a Hilbert–Schmidt bound on the raw
cross block divides down to a bound on the *normalized* correlation with the extra factor `1/r`.
Subtracting that vanishing far contribution from a near-maximal total pairing leaves the collar
pairing near maximal, and comparing the collar pairing with the cross-capacity bound turns it into
a coefficient-mass floor of order `r/log²`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(447)`: the ridge-normalized cross bound -/

/-- **`(447)`: a Hilbert–Schmidt bound on the raw cross block divides down to the normalized
correlation with the extra factor `1/r`.** -/
theorem normalized_cross_le {cross hs xn yn Lq Dq r : ℝ} (hr : 0 < r)
    (hxn : 0 ≤ xn) (hyn : 0 ≤ yn) (hhs : 0 ≤ hs)
    (hL : r * xn ^ (2 : ℕ) ≤ Lq) (hD : r * yn ^ (2 : ℕ) ≤ Dq)
    (hcross : cross ≤ hs * (xn * yn)) :
    cross ≤ hs / r * Real.sqrt (Lq * Dq) := by
  have hprod : (r * xn ^ (2 : ℕ)) * (r * yn ^ (2 : ℕ)) ≤ Lq * Dq := by
    have h1 : (0 : ℝ) ≤ r * xn ^ (2 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ r * yn ^ (2 : ℕ) := by positivity
    exact mul_le_mul hL hD h2 (le_trans h1 hL)
  have heq : (r * xn ^ (2 : ℕ)) * (r * yn ^ (2 : ℕ)) = (r * (xn * yn)) ^ (2 : ℕ) := by ring
  have hsqrt : r * (xn * yn) ≤ Real.sqrt (Lq * Dq) := by
    calc r * (xn * yn) = Real.sqrt ((r * (xn * yn)) ^ (2 : ℕ)) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Lq * Dq) := Real.sqrt_le_sqrt (by rw [← heq]; exact hprod)
  have hfac : hs / r * (r * (xn * yn)) = hs * (xn * yn) := by
    field_simp
  calc cross ≤ hs * (xn * yn) := hcross
    _ = hs / r * (r * (xn * yn)) := hfac.symm
    _ ≤ hs / r * Real.sqrt (Lq * Dq) := by
        exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-! ## `(448)`: the collar pairing stays near maximal -/

/-- **`(448)`: subtracting a vanishing far contribution from a near-maximal total.** -/
theorem near_max_after_subtracting {tot far near θ δ : ℝ} (hsplit : tot = near + far)
    (htot : θ ≤ tot) (hfar : |far| ≤ δ) : θ - δ ≤ near := by
  have hf : far ≤ δ := le_trans (le_abs_self far) hfar
  linarith [hsplit ▸ htot]

/-! ## `(449)`: the collar coefficient-mass floor -/

/-- **`(449)`: comparing the collar pairing with the capacity bound gives a mass floor.** -/
theorem collar_mass_floor {θ C r ratio : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hcomp : θ ≤ C / r * ratio) : θ * r / C ≤ ratio := by
  have hmul : θ * (r / C) ≤ (C / r * ratio) * (r / C) :=
    mul_le_mul_of_nonneg_right hcomp (by positivity)
  have hsimp : (C / r * ratio) * (r / C) = ratio := by
    field_simp
  rw [hsimp] at hmul
  calc θ * r / C = θ * (r / C) := by ring
    _ ≤ ratio := hmul

end GaloisForLFunctions.RHTower
