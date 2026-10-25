import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeBandIsTheQuasiRiemannHypothesis

/-!
# A zero-free strip gives the balanced prime power saving

`ψ(N) - N ≪ N^{Θ+ε}` bounds the long-window partial sums of the centred prime window, and the
archimedean law turns them into `|Λ_d((Λ - 1)𝟙_{(Q,2Q]})| ≪ (d²/Q) Q^{-(1-Θ)/8}` on the band
`|log d - log Q| ≤ ((1-Θ)/8) log Q` (`centredPrimeBandPowerSaving_of_lt_one`). With the converse,
the balanced prime statistic is the quasi-Riemann hypothesis (`centredPrimeBandPowerSaving_iff`).
-/

open Finset Filter Topology ArithmeticFunction RHTower
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- `ψ(m) - m` in Mathlib's real form is the corpus remainder. -/
theorem chebyshev_psi_natCast_sub_eq (m : ℕ) :
    Chebyshev.psi (m : ℝ) - m = psiRemainder m := by
  rw [psiRemainder, chebyshevPsi, Chebyshev.psi, Nat.floor_natCast,
    ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- The harmonic tail of the prime window: at most `((1 + 2/ε₀)/6) D² q^{-1-ε₀}` when
`T ≤ (1 + log 2q)/q`. -/
theorem band_third_layer_le_log {q D T ε₀ : ℝ} (hq1 : 1 ≤ q) (hD1 : 1 ≤ D) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ ≤ 1 / 2) (hT0 : 0 ≤ T) (hT : T ≤ (1 + Real.log (2 * q)) / q) :
    (D ^ 2 - 1) / (12 * q) * T ≤ (1 + 2 / ε₀) / 6 * (D ^ 2 * q ^ (-1 - ε₀)) := by
  have hq0 : 0 < q := by linarith
  have hL : 1 + Real.log (2 * q) ≤ (1 + 2 / ε₀) * (2 * q ^ (ε₀ / 2)) := by
    have h := one_add_log_le_rpow (by linarith : (1 : ℝ) ≤ 2 * q) (by positivity : 0 < ε₀ / 2)
    rw [show 1 / (ε₀ / 2) = 2 / ε₀ by field_simp, Real.mul_rpow (by norm_num) hq0.le] at h
    have h2 : (2 : ℝ) ^ (ε₀ / 2) ≤ 2 := by
      calc (2 : ℝ) ^ (ε₀ / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    calc 1 + Real.log (2 * q) ≤ (1 + 2 / ε₀) * ((2 : ℝ) ^ (ε₀ / 2) * q ^ (ε₀ / 2)) := h
      _ ≤ (1 + 2 / ε₀) * (2 * q ^ (ε₀ / 2)) := by gcongr
  have h1 : (D ^ 2 - 1) / (12 * q) * T ≤ D ^ 2 / (12 * q) * ((1 + 2 / ε₀) * (2 * q ^ (ε₀ / 2)) / q) :=
    mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity))
      (hT.trans (div_le_div_of_nonneg_right hL hq0.le)) hT0 (by positivity)
  refine h1.trans ?_
  have e : D ^ 2 / (12 * q) * ((1 + 2 / ε₀) * (2 * q ^ (ε₀ / 2)) / q) =
      (1 + 2 / ε₀) / 6 * (D ^ 2 * q ^ (ε₀ / 2 - 2)) := by
    rw [Real.rpow_sub hq0, Real.rpow_two]; field_simp; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

/-- **A zero-free strip gives the balanced prime power saving.** -/
theorem centredPrimeBandPowerSaving_of_lt_one (hΘ : zetaZeroAbscissa < 1) :
    CentredPrimeBandPowerSaving := by
  set Θ := zetaZeroAbscissa
  have hΘ0 : (1 / 2 : ℝ) ≤ Θ := half_le_zetaZeroAbscissa
  set ε₀ : ℝ := (1 - Θ) / 8 with hε₀
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; linarith
  have hε₀1 : ε₀ ≤ 1 / 16 := by rw [hε₀]; linarith
  obtain ⟨C₀, hC₀, hR⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε₀ hε₀0
  set γ := Θ + ε₀ with hγdef
  have hγ : γ = 1 - 7 * ε₀ := by rw [hγdef, hε₀]; ring
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ ≤ 1 := by rw [hγ]; linarith
  refine ⟨ε₀, ε₀, Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 +
    Real.pi ^ 2 / 4 * C₀ + (1 + 2 / ε₀) / 6, hε₀0, hε₀0, fun Q d hQ hlo hhi => ?_⟩
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ Q := by linarith
  have hq0 : (0 : ℝ) < Q := by linarith
  have hD1 : (1 : ℝ) ≤ d := le_trans (Real.one_le_rpow hq1 (by linarith)) hlo
  have hd0 : 0 < d := by exact_mod_cast (show (0 : ℝ) < d by linarith)
  -- the long-window partial sums of the window
  have hA : ∀ x ≤ Q, |∑ i ∈ range x, centredPrimeBlock Q (Q + 1 + i)| ≤
      2 * C₀ * (2 * (Q : ℝ)) ^ γ := by
    intro x hx
    rw [sum_range_centredPrimeBlock Q x hx, chebyshev_psi_natCast_sub_eq,
      chebyshev_psi_natCast_sub_eq]
    have hxR : (x : ℝ) ≤ Q := by exact_mod_cast hx
    have h1 : |psiRemainder (Q + x)| ≤ C₀ * (2 * (Q : ℝ)) ^ γ :=
      (hR _ (by omega)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        (by push_cast; linarith) hγ0) hC₀)
    have h2 : |psiRemainder Q| ≤ C₀ * (2 * (Q : ℝ)) ^ γ :=
      (hR _ (by omega)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        (by linarith) hγ0) hC₀)
    calc |psiRemainder (Q + x) - psiRemainder Q| ≤ |psiRemainder (Q + x)| + |psiRemainder Q| :=
          abs_sub _ _
      _ ≤ 2 * C₀ * (2 * (Q : ℝ)) ^ γ := by linarith
  have hsupp : ∀ n, centredPrimeBlock Q n ≠ 0 → Q < n ∧ n ≤ 2 * Q :=
    fun n h => centredPrimeBlock_ne_zero_imp h
  have hlaw := abs_kernelStatisticAll_le_archimedean hd0 le_rfl hsupp hA (by omega : 1 ≤ Q)
  refine hlaw.trans ?_
  have hAle : 2 * C₀ * (2 * (Q : ℝ)) ^ γ ≤ 6 * C₀ * (Q : ℝ) ^ γ := by
    rw [Real.mul_rpow (by norm_num) hq0.le]
    have h2 : (2 : ℝ) ^ γ ≤ 2 := by
      calc (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1
        _ = 2 := Real.rpow_one 2
    have : 0 ≤ C₀ * (Q : ℝ) ^ γ := by positivity
    nlinarith
  have hT : ∑ n ∈ Icc 1 (2 * Q), |centredPrimeBlock Q n| / (n : ℝ) ^ 2 ≤
      (1 + Real.log (2 * (Q : ℝ))) / (Q : ℝ) := by
    have h := sum_Icc_abs_window_div_pow_le (N := 2 * Q) (A := 1 + Real.log (2 * (Q : ℝ)))
      (by omega : 1 ≤ Q) hsupp
      (fun n => (abs_centredPrimeBlock_le (by omega) n).trans (by linarith)) 2
    rwa [show (1 + Real.log (2 * (Q : ℝ))) * (Q : ℝ) / (Q : ℝ) ^ 2 =
      (1 + Real.log (2 * (Q : ℝ))) / (Q : ℝ) by field_simp] at h
  have hT0 : 0 ≤ ∑ n ∈ Icc 1 (2 * Q), |centredPrimeBlock Q n| / (n : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  have h1 := band_first_layer_le hq1 hD1 hlo hhi hε₀0 hε₀1 hγ hC₀ (by positivity) hAle
    (rootHarmonicSum_nonneg d) (rootHarmonicSum_le d)
  have h2 := band_second_layer_le hq1 hD1 hhi hε₀0 hγ hC₀ (by positivity) hAle
  have h3 := band_third_layer_le_log hq1 hD1 hε₀0 (by linarith) hT0 hT
  have hP : ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-ε₀) = (d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀) := by
    rw [show (-1 - ε₀ : ℝ) = -1 + -ε₀ by ring, Real.rpow_add hq0, Real.rpow_neg_one]; ring
  rw [mul_assoc (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 + Real.pi ^ 2 / 4 * C₀ +
    (1 + 2 / ε₀) / 6), hP]
  have e : (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 + Real.pi ^ 2 / 4 * C₀ +
      (1 + 2 / ε₀) / 6) * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) =
      (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2) * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) +
        Real.pi ^ 2 / 4 * C₀ * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) +
        (1 + 2 / ε₀) / 6 * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) := by ring
  rw [e]
  linarith

/-- **The balanced prime statistic is the quasi-Riemann hypothesis.** A power saving for the
statistic of the centred prime windows on some neighbourhood of the diagonal holds if and only if
`Θ < 1`. -/
theorem centredPrimeBandPowerSaving_iff : CentredPrimeBandPowerSaving ↔ zetaZeroAbscissa < 1 :=
  ⟨zetaZeroAbscissa_lt_one_of_centredPrimeBandPowerSaving, centredPrimeBandPowerSaving_of_lt_one⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
