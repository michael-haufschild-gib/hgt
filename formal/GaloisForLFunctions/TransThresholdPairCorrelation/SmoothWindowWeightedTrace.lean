import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowGridComparison
import GaloisForLFunctions.RHTower.ZetaTraceWide
import GaloisForLFunctions.RHTower.ZetaWeightedTrace

/-!
# The Weighted Trace of a Smooth Height Weight

For grid weights `0 ≤ W_k ≤ 1` the weighted trace `Σ_{k<d} W_k G_kk` of the Gram matrix of `ζ`
differs from the unweighted one by `Σ_k (1 − W_k) G_kk`. The archimedean and pole parts of the
diagonal are bounded pointwise, so they cost at most their size times the number of grid points
where `W_k < 1` (the collar of the weight). The prime part is a cosine polynomial
`−2 Σ_n a_n A_φ(y_n) Σ_k (1 − W_k) cos(τ_k y_n)`; for weights sampled from an `ℓ`-Lipschitz
profile, summation by parts against the telescoping identity
`2 sin(θ/2) Σ_{j<K} cos(φ + jθ) = sin(φ + (K − ½)θ) − sin(φ − θ/2)` gives
`|Σ_k c_k cos(τ_k y)| ≤ (|c_{d−1}| + Σ_k |c_{k+1} − c_k|)/|sin(hy/2)|`, and Jordan's inequality
`|sin(πy/L)| ≥ 2 min(y, L − y)/L` makes every frequency away from the alias `y = L` cheap
(`abs_sum_mul_cos_le_abel`, `abs_weighted_P_part_le_lipschitz`). The result is the collar form of
the trace (`sum_weighted_trace_ge`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide Zeta23.ThmE RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Summation by parts for trigonometric sums -/

/-- **Telescoping.** `2 sin(θ/2) Σ_{j<K} cos(φ + jθ) = sin(φ + (K − ½)θ) − sin(φ − θ/2)`. -/
theorem two_sin_mul_sum_cos (φ θ : ℝ) (K : ℕ) :
    2 * Real.sin (θ / 2) * ∑ j ∈ Finset.range K, Real.cos (φ + j * θ)
      = Real.sin (φ + (K - 1 / 2) * θ) - Real.sin (φ - θ / 2) := by
  have hstep : ∀ j : ℕ, 2 * Real.sin (θ / 2) * Real.cos (φ + j * θ)
      = Real.sin (φ + ((j + 1 : ℕ) - 1 / 2) * θ) - Real.sin (φ + ((j : ℕ) - 1 / 2) * θ) := by
    intro j
    push_cast
    rw [show φ + ((j : ℝ) + 1 - 1 / 2) * θ = (φ + j * θ) + θ / 2 by ring,
      show φ + ((j : ℝ) - 1 / 2) * θ = (φ + j * θ) - θ / 2 by ring, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => hstep j,
    Finset.sum_range_sub (fun j : ℕ => Real.sin (φ + ((j : ℕ) - 1 / 2) * θ)) K]
  push_cast
  ring_nf

/-- `|Σ_{j<K} cos(φ + jθ)| ≤ 1/|sin(θ/2)|`. -/
theorem abs_sum_cos_le {φ θ : ℝ} (hθ : Real.sin (θ / 2) ≠ 0) (K : ℕ) :
    |∑ j ∈ Finset.range K, Real.cos (φ + j * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h := two_sin_mul_sum_cos φ θ K
  have hs : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hθ
  have hs1 := Real.abs_sin_le_one (φ + ((K : ℝ) - 1 / 2) * θ)
  have hs2 := Real.abs_sin_le_one (φ - θ / 2)
  have hb : |Real.sin (φ + ((K : ℝ) - 1 / 2) * θ) - Real.sin (φ - θ / 2)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  rw [← h, abs_mul, abs_mul, abs_two] at hb
  rw [le_div_iff₀ hs]
  nlinarith [abs_nonneg (∑ j ∈ Finset.range K, Real.cos (φ + j * θ))]

/-- **Summation by parts.** For any coefficients `c_k`:
`|Σ_{k<d} c_k cos(φ + kθ)| ≤ (|c_{d−1}| + Σ_{k<d−1} |c_{k+1} − c_k|)/|sin(θ/2)|`. -/
theorem abs_sum_mul_cos_le_abel {φ θ : ℝ} (hθ : Real.sin (θ / 2) ≠ 0) (c : ℕ → ℝ) (d : ℕ) :
    |∑ k ∈ Finset.range d, c k * Real.cos (φ + k * θ)|
      ≤ (|c (d - 1)| + ∑ k ∈ Finset.range (d - 1), |c (k + 1) - c k|) / |Real.sin (θ / 2)| := by
  have hs : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hθ
  have hby := Finset.sum_range_by_parts c (fun k => Real.cos (φ + k * θ)) d
  simp only [smul_eq_mul] at hby
  rw [hby]
  have hG := abs_sum_cos_le (φ := φ) hθ
  refine (abs_sub _ _).trans ?_
  rw [add_div, Finset.sum_div]
  refine add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_))
  · rw [abs_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (hG d) (abs_nonneg _)
  · rw [abs_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (hG (k + 1)) (abs_nonneg _)

/-- **Jordan's inequality on the alias interval.** For `0 ≤ y ≤ L`:
`|sin(πy/L)| ≥ 2 min(y, L − y)/L`. -/
theorem two_min_div_le_abs_sin {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    2 * min y (L - y) / L ≤ |Real.sin (π * y / L)| := by
  have hπ := Real.pi_pos
  rcases le_total y (L / 2) with h | h
  · have hx0 : 0 ≤ π * y / L := by positivity
    have hx1 : π * y / L ≤ π / 2 := by
      rw [div_le_iff₀ hL]; nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hm : min y (L - y) ≤ y := min_le_left _ _
    have e : 2 / π * (π * y / L) = 2 * y / L := by field_simp
    have hpos : 0 ≤ 2 * y / L := by positivity
    rw [abs_of_nonneg (by linarith)]
    calc 2 * min y (L - y) / L ≤ 2 * y / L := by gcongr
      _ ≤ _ := by linarith
  · have hx0 : 0 ≤ π * (L - y) / L := by
      have : 0 ≤ L - y := by linarith
      positivity
    have hx1 : π * (L - y) / L ≤ π / 2 := by
      rw [div_le_iff₀ hL]; nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hm : min y (L - y) ≤ L - y := min_le_right _ _
    have e : 2 / π * (π * (L - y) / L) = 2 * (L - y) / L := by field_simp
    have hpos : 0 ≤ 2 * (L - y) / L := by
      have : 0 ≤ L - y := by linarith
      positivity
    have hsym : Real.sin (π * y / L) = Real.sin (π * (L - y) / L) := by
      rw [show π * (L - y) / L = π - π * y / L by field_simp, Real.sin_pi_sub]
    rw [hsym, abs_of_nonneg (by linarith)]
    calc 2 * min y (L - y) / L ≤ 2 * (L - y) / L := by gcongr
      _ ≤ _ := by linarith

/-! ## 2. The prime part of the diagonal at any bandwidth -/

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- The prime part of `G_kk` at one grid point, at any bandwidth:
`∫ φ̂(r)² P_X(t + r) dr = −2 Σ_n a_n A_φ(y_n) cos(t y_n)`. -/
theorem P_part_eq_W (hF : LocalHypsCoreW cϱ p F) (t : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)
      = -2 * ∑ n ∈ primeRange p.X, acoef n * F.Aphi (ycoef n) * Real.cos (t * ycoef n) := by
  have h1 : (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r))
      = fun r => ∑ n ∈ primeRange p.X,
          (-(1 / Real.pi) * acoef n) * (F.phiHat r ^ 2 * Real.cos ((t + r) * ycoef n)) := by
    funext r
    rw [PX_eq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1, integral_finsetSum _ (fun n _ =>
    ((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_cos_le_one _)).const_mul _))]
  simp_rw [integral_const_mul, integral_phiHat_sq_mul_cos_shift_core hF]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp

/-- **The weighted prime part for Lipschitz weights.** Let `c_k` satisfy `|c_k| ≤ 1`,
`|c_{k+1} − c_k| ≤ ℓh` and `0 < B ≤ log 2 ≤ L − B`. Then
`|Σ_k c_k G^P_kk| ≤ 2 (L · (1 + ℓT) L/(2B) · Σ a_n + B d Σ_{y_n > L − B} a_n)`. -/
theorem abs_weighted_P_part_le_lipschitz (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T)
    {c : ℕ → ℝ} {ℓ B : ℝ} (hℓ : 0 ≤ ℓ) (hB : 0 < B) (hB2 : B ≤ Real.log 2)
    (hc1 : ∀ k, |c k| ≤ 1) (hcL : ∀ k, |c (k + 1) - c k| ≤ ℓ * p.h) :
    |∑ k ∈ Finset.range p.d, c k * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ 2 * (p.L * ((1 + ℓ * p.T) * p.L / (2 * B)) * ∑ n ∈ primeRange p.X, acoef n
        + B * p.d * ∑ n ∈ (primeRange p.X).filter (fun n => p.L - B < ycoef n), acoef n) := by
  have hL := hF.L_pos
  have hh := h_pos hF
  set E := (1 + ℓ * p.T) * p.L / (2 * B) with hE
  have hE0 : 0 ≤ E := by positivity
  -- the cosine sums on the band `log 2 ≤ y ≤ L − B`
  have hcos : ∀ n ∈ primeRange p.X, Real.log 2 ≤ ycoef n → ycoef n ≤ p.L - B →
      |∑ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * ycoef n)| ≤ E := by
    intro n _ hy2 hyL
    set y := ycoef n
    have hy0 : 0 < y := lt_of_lt_of_le (Real.log_pos one_lt_two) hy2
    have hmin : B ≤ min y (p.L - y) := le_min (hB2.trans hy2) (by linarith)
    have hsin : 2 * B / p.L ≤ |Real.sin (π * y / p.L)| := by
      refine le_trans ?_ (two_min_div_le_abs_sin hL hy0.le (by linarith))
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    have hsin0 : 0 < |Real.sin (π * y / p.L)| := lt_of_lt_of_le (by positivity) hsin
    have hθ : (p.h * y) / 2 = π * y / p.L := by unfold Setting.h; field_simp
    have hform : ∀ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * y)
        = c k * Real.cos (p.T * y + k * (p.h * y)) := fun k _ => by
      rw [show p.tau k = p.T + k * p.h by unfold Setting.tau; push_cast; ring]; ring_nf
    rw [Finset.sum_congr rfl hform]
    have hab := abs_sum_mul_cos_le_abel (φ := p.T * y) (θ := p.h * y)
      (by rw [hθ]; exact abs_pos.mp hsin0) c p.d
    rw [hθ] at hab
    refine hab.trans ?_
    have hvar : |c (p.d - 1)| + ∑ k ∈ Finset.range (p.d - 1), |c (k + 1) - c k| ≤ 1 + ℓ * p.T := by
      have h1 := hc1 (p.d - 1)
      have h2 : ∑ k ∈ Finset.range (p.d - 1), |c (k + 1) - c k| ≤ (p.d - 1 : ℕ) * (ℓ * p.h) := by
        calc ∑ k ∈ Finset.range (p.d - 1), |c (k + 1) - c k|
            ≤ ∑ _k ∈ Finset.range (p.d - 1), ℓ * p.h := Finset.sum_le_sum fun k _ => hcL k
          _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h3 : ((p.d - 1 : ℕ) : ℝ) * (ℓ * p.h) ≤ ℓ * p.T := by
        have hd : (p.d : ℝ) * p.h ≤ p.T := by
          unfold Setting.d Setting.h
          have := Nat.floor_le (show 0 ≤ p.L * p.T / (2 * π) by positivity)
          calc (⌊p.L * p.T / (2 * π)⌋₊ : ℝ) * (2 * π / p.L)
              ≤ p.L * p.T / (2 * π) * (2 * π / p.L) := mul_le_mul_of_nonneg_right this (by positivity)
            _ = p.T := by field_simp
        have hd1 : ((p.d - 1 : ℕ) : ℝ) ≤ p.d := by exact_mod_cast Nat.sub_le _ _
        nlinarith [mul_le_mul_of_nonneg_right hd1 (mul_nonneg hℓ hh.le)]
      linarith
    calc (|c (p.d - 1)| + ∑ k ∈ Finset.range (p.d - 1), |c (k + 1) - c k|) / |Real.sin (π * y / p.L)|
        ≤ (1 + ℓ * p.T) / (2 * B / p.L) :=
          div_le_div₀ (by positivity) hvar (by positivity) hsin
      _ = E := by rw [hE]; field_simp
  -- the prime expansion, as in the `λ ≤ 1` case
  have hexp : ∑ k ∈ Finset.range p.d, c k * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)
      = -2 * ∑ n ∈ primeRange p.X, acoef n * F.Aphi (ycoef n)
          * ∑ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * ycoef n) := by
    simp_rw [P_part_eq_W hF]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, abs_mul, abs_neg, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hsplit : p.L * E * ∑ n ∈ primeRange p.X, acoef n
      + B * p.d * ∑ n ∈ (primeRange p.X).filter (fun n => p.L - B < ycoef n), acoef n
      = ∑ n ∈ primeRange p.X, (p.L * E * acoef n
          + if p.L - B < ycoef n then B * p.d * acoef n else 0) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      ← Finset.mul_sum]
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have ha : 0 ≤ acoef n := acoef_nonneg n
  have hA0 : 0 ≤ F.Aphi (ycoef n) := (hF.g_nonneg _).trans (hF.g_le_Aphi _)
  have htriv : |∑ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * ycoef n)| ≤ p.d := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range p.d, |c k * Real.cos (p.tau k * ycoef n)|
        ≤ ∑ k ∈ Finset.range p.d, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact (mul_le_mul (hc1 k) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans
            (le_of_eq (one_mul 1))
      _ = p.d := by simp
  have hLE : 0 ≤ p.L * E * acoef n := mul_nonneg (mul_nonneg hL.le hE0) ha
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by have := (Finset.mem_Ioc.1 hn).1; omega
    subst hn1
    have h0 : acoef 1 = 0 := by
      simp only [acoef, ArithmeticFunction.vonMangoldt_apply_one, Nat.cast_one, Real.sqrt_one, div_one]
    simp only [h0, zero_mul, abs_zero, mul_zero]
    split_ifs <;> simp
  have hy2 : Real.log 2 ≤ ycoef n := Real.log_le_log two_pos (by exact_mod_cast hn2)
  have hy0 : 0 ≤ ycoef n := le_trans (Real.log_nonneg one_le_two) hy2
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hA0]
  split_ifs with hyL
  · have hAle : F.Aphi (ycoef n) ≤ B := (hF.Aphi_le _).trans (by
      apply max_le _ hB.le; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * ycoef n)|
        ≤ B * p.d := mul_le_mul hAle htriv (abs_nonneg _) hB.le
    have h2 := mul_le_mul_of_nonneg_left h1 ha
    nlinarith
  · have hyL' : ycoef n ≤ p.L - B := le_of_not_gt hyL
    have hAle : F.Aphi (ycoef n) ≤ p.L := (hF.Aphi_le _).trans (by
      apply max_le _ hL.le; rw [abs_of_nonneg hy0]; linarith)
    have h1 : F.Aphi (ycoef n) * |∑ k ∈ Finset.range p.d, c k * Real.cos (p.tau k * ycoef n)|
        ≤ p.L * E := mul_le_mul hAle (hcos n hn hy2 hyL') (abs_nonneg _) hL.le
    have h2 := mul_le_mul_of_nonneg_left h1 ha
    nlinarith

/-! ## 3. The collar form of the weighted trace -/

/-- The archimedean and pole parts of `G_kk` at one grid point, at any bandwidth:
`|G^μ_kk + G^Π_kk| ≤ 2πaL M + K(∫φ̂²|r| + ∫φ̂²r²)/T + (6√X/T) 2πaL + (12√X/T²) ∫φ̂²r²`
when `|μ| ≤ M` on `[T, 2T]`. -/
theorem abs_mu_add_Pi_part_le (hF : LocalHypsCoreW cϱ p F) (hT : 2 ≤ p.T) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq 0 1 (t + r) - muq 0 1 t| ≤ K * (|r| + r ^ 2) / t)
    {M : ℝ} (hM : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ M) {k : ℕ} (hk : k ∈ Finset.range p.d) :
    |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)) + ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)|
      ≤ 2 * π * F.a * p.L * M
        + K * ((∫ r, F.phiHat r ^ 2 * |r|) + ∫ r, F.phiHat r ^ 2 * r ^ 2) / p.T
        + ((6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2) := by
  have hL := hF.L_pos
  have hT0 : 0 < p.T := by linarith
  have hτk := p.tau_mem hL hT0.le hk
  have h2 : 2 ≤ p.tau k := by linarith [hτk.1]
  have hΓq := GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl
  have hμ := muq_part_bound hΓq le_rfl hF hK0 hK h2
  rw [← mu_eq_muq] at hμ
  have hPi := Pi_part_bound_W hF h2
  have ha0 : 0 ≤ F.a := (hF.b_ge_half.trans' (by norm_num)).trans hF.b_le_a
  have hI1 : 0 ≤ ∫ r, F.phiHat r ^ 2 * |r| := integral_nonneg fun r => by positivity
  have hI2 : 0 ≤ ∫ r, F.phiHat r ^ 2 * r ^ 2 := integral_nonneg fun r => by positivity
  have hsX := Real.sqrt_nonneg p.X
  -- `1/τ_k ≤ 1/T`
  have hμ' : |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)) - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)|
      ≤ K * ((∫ r, F.phiHat r ^ 2 * |r|) + ∫ r, F.phiHat r ^ 2 * r ^ 2) / p.T :=
    hμ.trans (div_le_div_of_nonneg_left (by positivity) hT0 hτk.1)
  have hPi' : |∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)|
      ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
        + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2 := by
    refine hPi.trans (add_le_add (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) hT0 hτk.1) (by positivity))
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hT0.le hτk.1 2)) hI2))
  have hmuM : |2 * π * F.a * p.L * Zeta23.mu (p.tau k)| ≤ 2 * π * F.a * p.L * M := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hM _ hτk) (by positivity)
  calc |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)) + ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)|
      = |(2 * π * F.a * p.L * Zeta23.mu (p.tau k)
          + ((∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)) - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)))
          + ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hmuM hμ')) hPi')

/-- **The weighted trace loses only its collar.** For `0 ≤ W_k ≤ 1` with `W_k = 1` on `S`, and
`C` bounding the archimedean and pole parts of every `G_kk`:
`Σ_k W_k G_kk ≥ Σ_k G_kk − #(range d ∖ S)·C − |Σ_k (1 − W_k) G^P_kk|`. -/
theorem sum_weighted_trace_ge (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {W : ℕ → ℝ}
    (hW0 : ∀ k, 0 ≤ W k) (hW1 : ∀ k, W k ≤ 1) (S : Finset ℕ) (hS : ∀ k ∈ S, W k = 1) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ k ∈ Finset.range p.d, |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)| ≤ C) :
    ∑ k ∈ Finset.range p.d, GentryA p F k k - ((Finset.range p.d \ S).card : ℝ) * C
        - |∑ k ∈ Finset.range p.d, (1 - W k) * ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ ∑ k ∈ Finset.range p.d, W k * GentryA p F k k := by
  have hL := hF.L_pos
  set A : ℕ → ℝ := fun k => (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
    + ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r) with hAdef
  set P : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) with hPdef
  have hdiag : ∀ k ∈ Finset.range p.d, GentryA p F k k = A k + P k := by
    intro k hk
    have hτ := p.tau_mem hL hT.le hk
    rw [GentryA_diag_eq_W Zeta23.gammaFacts hF k (by linarith [hτ.1])]
  have hdiff : ∑ k ∈ Finset.range p.d, GentryA p F k k - ∑ k ∈ Finset.range p.d, W k * GentryA p F k k
      = ∑ k ∈ Finset.range p.d, (1 - W k) * A k + ∑ k ∈ Finset.range p.d, (1 - W k) * P k := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hdiag k hk]; ring
  have hA : ∑ k ∈ Finset.range p.d, (1 - W k) * A k ≤ ((Finset.range p.d \ S).card : ℝ) * C := by
    have h1 : ∑ k ∈ Finset.range p.d, (1 - W k) * A k ≤ ∑ k ∈ Finset.range p.d, (1 - W k) * C :=
      Finset.sum_le_sum fun k hk => by
        have h0 : 0 ≤ 1 - W k := by linarith [hW1 k]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC k hk)) h0
    have h2 := sum_one_sub_le_of_bulk (W := W) le_rfl (d := p.d) S (fun k hk => by rw [hS k hk]; simp) hW0
    rw [zero_mul, add_zero] at h2
    rw [← Finset.sum_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hC0)
  have hP := le_abs_self (∑ k ∈ Finset.range p.d, (1 - W k) * P k)
  linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
