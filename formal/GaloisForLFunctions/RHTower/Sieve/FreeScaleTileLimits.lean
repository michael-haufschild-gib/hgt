import GaloisForLFunctions.RHTower.Sieve.FreeScaleTile
import GaloisForLFunctions.RHTower.Sieve.ConstQuotientLimit

/-!
# The asymptotics of the tile family

All the numerical side conditions of one tile are eventual statements in the index `u` of the start
modulus `m = 2^{K₀+1}u`.  They are collected here.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

theorem tendsto_tileM (K₀ : ℕ) : Tendsto (fun u : ℕ => tileM K₀ u) atTop atTop := by
  have h : Tendsto (fun u : ℕ => 2 ^ (K₀ + 1) * u) atTop atTop :=
    Filter.tendsto_atTop_mono (fun u => Nat.le_mul_of_pos_left u (by positivity))
      Filter.tendsto_id
  exact h

theorem tendsto_tileM_cast (K₀ : ℕ) :
    Tendsto (fun u : ℕ => ((tileM K₀ u : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_tileM K₀)

/-- The scale of the base block is the square of the start modulus. -/
theorem freeScale_zero (m : ℕ) : freeScale m 0 = ((m : ℕ) : ℝ) ^ (2 : ℕ) := by
  rw [freeScale, freeStart_zero]

theorem tendsto_tileScale (K₀ : ℕ) :
    Tendsto (fun u : ℕ => freeScale (tileM K₀ u) 0) atTop atTop := by
  have hmul := (tendsto_tileM_cast K₀).atTop_mul_atTop₀ (tendsto_tileM_cast K₀)
  have h : Tendsto (fun u : ℕ => ((tileM K₀ u : ℕ) : ℝ) ^ (2 : ℕ)) atTop atTop :=
    hmul.congr fun u => by ring
  exact h.congr fun u => (freeScale_zero _).symm

/-- **The scale of the `k`-th block is the base scale divided by `4^k`.** -/
theorem freeScale_tile_div {K₀ u k : ℕ} (hk : k ≤ K₀ + 1) :
    freeScale (tileM K₀ u) k = freeScale (tileM K₀ u) 0 / (4 : ℝ) ^ k := by
  rw [freeScale, freeScale, tileM, freeStart_pow_mul hk, freeStart_pow_mul (by omega)]
  have hsplit : (2 : ℕ) ^ (K₀ + 1 - 0) = 2 ^ k * 2 ^ (K₀ + 1 - k) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (2 : ℕ) := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    congr 1
    ring
  rw [h4]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  field_simp
  try ring

/-- **The window at every block is eventually at least half the base window.** -/
theorem eventually_tile_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ k : ℕ) (hk : k ≤ K₀ + 1) :
    ∀ᶠ u : ℕ in atTop, tileC β K₀ u / 2 ≤ cardLength β (freeScale (tileM K₀ u) k) := by
  have hc1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hev := eventually_half_cardLength_le_dilated (β := β) (c := (4 : ℝ) ^ k) hβ0 hβ1 hc1
  filter_upwards [(tendsto_tileScale K₀).eventually hev] with u hu
  rw [tileC, freeScale_tile_div hk]
  exact hu

/-- **The base window is eventually above any bound.** -/
theorem eventually_tileC_ge {β : ℝ} (hβ : 0 < β) (K₀ : ℕ) (B : ℝ) :
    ∀ᶠ u : ℕ in atTop, B ≤ tileC β K₀ u := by
  have hev := (tendsto_cardLength hβ).eventually_ge_atTop B
  filter_upwards [(tendsto_tileScale K₀).eventually hev] with u hu
  exact hu

/-- **The base window is eventually below any fixed fraction of the start modulus.** -/
theorem eventually_tileC_small {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u : ℕ in atTop, tileC β K₀ u ≤ c * ((tileM K₀ u : ℕ) : ℝ) := by
  have hlim := tendsto_cardLength_div_sqrt (β := β) hβ0 hβ1
  have hev : ∀ᶠ y : ℝ in atTop, cardLength β y / Real.sqrt y ≤ c := by
    filter_upwards [hlim.eventually (eventually_le_nhds (show (0:ℝ) < c from hc))] with y hy
    exact hy
  filter_upwards [(tendsto_tileScale K₀).eventually hev,
    (tendsto_tileM K₀).eventually_ge_atTop 1] with u hu hm1
  have hm0 : (0 : ℝ) < ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm1
  have hsq : Real.sqrt (freeScale (tileM K₀ u) 0) = ((tileM K₀ u : ℕ) : ℝ) := by
    rw [freeScale_zero, Real.sqrt_sq hm0.le]
  rw [hsq, div_le_iff₀ hm0] at hu
  rw [tileC]
  linarith [hu]

/-! ## The integer logarithm -/

theorem tendsto_tileLogR (K₀ : ℕ) :
    Tendsto (fun u : ℕ => Real.log ((tileM K₀ u : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_tileM_cast K₀)

theorem eventually_tileLog_ge (K₀ N : ℕ) : ∀ᶠ u : ℕ in atTop, N ≤ tileLog K₀ u := by
  filter_upwards [(tendsto_tileLogR K₀).eventually_ge_atTop ((N : ℝ) + 1)] with u hu
  rw [tileLog]
  refine Nat.le_floor ?_
  linarith

theorem tileLog_le {K₀ u : ℕ} (hu : 0 < u) :
    ((tileLog K₀ u : ℕ) : ℝ) ≤ Real.log ((tileM K₀ u : ℕ) : ℝ) := by
  have hm1 : 1 ≤ tileM K₀ u := tileM_pos hu
  have hm1R : (1 : ℝ) ≤ ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm1
  rw [tileLog]
  exact Nat.floor_le (Real.log_nonneg hm1R)

theorem tileLog_ge {K₀ u : ℕ} :
    Real.log ((tileM K₀ u : ℕ) : ℝ) - 1 ≤ ((tileLog K₀ u : ℕ) : ℝ) := by
  rw [tileLog]
  linarith [Nat.lt_floor_add_one (Real.log ((tileM K₀ u : ℕ) : ℝ))]

end

end RHTower.Sieve
