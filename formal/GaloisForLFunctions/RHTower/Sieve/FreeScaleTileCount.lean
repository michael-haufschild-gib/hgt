import GaloisForLFunctions.RHTower.Sieve.FreeScaleTileLimits
import GaloisForLFunctions.RHTower.Sieve.FreeScaleBudget
import GaloisForLFunctions.RHTower.Sieve.FreeScaleBadStart

/-!
# The sign count on one tile

Choosing the number of dyadic blocks `K₀` so that the net harmonic mass is positive, and then the
exceptional-start density `ε` so that the two scale-free inequalities `T₁`, `T₂` hold, every
remaining condition of `Sieve/FreeScaleBudget.free_count_master` is an eventual statement in the
index `u` of the start modulus.
-/

namespace RHTower.Sieve

open Finset Filter ArithmeticFunction

noncomputable section

/-- **A squared logarithm is eventually below any fixed power.** -/
private theorem eventually_log_sq_le (c₁ : ℝ) {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∀ᶠ M : ℕ in atTop, c₁ * (Real.log (M : ℝ)) ^ 2 ≤ c₂ * (M : ℝ) ^ ((1 : ℝ) / 4) := by
  have hlo : (fun y : ℝ => Real.log y ^ (2 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((1 : ℝ) / 4) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  have hc : (0 : ℝ) < c₂ / (|c₁| + 1) := by positivity
  have hev : ∀ᶠ y : ℝ in atTop,
      c₁ * (Real.log y) ^ 2 ≤ c₂ * y ^ ((1 : ℝ) / 4) := by
    filter_upwards [hlo.def hc, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
    have hpow : Real.log y ^ (2 : ℝ) = (Real.log y) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
    have habs : c₁ ≤ |c₁| + 1 := by
      have := le_abs_self c₁; linarith
    have hkey : (|c₁| + 1) * (Real.log y) ^ 2 ≤ c₂ * y ^ ((1 : ℝ) / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hy
      linarith [hy]
    nlinarith [hkey, habs, sq_nonneg (Real.log y)]
  exact tendsto_natCast_atTop_atTop.eventually hev

/-- The number of dyadic blocks that makes the net harmonic mass positive. -/
def harmBlocks : ℕ := ⌈4 * (2 * mertensFirstConst + 1 / 2) / Real.log 2⌉₊

theorem multiHarmConst_harmBlocks_pos : 0 < multiHarmConst harmBlocks := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) ≤ 4 * (2 * mertensFirstConst + 1 / 2) / Real.log 2 := by
    have := mertensFirstConst_nonneg
    positivity
  have hK : 4 * (2 * mertensFirstConst + 1 / 2) / Real.log 2 ≤ (harmBlocks : ℝ) := by
    rw [harmBlocks]; exact Nat.le_ceil _
  rw [multiHarmConst]
  have hstep : 4 * (2 * mertensFirstConst + 1 / 2) ≤ (harmBlocks : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hK
    exact hK
  nlinarith [hstep, hlog2]

set_option maxHeartbeats 1600000 in
/-- **The sign count on one tile.** -/
theorem exists_tile_count {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (K₀ : ℕ) (hharm : 0 < multiHarmConst K₀) :
    ∀ᶠ u : ℕ in atTop, ∀ X : ℕ, tileBase K₀ u ≤ X → X ≤ 2 * tileBase K₀ u →
      (squarefreeDensity / 256)
          * (((tileLen β K₀ u : ℕ) : ℝ)
              * (multiHarmConst K₀
                  / (2 * Real.log ((X / tileM K₀ u : ℕ) : ℝ)))
            - 64 * 2 ^ (K₀ + 2) * ((X / tileM K₀ u : ℕ) : ℝ)
                / Real.log ((X / tileM K₀ u : ℕ) : ℝ))
        ≤ ((((Finset.Ioc X (X + tileLen β K₀ u)).filter
              (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hβpos : (0 : ℝ) < β := by linarith
  set A : ℝ := multiHarmConst K₀ / 2 with hAdef
  have hA0 : (0 : ℝ) < A := by rw [hAdef]; linarith
  have hpc := pairMainConst_pos
  -- the exceptional-start density
  set ε : ℝ := min (A ^ 2 / (768 * 2 ^ (K₀ + 3)))
    (A ^ 2 / (6 * pairMainConst * 2 ^ (3 * K₀ + 6))) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    refine lt_min ?_ ?_
    · positivity
    · positivity
  have hεT1 : 768 * ε * 2 ^ (K₀ + 3) ≤ A ^ 2 := by
    have h1 : ε ≤ A ^ 2 / (768 * 2 ^ (K₀ + 3)) := by rw [hεdef]; exact min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith [h1]
  have hεT2 : 6 * ε * pairMainConst * 2 ^ (3 * K₀ + 6) ≤ A ^ 2 := by
    have h1 : ε ≤ A ^ 2 / (6 * pairMainConst * 2 ^ (3 * K₀ + 6)) := by
      rw [hεdef]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith [h1]
  -- the two conditions that hold for every large base
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (eventually_btError (32 * 2 ^ (K₀ + 2)) (by positivity))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (eventually_log_sq_le (12 * ε * 2 ^ (2 * K₀ + 4)) (show (0 : ℝ) < A ^ 2 by positivity))
  -- the eventual conditions on the start modulus
  have hhalf : ∀ᶠ u : ℕ in atTop, ∀ k, k ≤ K₀ →
      tileC β K₀ u / 2 ≤ cardLength β (freeScale (tileM K₀ u) k) := by
    have := (Finset.range (K₀ + 1)).eventually_all.2
      (fun k hk => eventually_tile_half hβpos hβ1 K₀ k
        (by have := Finset.mem_range.1 hk; omega))
    filter_upwards [this] with u hu k hk
    exact hu k (Finset.mem_range.2 (by omega))
  filter_upwards [(tendsto_tileM K₀).eventually_ge_atTop 2,
    eventually_gt_atTop 0,
    eventually_tileLog_ge K₀ 4,
    eventually_tileC_small hβpos hβ1 K₀ (show (0 : ℝ) < 1 / 4 by norm_num),
    eventually_tileC_ge hβpos K₀ ((2 : ℝ) ^ (K₀ + 2) + 48 * 2 ^ K₀ + 1),
    hhalf,
    (tendsto_tileLogR K₀).eventually_ge_atTop (markerLogBound K₀),
    (tendsto_tileLogR K₀).eventually_ge_atTop 4,
    (tendsto_tileM K₀).eventually_ge_atTop (max N₁ N₂),
    (tendsto_tileM K₀).eventually_ge_atTop (2 ^ (K₀ + 2) + 1),
    eventually_card_freeBadStartUnion_le hβ0 hβ1 K₀ hε0,
    (tendsto_tileM_cast K₀).eventually
      (Real.tendsto_log_atTop.eventually_ge_atTop 0
        |>.and (eventually_ge_atTop (1 : ℝ)))]
    with u hm2 hu0 hlog4 hCsmall hCbig hhalfu hlogbig hlog4R hMbig hMpow hbad _
  intro X hX1 hX2
  -- notation
  set m : ℕ := tileM K₀ u with hmdef
  set M : ℕ := X / m with hMdef
  set h : ℕ := tileLen β K₀ u with hhdef
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hlog1 : 1 ≤ tileLog K₀ u := by omega
  -- the base is between `m·⌊log m⌋` and twice that
  have hbase_eq : tileBase K₀ u = m * (m * tileLog K₀ u) := by
    rw [tileBase, ← hmdef]; ring
  have hMlo : m * tileLog K₀ u ≤ M := by
    have hstep : m * (m * tileLog K₀ u) ≤ X := by rw [← hbase_eq]; exact hX1
    have hcalc : (m * (m * tileLog K₀ u)) / m ≤ X / m := Nat.div_le_div_right hstep
    rw [Nat.mul_div_cancel_left _ hm0] at hcalc
    rw [hMdef]
    exact hcalc
  have hMhi : M ≤ 2 * (m * tileLog K₀ u) := by
    have h2 : 2 * tileBase K₀ u = m * (2 * (m * tileLog K₀ u)) := by rw [hbase_eq]; ring
    have hcalc : X / m ≤ (2 * tileBase K₀ u) / m := Nat.div_le_div_right hX2
    rw [h2, Nat.mul_div_cancel_left _ hm0] at hcalc
    rw [hMdef]
    exact hcalc
  have hmM : m ≤ M := le_trans (by nlinarith [hlog1, hm0]) hMlo
  have hM2 : 2 ≤ M := le_trans hm2 hmM
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hmMR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hlogmM : Real.log (m : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log hmR hmMR
  have hlogM0 : (0 : ℝ) < Real.log (M : ℝ) := by
    have : (0 : ℝ) < Real.log (m : ℝ) := by linarith [hlog4R]
    linarith
  -- the logarithm of the base
  have hlogM : markerLogBound K₀ ≤ Real.log ((M : ℕ) : ℝ) := le_trans hlogbig hlogmM
  have hlogmR : (4 : ℝ) ≤ Real.log ((m : ℕ) : ℝ) := hlog4R
  set T : ℝ := ((tileLog K₀ u : ℕ) : ℝ) with hTdef
  have hT4 : (4 : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast hlog4
  have hTlog : T ≤ Real.log ((m : ℕ) : ℝ) := by rw [hTdef, hmdef]; exact tileLog_le hu0
  have hTge : Real.log ((m : ℕ) : ℝ) - 1 ≤ T := by rw [hTdef, hmdef]; exact tileLog_ge
  have hlogm_le : Real.log ((m : ℕ) : ℝ) ≤ (m : ℝ) := by
    have := Real.log_le_sub_one_of_pos hmR; linarith
  have hTm : T ≤ (m : ℝ) := le_trans hTlog hlogm_le
  have hMloR : (m : ℝ) * T ≤ (M : ℝ) := by
    rw [hTdef]; exact_mod_cast hMlo
  have hMhiR : (M : ℝ) ≤ 2 * ((m : ℝ) * T) := by
    rw [hTdef]; exact_mod_cast hMhi
  -- the sieve conditions that hold for every large base
  have hmM' : max N₁ N₂ ≤ M := le_trans hMbig hmM
  have hbt : Real.exp (4 * mertensSecondUpperConst) * (Real.log ((M : ℕ) : ℝ)) ^ 5
      ≤ 32 * 2 ^ (K₀ + 2) * ((M : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
    hN₁ M (le_trans (le_max_left N₁ N₂) hmM')
  have hT3 : 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log ((M : ℕ) : ℝ)) ^ 2
      ≤ A ^ 2 * ((M : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    hN₂ M (le_trans (le_max_right N₁ N₂) hmM')
  -- the ratio of the smallest start to the base
  have hmtile : m = 2 ^ (K₀ + 1) * u := by rw [hmdef, tileM]
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 1) := by positivity
  have huR : (u : ℝ) = (m : ℝ) / 2 ^ (K₀ + 1) := by
    rw [hmtile]; push_cast; field_simp
  have hMle2m2 : (M : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
    have hmm := mul_le_mul_of_nonneg_left hTm hmR.le
    linarith [hMhiR, hmm]
  have hlogM3 : Real.log ((M : ℕ) : ℝ) ≤ 3 * Real.log ((m : ℕ) : ℝ) := by
    have hlog2 : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) := by
      have h2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hstep : Real.log ((M : ℕ) : ℝ) ≤ Real.log (2 * (m : ℝ) ^ 2) :=
      Real.log_le_log hMR0 hMle2m2
    have hval : Real.log (2 * (m : ℝ) ^ 2) = Real.log 2 + 2 * Real.log ((m : ℕ) : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    rw [hval] at hstep
    linarith
  have hmlogm : (m : ℝ) * Real.log ((m : ℕ) : ℝ) ≤ (4 / 3) * (M : ℝ) := by
    have hT34 : (3 / 4) * Real.log ((m : ℕ) : ℝ) ≤ T := by linarith [hTge, hlogmR]
    have hmul := mul_le_mul_of_nonneg_left hT34 hmR.le
    linarith [hmul, hMloR]
  have hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (u : ℝ) * Real.log ((M : ℕ) : ℝ)
      ≤ (M : ℝ) * A ^ 2 := by
    have hlogM0' : (0 : ℝ) ≤ Real.log ((M : ℕ) : ℝ) := hlogM0.le
    have hkey0 : (m : ℝ) * Real.log ((M : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hlogM3 hmR.le
      linarith [h1, hmlogm]
    have hkey : (u : ℝ) * Real.log ((M : ℕ) : ℝ) ≤ 4 * (M : ℝ) / 2 ^ (K₀ + 1) := by
      rw [huR, div_mul_eq_mul_div, div_le_div_iff₀ hpow0 hpow0]
      exact mul_le_mul_of_nonneg_right hkey0 hpow0.le
    have hεnn : (0 : ℝ) ≤ 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkey hεnn
    refine le_trans (le_of_eq (by ring)) (hmul.trans ?_)
    have hsplit : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (4 * (M : ℝ) / 2 ^ (K₀ + 1))
        = (768 * ε * 2 ^ (K₀ + 3)) * (M : ℝ) := by
      rw [show (2 : ℝ) ^ (2 * K₀ + 4) = 2 ^ (K₀ + 1) * 2 ^ (K₀ + 3) by
        rw [← pow_add]; congr 1; ring]
      field_simp
      try ring
    rw [hsplit]
    have := mul_le_mul_of_nonneg_right hεT1 hMR0.le
    linarith [this]
  -- the window fits inside the square of the base
  have hXH : X + h ≤ M * M := by
    have hcast : ((X + h : ℕ) : ℝ) ≤ ((M * M : ℕ) : ℝ) := by
      push_cast
      set Y : ℝ := (m : ℝ) * T with hYdef
      have hY0 : (0 : ℝ) < Y := by rw [hYdef]; nlinarith [hmR, hT4]
      have hY4m : 4 * (m : ℝ) ≤ Y := by rw [hYdef]; nlinarith [hmR, hT4]
      have hY1 : (1 : ℝ) ≤ Y := by nlinarith [hY4m, hm2R]
      have hbaseR : ((tileBase K₀ u : ℕ) : ℝ) = (m : ℝ) * Y := by
        rw [hbase_eq, hYdef, hTdef]; push_cast; ring
      have hXR : (X : ℝ) ≤ 2 * ((m : ℝ) * Y) := by
        have : (X : ℝ) ≤ 2 * ((tileBase K₀ u : ℕ) : ℝ) := by exact_mod_cast hX2
        rw [hbaseR] at this; linarith
      have hC0 := tileC_pos β K₀ u
      have hcoef : (0 : ℝ) < 2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1) := by positivity
      have hhR : (h : ℝ) ≤ (4 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 2)) * Y + 1 := by
        have hnn : (0 : ℝ) ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
            * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ) := by
          have : (0 : ℝ) ≤ ((tileBase K₀ u : ℕ) : ℝ) := Nat.cast_nonneg _
          positivity
        have hceil : (h : ℝ) ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
            * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ) + 1 := by
          rw [hhdef, tileLen]
          linarith [Nat.ceil_lt_add_one hnn]
        have hval : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
            * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ)
            = (4 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 2)) * Y := by
          rw [hbaseR, ← hmdef, show (2 : ℝ) ^ (K₀ + 2) = 2 * 2 ^ (K₀ + 1) by rw [pow_succ]; ring]
          field_simp
          ring
        rw [hval] at hceil
        exact hceil
      have h4C : 4 * tileC β K₀ u ≤ (m : ℝ) := by linarith [hCsmall]
      have hpowm : (2 : ℝ) ^ (K₀ + 2) + 1 ≤ (m : ℝ) := by exact_mod_cast hMpow
      have hMY : Y ≤ (M : ℝ) := by rw [hYdef]; exact hMloR
      have hchain : (X : ℝ) + (h : ℝ) ≤ 4 * (m : ℝ) * Y := by
        nlinarith [hXR, hhR, h4C, hpowm, hY1, hY0, hmR]
      have hlast : 4 * (m : ℝ) * Y ≤ Y * Y := by nlinarith [hY4m, hY0]
      have hMM : Y * Y ≤ (M : ℝ) * (M : ℝ) := by nlinarith [hMY, hY0]
      linarith [hchain, hlast, hMM]
    exact_mod_cast hcast
  -- the exceptional starts
  have hEbad : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ) ≤ ε * (m : ℝ) := by
    rw [freeStart_zero] at hbad
    rw [hmtile]
    exact hbad
  -- the geometry
  have hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k := fun k hk => by
    rw [hmdef]; exact tile_start_two hu0 hk
  have hfitall : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      (freeWindow β m k + 1) * (p : ℝ) ≤ (h : ℝ) := fun k hk p hp => by
    rw [hmdef, hhdef]
    rw [hmdef] at hp
    exact tile_fit hβpos hu0 hk hX2 hp
  have hCbig8 : (2 : ℝ) ^ (K₀ + 2) + 48 * 2 ^ K₀ + 1 ≤ 8 * tileC β K₀ u := by
    have := tileC_pos β K₀ u; linarith [hCbig]
  have hsupall : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      (squarefreeDensity / 256) * ((h : ℝ) / (p : ℝ) - 1)
        ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1) := fun k hk p hp => by
    rw [hmdef, hhdef]
    rw [hmdef] at hp
    exact tile_supply hu0 hk hlog1 hX1 (hhalfu k hk) hCbig8 hp
  -- the master count
  rw [hAdef] at hT1 hT3
  have hfinal := free_count_master (β := β) (K₀ := K₀) (X := X) (u := u) (m := m) (M := M)
    (Mt := X / u) (K := X / (u * u)) (H := h) (σ := σ) (ε := ε)
    (rho := squarefreeDensity / 256)
    hmtile hMdef rfl rfl hu0 hσ hε0.le
    (div_nonneg squarefreeDensity_pos.le (by norm_num)) hharm hM2 hlogM hbt hXH hmk2
    hfitall hsupall hEbad hT1 (by rw [← hAdef]; exact hεT2) hT3
  exact hfinal

/-- The per-tile constant of the marker construction. -/
def tileConst (K₀ : ℕ) : ℝ := squarefreeDensity * multiHarmConst K₀ / 1024

theorem tileConst_pos (K₀ : ℕ) (h : 0 < multiHarmConst K₀) : 0 < tileConst K₀ := by
  rw [tileConst]
  have := squarefreeDensity_pos
  positivity

set_option maxHeartbeats 1600000 in
/-- **The sign count on one tile, in the card's normalization.** -/
theorem tile_count_clean {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (K₀ : ℕ) (hharm : 0 < multiHarmConst K₀) :
    ∀ᶠ u : ℕ in atTop, ∀ X : ℕ, tileBase K₀ u ≤ X → X ≤ 2 * tileBase K₀ u →
      tileConst K₀ * (((tileLen β K₀ u : ℕ) : ℝ) / Real.log (X : ℝ))
        ≤ ((((Finset.Ioc X (X + tileLen β K₀ u)).filter
            (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hβpos : (0 : ℝ) < β := by linarith
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  filter_upwards [exists_tile_count hβ0 hβ1 hσ K₀ hharm, eventually_gt_atTop 0,
    (tendsto_tileM K₀).eventually_ge_atTop 2, eventually_tileLog_ge K₀ 4,
    eventually_tileC_ge hβpos K₀ (128 * 2 ^ (K₀ + 2) / multiHarmConst K₀)]
    with u hcount hu0 hm2 hlog4 hCbig
  intro X hX1 hX2
  set m : ℕ := tileM K₀ u with hmdef
  set M : ℕ := X / m with hMdef
  set h : ℕ := tileLen β K₀ u with hhdef
  set C : ℝ := tileC β K₀ u with hCdef
  set T : ℝ := ((tileLog K₀ u : ℕ) : ℝ) with hTdef
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hT4 : (4 : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast hlog4
  have hlog1 : 1 ≤ tileLog K₀ u := by omega
  have hbase_eq : tileBase K₀ u = m * (m * tileLog K₀ u) := by rw [tileBase, ← hmdef]; ring
  have hMlo : m * tileLog K₀ u ≤ M := by
    have hstep : m * (m * tileLog K₀ u) ≤ X := by rw [← hbase_eq]; exact hX1
    have hcalc : (m * (m * tileLog K₀ u)) / m ≤ X / m := Nat.div_le_div_right hstep
    rw [Nat.mul_div_cancel_left _ hm0] at hcalc
    rw [hMdef]; exact hcalc
  have hMhi : M ≤ 2 * (m * tileLog K₀ u) := by
    have h2 : 2 * tileBase K₀ u = m * (2 * (m * tileLog K₀ u)) := by rw [hbase_eq]; ring
    have hcalc : X / m ≤ (2 * tileBase K₀ u) / m := Nat.div_le_div_right hX2
    rw [h2, Nat.mul_div_cancel_left _ hm0] at hcalc
    rw [hMdef]; exact hcalc
  have hmM : m ≤ M := le_trans (by nlinarith [hlog1, hm0]) hMlo
  have hM2 : 2 ≤ M := le_trans hm2 hmM
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hMhiR : (M : ℝ) ≤ 2 * ((m : ℝ) * T) := by rw [hTdef]; exact_mod_cast hMhi
  -- the physical scale dominates the base
  have hMX : M ≤ X := Nat.div_le_self _ _
  have hMXR : (M : ℝ) ≤ (X : ℝ) := by exact_mod_cast hMX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hlogM0 : (0 : ℝ) < Real.log ((M : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogMX : Real.log ((M : ℕ) : ℝ) ≤ Real.log ((X : ℕ) : ℝ) :=
    Real.log_le_log hMR0 hMXR
  have hlogX0 : (0 : ℝ) < Real.log ((X : ℕ) : ℝ) := by linarith
  -- the window dominates the marker count
  have hC0 : (0 : ℝ) < C := by rw [hCdef]; exact tileC_pos _ _ _
  have hhge : 4 * C * (m : ℝ) * T ≤ (h : ℝ) := by
    have hbaseR : ((tileBase K₀ u : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) * T) := by
      rw [hbase_eq, hTdef]; push_cast; ring
    have hval : (2 * C + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
        / ((tileM K₀ u : ℕ) : ℝ) = (2 * C + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((m : ℝ) * T)) := by
      rw [hbaseR, ← hmdef]
      field_simp
      try ring
    have hceil : (2 * C + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
        / ((tileM K₀ u : ℕ) : ℝ) ≤ (h : ℝ) := by
      rw [hhdef, tileLen, ← hCdef]
      exact Nat.le_ceil _
    rw [hval] at hceil
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 1) := by positivity
    nlinarith [hceil, hpow, hmR, hT4]
  have hMcmp : 256 * 2 ^ (K₀ + 2) * (M : ℝ) ≤ (h : ℝ) * multiHarmConst K₀ := by
    have hCge : 128 * 2 ^ (K₀ + 2) / multiHarmConst K₀ ≤ C := by rw [hCdef]; exact hCbig
    have hCge' : 128 * 2 ^ (K₀ + 2) ≤ C * multiHarmConst K₀ := by
      rw [div_le_iff₀ hharm] at hCge
      linarith
    have hmT0 : (0 : ℝ) < (m : ℝ) * T := by nlinarith [hmR, hT4]
    have h1 : 256 * 2 ^ (K₀ + 2) * (M : ℝ) ≤ 512 * 2 ^ (K₀ + 2) * ((m : ℝ) * T) := by
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 2) := by positivity
      nlinarith [hMhiR, hpow]
    have h2 : 512 * 2 ^ (K₀ + 2) * ((m : ℝ) * T) ≤ 4 * (C * multiHarmConst K₀) * ((m : ℝ) * T) :=
      by nlinarith [hCge', hmT0]
    have h3 : 4 * (C * multiHarmConst K₀) * ((m : ℝ) * T) ≤ (h : ℝ) * multiHarmConst K₀ := by
      nlinarith [hhge, hharm]
    linarith [h1, h2, h3]
  -- the surplus over the discarded markers
  have hsurplus : 64 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log ((M : ℕ) : ℝ)
      ≤ (h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((M : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ hlogM0 (by linarith)]
    nlinarith [hMcmp, hlogM0]
  have hsplit : (h : ℝ) * (multiHarmConst K₀ / (2 * Real.log ((M : ℕ) : ℝ)))
      - (h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((M : ℕ) : ℝ))
      = (h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((M : ℕ) : ℝ)) := by
    field_simp
    ring
  have hstep : (squarefreeDensity / 256)
      * ((h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((M : ℕ) : ℝ)))
      ≤ (squarefreeDensity / 256)
        * ((h : ℝ) * (multiHarmConst K₀ / (2 * Real.log ((M : ℕ) : ℝ)))
          - 64 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log ((M : ℕ) : ℝ)) := by
    have hnn : (0 : ℝ) ≤ squarefreeDensity / 256 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hnn
    linarith [hsurplus, hsplit]
  refine le_trans ?_ (le_trans hstep (hcount X hX1 hX2))
  -- the logarithm of the base is below the logarithm of the physical scale
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hmono : (h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((X : ℕ) : ℝ))
      ≤ (h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((M : ℕ) : ℝ)) := by
    refine div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hlogXne : Real.log ((X : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogX0
  have heq : tileConst K₀ * ((h : ℝ) / Real.log ((X : ℕ) : ℝ))
      = (squarefreeDensity / 256)
        * ((h : ℝ) * multiHarmConst K₀ / (4 * Real.log ((X : ℕ) : ℝ))) := by
    rw [tileConst]
    field_simp
    try ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hmono (by linarith [hD])

end

end RHTower.Sieve
