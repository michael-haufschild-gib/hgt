import GaloisForLFunctions.RHTower.Sieve.MultiHarmonic
import GaloisForLFunctions.RHTower.Sieve.MultiPiBound
import GaloisForLFunctions.RHTower.Sieve.GenericPairBudget

/-!
# The analytic estimates of a marker range at an arbitrary base

A marker range `bigPrimeSet M b` spanning `K₀+1` dyadic blocks above `M` carries harmonic mass
`≍ (K₀+1)·log 2/log M` and cardinality `O(2^{K₀}M/log M)`.  Both are proved here for an arbitrary
base `M`, with the sieve parameters `btRoot M = ⌊M^{1/8}⌋` (Brun–Titchmarsh) and
`sieveSift M = ⌊M^{1/144}⌋` (the shifted-pair sieve).
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-! ## The two sieve parameters -/

/-- The Brun–Titchmarsh sieve parameter of a marker base. -/
def btRoot (M : ℕ) : ℕ := ⌊(M : ℝ) ^ ((1 : ℝ) / 8)⌋₊

theorem btRoot_le {M : ℕ} (hM : 1 ≤ M) : btRoot M ≤ M := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hle : (M : ℝ) ^ ((1 : ℝ) / 8) ≤ (M : ℝ) := by
    calc (M : ℝ) ^ ((1 : ℝ) / 8)
        ≤ (M : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = (M : ℝ) := Real.rpow_one _
  rw [btRoot]
  simpa using Nat.floor_le_of_le hle

/-- **The eighth root exceeds two once `log M ≥ 8 log 2`.** -/
theorem two_le_btRoot {M : ℕ} (hM : 8 * Real.log 2 ≤ Real.log (M : ℝ)) (hM1 : 1 ≤ M) :
    2 ≤ btRoot M := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hge : (2 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [Real.rpow_def_of_pos hM0]
    have : Real.log 2 ≤ Real.log (M : ℝ) * (1 / 8) := by linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (M : ℝ) * (1 / 8)) := Real.exp_le_exp.2 this
  rw [btRoot]
  exact Nat.le_floor (by exact_mod_cast hge)

/-- **The sieve sifting parameter exceeds three once `log M ≥ 144 log 3`.** -/
theorem three_le_sieveSift {M : ℕ} (hM : 144 * Real.log 3 ≤ Real.log (M : ℝ)) (hM1 : 1 ≤ M) :
    3 ≤ sieveSift M := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hge : (3 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 144) := by
    rw [Real.rpow_def_of_pos hM0]
    have : Real.log 3 ≤ Real.log (M : ℝ) * (1 / 144) := by linarith
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (M : ℝ) * (1 / 144)) := Real.exp_le_exp.2 this
  rw [sieveSift]
  exact Nat.le_floor (by exact_mod_cast hge)

/-- **The Brun–Titchmarsh parameter is a fixed fraction of the base, logarithmically.** -/
theorem log_btRoot_ge {M : ℕ} (hM : 2 ≤ M) (hbig : 16 * Real.log 2 ≤ Real.log (M : ℝ))
    (hY2 : 2 ≤ btRoot M) : Real.log (M : ℝ) / 16 ≤ Real.log (btRoot M) := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  set x : ℝ := (M : ℝ) ^ ((1 : ℝ) / 8) with hx
  have hx0 : (0 : ℝ) < x := Real.rpow_pos_of_pos hM0 _
  have hlogx : Real.log x = Real.log (M : ℝ) / 8 := by rw [hx, Real.log_rpow hM0]; ring
  have hfl : x - 1 < ((btRoot M : ℕ) : ℝ) := by
    rw [btRoot, ← hx]
    have := Nat.lt_floor_add_one x
    linarith
  have hY2R : (2 : ℝ) ≤ ((btRoot M : ℕ) : ℝ) := by exact_mod_cast hY2
  have hhalf : x / 2 ≤ ((btRoot M : ℕ) : ℝ) := by
    rcases le_or_gt x 2 with hle | hgt
    · linarith
    · linarith
  have hmono : Real.log (x / 2) ≤ Real.log (btRoot M) := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2:ℝ) ≠ 0), hlogx] at hmono
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : Real.log (M : ℝ) / 16 ≤ Real.log (M : ℝ) / 8 - Real.log 2 := by linarith [hbig]
  linarith [hmono, hstep]

/-- **The sieve sifting parameter is a fixed fraction of the base, logarithmically.** -/
theorem log_sieveSift_ge {M : ℕ} (hM : 2 ≤ M) (hbig : 288 * Real.log 2 ≤ Real.log (M : ℝ))
    (hs2 : 2 ≤ sieveSift M) : Real.log (M : ℝ) / 288 ≤ Real.log (sieveSift M) := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  set x : ℝ := (M : ℝ) ^ ((1 : ℝ) / 144) with hx
  have hx0 : (0 : ℝ) < x := Real.rpow_pos_of_pos hM0 _
  have hlogx : Real.log x = Real.log (M : ℝ) / 144 := by rw [hx, Real.log_rpow hM0]; ring
  have hfl : x - 1 < ((sieveSift M : ℕ) : ℝ) := by
    rw [sieveSift, ← hx]
    have := Nat.lt_floor_add_one x
    linarith
  have hs2R : (2 : ℝ) ≤ ((sieveSift M : ℕ) : ℝ) := by exact_mod_cast hs2
  have hhalf : x / 2 ≤ ((sieveSift M : ℕ) : ℝ) := by
    rcases le_or_gt x 2 with hle | hgt
    · linarith
    · linarith
  have hmono : Real.log (x / 2) ≤ Real.log (sieveSift M) := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2:ℝ) ≠ 0), hlogx] at hmono
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : Real.log (M : ℝ) / 288 ≤ Real.log (M : ℝ) / 144 - Real.log 2 := by linarith [hbig]
  linarith [hmono, hstep]

/-! ## The harmonic mass -/

/-- **The harmonic mass of a marker range spanning `K₀+1` dyadic blocks, from below.** -/
theorem harm_ge_generic {K₀ M b : ℕ} (hM2 : 2 ≤ M) (hb : 2 ^ (K₀ + 1) * M ≤ b)
    (hbig : ((K₀ : ℝ) + 1) * Real.log 2 ≤ Real.log (M : ℝ)) (hlog1 : 1 ≤ Real.log (M : ℝ)) :
    multiHarmConst K₀ / Real.log (M : ℝ) ≤ ∑ p ∈ bigPrimeSet M b, 1 / (p : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log (M : ℝ) := by linarith
  have hp1 : (1 : ℕ) ≤ 2 ^ (K₀ + 1) := Nat.one_le_two_pow
  have hzb : M ≤ b := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hb
  have hbase := sum_inv_bigPrimeSet_ge_sharp hM2 hzb
  refine le_trans ?_ hbase
  set A : ℝ := ((K₀ : ℝ) + 1) * Real.log 2 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  -- the logarithm of the top of the range
  have hbR : ((2 ^ (K₀ + 1) * M : ℕ) : ℝ) = (2 : ℝ) ^ (K₀ + 1) * (M : ℝ) := by push_cast; ring
  have hlogpow : Real.log ((2 ^ (K₀ + 1) * M : ℕ) : ℝ) = A + Real.log (M : ℝ) := by
    rw [hbR, Real.log_mul (by positivity) (ne_of_gt hM0), Real.log_pow, hA]
    push_cast; ring
  have hbge : ((2 ^ (K₀ + 1) * M : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlogb0 : (0 : ℝ) < Real.log ((2 ^ (K₀ + 1) * M : ℕ) : ℝ) := by rw [hlogpow]; linarith
  have hlogbge : A + Real.log (M : ℝ) ≤ Real.log (b : ℝ) := by
    rw [← hlogpow]
    exact Real.log_le_log (by positivity) hbge
  have hlogbpos : (0 : ℝ) < Real.log (b : ℝ) := by linarith
  -- `logLog b − logLog M ≥ A/(2 log M)`
  have hu1 : A / Real.log (M : ℝ) ≤ 1 := by rw [div_le_one hlogM]; exact hbig
  have hlow : A / (2 * Real.log (M : ℝ)) ≤ logLog b - logLog M := by
    set u : ℝ := A / Real.log (M : ℝ) with hu
    have hu0 : (0 : ℝ) < u := by rw [hu]; positivity
    have hratio : Real.log (1 + u) ≤ logLog b - logLog M := by
      rw [logLog, logLog, ← Real.log_div (ne_of_gt hlogbpos) (ne_of_gt hlogM)]
      refine Real.log_le_log (by positivity) ?_
      rw [le_div_iff₀ hlogM, hu]
      field_simp
      linarith [hlogbge]
    have hkey : u / (1 + u) ≤ Real.log (1 + u) := by
      have h1 : (0 : ℝ) < 1 + u := by linarith
      have h2 := Real.add_one_le_exp (-Real.log (1 + u))
      have h3 : Real.exp (-Real.log (1 + u)) = 1 / (1 + u) := by
        rw [Real.exp_neg, Real.exp_log h1, one_div]
      rw [h3] at h2
      have h4 : 1 / (1 + u) = 1 - u / (1 + u) := by
        have hone : 1 / (1 + u) + u / (1 + u) = 1 := by
          rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h1), div_eq_one_iff_eq (by positivity)]
          ring
        linarith
      linarith [h2, h4]
    have hcmp : u / 2 ≤ u / (1 + u) :=
      div_le_div_of_nonneg_left hu0.le (by linarith) (by linarith [hu1])
    have hval : A / (2 * Real.log (M : ℝ)) = u / 2 := by rw [hu]; field_simp
    linarith [hval, hcmp, hkey, hratio]
  -- the two error terms
  have hC0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
    have := mertensFirstConst_nonneg; linarith
  have herr : (2 * mertensFirstConst + 1 / 2) / Real.log (b : ℝ)
      + (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ)
      ≤ 2 * (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ) := by
    have hmono : (2 * mertensFirstConst + 1 / 2) / Real.log (b : ℝ)
        ≤ (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ) :=
      div_le_div_of_nonneg_left hC0 hlogM (by linarith)
    have hsplit : 2 * (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ)
        = (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ)
          + (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ) := by ring
    linarith [hmono, hsplit]
  have hfin : multiHarmConst K₀ / Real.log (M : ℝ)
      = A / (2 * Real.log (M : ℝ)) - 2 * (2 * mertensFirstConst + 1 / 2) / Real.log (M : ℝ) := by
    rw [multiHarmConst, hA]; field_simp
  rw [hfin]
  linarith [hlow, herr]

/-! ## The number of markers -/

/-- **The sieve error term of Brun–Titchmarsh is eventually beaten by the main term.** -/
theorem eventually_btError (c : ℝ) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop,
      Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5 ≤ c * (M : ℝ) ^ ((3:ℝ)/4) := by
  have hlo : (fun y : ℝ => Real.log y ^ (5 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((3 : ℝ) / 4) :=
    isLittleO_log_rpow_rpow_atTop 5 (by norm_num)
  have hc' : (0 : ℝ) < c / Real.exp (4 * mertensSecondUpperConst) := by
    have := Real.exp_pos (4 * mertensSecondUpperConst); positivity
  have hev : ∀ᶠ y : ℝ in atTop,
      Real.exp (4 * mertensSecondUpperConst) * (Real.log y) ^ 5 ≤ c * y ^ ((3:ℝ)/4) := by
    filter_upwards [hlo.def hc', eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
    have hpow : Real.log y ^ (5 : ℝ) = (Real.log y) ^ 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
    have hE : (0 : ℝ) < Real.exp (4 * mertensSecondUpperConst) := Real.exp_pos _
    rw [div_mul_eq_mul_div, le_div_iff₀ hE] at hy
    nlinarith [hy, Real.rpow_nonneg hy0.le ((3:ℝ)/4)]
  exact tendsto_natCast_atTop_atTop.eventually hev

/-- **The number of markers in a range spanning `K₀+1` dyadic blocks, from above.** -/
theorem count_le_generic {K₀ M b : ℕ} (hM2 : 2 ≤ M) (hMb : M ≤ b) (hb : b ≤ 2 ^ (K₀ + 2) * M)
    (hbig : 16 * Real.log 2 ≤ Real.log (M : ℝ))
    (hsec : Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
      ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)) :
    (((bigPrimeSet M b).card : ℕ) : ℝ) ≤ 64 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : 1 ≤ M := by omega
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log (M : ℝ) := by linarith
  have hY2 : 2 ≤ btRoot M := two_le_btRoot (by linarith) hM1
  have hY2R : (2 : ℝ) ≤ ((btRoot M : ℕ) : ℝ) := by exact_mod_cast hY2
  have hlogY : (0 : ℝ) < Real.log (btRoot M) := Real.log_pos (by linarith)
  have hbase := card_bigPrimeSet_le_explicit hMb (by omega : 1 ≤ btRoot M) (btRoot_le hM1) hM2 hlogY
  refine hbase.trans ?_
  have hlogYge := log_btRoot_ge hM2 hbig hY2
  have hbRle : (b : ℝ) ≤ 2 ^ (K₀ + 2) * (M : ℝ) := by exact_mod_cast hb
  -- the Brun--Titchmarsh main term
  have hfirst : 2 * ((b : ℝ) - (M : ℝ)) / Real.log (btRoot M)
      ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ) := by
    have hp0 : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 2) := by positivity
    have hnum : 2 * ((b : ℝ) - (M : ℝ)) ≤ 2 * (2 ^ (K₀ + 2) * (M : ℝ)) := by linarith
    have hnum0 : (0 : ℝ) ≤ 2 * ((b : ℝ) - (M : ℝ)) := by
      have : (M : ℝ) ≤ (b : ℝ) := by exact_mod_cast hMb
      linarith
    rw [div_le_div_iff₀ hlogY hlogM]
    nlinarith [hlogYge, hlogY, hlogM, hM0, hp0, hnum, hnum0]
  -- the sieve error term
  have hYsq : ((btRoot M * btRoot M : ℕ) : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) := by
    have hfl : ((btRoot M : ℕ) : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [btRoot]; exact Nat.floor_le (Real.rpow_nonneg hM0.le _)
    have hnn : (0 : ℝ) ≤ ((btRoot M : ℕ) : ℝ) := Nat.cast_nonneg _
    have hval : (M : ℝ) ^ ((1 : ℝ) / 8) * (M : ℝ) ^ ((1 : ℝ) / 8) = (M : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hM0]; norm_num
    push_cast
    nlinarith [hfl, hnn, hval]
  have hlog4 : (Real.log (M : ℝ)) ^ (4 : ℝ) = (Real.log (M : ℝ)) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsecond : ((btRoot M * btRoot M : ℕ) : ℝ)
        * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ (4 : ℝ))
      ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ) := by
    rw [hlog4, le_div_iff₀ hlogM]
    have hE0 : (0 : ℝ) < Real.exp (4 * mertensSecondUpperConst) := Real.exp_pos _
    have hpow34 : (M : ℝ) ^ ((1 : ℝ) / 4) * (M : ℝ) ^ ((3 : ℝ) / 4) = (M : ℝ) := by
      rw [← Real.rpow_add hM0]; norm_num
    have hstep : ((btRoot M * btRoot M : ℕ) : ℝ)
        * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 4 * Real.log (M : ℝ))
        ≤ (M : ℝ) ^ ((1 : ℝ) / 4) * (32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)) := by
      have h2 : (0 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hM0.le _
      have hc0 : (0 : ℝ) ≤ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5 :=
        mul_nonneg hE0.le (pow_nonneg hlogM.le 5)
      have hrw : ((btRoot M * btRoot M : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 4
              * Real.log (M : ℝ))
          = ((btRoot M * btRoot M : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5) := by ring
      rw [hrw]
      exact mul_le_mul hYsq hsec hc0 h2
    calc ((btRoot M * btRoot M : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 4)
          * Real.log (M : ℝ)
        = ((btRoot M * btRoot M : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 4
            * Real.log (M : ℝ)) := by ring
      _ ≤ (M : ℝ) ^ ((1 : ℝ) / 4) * (32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)) := hstep
      _ = 32 * 2 ^ (K₀ + 2) * (M : ℝ) := by
          rw [show (M : ℝ) ^ ((1 : ℝ) / 4) * (32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4))
            = 32 * 2 ^ (K₀ + 2) * ((M : ℝ) ^ ((1 : ℝ) / 4) * (M : ℝ) ^ ((3 : ℝ) / 4)) by ring,
            hpow34]
  have hsplit : 64 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ)
      = 32 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ)
        + 32 * 2 ^ (K₀ + 2) * (M : ℝ) / Real.log (M : ℝ) := by
    field_simp; ring
  rw [hsplit]
  exact add_le_add hfirst hsecond

/-! ## The shifted-pair budget -/

/-- The constant of the shifted-pair budget at an arbitrary base. -/
def pairMainConst : ℝ := 2 * Real.exp 1 * (288 * Real.log 3) ^ 2 * Real.exp (2 * mertensGapConst)

theorem pairMainConst_pos : 0 < pairMainConst := by
  rw [pairMainConst]
  have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  positivity

/-- The logarithmic threshold beyond which every sieve estimate applies. -/
def markerLogBase : ℝ := 288 * Real.log 2 + 144 * Real.log 3 + 5760 * mertensFirstConst + 1

/-- The logarithmic threshold beyond which every marker estimate applies. -/
def markerLogBound (K₀ : ℕ) : ℝ := ((K₀ : ℝ) + 1) * Real.log 2 + markerLogBase

theorem markerLogBase_le_bound (K₀ : ℕ) : markerLogBase ≤ markerLogBound K₀ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : (0 : ℝ) ≤ ((K₀ : ℝ) + 1) * Real.log 2 := by positivity
  rw [markerLogBound]; linarith

theorem markerLogBase_pos : 0 < markerLogBase := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have := mertensFirstConst_nonneg
  rw [markerLogBase]; linarith

/-- **The shifted-pair budget of a marker range at an arbitrary base.**  The Rankin truncation at
exponent `1/log M` makes the sieve level a fixed power of the base, so the whole `(log M)²` saving
of the two-dimensional Selberg sieve survives. -/
theorem generic_pair_le' {M b K : ℕ} (hM2 : 2 ≤ M) (hbig : markerLogBase ≤ Real.log (M : ℝ)) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M b).filter (fun p => p + d ∈ bigPrimeSet M b)).card : ℕ) : ℝ)
      ≤ pairMainConst * (K : ℝ) * (b : ℝ) / (Real.log (M : ℝ)) ^ 2
        + (K : ℝ) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hc1 := mertensFirstConst_nonneg
  have hM1 : 1 ≤ M := by omega
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  rw [markerLogBase] at hbig
  have hb288 : 288 * Real.log 2 ≤ Real.log (M : ℝ) := by linarith
  have hb144 : 144 * Real.log 3 ≤ Real.log (M : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log (M : ℝ) := by linarith
  have hs3 : 3 ≤ sieveSift M := three_le_sieveSift hb144 hM1
  have hs2 : 2 ≤ sieveSift M := by omega
  have hsift := log_sieveSift_ge hM2 hb288 hs2
  have hlog20 : 20 * mertensFirstConst ≤ Real.log (sieveSift M) := by linarith
  have hbase := generic_pair_le (M₀ := M) (b := b) (K := K) hM1 hs3 hlog20
  refine hbase.trans (add_le_add ?_ ?_)
  · -- the sieve saving beats `(log M)²` up to the Mertens gap
    have hsY3 : (3 : ℕ) ≤ sieveSift M := hs3
    have hsav := sieve_saving_ge hsY3
    have hlogY0 : (0 : ℝ) < Real.log (sieveSift M) := by linarith
    have hlow : Real.log (M : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)
        ≤ Real.exp (mertensS (sieveSift M) - mertensS 3) := by
      refine le_trans ?_ hsav
      have hstep : Real.log (M : ℝ) / (288 * Real.log 3)
          ≤ Real.log (sieveSift M) / Real.log 3 := by
        rw [div_le_div_iff₀ (by positivity) hlog3]
        nlinarith [hsift, hlog3]
      have hexp0 : (0 : ℝ) < Real.exp (-mertensGapConst) := Real.exp_pos _
      exact mul_le_mul_of_nonneg_right hstep hexp0.le
    have hpos : (0 : ℝ) < Real.log (M : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst) := by
      have := Real.exp_pos (-mertensGapConst); positivity
    have hsq : (Real.log (M : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)) ^ 2
        ≤ (Real.exp (mertensS (sieveSift M) - mertensS 3)) ^ 2 := by
      exact pow_le_pow_left₀ hpos.le hlow 2
    have hden0 : (0 : ℝ)
        < (Real.log (M : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)) ^ 2 := by
      positivity
    have hnum0 : (0 : ℝ) ≤ 2 * Real.exp 1 * (K : ℝ) * (b : ℝ) := by
      have h1 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
      have := Real.exp_pos (1 : ℝ)
      positivity
    have hmono : 2 * Real.exp 1 * (K : ℝ) * (b : ℝ)
          / (Real.exp (mertensS (sieveSift M) - mertensS 3)) ^ 2
        ≤ 2 * Real.exp 1 * (K : ℝ) * (b : ℝ)
          / (Real.log (M : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)) ^ 2 :=
      div_le_div_of_nonneg_left hnum0 hden0 hsq
    refine hmono.trans (le_of_eq ?_)
    have hexpsq : (Real.exp (-mertensGapConst)) ^ 2 = 1 / Real.exp (2 * mertensGapConst) := by
      rw [← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * -mertensGapConst = -(2 * mertensGapConst) by push_cast; ring,
        Real.exp_neg, one_div]
    rw [mul_pow, div_pow, hexpsq, pairMainConst]
    have hE : (0 : ℝ) < Real.exp (2 * mertensGapConst) := Real.exp_pos _
    field_simp
  · -- the sieve remainder
    have hlev : (sieveLevel M) ^ 3 = (M : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (sieveLevel M) 3, sieveLevel, ← Real.rpow_mul hM0.le]
      norm_num
    rw [hlev]

end

end RHTower.Sieve
