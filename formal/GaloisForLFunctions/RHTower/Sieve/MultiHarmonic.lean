import GaloisForLFunctions.RHTower.Sieve.MultiEventual
import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp
import GaloisForLFunctions.RHTower.Sieve.MarkerCountUpper

/-!
# The harmonic mass and the number of the markers

The marker range spans `K₀+1` dyadic blocks, so its harmonic mass is `(K₀+1)·log 2/log M₀` up to the
explicit constant of Mertens' second theorem — which a single block cannot beat but `K₀+1` blocks
can.  Its cardinality is `O(2^{K₀}M₀/log M₀)` by Brun–Titchmarsh at the eighth root.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- The net harmonic mass constant of the family. -/
def multiHarmConst (K₀ : ℕ) : ℝ :=
  ((K₀ : ℝ) + 1) * Real.log 2 / 2 - 2 * (2 * mertensFirstConst + 1 / 2)

/-- **The harmonic mass of the marker range from below.** -/
theorem eventually_multiHarm_ge (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop,
      multiHarmConst K₀ / Real.log ((multiBase K₀ v : ℕ) : ℝ)
        ≤ ∑ p ∈ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v), 1 / (p : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [(tendsto_multiBase K₀).eventually_ge_atTop 2,
    eventually_log_multiBase_ge K₀ (((K₀ : ℝ) + 1) * Real.log 2),
    eventually_log_multiBase_ge K₀ 1] with v hM2R hbig hlog1
  have hM2 : 2 ≤ multiBase K₀ v := by exact_mod_cast hM2R
  have hM0 : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hzb : multiBase K₀ v ≤ 2 ^ (K₀ + 1) * multiBase K₀ v :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hbase := sum_inv_bigPrimeSet_ge_sharp hM2 hzb
  refine le_trans ?_ hbase
  -- the logarithm of the top of the range
  have hbR : ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
      = (2 : ℝ) ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) := by push_cast; ring
  have hlogb : Real.log ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
      = ((K₀ : ℝ) + 1) * Real.log 2 + Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [hbR, Real.log_mul (by positivity) (ne_of_gt hM0), Real.log_pow]
    push_cast
    ring
  set A : ℝ := ((K₀ : ℝ) + 1) * Real.log 2 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  have hlogb0 : (0 : ℝ) < Real.log ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ) := by
    rw [hlogb]; linarith
  -- `logLog b − logLog M₀ ≥ A/(2 log M₀)`
  have hratio : (1 : ℝ) + A / Real.log ((multiBase K₀ v : ℕ) : ℝ)
      = Real.log ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
        / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [hlogb]
    field_simp
    ring
  have hu1 : A / Real.log ((multiBase K₀ v : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hlogM]
    exact hbig
  have hlow : A / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ))
      ≤ logLog (2 ^ (K₀ + 1) * multiBase K₀ v) - logLog (multiBase K₀ v) := by
    set u : ℝ := A / Real.log ((multiBase K₀ v : ℕ) : ℝ) with hu
    have hu0 : (0 : ℝ) < u := by rw [hu]; positivity
    have hlogdiff : logLog (2 ^ (K₀ + 1) * multiBase K₀ v) - logLog (multiBase K₀ v)
        = Real.log (1 + u) := by
      rw [logLog, logLog, ← Real.log_div (ne_of_gt hlogb0) (ne_of_gt hlogM), hratio]
    rw [hlogdiff]
    have hkey : u / (1 + u) ≤ Real.log (1 + u) := by
      have h1 : (0 : ℝ) < 1 + u := by linarith
      have h2 := Real.add_one_le_exp (-Real.log (1 + u))
      have h3 : Real.exp (-Real.log (1 + u)) = 1 / (1 + u) := by
        rw [Real.exp_neg, Real.exp_log h1, one_div]
      rw [h3] at h2
      have h4 : 1 / (1 + u) = 1 - u / (1 + u) := by
        have hone : 1 / (1 + u) + u / (1 + u) = 1 := by
          rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h1)]
          rw [div_eq_one_iff_eq (by positivity)]
          ring
        linarith
      linarith [h2, h4]
    have hcmp : u / 2 ≤ u / (1 + u) := by
      refine div_le_div_of_nonneg_left hu0.le (by linarith) (by linarith [hu1])
    have hval : A / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) = u / 2 := by
      rw [hu]
      field_simp
    linarith [hval, hcmp, hkey]
  -- the two error terms
  have herr : (2 * mertensFirstConst + 1 / 2)
        / Real.log ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
      + (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ)
      ≤ 2 * (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    have hC0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have hmono : (2 * mertensFirstConst + 1 / 2)
        / Real.log ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
        ≤ (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hC0 hlogM (by rw [hlogb]; linarith)
    have : 2 * (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ)
        = (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ)
          + (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
      ring
    linarith [hmono, this]
  have hfin : multiHarmConst K₀ / Real.log ((multiBase K₀ v : ℕ) : ℝ)
      = A / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ))
        - 2 * (2 * mertensFirstConst + 1 / 2) / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiHarmConst, hA]
    field_simp
  rw [hfin]
  linarith [hlow, herr]

/-! ## The number of markers -/

/-- The Brun–Titchmarsh sieve parameter of the family. -/
def multiBTRoot (K₀ v : ℕ) : ℕ := ⌊((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8)⌋₊

/-- The count of the marker range. -/
def multiCount (K₀ v : ℕ) : ℝ :=
  64 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) / Real.log ((multiBase K₀ v : ℕ) : ℝ)

theorem multiBTRoot_le_base {K₀ v : ℕ} (hM : 1 ≤ multiBase K₀ v) :
    multiBTRoot K₀ v ≤ multiBase K₀ v := by
  have hMR : (1 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM
  have hle : ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by
    calc ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8)
        ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = ((multiBase K₀ v : ℕ) : ℝ) := Real.rpow_one _
  rw [multiBTRoot]
  simpa using Nat.floor_le_of_le hle

theorem log_multiBTRoot_ge {K₀ v : ℕ} (hM : 2 ≤ multiBase K₀ v)
    (hbig : 16 * Real.log 2 ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ))
    (hY2 : 2 ≤ multiBTRoot K₀ v) :
    Real.log ((multiBase K₀ v : ℕ) : ℝ) / 16 ≤ Real.log (multiBTRoot K₀ v) := by
  have hMR : (2 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  set x : ℝ := ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) with hx
  have hx0 : (0 : ℝ) < x := Real.rpow_pos_of_pos hM0 _
  have hlogx : Real.log x = Real.log ((multiBase K₀ v : ℕ) : ℝ) / 8 := by
    rw [hx, Real.log_rpow hM0]
    ring
  have hfl : x - 1 < ((multiBTRoot K₀ v : ℕ) : ℝ) := by
    rw [multiBTRoot, ← hx]
    have := Nat.lt_floor_add_one x
    linarith
  have hY2R : (2 : ℝ) ≤ ((multiBTRoot K₀ v : ℕ) : ℝ) := by exact_mod_cast hY2
  have hhalf : x / 2 ≤ ((multiBTRoot K₀ v : ℕ) : ℝ) := by
    rcases le_or_gt x 2 with hle | hgt
    · linarith
    · linarith
  have hmono : Real.log (x / 2) ≤ Real.log (multiBTRoot K₀ v) :=
    Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2:ℝ) ≠ 0), hlogx] at hmono
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : Real.log ((multiBase K₀ v : ℕ) : ℝ) / 16
      ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ) / 8 - Real.log 2 := by
    linarith [hbig]
  linarith [hmono, hstep]

/-- **The eighth root exceeds two, eventually.** -/
theorem eventually_two_le_multiBTRoot (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop, 2 ≤ multiBTRoot K₀ v := by
  have hev : ∀ᶠ y : ℝ in atTop, (2 : ℝ) ^ (8 : ℕ) ≤ y := eventually_ge_atTop _
  filter_upwards [(tendsto_multiBase K₀).eventually hev] with v hv
  rw [multiBTRoot]
  refine Nat.le_floor ?_
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hkey : ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8)
      ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (by positivity) hv (by norm_num)
  refine le_trans (le_of_eq ?_) hkey
  rw [← Real.rpow_natCast (2 : ℝ) 8, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **The number of markers, from above.** -/
theorem eventually_multiCount_le (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop,
      (((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
        ≤ multiCount K₀ v := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the second term is beaten by the first, eventually
  have hlo : (fun y : ℝ => Real.log y ^ (5 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((3 : ℝ) / 4) :=
    isLittleO_log_rpow_rpow_atTop 5 (by norm_num)
  have hc : (0 : ℝ) < 1 / (Real.exp (4 * mertensSecondUpperConst) * 32 * 2 ^ (K₀ + 1)) := by
    have := Real.exp_pos (4 * mertensSecondUpperConst)
    positivity
  have hsecond : ∀ᶠ y : ℝ in atTop,
      Real.exp (4 * mertensSecondUpperConst) * (Real.log y) ^ 5
        ≤ 32 * 2 ^ (K₀ + 1) * y ^ ((3 : ℝ) / 4) := by
    filter_upwards [hlo.def hc, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
    have hpow : Real.log y ^ (5 : ℝ) = (Real.log y) ^ 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
    have hK : (0 : ℝ) < Real.exp (4 * mertensSecondUpperConst) * 32 * 2 ^ (K₀ + 1) := by
      have := Real.exp_pos (4 * mertensSecondUpperConst)
      positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK] at hy
    have hpk : (1 : ℝ) ≤ 32 * 2 ^ (K₀ + 1) := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (K₀ + 1) := one_le_pow₀ (by norm_num)
      linarith
    have hEL0 : (0 : ℝ) ≤ Real.exp (4 * mertensSecondUpperConst) * (Real.log y) ^ 5 := by
      have := Real.exp_pos (4 * mertensSecondUpperConst)
      positivity
    nlinarith [hy, hpk, hEL0, Real.rpow_nonneg hy0.le ((3:ℝ)/4)]
  filter_upwards [(tendsto_multiBase K₀).eventually_ge_atTop 2,
    eventually_log_multiBase_ge K₀ (16 * Real.log 2),
    eventually_log_multiBase_ge K₀ 1,
    eventually_two_le_multiBTRoot K₀,
    (tendsto_multiBase K₀).eventually hsecond] with v hM2R hbig hlog1 hY2 hsec
  have hM2 : 2 ≤ multiBase K₀ v := by exact_mod_cast hM2R
  have hM1 : 1 ≤ multiBase K₀ v := by omega
  have hM0 : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hY2R : (2 : ℝ) ≤ ((multiBTRoot K₀ v : ℕ) : ℝ) := by exact_mod_cast hY2
  have hlogY : (0 : ℝ) < Real.log (multiBTRoot K₀ v) := by
    refine Real.log_pos ?_
    linarith
  have hbase := card_bigPrimeSet_le_explicit (M := multiBase K₀ v)
    (b := 2 ^ (K₀ + 1) * multiBase K₀ v) (Y := multiBTRoot K₀ v)
    (Nat.le_mul_of_pos_left _ (by positivity)) (by omega) (multiBTRoot_le_base hM1) hM2 hlogY
  refine hbase.trans ?_
  -- the main Brun--Titchmarsh term
  have hlogYge := log_multiBTRoot_ge hM2 hbig hY2
  have hbR : ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
      = (2 : ℝ) ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) := by push_cast; ring
  have hfirst : 2 * (((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ) - ((multiBase K₀ v : ℕ) : ℝ))
        / Real.log (multiBTRoot K₀ v)
      ≤ 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ)
        / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [hbR, div_le_div_iff₀ hlogY hlogM]
    have hp0 : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 1) := by positivity
    nlinarith [hlogYge, hlogY, hlogM, hM0, hp0]
  -- the sieve error term
  have hYsq : ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
      ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    have hfl : ((multiBTRoot K₀ v : ℕ) : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [multiBTRoot]
      exact Nat.floor_le (Real.rpow_nonneg hM0.le _)
    have hnn : (0 : ℝ) ≤ ((multiBTRoot K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
    have hval : ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8)
        * ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 8)
        = ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hM0]
      norm_num
    push_cast
    nlinarith [hfl, hnn, hval]
  have hlog4 : (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ (4 : ℝ)
      = (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsecond' : ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
        * (Real.exp (4 * mertensSecondUpperConst)
          * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ (4 : ℝ))
      ≤ 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ)
        / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [hlog4, le_div_iff₀ hlogM]
    have hE0 : (0 : ℝ) < Real.exp (4 * mertensSecondUpperConst) := Real.exp_pos _
    have hpow34 : ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4) = ((multiBase K₀ v : ℕ) : ℝ) := by
      rw [← Real.rpow_add hM0]
      norm_num
    have hstep : ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
        * (Real.exp (4 * mertensSecondUpperConst)
          * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 4
          * Real.log ((multiBase K₀ v : ℕ) : ℝ))
        ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
          * (32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
      have h1 : Real.exp (4 * mertensSecondUpperConst)
            * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := hsec
      have h2 : (0 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_nonneg hM0.le _
      have h3 : (0 : ℝ) ≤ ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
      have hc0 : (0 : ℝ) ≤ Real.exp (4 * mertensSecondUpperConst)
          * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 5 :=
        mul_nonneg hE0.le (pow_nonneg hlogM.le 5)
      have hrw : ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst)
              * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 4
              * Real.log ((multiBase K₀ v : ℕ) : ℝ))
          = ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst)
              * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 5) := by ring
      rw [hrw]
      exact mul_le_mul hYsq h1 hc0 h2
    calc ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst)
            * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 4)
          * Real.log ((multiBase K₀ v : ℕ) : ℝ)
        = ((multiBTRoot K₀ v * multiBTRoot K₀ v : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst)
            * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 4
            * Real.log ((multiBase K₀ v : ℕ) : ℝ)) := by ring
      _ ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
          * (32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := hstep
      _ = 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) := by
          rw [show ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
              * (32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4))
            = 32 * 2 ^ (K₀ + 1) * (((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
              * ((multiBase K₀ v : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) by ring, hpow34]
  rw [multiCount]
  have hsplit : 64 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ)
        / Real.log ((multiBase K₀ v : ℕ) : ℝ)
      = 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ)
          / Real.log ((multiBase K₀ v : ℕ) : ℝ)
        + 32 * 2 ^ (K₀ + 1) * ((multiBase K₀ v : ℕ) : ℝ)
          / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    field_simp
    ring
  rw [hsplit]
  exact add_le_add hfirst hsecond'

end

end RHTower.Sieve
