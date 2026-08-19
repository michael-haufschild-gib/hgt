import GaloisForLFunctions.RHTower.Sieve.MultiPairBudget

/-!
# The shifted-pair budget is proportional to the number of starts

The sieve saving is `exp(mertensS h − mertensS 3) ≥ (log h/log 3)·e^{-c}` by Mertens' second theorem,
and the sifting bound is the `144`-th root of the marker base, so the saving is a fixed fraction of
`log M₀`.  Since the shift range is `≍ log M₀` and the marker range is `≍ M₀`, the main term of the
pair budget is `≍ M₀/log M₀ ≍ m`; the remainder is `M₀^{3/4}`, which is smaller still.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- The constant lost to Mertens' second theorem. -/
def mertensGapConst : ℝ := mertensSecondLowerConst + mertensSecondUpperConst

/-- **The sieve saving from below.** -/
theorem sieve_saving_ge {h : ℕ} (hh : 3 ≤ h) :
    (Real.log h / Real.log 3) * Real.exp (-mertensGapConst)
      ≤ Real.exp (mertensS h - mertensS 3) := by
  have hh2 : 2 ≤ h := by omega
  have hlow := le_mertensS hh2
  have hup := mertensS_le (N := 3) (by norm_num)
  have hlogh : (0 : ℝ) < Real.log h := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < h)
  have hcast3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hlog3 : (0 : ℝ) < Real.log ((3 : ℕ) : ℝ) := by
    rw [hcast3]
    exact Real.log_pos (by norm_num)
  have hstep : Real.log (Real.log h) - Real.log (Real.log ((3 : ℕ) : ℝ)) - mertensGapConst
      ≤ mertensS h - mertensS 3 := by
    rw [logLog] at hlow hup
    rw [mertensGapConst]
    linarith
  refine le_trans (le_of_eq ?_) (Real.exp_le_exp.2 hstep)
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hlogh, Real.exp_log hlog3, hcast3]
  rw [Real.exp_neg]
  field_simp

/-- **The sifting bound is a fixed fraction of the marker base, logarithmically.** -/
theorem log_multiSift_ge {K₀ v : ℕ} (hM : 2 ≤ multiBase K₀ v)
    (hbig : 288 * Real.log 2 ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ))
    (hs2 : 2 ≤ multiSift K₀ v) :
    Real.log ((multiBase K₀ v : ℕ) : ℝ) / 288 ≤ Real.log (multiSift K₀ v) := by
  have hMR : (2 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  set x : ℝ := ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144) with hx
  have hx0 : (0 : ℝ) < x := Real.rpow_pos_of_pos hM0 _
  have hlogx : Real.log x = Real.log ((multiBase K₀ v : ℕ) : ℝ) / 144 := by
    rw [hx, Real.log_rpow hM0]
    ring
  have hfl : x - 1 < ((multiSift K₀ v : ℕ) : ℝ) := by
    rw [multiSift, ← hx]
    have := Nat.lt_floor_add_one x
    linarith
  have hs2R : (2 : ℝ) ≤ ((multiSift K₀ v : ℕ) : ℝ) := by exact_mod_cast hs2
  have hhalf : x / 2 ≤ ((multiSift K₀ v : ℕ) : ℝ) := by
    rcases le_or_gt x 2 with hle | hgt
    · linarith
    · linarith
  have hmono : Real.log (x / 2) ≤ Real.log (multiSift K₀ v) :=
    Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2:ℝ) ≠ 0), hlogx] at hmono
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log ((multiBase K₀ v : ℕ) : ℝ) / 288
      ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ) / 144 - Real.log 2 := by
    linarith [hbig]
  linarith [hmono, this]

/-- The explicit shifted-pair budget of the family. -/
def multiPi (K₀ v : ℕ) : ℝ :=
  2 * Real.exp 1 * ((multiPairK K₀ v : ℕ) : ℝ)
        * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
        / (Real.exp (mertensS (multiSift K₀ v) - mertensS 3)) ^ 2
    + ((multiPairK K₀ v : ℕ) : ℝ) * (2 * (multiLevel K₀ v) ^ 3)

/-- The constant of the pair budget. -/
def multiPiConst (K₀ : ℕ) : ℝ :=
  8 * Real.exp 1 * 8 ^ (K₀ + 1) * (288 * Real.log 3) ^ 2
      * Real.exp (2 * mertensGapConst) + 1

theorem multiPiConst_pos (K₀ : ℕ) : 0 < multiPiConst K₀ := by
  rw [multiPiConst]
  have h1 : (0 : ℝ) < 8 * Real.exp 1 * 8 ^ (K₀ + 1) * (288 * Real.log 3) ^ 2
      * Real.exp (2 * mertensGapConst) := by
    have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  linarith

/-- **The pair budget is proportional to the number of starts.** -/
theorem multiPi_le {K₀ v : ℕ} (hM2 : 2 ≤ multiBase K₀ v) (hW1 : 1 ≤ multiFactor K₀ v)
    (hbig : 288 * Real.log 2 ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ))
    (hs3 : 3 ≤ multiSift K₀ v)
    (hrem : 8 * 4 ^ (K₀ + 1) * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 2
      ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) :
    multiPi K₀ v ≤ multiPiConst K₀ * ((multiScale K₀ v : ℕ) : ℝ) := by
  have hMR : (2 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM2
  have hM0 : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) := by linarith [hbig]
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hbase : multiBase K₀ v = multiScale K₀ v * multiFactor K₀ v := rfl
  have hm1 : 1 ≤ multiScale K₀ v := by
    rcases Nat.eq_zero_or_pos (multiScale K₀ v) with h0 | hpos
    · rw [hbase, h0, Nat.zero_mul] at hM2
      omega
    · exact hpos
  have hmR : (1 : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by exact_mod_cast hm1
  have hWR : (1 : ℝ) ≤ ((multiFactor K₀ v : ℕ) : ℝ) := by exact_mod_cast hW1
  have hbaseR : ((multiBase K₀ v : ℕ) : ℝ)
      = ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) := by
    rw [hbase]
    push_cast
    ring
  -- the lift factor against the logarithm of the base
  have hWlog : ((multiFactor K₀ v : ℕ) : ℝ) ≤ 2 * Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    have hfl : ((multiFactor K₀ v : ℕ) : ℝ) ≤ Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2) := by
      rw [multiFactor]
      exact Nat.floor_le (Real.log_nonneg (by nlinarith [hmR]))
    have hsq : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)
        = 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring
    have hmono : Real.log ((multiScale K₀ v : ℕ) : ℝ)
        ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      rw [hbaseR]
      nlinarith [hmR, hWR]
    rw [hsq] at hfl
    linarith
  have hWsq : ((multiFactor K₀ v : ℕ) : ℝ) ^ 2
      ≤ 4 * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 2 := by
    nlinarith [hWlog, hWR, hlogM]
  -- the sieve saving
  set kappa : ℝ := Real.exp (-mertensGapConst) / (288 * Real.log 3) with hkappa
  have hkappa0 : (0 : ℝ) < kappa := by
    rw [hkappa]
    have := Real.exp_pos (-mertensGapConst)
    positivity
  have hE : Real.log ((multiBase K₀ v : ℕ) : ℝ) * kappa
      ≤ Real.exp (mertensS (multiSift K₀ v) - mertensS 3) := by
    have hsav := sieve_saving_ge hs3
    have hsift := log_multiSift_ge hM2 hbig (by omega)
    refine le_trans ?_ hsav
    rw [hkappa]
    have hexpc : (0 : ℝ) < Real.exp (-mertensGapConst) := Real.exp_pos _
    rw [show Real.log ((multiBase K₀ v : ℕ) : ℝ)
          * (Real.exp (-mertensGapConst) / (288 * Real.log 3))
        = (Real.log ((multiBase K₀ v : ℕ) : ℝ) / 288 / Real.log 3)
          * Real.exp (-mertensGapConst) by field_simp]
    refine mul_le_mul_of_nonneg_right ?_ hexpc.le
    exact div_le_div_of_nonneg_right hsift hlog3.le
  have hE0 : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) * kappa := by positivity
  have hE2 : (Real.log ((multiBase K₀ v : ℕ) : ℝ) * kappa) ^ 2
      ≤ (Real.exp (mertensS (multiSift K₀ v) - mertensS 3)) ^ 2 :=
    pow_le_pow_left₀ hE0.le hE 2
  -- the main term
  have hKb : ((multiPairK K₀ v : ℕ) : ℝ) * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
      = (8 : ℝ) ^ (K₀ + 1) * ((multiFactor K₀ v : ℕ) : ℝ) ^ 2
        * ((multiScale K₀ v : ℕ) : ℝ) := by
    rw [multiPairK]
    push_cast
    rw [hbaseR, show (8 : ℝ) ^ (K₀ + 1) = (4 : ℝ) ^ (K₀ + 1) * (2 : ℝ) ^ (K₀ + 1) by
      rw [← mul_pow]; norm_num]
    ring
  have hterm1 : 2 * Real.exp 1 * ((multiPairK K₀ v : ℕ) : ℝ)
        * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
        / (Real.exp (mertensS (multiSift K₀ v) - mertensS 3)) ^ 2
      ≤ (8 * Real.exp 1 * 8 ^ (K₀ + 1) / kappa ^ 2) * ((multiScale K₀ v : ℕ) : ℝ) := by
    have hnum : (0 : ℝ) ≤ 2 * Real.exp 1 * ((multiPairK K₀ v : ℕ) : ℝ)
        * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ) := by positivity
    refine le_trans (div_le_div_of_nonneg_left hnum (by positivity) hE2) ?_
    rw [show 2 * Real.exp 1 * ((multiPairK K₀ v : ℕ) : ℝ)
          * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)
        = 2 * Real.exp 1 * (((multiPairK K₀ v : ℕ) : ℝ)
            * ((2 ^ (K₀ + 1) * multiBase K₀ v : ℕ) : ℝ)) by ring, hKb,
      div_le_iff₀ (by positivity : (0:ℝ) < (Real.log ((multiBase K₀ v : ℕ) : ℝ) * kappa) ^ 2)]
    have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hpk : (0 : ℝ) < (8 : ℝ) ^ (K₀ + 1) := by positivity
    have hexp : (8 * Real.exp 1 * 8 ^ (K₀ + 1) / kappa ^ 2) * ((multiScale K₀ v : ℕ) : ℝ)
          * (Real.log ((multiBase K₀ v : ℕ) : ℝ) * kappa) ^ 2
        = 8 * Real.exp 1 * 8 ^ (K₀ + 1) * ((multiScale K₀ v : ℕ) : ℝ)
          * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 2 := by
      field_simp
    rw [hexp]
    nlinarith [mul_le_mul_of_nonneg_left hWsq
      (by positivity : (0:ℝ) ≤ 2 * Real.exp 1 * (8:ℝ) ^ (K₀ + 1) * ((multiScale K₀ v : ℕ) : ℝ))]
  -- the remainder term
  have hL0 : (0 : ℝ) < multiLevel K₀ v := by
    rw [multiLevel]
    exact Real.rpow_pos_of_pos hM0 _
  have hpow4 : (multiLevel K₀ v) ^ 4 = ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiLevel, ← Real.rpow_natCast (((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul hM0.le]
    norm_num
  have hLstep : 2 * (4 : ℝ) ^ (K₀ + 1) * ((multiFactor K₀ v : ℕ) : ℝ) ^ 2
      ≤ multiLevel K₀ v := by
    rw [multiLevel]
    nlinarith [mul_le_mul_of_nonneg_left hWsq (by positivity : (0:ℝ) ≤ 2 * (4:ℝ) ^ (K₀ + 1)),
      hrem]
  have hterm2 : ((multiPairK K₀ v : ℕ) : ℝ) * (2 * (multiLevel K₀ v) ^ 3)
      ≤ ((multiScale K₀ v : ℕ) : ℝ) := by
    have hWpos : (0 : ℝ) < ((multiFactor K₀ v : ℕ) : ℝ) := by linarith
    refine le_of_mul_le_mul_right ?_ hWpos
    have hlhs : ((multiPairK K₀ v : ℕ) : ℝ) * (2 * (multiLevel K₀ v) ^ 3)
          * ((multiFactor K₀ v : ℕ) : ℝ)
        = (2 * (4 : ℝ) ^ (K₀ + 1) * ((multiFactor K₀ v : ℕ) : ℝ) ^ 2)
          * (multiLevel K₀ v) ^ 3 := by
      rw [multiPairK]
      push_cast
      ring
    have hrhs : ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ)
        = multiLevel K₀ v * (multiLevel K₀ v) ^ 3 := by
      rw [← hbaseR, ← hpow4]
      ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right hLstep (by positivity)
  -- assemble
  have hconst : 8 * Real.exp 1 * (8 : ℝ) ^ (K₀ + 1) / kappa ^ 2
      = 8 * Real.exp 1 * 8 ^ (K₀ + 1) * (288 * Real.log 3) ^ 2
        * Real.exp (2 * mertensGapConst) := by
    rw [hkappa, Real.exp_neg,
      show (2 : ℝ) * mertensGapConst = mertensGapConst + mertensGapConst by ring, Real.exp_add]
    have hexp : (0 : ℝ) < Real.exp mertensGapConst := Real.exp_pos _
    field_simp
  rw [multiPi, multiPiConst]
  rw [hconst] at hterm1
  nlinarith [hterm1, hterm2, hmR]

end

end RHTower.Sieve
