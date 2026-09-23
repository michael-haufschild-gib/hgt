import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Paper-scale generalized-divisor collar bound

The largest product-boundary coefficient in Proposition 2.2 is `ζ^(6 : ℕ)`, whose squared short-interval
bound has logarithmic degree `35`.  At collar width `δ_(A-1) = (log X)^(-10(A-1))`, this leaves
exactly `(log X)^(-5)` when `A = 5`.  A polylogarithmic auxiliary cutoff removes the secondary
short-interval term without losing that endpoint exponent.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

/-- Polylogarithmic auxiliary cutoff used in the generalized-divisor short-interval estimate. -/
def mtProductBoundaryDivisorCutoff (A : ℕ) (X : ℝ) : ℕ :=
  Nat.floor ((Real.log X) ^ (2 * A + 35))

/-- Uniformize the explicit short-interval estimate over all divisor orders used by the four
Harman families. -/
theorem sum_zeta_pow_sq_Ioc_le_uniform_six
    (r T L U : ℕ) (W V B : ℝ)
    (hr : 2 ≤ r) (hr6 : r ≤ 6) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hTU : T ≤ U) (hpow : T ^ (r ^ 2) ≤ L)
    (hW : 0 ≤ W) (hV : 0 ≤ V) (hB : 1 ≤ B)
    (hwidth : ((U - L : ℕ) : ℝ) ≤ W)
    (hquot : ((U / T : ℕ) : ℝ) ≤ V)
    (hlog : 1 + Real.log (U / T : ℕ) ≤ B) :
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      36 * (W * B ^ 35 + V * B ^ 35) := by
  have hraw := sum_zeta_pow_sq_Ioc_le_polylog r T L U hr hT hL hLU hTU hpow
  have hrSq : r ^ 2 ≤ 36 := by
    have := Nat.pow_le_pow_left hr6 2
    norm_num at this ⊢
    exact this
  have hrOne : r ^ 2 - 1 ≤ 35 := by omega
  have hrTwo : r ^ 2 - 2 ≤ 35 := by omega
  have hlogOne : 1 ≤ 1 + Real.log (U / T : ℕ) := by
    have hUT : 1 ≤ U / T := Nat.div_pos hTU (Nat.zero_lt_one.trans_le hT)
    have : 0 ≤ Real.log (U / T : ℕ) := Real.log_nonneg (by exact_mod_cast hUT)
    linarith
  have hpOne : (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 1) ≤ B ^ 35 :=
    (pow_le_pow_left₀ (by linarith) hlog (r ^ 2 - 1)).trans
      (pow_le_pow_right₀ hB hrOne)
  have hpTwo : (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 2) ≤ B ^ 35 :=
    (pow_le_pow_left₀ (by linarith) hlog (r ^ 2 - 2)).trans
      (pow_le_pow_right₀ hB hrTwo)
  calc
    ∑ n ∈ Finset.Ioc L U,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      ((r ^ 2 : ℕ) : ℝ) *
        (((U - L : ℕ) : ℝ) *
            (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 1) +
          ((U / T : ℕ) : ℝ) *
            (1 + Real.log (U / T : ℕ)) ^ (r ^ 2 - 2)) := hraw
    _ ≤ 36 * (W * B ^ 35 + V * B ^ 35) := by
      gcongr
      exact_mod_cast hrSq

/-- One floor-defined multiplicative collar has a uniform order-six envelope. -/
theorem sum_zeta_pow_sq_floor_collar_le_uniform_six
    (r T : ℕ) (X Y eta a s : ℝ)
    (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (hY : 0 < Y) (hYX : Y ≤ X) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (ha : 0 < a) (hT : 1 ≤ T) (hTlower : a / 2 ≤ (T : ℝ))
    (hpow36 : T ^ 36 ≤ Nat.floor (Y / 2))
    (hs0 : 0 ≤ s) (hhalfSReal : Y / 2 ≤ s) (hsY : s ≤ 4 * Y)
    (hL : 1 ≤ Nat.floor s) (hlogX : 2 ≤ Real.log X) :
    ∑ n ∈ Finset.Ioc (Nat.floor s) (Nat.floor ((1 + eta) * s)),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      36 * ((4 * eta * Y + 1) * (5 * Real.log X) ^ 35 +
        (16 * Y / a) * (5 * Real.log X) ^ 35) := by
  let L := Nat.floor s
  let U := Nat.floor ((1 + eta) * s)
  have hscale : s ≤ (1 + eta) * s := by nlinarith
  have hLU : L ≤ U := Nat.floor_le_floor hscale
  have hTpow : T ^ (r ^ 2) ≤ Nat.floor (Y / 2) := by
    have hrSq : r ^ 2 ≤ 36 := by
      have := Nat.pow_le_pow_left hr6 2
      norm_num at this ⊢
      exact this
    exact (pow_le_pow_right₀ hT hrSq).trans hpow36
  have hhalfS : Nat.floor (Y / 2) ≤ L := by
    apply Nat.floor_le_floor
    exact hhalfSReal
  have hpow : T ^ (r ^ 2) ≤ L := hTpow.trans hhalfS
  have hTonePow : T ≤ T ^ (r ^ 2) := by
    have hrSqPos : 1 ≤ r ^ 2 := by
      have := Nat.pow_le_pow_left (by omega : 1 ≤ r) 2
      norm_num at this ⊢
      exact this
    simpa only [pow_one] using pow_le_pow_right₀ hT hrSqPos
  have hTU : T ≤ U := hTonePow.trans (hpow.trans hLU)
  have hUcast : (U : ℝ) ≤ (1 + eta) * s := Nat.floor_le (by positivity)
  have hU8 : (U : ℝ) ≤ 8 * Y := by nlinarith
  have hLnear := Nat.lt_floor_add_one s
  have hwidth : ((U - L : ℕ) : ℝ) ≤ 4 * eta * Y + 1 := by
    rw [Nat.cast_sub hLU]
    nlinarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (Nat.zero_lt_one.trans_le hT)
  have haHalf : 0 < a / 2 := by positivity
  have hquotRaw : ((U / T : ℕ) : ℝ) ≤ (U : ℝ) / (T : ℝ) := Nat.cast_div_le
  have hquotDiv : (U : ℝ) / (T : ℝ) ≤ (8 * Y) / (a / 2) :=
    div_le_div₀ (by positivity) hU8 haHalf hTlower
  have hquot : ((U / T : ℕ) : ℝ) ≤ 16 * Y / a := by
    calc
      ((U / T : ℕ) : ℝ) ≤ (U : ℝ) / (T : ℝ) := hquotRaw
      _ ≤ (8 * Y) / (a / 2) := hquotDiv
      _ = 16 * Y / a := by field_simp; ring
  have hqU : U / T ≤ U := Nat.div_le_self U T
  have hq8 : ((U / T : ℕ) : ℝ) ≤ 8 * X := by
    have hqUcast : ((U / T : ℕ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast hqU
    exact hqUcast.trans (hU8.trans (by nlinarith))
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlog : 1 + Real.log (U / T : ℕ) ≤ 5 * Real.log X := by
    by_cases hq0 : U / T = 0
    · simp [hq0]
      linarith
    · have hqpos : (0 : ℝ) < (U / T : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
      have hlogMono := Real.log_le_log hqpos hq8
      have hXpos : 0 < X := hY.trans_le hYX
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hXpos.ne'] at hlogMono
      linarith
  have hB : 1 ≤ 5 * Real.log X := by linarith
  have hW : 0 ≤ 4 * eta * Y + 1 := by positivity
  have hV : 0 ≤ 16 * Y / a := by positivity
  exact sum_zeta_pow_sq_Ioc_le_uniform_six r T L U
    (4 * eta * Y + 1) (16 * Y / a) (5 * Real.log X)
    hr hr6 hT hL hLU hTU hpow hW hV hB hwidth hquot hlog

/-- Both endpoint collars, uniformly for generalized-divisor orders `4,5,6`, satisfy the exact
paper saving.  Constant remains absolute; dependence on `A` enters only through eventual threshold. -/
theorem eventually_sum_mtProductScaleCollars_zeta_sq_le_paper
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y : ℝ) (r : ℕ),
      X ^ (1 / 2 : ℝ) ≤ Y → Y ≤ X → 2 ≤ r → r ≤ 6 →
      (∑ n ∈ mtLowerProductScaleCollar Y (mtPaperWidth (A - 1) X),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2)) +
        ∑ n ∈ mtUpperProductScaleCollar Y (mtPaperWidth (A - 1) X),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
        (1441 * (5 : ℝ) ^ 35) * Y *
          (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
  let K := 2 * A + 35
  have hcut := eventually_const_mul_rpow_polylog_le_rpow
    (C := (2 : ℝ)) (α := (0 : ℝ)) (β := (1 / 2 : ℝ)) (36 * K) (by norm_num)
  have hresid := eventually_const_mul_rpow_polylog_le_rpow
    (C := (72 : ℝ) * (5 : ℝ) ^ 35) (α := (0 : ℝ)) (β := (1 / 2 : ℝ))
      (A + 35) (by norm_num)
  have hsqrt := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop 4
  filter_upwards [hcut, hresid, hsqrt, Filter.eventually_ge_atTop (Real.exp 2)]
      with X hcutX hresidX hsqrtX hX
  intro Y r hXY hYX hr hr6
  have hlogX : 2 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 2) hX
    simpa only [Real.log_exp] using hmono
  have hlogPos : 0 < Real.log X := by linarith
  have hlogOne : 1 ≤ Real.log X := by linarith
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hY4 : 4 ≤ Y := hsqrtX.trans hXY
  have hYpos : 0 < Y := by linarith
  let a := (Real.log X) ^ K
  let T := mtProductBoundaryDivisorCutoff A X
  let eta := mtPaperWidth (A - 1) X
  have hKpos : 1 ≤ K := by dsimp [K]; omega
  have haLower : Real.log X ≤ a := by
    dsimp [a]
    simpa only [pow_one] using pow_le_pow_right₀ hlogOne hKpos
  have ha2 : 2 ≤ a := hlogX.trans haLower
  have haPos : 0 < a := zero_lt_two.trans_le ha2
  have hT : 1 ≤ T := by
    dsimp [T, mtProductBoundaryDivisorCutoff]
    apply Nat.floor_pos.mpr
    dsimp [a, K] at ha2
    linarith
  have hTlower : a / 2 ≤ (T : ℝ) := by
    have hnear := Nat.lt_floor_add_one a
    dsimp [T, mtProductBoundaryDivisorCutoff]
    dsimp [a, K] at hnear ⊢
    linarith
  have hlogPowCut : 2 * (Real.log X) ^ (36 * K) ≤ X ^ (1 / 2 : ℝ) := by
    have hbase : Real.log X ≤ 1 + |Real.log X| := by
      rw [abs_of_nonneg hlogPos.le]
      linarith
    have hp := pow_le_pow_left₀ hlogPos.le hbase (36 * K)
    have := hcutX
    rw [Real.rpow_zero, mul_one] at this
    exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans this
  have hpowReal : a ^ 36 ≤ Y / 2 := by
    have hpowEq : a ^ 36 = (Real.log X) ^ (36 * K) := by
      dsimp [a]
      simpa [Nat.mul_comm] using (pow_mul (Real.log X) K 36).symm
    rw [hpowEq]
    linarith
  have hTcastUpper : (T : ℝ) ≤ a := by
    dsimp [T, mtProductBoundaryDivisorCutoff, a, K]
    exact Nat.floor_le (by positivity)
  have hpow36 : T ^ 36 ≤ Nat.floor (Y / 2) := by
    apply Nat.le_floor
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg T) hTcastUpper 36).trans hpowReal
  have heta0 : 0 ≤ eta := by
    dsimp [eta, mtPaperWidth]
    exact Real.rpow_nonneg hlogPos.le _
  have heta1 : eta ≤ 1 := by
    dsimp [eta, mtPaperWidth]
    exact (Real.rpow_le_rpow_of_exponent_le hlogOne
      (neg_nonpos.mpr (Nat.cast_nonneg _))).trans_eq (by simp)
  have hLlower : 1 ≤ Nat.floor (Y / 2) := by
    exact Nat.le_floor (by norm_num; linarith)
  have hLupper : 1 ≤ Nat.floor (4 * Y) := by
    exact Nat.le_floor (by norm_num; linarith)
  have hlower := sum_zeta_pow_sq_floor_collar_le_uniform_six
    r T X Y eta a (Y / 2) hr hr6 hYpos hYX heta0 heta1 haPos hT hTlower hpow36
    (by positivity) (by rfl) (by linarith) hLlower hlogX
  have hupper := sum_zeta_pow_sq_floor_collar_le_uniform_six
    r T X Y eta a (4 * Y) hr hr6 hYpos hYX heta0 heta1 haPos hT hTlower hpow36
    (by positivity) (by linarith) (by linarith) hLupper hlogX
  have hraw :
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2)) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      72 * ((4 * eta * Y + 1) * (5 * Real.log X) ^ 35 +
        (16 * Y / a) * (5 * Real.log X) ^ 35) := by
    simp only [mtLowerProductScaleCollar, mtUpperProductScaleCollar] at hlower hupper ⊢
    linarith
  have hetaPower : eta * (5 * Real.log X) ^ 35 ≤
      (5 : ℝ) ^ 35 * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    have heq : (Real.log X) ^ (-((10 * (A - 1) : ℕ) : ℝ)) *
        (Real.log X) ^ 35 =
        (Real.log X) ^
          (-((10 * (A - 1) : ℕ) : ℝ) + (35 : ℝ)) := by
      simpa using (Real.rpow_add hlogPos
        (-((10 * (A - 1) : ℕ) : ℝ)) (35 : ℝ)).symm
    have hexp : -((10 * (A - 1) : ℕ) : ℝ) + (35 : ℝ) ≤ -((A : ℕ) : ℝ) := by
      have hsub : A - 1 + 1 = A := Nat.sub_add_cancel (by omega : 1 ≤ A)
      have hsubR : ((A - 1 : ℕ) : ℝ) + 1 = (A : ℝ) := by exact_mod_cast hsub
      push_cast
      linarith [show (5 : ℝ) ≤ A by exact_mod_cast hA]
    calc
      eta * (5 * Real.log X) ^ 35 =
          (5 : ℝ) ^ 35 * ((Real.log X) ^ (-((10 * (A - 1) : ℕ) : ℝ)) *
            (Real.log X) ^ 35) := by
        dsimp [eta, mtPaperWidth]
        rw [show (5 * Real.log X) ^ 35 =
          (5 : ℝ) ^ 35 * (Real.log X) ^ 35 by ring]
        ring
      _ = (5 : ℝ) ^ 35 * (Real.log X) ^
          (-((10 * (A - 1) : ℕ) : ℝ) + (35 : ℝ)) := by rw [heq]
      _ ≤ (5 : ℝ) ^ 35 * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
        gcongr
  have haBoundary : (5 * Real.log X) ^ 35 / a ≤
      (5 : ℝ) ^ 35 * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    have heq : (Real.log X) ^ 35 / (Real.log X) ^ K =
        (Real.log X) ^ ((35 : ℝ) - (K : ℝ)) := by
      rw [← Real.rpow_natCast (Real.log X) 35,
        ← Real.rpow_natCast (Real.log X) K]
      exact (Real.rpow_sub hlogPos (35 : ℝ) (K : ℝ)).symm
    have hexp : (35 : ℝ) - (K : ℝ) ≤ -((A : ℕ) : ℝ) := by
      dsimp [K]
      push_cast
      linarith
    calc
      (5 * Real.log X) ^ 35 / a =
          (5 : ℝ) ^ 35 * ((Real.log X) ^ 35 / (Real.log X) ^ K) := by
        dsimp [a]
        rw [show (5 * Real.log X) ^ 35 =
          (5 : ℝ) ^ 35 * (Real.log X) ^ 35 by ring]
        ring
      _ = (5 : ℝ) ^ 35 * (Real.log X) ^ ((35 : ℝ) - (K : ℝ)) := by rw [heq]
      _ ≤ (5 : ℝ) ^ 35 * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
        gcongr
  have hresidual : 72 * (5 * Real.log X) ^ 35 ≤
      Y * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    have hbase : (Real.log X) ^ (A + 35) ≤
        (1 + |Real.log X|) ^ (A + 35) := by
      apply pow_le_pow_left₀ hlogPos.le
      rw [abs_of_nonneg hlogPos.le]
      linarith
    have hresidReal :
        (72 : ℝ) * (5 : ℝ) ^ 35 * (Real.log X) ^ (A + 35) ≤
          X ^ (1 / 2 : ℝ) := by
      have := hresidX
      rw [Real.rpow_zero, mul_one] at this
      exact (mul_le_mul_of_nonneg_left hbase (by positivity)).trans this
    have hmul := mul_le_mul_of_nonneg_right hresidReal
      (Real.rpow_nonneg hlogPos.le (-((A : ℕ) : ℝ)))
    have heq : (Real.log X) ^ (A + 35) *
        (Real.log X) ^ (-((A : ℕ) : ℝ)) = (Real.log X) ^ 35 := by
      calc
        (Real.log X) ^ (A + 35) *
            (Real.log X) ^ (-((A : ℕ) : ℝ)) =
          (Real.log X) ^ (((A + 35 : ℕ) : ℝ) + (-((A : ℕ) : ℝ))) := by
            rw [← Real.rpow_natCast (Real.log X) (A + 35)]
            exact (Real.rpow_add hlogPos _ _).symm
        _ = (Real.log X) ^ (35 : ℝ) := by
          congr 1
          push_cast
          ring
        _ = (Real.log X) ^ 35 := Real.rpow_natCast _ _
    calc
      72 * (5 * Real.log X) ^ 35 =
          ((72 : ℝ) * (5 : ℝ) ^ 35 * (Real.log X) ^ (A + 35)) *
            (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
        rw [show (5 * Real.log X) ^ 35 = (5 : ℝ) ^ 35 * (Real.log X) ^ 35 by ring]
        rw [mul_assoc, mul_assoc, heq]
      _ ≤ X ^ (1 / 2 : ℝ) * (Real.log X) ^ (-((A : ℕ) : ℝ)) := hmul
      _ ≤ Y * (Real.log X) ^ (-((A : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hXY (Real.rpow_nonneg hlogPos.le _)
  calc
    (∑ n ∈ mtLowerProductScaleCollar Y (mtPaperWidth (A - 1) X),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y (mtPaperWidth (A - 1) X),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ 2) ≤
      72 * ((4 * eta * Y + 1) * (5 * Real.log X) ^ 35 +
        (16 * Y / a) * (5 * Real.log X) ^ 35) := by simpa [eta] using hraw
    _ ≤ (1441 * (5 : ℝ) ^ 35) * Y *
        (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
      have hmain := mul_le_mul_of_nonneg_left hetaPower (by positivity : 0 ≤ 288 * Y)
      have haux := mul_le_mul_of_nonneg_left haBoundary (by positivity : 0 ≤ 1152 * Y)
      have htarget0 : 0 ≤ Y * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by positivity
      have hfive : (1 : ℝ) ≤ (5 : ℝ) ^ 35 := by norm_num
      calc
        72 * ((4 * eta * Y + 1) * (5 * Real.log X) ^ 35 +
            (16 * Y / a) * (5 * Real.log X) ^ 35) =
          288 * Y * (eta * (5 * Real.log X) ^ 35) +
            72 * (5 * Real.log X) ^ 35 +
            1152 * Y * ((5 * Real.log X) ^ 35 / a) := by ring
        _ ≤ 288 * Y * ((5 : ℝ) ^ 35 *
              (Real.log X) ^ (-((A : ℕ) : ℝ))) +
            Y * (Real.log X) ^ (-((A : ℕ) : ℝ)) +
            1152 * Y * ((5 : ℝ) ^ 35 *
              (Real.log X) ^ (-((A : ℕ) : ℝ))) := by
          exact add_le_add (add_le_add hmain hresidual) haux
        _ ≤ (1441 * (5 : ℝ) ^ 35) * Y *
            (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
          nlinarith

end

end RHTower.Sieve
