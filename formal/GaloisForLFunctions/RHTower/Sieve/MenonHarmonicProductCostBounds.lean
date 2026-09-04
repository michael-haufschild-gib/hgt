import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicExactDefectAssembly
import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LadderErrorBudget
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Elementary bounds for Menon's harmonic product cost

The exact frequency assembly retains a reciprocal Halász--Montgomery mass and a cofactor-cardinality
factor at each geometric prime step.  This file exposes uniform elementary upper bounds for those
quantities without estimating the frequency-set measure or the prime polynomial.  In particular,
the cofactor factor has its true scale `Q_j / A₀`, rather than the unusable trivial scale `B₀`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Harmonic mass of one geometric prime block is at most its relative width plus the endpoint
rounding term. -/
theorem harmonicPrimeMass_geomBlock_le
    {P : Finset ℕ} {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) (j : ℕ) :
    harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤
      eta + 1 / (Q * (1 + eta) ^ j) := by
  let Qj : ℝ := Q * (1 + eta) ^ j
  have hQj : 0 < Qj := by
    dsimp only [Qj]
    positivity
  rw [harmonicPrimeMass]
  calc
    ∑ p ∈ geomBlock P Q (1 + eta) j, 1 / (p : ℝ) ≤
        ∑ _p ∈ geomBlock P Q (1 + eta) j, 1 / Qj := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact one_div_le_one_div_of_le hQj (Finset.mem_filter.mp hp).2.1.le
    _ = ((geomBlock P Q (1 + eta) j).card : ℝ) / Qj := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (Qj * eta + 1) / Qj := by
      exact div_le_div_of_nonneg_right
        (by simpa only [Qj] using card_geomBlock_le P hQ heta j) hQj.le
    _ = eta + 1 / (Q * (1 + eta) ^ j) := by
      dsimp only [Qj]
      field_simp

/-- The reciprocal coefficient energy of a common cofactor block has scale `Q_j / A₀`.
Natural ceiling and floor endpoints are retained exactly on the left. -/
theorem cofactorReciprocalCardFactor_le
    {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q eta : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) (j : ℕ) :
    (1 / (⌈(A₀ : ℝ) /
        ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt A₀ B₀ Q eta j).card : ℝ) ≤
      (((Q * (1 + eta) ^ j) * (1 + eta)) / (A₀ : ℝ)) ^ 2 *
        ((B₀ : ℝ) / (Q * (1 + eta) ^ j) + 1) := by
  let D : ℝ := (Q * (1 + eta) ^ j) * (1 + eta)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hAreal : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
  have hfrac : 0 < (A₀ : ℝ) / D := div_pos hAreal hD
  have hceil : (A₀ : ℝ) / D ≤ (⌈(A₀ : ℝ) / D⌉₊ : ℝ) := Nat.le_ceil _
  have hinv : 1 / (⌈(A₀ : ℝ) / D⌉₊ : ℝ) ≤ D / (A₀ : ℝ) := by
    calc
      1 / (⌈(A₀ : ℝ) / D⌉₊ : ℝ) ≤ 1 / ((A₀ : ℝ) / D) :=
        one_div_le_one_div_of_le hfrac hceil
      _ = D / (A₀ : ℝ) := by field_simp
  have hinv0 : 0 ≤ 1 / (⌈(A₀ : ℝ) / D⌉₊ : ℝ) := by positivity
  have hDdiv0 : 0 ≤ D / (A₀ : ℝ) := (div_pos hD hAreal).le
  have hcard := card_geomCofactorBlockAt_le (A₀ := A₀) (B₀ := B₀) hQ heta j
  calc
    (1 / (⌈(A₀ : ℝ) /
        ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt A₀ B₀ Q eta j).card : ℝ) =
      (1 / (⌈(A₀ : ℝ) / D⌉₊ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt A₀ B₀ Q eta j).card : ℝ) := by rfl
    _ ≤ (D / (A₀ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt A₀ B₀ Q eta j).card : ℝ) := by
      gcongr
    _ ≤ (D / (A₀ : ℝ)) ^ 2 *
        ((B₀ : ℝ) / (Q * (1 + eta) ^ j) + 1) := by
      exact mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
    _ = (((Q * (1 + eta) ^ j) * (1 + eta)) / (A₀ : ℝ)) ^ 2 *
        ((B₀ : ℝ) / (Q * (1 + eta) ^ j) + 1) := by rfl

/-- Nonnegativity of the reciprocal Halász--Montgomery mass, with its genuine measure parameter. -/
theorem hmMassRecip_nonneg
    (N : ℕ) {T volE : ℝ} (hT : 1 ≤ T) (hvolE : 0 ≤ volE) :
    0 ≤ hmMassRecip N T volE := by
  rw [hmMassRecip]
  have hfar : 0 ≤ plainKernelFarConst N T := plainKernelFarConst_nonneg N hT
  have hlog : 0 ≤ Real.log (2 + 2 * T) := Real.log_nonneg (by linarith)
  positivity

/-- Explicit square-root/logarithmic upper bound for the far reciprocal kernel constant. -/
theorem plainKernelFarConst_le_log
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    plainKernelFarConst N T ≤
      (1 + 2 * Real.log (2 * T + 1)) * (214 * Real.sqrt (2 * T)) +
        12288 * Real.sqrt (2 * T) + (1 + 2 * Real.log (N : ℝ)) := by
  have h2T : 0 ≤ 2 * T := by positivity
  have hceil : 1 ≤ ⌈2 * T⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  have hceilPos : (0 : ℝ) < (⌈2 * T⌉₊ : ℝ) := by exact_mod_cast hceil
  have hceilUpper : (⌈2 * T⌉₊ : ℝ) ≤ 2 * T + 1 :=
    (Nat.ceil_lt_add_one h2T).le
  have hlogceil : Real.log (⌈2 * T⌉₊ : ℝ) ≤ Real.log (2 * T + 1) :=
    Real.log_le_log hceilPos hceilUpper
  have hcountT : (Nat.log 2 ⌈2 * T⌉₊ : ℝ) + 1 ≤
      1 + 2 * Real.log (2 * T + 1) := by
    have hnat := natLogTwo_add_one_cast_le hceil
    push_cast at hnat
    linarith
  have hcountN : (Nat.log 2 N : ℝ) + 1 ≤ 1 + 2 * Real.log (N : ℝ) := by
    have hnat := natLogTwo_add_one_cast_le hN
    push_cast at hnat
    exact hnat
  rw [plainKernelFarConst]
  gcongr

/-- At final-shell height, the reciprocal kernel's far constant has the expected
`O(√x log x)` scale, uniformly for every polynomial length at most `3x`. -/
theorem plainKernelFarConst_finalRange_le
    {x : ℝ} (hx : Real.exp 1 ≤ x) {N : ℕ} (hN : 1 ≤ N)
    (hNx : (N : ℝ) ≤ 3 * x) :
    plainKernelFarConst N (2 * Real.pi * x) ≤
      80000 * Real.sqrt x * Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hx1 : 1 ≤ x :=
    (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hx
  have hlogx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hT : 1 ≤ 2 * Real.pi * x := by
    nlinarith [Real.pi_gt_three]
  have hsqrtx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hsqrt : Real.sqrt (2 * (2 * Real.pi * x)) ≤ 4 * Real.sqrt x := by
    calc
      Real.sqrt (2 * (2 * Real.pi * x)) ≤ Real.sqrt (16 * x) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.pi_lt_four]
      _ = 4 * Real.sqrt x := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have harg : 2 * (2 * Real.pi * x) + 1 ≤ 17 * x := by
    nlinarith [Real.pi_lt_four]
  have harg0 : 0 < 2 * (2 * Real.pi * x) + 1 := by positivity
  have hlogArgRaw : Real.log (2 * (2 * Real.pi * x) + 1) ≤ Real.log (17 * x) :=
    Real.log_le_log harg0 harg
  have hlog17 : Real.log (17 : ℝ) ≤ 16 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17)
    norm_num at h ⊢
    exact h
  have hlogArg : Real.log (2 * (2 * Real.pi * x) + 1) ≤ 17 * Real.log x := by
    rw [Real.log_mul (by norm_num : (17 : ℝ) ≠ 0) (ne_of_gt hx0)] at hlogArgRaw
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogNRaw : Real.log (N : ℝ) ≤ Real.log (3 * x) :=
    Real.log_le_log hNpos hNx
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogN : Real.log (N : ℝ) ≤ 3 * Real.log x := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx0)] at hlogNRaw
    linarith
  have hlogArg0 : 0 ≤ Real.log (2 * (2 * Real.pi * x) + 1) :=
    Real.log_nonneg (by nlinarith [hx1, Real.pi_gt_three])
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    plainKernelFarConst N (2 * Real.pi * x) ≤
        (1 + 2 * Real.log (2 * (2 * Real.pi * x) + 1)) *
            (214 * Real.sqrt (2 * (2 * Real.pi * x))) +
          12288 * Real.sqrt (2 * (2 * Real.pi * x)) +
          (1 + 2 * Real.log (N : ℝ)) := plainKernelFarConst_le_log hN hT
    _ ≤ (35 * Real.log x) * (214 * (4 * Real.sqrt x)) +
          12288 * (4 * Real.sqrt x) + 7 * Real.log x := by
      gcongr <;> linarith
    _ ≤ 80000 * Real.sqrt x * Real.log x := by
      nlinarith

/-- One exact harmonic product cost with the cofactor coefficient energy reduced to its explicit
`Q_j / A₀` scale. -/
theorem menonHarmonicProductCostVolume_le
    (P : Finset ℕ) {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q eta W V volE : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hvolE : 0 ≤ volE) (j : ℕ) :
    menonHarmonicProductCostVolume P A₀ B₀ Q eta W V volE j ≤
      V ^ 2 * ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volE) *
            ((((Q * (1 + eta) ^ j) * (1 + eta)) / (A₀ : ℝ)) ^ 2 *
              ((B₀ : ℝ) / (Q * (1 + eta) ^ j) + 1)))) := by
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hvol : 0 ≤ 2 * Real.pi * volE := mul_nonneg (by positivity) hvolE
  have hmass : 0 ≤ hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
      (2 * Real.pi * W) (2 * Real.pi * volE) := hmMassRecip_nonneg _ hT hvol
  unfold menonHarmonicProductCostVolume
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg V)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (cofactorReciprocalCardFactor_le hA hQ heta j) hmass

/-- On Menon's literal shell, the exact cofactor coefficient energy is at most
`24 Q_j / x`.  This keeps both natural endpoint roundings on the left and uses only the true
geometric-block upper endpoint on the right. -/
theorem finalRangeCofactorReciprocalCardFactor_le
    {x Q eta : ℝ} (hx : 1 ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (j : ℕ) (hQjTop : Q * (1 + eta) ^ j ≤ 3 * x) :
    (1 / (⌈(⌈x⌉₊ : ℝ) /
        ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt ⌈x⌉₊ (menonFinalRangeTopNat x) Q eta j).card : ℝ) ≤
      24 * (Q * (1 + eta) ^ j) / x := by
  let q : ℝ := Q * (1 + eta) ^ j
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hceilPos : 0 < ⌈x⌉₊ := by
    rw [Nat.ceil_pos]
    exact hx0
  have hbase := cofactorReciprocalCardFactor_le
    (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x) hceilPos hQ heta j
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
  have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hnum : q * (1 + eta) ≤ 2 * q := by nlinarith
  have hratio : q * (1 + eta) / (⌈x⌉₊ : ℝ) ≤ 2 * q / x := by
    exact div_le_div₀ (by positivity) hnum hx0 hceil
  have hratio0 : 0 ≤ q * (1 + eta) / (⌈x⌉₊ : ℝ) := by positivity
  have hratioUpper0 : 0 ≤ 2 * q / x := by positivity
  have hcardFactor : ((menonFinalRangeTopNat x : ℕ) : ℝ) / q + 1 ≤
      3 * x / q + 1 := by
    linarith [div_le_div_of_nonneg_right htop hq0.le]
  have hcardFactor0 : 0 ≤ ((menonFinalRangeTopNat x : ℕ) : ℝ) / q + 1 := by positivity
  have hcardFactorUpper0 : 0 ≤ 3 * x / q + 1 := by positivity
  calc
    (1 / (⌈(⌈x⌉₊ : ℝ) /
        ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
        ((geomCofactorBlockAt ⌈x⌉₊ (menonFinalRangeTopNat x) Q eta j).card : ℝ) ≤
      (q * (1 + eta) / (⌈x⌉₊ : ℝ)) ^ 2 *
        (((menonFinalRangeTopNat x : ℕ) : ℝ) / q + 1) := by
          simpa only [q] using hbase
    _ ≤ (2 * q / x) ^ 2 * (3 * x / q + 1) := by gcongr
    _ ≤ 24 * q / x := by
      field_simp
      nlinarith
    _ = 24 * (Q * (1 + eta) ^ j) / x := by rfl

/-- Product-cost specialization for Menon's final shell.  All cofactor support geometry is reduced
to the factor `24 Q_j / x`; the exact reciprocal HM mass and exposed frequency-set volume remain. -/
theorem menonFinalRangeProductCostVolume_le
    {P : Finset ℕ} {x Q eta W V volE : ℝ} (hx : 1 ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) (hW : 1 ≤ W) (hvolE : 0 ≤ volE) (j : ℕ)
    (hQjTop : Q * (1 + eta) ^ j ≤ 3 * x) :
    menonHarmonicProductCostVolume P ⌈x⌉₊
        (menonFinalRangeTopNat x) Q eta W V volE j ≤
      V ^ 2 * ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volE) *
            (24 * (Q * (1 + eta) ^ j) / x))) := by
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hvol : 0 ≤ 2 * Real.pi * volE := mul_nonneg (by positivity) hvolE
  have hmass : 0 ≤ hmMassRecip
      ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊
      (2 * Real.pi * W) (2 * Real.pi * volE) := hmMassRecip_nonneg _ hT hvol
  unfold menonHarmonicProductCostVolume
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg V)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (finalRangeCofactorReciprocalCardFactor_le hx hQ heta heta1 j hQjTop) hmass

/-- After multiplication by `Q_j/x`, the diagonal and reciprocal-kernel logarithmic parts of the
final-range HM mass are independent of the cofactor length.  Only the exposed far-kernel measure
term retains `Q_j/x`. -/
theorem hmMassRecip_finalRange_mul_stepRatio_le
    {x q T volE : ℝ} (hx : 1 ≤ x) (hq : 0 < q) (hT : 1 ≤ T) :
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ T volE * q / x ≤
      6 + plainKernelFarConst ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ T * volE * q / x +
        144 * Real.pi * Real.log (2 + 2 * T) := by
  let N : ℕ := ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hfloor : (N : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) / q := by
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  have hNle : (N : ℝ) ≤ 3 * x / q :=
    hfloor.trans (div_le_div_of_nonneg_right htop hq.le)
  have hNq : (N : ℝ) * q ≤ 3 * x := (le_div_iff₀ hq).mp hNle
  have hNscale : (N : ℝ) * q / x ≤ 3 := by
    rw [div_le_iff₀ hx0]
    nlinarith
  have hNscale0 : 0 ≤ (N : ℝ) * q / x := by positivity
  have hfar : 0 ≤ plainKernelFarConst N T := plainKernelFarConst_nonneg N hT
  have hlog : 0 ≤ Real.log (2 + 2 * T) := Real.log_nonneg (by linarith)
  calc
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ T volE * q / x =
        2 * ((N : ℝ) * q / x) +
          plainKernelFarConst N T * volE * q / x +
          48 * Real.pi * ((N : ℝ) * q / x) * Real.log (2 + 2 * T) := by
      rw [hmMassRecip]
      dsimp only [N]
      ring
    _ ≤ 2 * 3 + plainKernelFarConst N T * volE * q / x +
        48 * Real.pi * 3 * Real.log (2 + 2 * T) := by gcongr
    _ = 6 + plainKernelFarConst ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ T * volE * q / x +
        144 * Real.pi * Real.log (2 + 2 * T) := by
      dsimp only [N]
      ring

/-- Final-shell reciprocal HM mass after the cofactor scale is inserted, with the far kernel
replaced by its uniform `80000 √x log x` majorant. -/
theorem hmMassRecip_finalRange_mul_stepRatio_le_explicit
    {x q volE : ℝ} (hx : Real.exp 1 ≤ x) (hq : 1 ≤ q) (hvolE : 0 ≤ volE)
    (hN : 1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊) :
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
        (2 * Real.pi * x) (2 * Real.pi * volE) * q / x ≤
      6 + 80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x)) := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hx1 : 1 ≤ x :=
    (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hx
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let N : ℕ := ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
  have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hfloor : (N : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) / q := by
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  have hdiv : (menonFinalRangeTopNat x : ℝ) / q ≤ 3 * x := by
    calc
      (menonFinalRangeTopNat x : ℝ) / q ≤ 3 * x / q :=
        div_le_div_of_nonneg_right htop hq0.le
      _ ≤ 3 * x := by
        rw [div_le_iff₀ hq0]
        nlinarith
  have hNreal : (N : ℝ) ≤ 3 * x := hfloor.trans hdiv
  have hfar := plainKernelFarConst_finalRange_le hx
    (N := N) (by simpa only [N] using hN) hNreal
  have hbase := hmMassRecip_finalRange_mul_stepRatio_le
    hx1 hq0 (by nlinarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi * x)
    (volE := 2 * Real.pi * volE)
  calc
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
        (2 * Real.pi * x) (2 * Real.pi * volE) * q / x ≤
      6 + plainKernelFarConst ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * x) * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x)) := hbase
    _ ≤ 6 + 80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x)) := by
      have hfac : 0 ≤ (2 * Real.pi * volE) * q / x := by positivity
      gcongr

/-- Complete scalar bound for one harmonic product on Menon's final shell.  It is uniform in the
designated prime set and exposes the exceptional-set measure only through
`√x log x · volE · Q_j/x`. -/
theorem menonFinalShellProductCostVolume_le_explicit
    {P : Finset ℕ} {x Q eta V volE : ℝ} (hx : Real.exp 1 ≤ x)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hvolE : 0 ≤ volE)
    (j : ℕ) (hQjOne : 1 ≤ Q * (1 + eta) ^ j)
    (hQjTop : Q * (1 + eta) ^ j ≤ 3 * x)
    (hN : 1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta x V volE j ≤
      V ^ 2 * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) *
            (Q * (1 + eta) ^ j) / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x))))) := by
  have hx1 : 1 ≤ x :=
    (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hx
  let q : ℝ := Q * (1 + eta) ^ j
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hbase := menonFinalRangeProductCostVolume_le
    (P := P) (V := V) (volE := volE) hx1 hQ heta heta1 hx1 hvolE j hQjTop
  have hmass := hmMassRecip_finalRange_mul_stepRatio_le_explicit
    hx (q := q) (volE := volE) (by simpa only [q] using hQjOne) hvolE
      (by simpa only [q] using hN)
  have hmass0 : 0 ≤ hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
      (2 * Real.pi * x) (2 * Real.pi * volE) := by
    exact hmMassRecip_nonneg _ (by nlinarith [Real.pi_gt_three]) (by positivity)
  calc
    menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta x V volE j ≤
      V ^ 2 * ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * x) (2 * Real.pi * volE) * (24 * q / x))) := by
            simpa only [q] using hbase
    _ = V ^ 2 * ((2 * Real.pi)⁻¹ *
        (24 * (hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * x) (2 * Real.pi * volE) * q / x))) := by ring
    _ ≤ V ^ 2 * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) * q / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x))))) := by
      gcongr
    _ = V ^ 2 * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) *
            (Q * (1 + eta) ^ j) / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x))))) := by rfl

end

end RHTower.Sieve
