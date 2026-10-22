import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeCesaroAnchoredMoment

/-!
# Literal logarithmic polar-cell quadrature for critical CCM-FU

This module treats only the deterministic polar side of the critical CCM-FU reporter.  Its cells
are the literal intervals `log (k - 1)..log k`, not the atom-mass-centred matched cells used by
the rectangular transport.  The Peano identity below therefore applies to the sole polar
normalization defect in the exact CCM-FU/marked-current bridge without touching its arithmetic
source.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Right-endpoint error of the literal outgoing polar logarithmic cell. -/
def ccmFUSuzukiCriticalOutgoingPolarCellError (H : ℝ) (k : ℕ) : ℝ :=
  (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) * Real.sqrt k *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k) -
    ∫ h in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h

/-- Derivative of the outgoing half-polar profile on a positive logarithmic cell. -/
def ccmFUSuzukiCriticalOutgoingPolarCellDerivative (H h : ℝ) : ℝ :=
  Real.exp (h / 2) *
    (ccmGuinandWeilThirdGradeCesaroTriangularWeight H h / 2 -
      ccmGuinandWeilThirdGradeCesaroErrorKernel H h)

/-- The literal outgoing polar profile is integrable on every physical logarithmic cell. -/
theorem intervalIntegrable_ccmFU_outgoingPolarProfile_log_cell
    (H : ℝ) {k : ℕ} (hk : 3 ≤ k) :
    IntervalIntegrable (fun h : ℝ => Real.exp (h / 2) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume
      (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ)) := by
  have hpredpos : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlogle : Real.log ((k - 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    (Real.log_le_log_iff hpredpos hkpos).mpr (by exact_mod_cast (Nat.sub_le k 1))
  have hcont : ContinuousOn (fun h : ℝ => Real.exp (h / 2) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h)
      (Icc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
    intro h hh
    have hlogpos : 0 < Real.log ((k - 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k - 1))
    have hhpos : 0 < h := hlogpos.trans_le hh.1
    exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousAt.mul
      (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
        (ne_of_gt hhpos)).continuousAt).continuousWithinAt)
  have hcont' : ContinuousOn (fun h : ℝ => Real.exp (h / 2) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h)
      (uIcc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
    simpa only [uIcc_of_le hlogle] using hcont
  exact hcont'.intervalIntegrable

/-- Consecutive literal outgoing polar cells tile their logarithmic interval exactly. -/
theorem sum_range_ccmFU_outgoingPolar_log_cells
    (H : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ h in Real.log ((j + 2 : ℕ) : ℝ)..Real.log ((j + 3 : ℕ) : ℝ),
        Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) =
      ∫ h in Real.log (2 : ℝ)..Real.log ((N + 2 : ℕ) : ℝ),
        Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
  let a : ℕ → ℝ := fun j => Real.log ((j + 2 : ℕ) : ℝ)
  let f : ℝ → ℝ := fun h => Real.exp (h / 2) *
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H h
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (f := f) (n := N) (fun j _ => by
      have hleft : j + 3 - 1 = j + 2 := by omega
      have hright : j + 1 + 2 = j + 3 := by omega
      simpa only [a, f, hleft, hright] using
        (intervalIntegrable_ccmFU_outgoingPolarProfile_log_cell H
          (k := j + 3) (by omega : 3 ≤ j + 3)))
  change
    (∑ j ∈ Finset.range N,
      ∫ h in Real.log ((j + 2 : ℕ) : ℝ)..Real.log ((j + 3 : ℕ) : ℝ),
        Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) = _
  change _ =
    ∫ h in Real.log ((0 + 2 : ℕ) : ℝ)..Real.log ((N + 2 : ℕ) : ℝ),
      Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h
  rw [← hsum]

/-- The exact Peano-kernel form of one literal outgoing polar cell.  The squared logarithmic
mesh-width is therefore the available deterministic summability mechanism. -/
theorem ccmFUSuzukiCriticalOutgoingPolarCellError_eq_peano
    (H : ℝ) {k : ℕ} (hk : 3 ≤ k) :
    ccmFUSuzukiCriticalOutgoingPolarCellError H k =
      ∫ h in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        (h - Real.log ((k - 1 : ℕ) : ℝ)) *
          ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h := by
  let r : ℝ := Real.log ((k - 1 : ℕ) : ℝ)
  let s : ℝ := Real.log (k : ℝ)
  let W : ℝ → ℝ := ccmGuinandWeilThirdGradeCesaroTriangularWeight H
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * W h
  let D : ℝ → ℝ := ccmFUSuzukiCriticalOutgoingPolarCellDerivative H
  have hkm1pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkm1lt : (k - 1 : ℕ) < k := by omega
  have hrs : r ≤ s := (Real.log_lt_log hkm1pos (by exact_mod_cast hkm1lt)).le
  have hrpos : 0 < r := by
    dsimp only [r]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < k - 1))
  have hG : ∀ h ∈ Set.uIcc r s, HasDerivAt G (D h) h := by
    intro h hh
    have hhr : r ≤ h := by
      rw [Set.uIcc_of_le hrs] at hh
      exact hh.1
    have hh0 : h ≠ 0 := ne_of_gt (hrpos.trans_le hhr)
    have hExp : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
        (Real.exp (h / 2) * (1 / 2)) h := by
      have hinner : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) h := by
        simpa using (hasDerivAt_id h).div_const 2
      simpa using hinner.exp
    have hW : HasDerivAt W (-ccmGuinandWeilThirdGradeCesaroErrorKernel H h) h :=
      hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight hh0
    apply (hExp.mul hW).congr_deriv
    dsimp only [G, D, W, ccmFUSuzukiCriticalOutgoingPolarCellDerivative]
    ring
  have hU : ∀ h ∈ Set.uIcc r s,
      HasDerivAt (fun y : ℝ => y - r) 1 h := by
    intro h hh
    simpa using (hasDerivAt_id h).sub_const r
  have hUint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume r s :=
    intervalIntegrable_const
  have hDcont : ContinuousOn D (Set.uIcc r s) := by
    intro h hh
    have hhr : r ≤ h := by
      rw [Set.uIcc_of_le hrs] at hh
      exact hh.1
    have hh0 : h ≠ 0 := ne_of_gt (hrpos.trans_le hhr)
    have hWcont : ContinuousAt W h :=
      (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight hh0).continuousAt
    have hKcont : ContinuousAt (ccmGuinandWeilThirdGradeCesaroErrorKernel H) h := by
      unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
      exact (continuousAt_const.sub ((continuousAt_const.mul continuousAt_id).div_const H)).div
        (continuousAt_id.pow 4) (pow_ne_zero 4 hh0)
    have hExpCont : ContinuousAt (fun x : ℝ => Real.exp (x / 2)) h := by fun_prop
    dsimp only [D, ccmFUSuzukiCriticalOutgoingPolarCellDerivative]
    exact (hExpCont.mul ((hWcont.div_const 2).sub hKcont)).continuousWithinAt
  have hDint : IntervalIntegrable D volume r s := hDcont.intervalIntegrable
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hG hUint hDint
  have hsqrt : Real.exp (s / 2) = Real.sqrt k := by
    dsimp only [s]
    rw [← Real.log_sqrt hkpos.le, Real.exp_log (Real.sqrt_pos.mpr hkpos)]
  unfold ccmFUSuzukiCriticalOutgoingPolarCellError
  change (s - r) * Real.sqrt k * W s - (∫ h in r..s, G h) =
    ∫ h in r..s, (h - r) * D h
  rw [← hsqrt]
  calc
    (s - r) * Real.exp (s / 2) * W s - (∫ h in r..s, G h) =
      (s - r) * G s - (0 : ℝ) * G r - ∫ h in r..s, (1 : ℝ) * G h := by
        simp only [G, zero_mul, one_mul]
        ring
    _ = ∫ h in r..s, (h - r) * D h := by simpa using hip.symm

/-- The width of a literal logarithmic cell is positive and is controlled by its left reciprocal
integer scale. -/
theorem log_nat_step_nonneg_le_inv_pred {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) ∧
      Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) ≤
        1 / ((k - 1 : ℕ) : ℝ) := by
  have hpredpos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hpredpos (by exact_mod_cast (by omega : k - 1 ≤ k)))
  · rw [← Real.log_div hkpos.ne' hpredpos.ne']
    calc
      Real.log ((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤
          (k : ℝ) / ((k - 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hkpos hpredpos)
      _ = 1 / ((k - 1 : ℕ) : ℝ) := by
        have hstep : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          norm_num
        field_simp [hpredpos.ne']
        linarith

/-- On the physical triangular window the third-grade reporter is nonnegative and has a fixed
lower-wall bound. -/
theorem ccmFU_triangular_weight_nonneg_le_32
    {H h : ℝ} (hH : 2 ≤ H) (hh : 1 ≤ h) (hhH : h ≤ H) :
    0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ∧
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ≤ 32 := by
  have hH0 : 0 < H := by linarith
  have hh0 : 0 < h := by linarith
  have hfac0 : 0 ≤ 1 - h / H := by
    rw [sub_nonneg, div_le_one hH0]
    exact hhH
  have hfac1 : 1 - h / H ≤ 1 := by
    have : 0 ≤ h / H := by positivity
    linarith
  have hpow : 1 ≤ h ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hh 3
  have hbase0 : 0 ≤ 32 / h ^ 3 := by positivity
  have hbase : 32 / h ^ 3 ≤ 32 := by
    rw [div_le_iff₀ (pow_pos hh0 3)]
    nlinarith
  unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  constructor
  · exact mul_nonneg hbase0 hfac0
  · calc
      (32 / h ^ 3) * (1 - h / H) ≤ 32 * (1 - h / H) :=
        mul_le_mul_of_nonneg_right hbase hfac0
      _ ≤ 32 * 1 := mul_le_mul_of_nonneg_left hfac1 (by norm_num)
      _ = 32 := by ring

/-- The forced triangular error kernel has a fixed physical-cell envelope. -/
theorem ccmFU_triangular_errorKernel_nonneg_le_96
    {H h : ℝ} (hH : 2 ≤ H) (hh : 1 ≤ h) (hhH : h ≤ H) :
    0 ≤ ccmGuinandWeilThirdGradeCesaroErrorKernel H h ∧
      ccmGuinandWeilThirdGradeCesaroErrorKernel H h ≤ 96 := by
  have hH0 : 0 < H := by linarith
  have hh0 : 0 < h := by linarith
  have hq0 : 0 ≤ 64 * h / H := by positivity
  have hq1 : 64 * h / H ≤ 64 := by
    rw [div_le_iff₀ hH0]
    nlinarith
  have hnum0 : 0 ≤ 96 - 64 * h / H := by linarith
  have hnum : 96 - 64 * h / H ≤ 96 := by linarith
  have hpow : 1 ≤ h ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hh 4
  unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
  constructor
  · exact div_nonneg hnum0 (pow_nonneg hh0.le 4)
  · have hden0 : 0 < h ^ 4 := pow_pos hh0 4
    rw [div_le_iff₀ hden0]
    nlinarith

/-- The literal outgoing Peano derivative is controlled by the critical half-density with a
fixed physical-cell constant. -/
theorem abs_ccmFU_outgoingPolarCellDerivative_le
    {H h : ℝ} (hH : 2 ≤ H) (hh : 1 ≤ h) (hhH : h ≤ H) :
    |ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h| ≤
      112 * Real.exp (h / 2) := by
  obtain ⟨hW0, hW⟩ := ccmFU_triangular_weight_nonneg_le_32 hH hh hhH
  obtain ⟨hK0, hK⟩ := ccmFU_triangular_errorKernel_nonneg_le_96 hH hh hhH
  unfold ccmFUSuzukiCriticalOutgoingPolarCellDerivative
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (h / 2) *
        |ccmGuinandWeilThirdGradeCesaroTriangularWeight H h / 2 -
          ccmGuinandWeilThirdGradeCesaroErrorKernel H h| ≤
      Real.exp (h / 2) *
        (|ccmGuinandWeilThirdGradeCesaroTriangularWeight H h / 2| +
          |ccmGuinandWeilThirdGradeCesaroErrorKernel H h|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.exp_pos _).le
    _ = Real.exp (h / 2) *
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H h / 2 +
          ccmGuinandWeilThirdGradeCesaroErrorKernel H h) := by
        rw [abs_of_nonneg (div_nonneg hW0 (by norm_num)), abs_of_nonneg hK0]
    _ ≤ Real.exp (h / 2) * (32 / 2 + 96) := by gcongr
    _ = 112 * Real.exp (h / 2) := by ring

private theorem exp_half_log_nat {k : ℕ} (hk : 0 < k) :
    Real.exp (Real.log (k : ℝ) / 2) = Real.sqrt k := by
  rw [← Real.log_sqrt (by exact_mod_cast hk.le), Real.exp_log]
  exact Real.sqrt_pos.mpr (by exact_mod_cast hk)

private theorem rpow_neg_three_halves_mul_sqrt (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) * Real.sqrt x = x⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  convert Real.rpow_neg_one x using 1 <;> ring

private theorem inv_mul_sqrt_eq_rpow_neg_three_halves (x : ℝ) (hx : 0 < x) :
    1 / (x * Real.sqrt x) = x ^ (-(3 / 2 : ℝ)) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hr := rpow_neg_three_halves_mul_sqrt x hx
  apply (div_eq_iff (mul_ne_zero hx.ne' hs)).2
  calc
    1 = x * x⁻¹ := by field_simp
    _ = x * (x ^ (-(3 / 2 : ℝ)) * Real.sqrt x) := by rw [hr]
    _ = x ^ (-(3 / 2 : ℝ)) * (x * Real.sqrt x) := by ring

/-- Every outgoing logarithmic polar cell after the fixed physical edge has a summable
`(k - 1)⁻³ᐟ²` error envelope. This controls only deterministic quadrature; it never separates
the prime--polar arithmetic source. -/
theorem abs_ccmFU_outgoingPolarCellError_le_majorant
    {H : ℝ} (hH : 2 ≤ H) {k : ℕ} (hk : 4 ≤ k)
    (hkH : Real.log (k : ℝ) ≤ H) :
    |ccmFUSuzukiCriticalOutgoingPolarCellError H k| ≤
      224 * (((k - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := Real.log ((k - 1 : ℕ) : ℝ)
  let s : ℝ := Real.log (k : ℝ)
  let delta : ℝ := s - r
  have hpred3 : 3 ≤ k - 1 := by omega
  have hpredpos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hrs : r ≤ s :=
    (Real.log_lt_log hpredpos (by exact_mod_cast (by omega : k - 1 < k))).le
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    calc
      1 ≤ Real.log (3 : ℝ) :=
        ((Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three).le
      _ ≤ Real.log ((k - 1 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hpred3)
  have hsH : s ≤ H := by simpa only [s] using hkH
  have hdelta0 : 0 ≤ delta := sub_nonneg.mpr hrs
  have hdelta : delta ≤ 1 / ((k - 1 : ℕ) : ℝ) := by
    dsimp only [delta, r, s]
    exact (log_nat_step_nonneg_le_inv_pred (by omega)).2
  rw [ccmFUSuzukiCriticalOutgoingPolarCellError_eq_peano H (by omega : 3 ≤ k)]
  have hpoint : ∀ h ∈ Set.uIoc r s,
      ‖(h - r) * ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h‖ ≤
        112 * delta * Real.sqrt k := by
    intro h hh
    rw [Set.uIoc_of_le hrs] at hh
    have hhr0 : 0 ≤ h - r := sub_nonneg.mpr hh.1.le
    have hhrs : h - r ≤ delta := by
      dsimp only [delta]
      exact sub_le_sub_right hh.2 r
    have hh1 : 1 ≤ h := hr1.trans hh.1.le
    have hhH : h ≤ H := hh.2.trans hsH
    have hderiv := abs_ccmFU_outgoingPolarCellDerivative_le hH hh1 hhH
    have hexp : Real.exp (h / 2) ≤ Real.sqrt k := by
      rw [← exp_half_log_nat (by omega : 0 < k)]
      apply Real.exp_le_exp.mpr
      calc
        h / 2 ≤ s / 2 := by linarith [hh.2]
        _ = Real.log (k : ℝ) / 2 := by rfl
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hhr0]
    calc
      (h - r) * |ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h| ≤
          (h - r) * (112 * Real.exp (h / 2)) :=
        mul_le_mul_of_nonneg_left hderiv hhr0
      _ ≤ delta * (112 * Real.sqrt k) := by gcongr
      _ = 112 * delta * Real.sqrt k := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [Real.norm_eq_abs, abs_of_nonneg hdelta0] at hint
  have hinterr :
      |∫ h in r..s,
          (h - r) * ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h| ≤
        (112 * delta * Real.sqrt k) * delta := by
    simpa only [sub_eq_add_neg, add_sub_cancel_left] using hint
  have hroot : Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
    have hsqk : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (by positivity)
    have hsqpred : Real.sqrt ((k - 1 : ℕ) : ℝ) ^ 2 = (k - 1 : ℕ) :=
      Real.sq_sqrt (by positivity)
    have hkpNat : k ≤ 2 * (k - 1) := by omega
    have hkp : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hkpNat
    nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg ((k - 1 : ℕ) : ℝ)]
  have hmajor :
      (112 * (1 / ((k - 1 : ℕ) : ℝ)) * Real.sqrt k) *
          (1 / ((k - 1 : ℕ) : ℝ)) ≤
        224 * (1 / (((k - 1 : ℕ) : ℝ) * Real.sqrt ((k - 1 : ℕ) : ℝ))) := by
    calc
      (112 * (1 / ((k - 1 : ℕ) : ℝ)) * Real.sqrt k) *
          (1 / ((k - 1 : ℕ) : ℝ)) =
          112 * Real.sqrt k / (((k - 1 : ℕ) : ℝ) ^ 2) := by
            field_simp [hpredpos.ne']
      _ ≤ 112 * (2 * Real.sqrt ((k - 1 : ℕ) : ℝ)) /
          (((k - 1 : ℕ) : ℝ) ^ 2) := by gcongr
      _ = 224 * (1 / (((k - 1 : ℕ) : ℝ) * Real.sqrt ((k - 1 : ℕ) : ℝ))) := by
          have hsq : Real.sqrt ((k - 1 : ℕ) : ℝ) ^ 2 = (k - 1 : ℕ) :=
            Real.sq_sqrt hpredpos.le
          field_simp [hpredpos.ne', (Real.sqrt_pos.2 hpredpos).ne']
          nlinarith
  change |∫ h in r..s,
      (h - r) * ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h| ≤
    224 * (((k - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
  calc
    |∫ h in r..s,
        (h - r) * ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h| ≤
      (112 * delta * Real.sqrt k) * delta := hinterr
    _ ≤ (112 * (1 / ((k - 1 : ℕ) : ℝ)) * Real.sqrt k) *
        (1 / ((k - 1 : ℕ) : ℝ)) := by gcongr
    _ ≤ 224 * (1 / (((k - 1 : ℕ) : ℝ) * Real.sqrt ((k - 1 : ℕ) : ℝ))) := hmajor
    _ = 224 * (((k - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [inv_mul_sqrt_eq_rpow_neg_three_halves _ hpredpos]

/-- Any finite family of physical outgoing cells has a horizon-independent budget.  This is a
pure quadrature statement: it controls the deterministic polar seam after the literal signed
prime--polar action has already been kept intact. -/
theorem abs_sum_ccmFU_outgoingPolarCellError_le_tsum
    {H : ℝ} (hH : 2 ≤ H) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 4 ≤ k ∧ Real.log (k : ℝ) ≤ H) :
    |∑ k ∈ s, ccmFUSuzukiCriticalOutgoingPolarCellError H k| ≤
      224 * ∑' n : ℕ, (((n - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let G : ℕ → ℝ := fun n => ((n - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  let M : ℕ → ℝ := fun n => 224 * G n
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hG : Summable G := by
    apply Summable.comp_nat_add (k := 1)
    simpa only [G, Nat.add_sub_cancel] using hbase
  have hM : Summable M := hG.mul_left 224
  calc
    |∑ k ∈ s, ccmFUSuzukiCriticalOutgoingPolarCellError H k| ≤
        ∑ k ∈ s, |ccmFUSuzukiCriticalOutgoingPolarCellError H k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, M k := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_ccmFU_outgoingPolarCellError_le_majorant hH (hs k hk).1 (hs k hk).2
    _ ≤ ∑' n : ℕ, M n := hM.sum_le_tsum s (by
      intro n _
      dsimp only [M]
      positivity)
    _ = 224 * ∑' n : ℕ, (((n - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      dsimp only [M, G]
      rw [tsum_mul_left]

/-- The `k ≥ 4` literal cells retain the same uniform summability budget after reindexing from
their checkpoint labels. -/
theorem abs_sum_range_ccmFU_outgoingPolarCellError_shift_four_le_tsum
    {H : ℝ} (hH : 2 ≤ H) (n : ℕ)
    (hlog : ∀ j ∈ Finset.range n, Real.log ((j + 4 : ℕ) : ℝ) ≤ H) :
    |∑ j ∈ Finset.range n, ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4)| ≤
      224 * ∑' m : ℕ, (((m - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let s : Finset ℕ := (Finset.range n).image (fun j : ℕ => j + 4)
  have hinj : Set.InjOn (fun j : ℕ => j + 4) (↑(Finset.range n) : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  have hs : ∀ k ∈ s, 4 ≤ k ∧ Real.log (k : ℝ) ≤ H := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact ⟨by omega, hlog j hj⟩
  have hbound := abs_sum_ccmFU_outgoingPolarCellError_le_tsum hH s hs
  have hsum := Finset.sum_image (f := fun k : ℕ =>
    ccmFUSuzukiCriticalOutgoingPolarCellError H k) hinj
  change |∑ j ∈ Finset.range n, ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4)| ≤ _
  rw [← hsum]
  exact hbound

end GaloisForLFunctions.RHTower
