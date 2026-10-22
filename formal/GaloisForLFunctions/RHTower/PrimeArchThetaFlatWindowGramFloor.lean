import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoAtomHankelDominance
import GaloisForLFunctions.HTGeometry.WeightedMonicQuadraticHalfWindow

/-!
# Quantitative flat-window floor of the literal theta source

The completed source is decreasing on the positive half-line, so its endpoint value is the
largest constant floor on `(0,R]`. The exact flat-window Hankel determinant gives an explicit
positive residual floor for the K-RVM fifth-moment Schur complement. The weighted monic quadratic
extremal inequality supplies an independent variational interpretation of its degree-two factor.
-/

open MeasureTheory Set
namespace RHTower
noncomputable section

open HedenmalmThetaSource

private theorem thetaCuspFullSource_antitoneOn :
    AntitoneOn thetaCuspFullSource (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  · have hprod := strictAntiOn_thetaCuspFullSource_mul_reflect 0 hs ht hst
    simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at hprod
    nlinarith [thetaCuspFullSource_pos_all s, thetaCuspFullSource_pos_all t]

/-- The endpoint value is the maximal constant minorant of the source on a positive window. -/
theorem thetaCuspFullSource_ge_endpoint
    {R x : ℝ} (hx : 0 < x) (hxR : x ≤ R) :
    thetaCuspFullSource R ≤ thetaCuspFullSource x :=
  thetaCuspFullSource_antitoneOn hx.le (hx.trans_le hxR).le hxR

/-- A pointwise source floor on every positive finite window. -/
theorem thetaCuspFullSource_ge_flatWindow
    {R x : ℝ} (hx : 0 < x) (hxR : x ≤ R) :
    thetaEnvelopeLower * Real.exp (-Real.pi * Real.exp (2 * R)) ≤
      thetaCuspFullSource x := by
  have hbase := thetaCuspFullSource_ge_envelope hx
  have hlower : 0 ≤ thetaEnvelopeLower := thetaEnvelopeLower_pos.le
  have hrates : Real.exp (2 * x) ≤ Real.exp (2 * R) :=
    Real.exp_le_exp.mpr (by linarith)
  have hneg : -Real.pi * Real.exp (2 * R) ≤
      -Real.pi * Real.exp (2 * x) := by
    nlinarith [mul_le_mul_of_nonneg_left hrates Real.pi_pos.le]
  have hExp : Real.exp (-Real.pi * Real.exp (2 * R)) ≤
      Real.exp (-Real.pi * Real.exp (2 * x)) := Real.exp_le_exp.mpr hneg
  have hOne : 1 ≤ Real.exp (9 * x / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hProd : Real.exp (-Real.pi * Real.exp (2 * x)) ≤
      Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hOne)
      (Real.exp_pos (-Real.pi * Real.exp (2 * x))).le]
  calc
    thetaEnvelopeLower * Real.exp (-Real.pi * Real.exp (2 * R)) ≤
        thetaEnvelopeLower * Real.exp (-Real.pi * Real.exp (2 * x)) :=
          mul_le_mul_of_nonneg_left hExp hlower
    _ ≤ thetaEnvelopeLower * thetaEnvelope x := by
      rw [thetaEnvelope]
      exact mul_le_mul_of_nonneg_left hProd hlower
    _ ≤ thetaCuspFullSource x := hbase

/-- Constant lower density obtained from the completed theta envelope on `(0,R]`. -/
def thetaCuspFlatWindowFloor (R : ℝ) : ℝ :=
  thetaCuspFullSource R

theorem thetaCuspFlatWindowFloor_pos (R : ℝ) :
    0 < thetaCuspFlatWindowFloor R := by
  exact thetaCuspFullSource_pos_all R

/-- The flat source supported on the finite positive half-window. -/
def thetaCuspFlatWindowWeight (R x : ℝ) : ℝ :=
  if x ∈ Ioc 0 R then thetaCuspFlatWindowFloor R else 0

theorem thetaCuspFlatWindowWeight_nonneg (R x : ℝ) :
    0 ≤ thetaCuspFlatWindowWeight R x := by
  by_cases hx : x ∈ Ioc 0 R
  · simp [thetaCuspFlatWindowWeight, hx, (thetaCuspFlatWindowFloor_pos R).le]
  · simp [thetaCuspFlatWindowWeight, hx]

theorem thetaCuspFlatWindowWeight_le_full (R : ℝ) {x : ℝ} (hx : 0 < x) :
    thetaCuspFlatWindowWeight R x ≤ thetaCuspFullSource x := by
  by_cases hw : x ∈ Ioc 0 R
  · simpa only [thetaCuspFlatWindowWeight, if_pos hw, thetaCuspFlatWindowFloor] using
      thetaCuspFullSource_ge_endpoint hx hw.2
  · simp only [thetaCuspFlatWindowWeight, if_neg hw]
    exact (thetaCuspFullSource_pos_of_pos hx).le

private theorem thetaCuspFlatWindowWeight_moment_integrable (R : ℝ) (j : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) * thetaCuspFlatWindowWeight R x) (Ioi 0) := by
  have hcont : Continuous (fun x : ℝ =>
      thetaCuspFlatWindowFloor R * x ^ (2 * j)) := by fun_prop
  have hbase : IntegrableOn (fun x : ℝ =>
      thetaCuspFlatWindowFloor R * x ^ (2 * j)) (Ioc 0 R) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfun : (fun x : ℝ => x ^ (2 * j) * thetaCuspFlatWindowWeight R x) =
      (Ioc 0 R).indicator (fun x => thetaCuspFlatWindowFloor R * x ^ (2 * j)) := by
    funext x
    by_cases hx : x ∈ Ioc 0 R
    · simp [thetaCuspFlatWindowWeight, hx, Set.indicator]; ring
    · simp [thetaCuspFlatWindowWeight, hx, Set.indicator]
  rw [hfun]
  exact (hbase.integrable_indicator measurableSet_Ioc).integrableOn

/-- The completed theta source dominates the constant-window model at every shifted
Hankel determinant size. -/
theorem thetaCuspFlatWindow_shiftedRawHankel_det_le_full (R : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (weightedRawEvenMoment (thetaCuspFlatWindowWeight R) ∘ Nat.succ) n).det ≤
    (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + 1)) n).det := by
  have hmono := weightedShiftedHankel_det_mono
    (thetaCuspFlatWindowWeight R) thetaCuspFullSource n
    (thetaCuspFlatWindowWeight_moment_integrable R)
    (fun j => integrableOn_thetaCuspRawMoment (2 * j))
    (fun x hx => thetaCuspFlatWindowWeight_nonneg R x)
    (fun x hx => sub_nonneg.mpr (thetaCuspFlatWindowWeight_le_full R hx))
  convert hmono using 1
  rfl

/-- Exact even moment of the constant density on `(0,R]`. -/
theorem thetaCuspFlatWindow_rawEvenMoment (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    weightedRawEvenMoment (thetaCuspFlatWindowWeight R) j =
      2 * thetaCuspFlatWindowFloor R * R ^ (2 * j + 1) / (2 * j + 1) := by
  have hfun : (fun x : ℝ => x ^ (2 * j) * thetaCuspFlatWindowWeight R x) =
      (Ioc 0 R).indicator (fun x => thetaCuspFlatWindowFloor R * x ^ (2 * j)) := by
    funext x
    by_cases hx : x ∈ Ioc 0 R
    · simp [thetaCuspFlatWindowWeight, hx, Set.indicator]; ring
    · simp [thetaCuspFlatWindowWeight, hx, Set.indicator]
  have hset : Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R := by
    ext x
    simp [Set.mem_Ioi, Set.mem_Ioc]
  unfold weightedRawEvenMoment
  rw [hfun, setIntegral_indicator measurableSet_Ioc, hset]
  rw [← intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  norm_num
  ring

/-- The flat-window size-three shifted determinant has a sharp closed form. -/
theorem thetaCuspFlatWindow_shiftedRawHankel_three_det
    (R : ℝ) (hR : 0 ≤ R) :
    (HTGeometry.momentHankelMatrix
      (weightedRawEvenMoment (thetaCuspFlatWindowWeight R) ∘ Nat.succ) 3).det =
      (2048 / 22920975 : ℝ) *
        thetaCuspFlatWindowFloor R ^ (3 : ℕ) * R ^ (21 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp only [HTGeometry.momentHankelMatrix, Function.comp_apply,
    thetaCuspFlatWindow_rawEvenMoment R hR]
  norm_num
  ring

/-- Explicit unconditional positive lower bound for the literal source's first open shifted
raw determinant. -/
theorem thetaCuspRawEvenMoment_shiftedHankel_three_det_ge_flatWindow
    (R : ℝ) (hR : 0 ≤ R) :
    (2048 / 22920975 : ℝ) *
      thetaCuspFlatWindowFloor R ^ (3 : ℕ) * R ^ (21 : ℕ) ≤
    (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + 1)) 3).det := by
  rw [← thetaCuspFlatWindow_shiftedRawHankel_three_det R hR]
  exact thetaCuspFlatWindow_shiftedRawHankel_det_le_full R 3

/-- An explicit normalized floor for the exact fifth-moment residual in K-RVM. -/
theorem thetaCuspNormalizedEvenMoment_shiftedDelta_ge_flatWindow
    (R : ℝ) (hR : 0 ≤ R) :
    (thetaCuspRawEvenMoment 0)⁻¹ ^ (3 : ℕ) *
      ((2048 / 22920975 : ℝ) *
        thetaCuspFlatWindowFloor R ^ (3 : ℕ) * R ^ (21 : ℕ)) ≤
    (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
      thetaCuspNormalizedEvenMoment 2 ^ 2) * thetaCuspNormalizedEvenMoment 5 -
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 ^ 2 -
        2 * thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 *
          thetaCuspNormalizedEvenMoment 4 +
        thetaCuspNormalizedEvenMoment 3 ^ 3) := by
  let Raw : Matrix (Fin 3) (Fin 3) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + 1)) 3
  let Norm : Matrix (Fin 3) (Fin 3) ℝ :=
    HTGeometry.momentHankelMatrix
      (fun j => thetaCuspNormalizedEvenMoment (j + 1)) 3
  have hEq : Norm = (thetaCuspRawEvenMoment 0)⁻¹ • Raw := by
    ext i j
    change thetaCuspRawEvenMoment ((i : ℕ) + (j : ℕ) + 1) /
      thetaCuspRawEvenMoment 0 =
        (thetaCuspRawEvenMoment 0)⁻¹ *
          thetaCuspRawEvenMoment ((i : ℕ) + (j : ℕ) + 1)
    rw [div_eq_mul_inv]
    ring
  have hraw := thetaCuspRawEvenMoment_shiftedHankel_three_det_ge_flatWindow R hR
  have hfactor : 0 ≤ (thetaCuspRawEvenMoment 0)⁻¹ ^ (3 : ℕ) := by
    exact (pow_pos (inv_pos.mpr thetaCuspRawEvenMoment_zero_pos) _).le
  have hNorm : (thetaCuspRawEvenMoment 0)⁻¹ ^ (3 : ℕ) *
      ((2048 / 22920975 : ℝ) *
        thetaCuspFlatWindowFloor R ^ (3 : ℕ) * R ^ (21 : ℕ)) ≤ Norm.det := by
    rw [hEq, Matrix.det_smul]
    exact mul_le_mul_of_nonneg_left hraw hfactor
  have hDelta : Norm.det =
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
        thetaCuspNormalizedEvenMoment 2 ^ 2) * thetaCuspNormalizedEvenMoment 5 -
        (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 ^ 2 -
          2 * thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 *
            thetaCuspNormalizedEvenMoment 4 +
          thetaCuspNormalizedEvenMoment 3 ^ 3) := by
    dsimp [Norm]
    rw [Matrix.det_fin_three]
    simp only [HTGeometry.momentHankelMatrix]
    norm_num
    ring
  rw [hDelta] at hNorm
  exact hNorm

end
end RHTower
