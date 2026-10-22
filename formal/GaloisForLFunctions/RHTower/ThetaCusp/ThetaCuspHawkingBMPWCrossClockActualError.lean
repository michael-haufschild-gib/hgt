import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedParticularCuspFlux
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCrossClockErrorTransfer
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalCuspCutoff
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceAngularAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticResponseCuspPair

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open RHTower RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMMixedParticularCuspFlux
open RHTower.D4BMPWThreePowerDominance
open RHTower.D4BMPWCrossClockErrorTransfer
open RHTower.D4BMModularCore RHTower.D4BMJointSource
open RHTower.D4BMAngularSeries
open RHTower.D4BMCuspResponse

namespace RHTower.D4BMPWCrossClockActualError
noncomputable section
set_option autoImplicit false

theorem cuspResponse_left_sharp_bound (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (b : Bool)
    (y : ℝ) (hy : 1 ≤ y) :
    ‖cuspResponse q b ![0,y]‖ ≤
      (‖responseCoefficient q b 0‖ + ‖responseCoefficient q b 1‖ +
        ‖responseCoefficient q b 2‖) * y ^ (2 - 2 * (q.1 : ℂ)).re := by
  have he : cuspResponse q b ![0,y] =
      reflectedThreePower (q.1 : ℂ)
        (responseCoefficient q b 0) (responseCoefficient q b 1)
        (responseCoefficient q b 2) y := by
    rw [cuspResponse_eq_sum]
    simp [Fin.sum_univ_three, sourcePower, reflectedThreePower]
  rw [he]
  exact reflectedThreePower_left_sharp_bound _ _ _ _ hleft y hy

/-- Real exponent of the reflected extreme cusp channel. -/
def beta (q : XiZeroCopy) : ℝ := (2 - 2 * (q.1 : ℂ)).re

/-- Globally bounded weight equal to `y⁻ᵝ` on the high cusp. -/
def weight (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  ((max 1 (z 1)) ^ (-beta q) : ℝ)

theorem beta_gt_one (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) : 1 < beta q := by
  dsimp [beta]
  norm_num [Complex.sub_re, Complex.mul_re]
  linarith

theorem weight_norm_le_one (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    ‖weight q z‖ ≤ 1 := by
  have hb : 1 ≤ max 1 (z 1) := le_max_left _ _
  have hp : 0 ≤ (max 1 (z 1)) ^ (-beta q) :=
    Real.rpow_nonneg (by linarith) _
  have hle : (max 1 (z 1)) ^ (-beta q) ≤ 1 := by
    calc
      _ ≤ (max 1 (z 1)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by
          have hs := xi_divisor_support_re_mem_open_unit q.1
          dsimp [beta]
          norm_num [Complex.sub_re, Complex.mul_re]
          linarith [hs.1, hs.2])
      _ = 1 := by simp
  simpa [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] using hle

theorem weight_continuous (q : XiZeroCopy) : Continuous (weight q) := by
  have hm : Continuous (fun z : Fin 2 → ℝ => max 1 (z 1)) :=
    continuous_const.max (continuous_apply 1)
  have hp : Continuous (fun z : Fin 2 → ℝ => (max 1 (z 1)) ^ (-beta q)) :=
    hm.rpow_const (by
      intro z
      left
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
  exact Complex.continuous_ofReal.comp hp

private theorem cuspResponse_same_height (q : XiZeroCopy) (b : Bool)
    (z : Fin 2 → ℝ) :
    cuspResponse q b z = cuspResponse q b ![0,z 1] := rfl

theorem weighted_cutoffResponse_memLp (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (b : Bool) :
    MemLp (fun z : UpperHalfPlane =>
      weight q (coordinates z) * cutoffResponse q b (coordinates z))
      2 measure := by
  let C : ℝ := ‖responseCoefficient q b 0‖ + ‖responseCoefficient q b 1‖ +
    ‖responseCoefficient q b 2‖
  have hc : ContinuousOn (fun z : Fin 2 → ℝ => weight q z * cutoffResponse q b z)
      domain := (weight_continuous q).continuousOn.mul
        (D4BMModularCore.cutoffResponse_contDiffOn q b).continuousOn
  apply cuspBound_memLp (fun z => weight q z * cutoffResponse q b z) hc C
  intro z hz
  have hy : 1 ≤ z 1 := by linarith
  have hypos : 0 < z 1 := by linarith
  have hcut : cutoff z = 1 := by
    simp only [cutoff]
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    norm_num
  have he : cutoffResponse q b z = cuspResponse q b ![0,z 1] := by
    rw [cutoffResponse,hcut,one_mul,cuspResponse_same_height]
  have hp : 0 ≤ (z 1) ^ (-beta q) := Real.rpow_nonneg hypos.le _
  have hnorm : ‖weight q z‖ = (z 1) ^ (-beta q) := by
    simp only [weight, max_eq_right hy, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp]
  have hk := cuspResponse_left_sharp_bound q hleft b (z 1) hy
  have hb : beta q = (2 - 2 * (q.1 : ℂ)).re := rfl
  calc
    ‖weight q z * cutoffResponse q b z‖ =
        (z 1) ^ (-beta q) * ‖cuspResponse q b ![0,z 1]‖ := by
      rw [norm_mul,hnorm,he]
    _ ≤ (z 1) ^ (-beta q) * (C * (z 1) ^ (beta q)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [C,beta] using hk) hp
    _ = C * ((z 1) ^ (-beta q) * (z 1) ^ (beta q)) := by ring
    _ = C := by
      rw [← Real.rpow_add hypos]
      simp

/-- The actual two-branch cusp decomposition has a weighted integrable cross
error in the original modular measure. -/
theorem actual_cross_error_integrable (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    Integrable (fun z : UpperHalfPlane => weight q (coordinates z) *
      ((cutoffResponse q true (coordinates z) + globalResponse q true z) *
          (cutoffResponse q false (coordinates z) + globalResponse q false z) -
        cutoffResponse q true (coordinates z) *
          cutoffResponse q false (coordinates z))) measure := by
  let K (b : Bool) : UpperHalfPlane → ℂ :=
    fun z => cutoffResponse q b (coordinates z)
  let R (b : Bool) : UpperHalfPlane → ℂ := globalResponse q b
  let w : UpperHalfPlane → ℂ := fun z => weight q (coordinates z)
  have hK (b : Bool) : MemLp (fun z => w z * K b z) 2 measure := by
    simpa only [w,K] using weighted_cutoffResponse_memLp q hleft b
  have hR (b : Bool) : MemLp (R b) 2 measure := by
    exact (memLp_congr_ae (globalResponse_native_ae q b)).mpr (Lp.memLp _)
  have hcoord : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hw : AEStronglyMeasurable w measure :=
    ((weight_continuous q).comp hcoord).aestronglyMeasurable
  have hwb : ∀ᵐ z ∂measure, ‖w z‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun z => weight_norm_le_one q (coordinates z))
  change Integrable (fun z => w z *
    ((K true z + R true z) * (K false z + R false z) - K true z * K false z)) measure
  exact weighted_cross_error_integrable measure (K true) (K false)
    (R true) (R false) w (hK true) (hK false) (hR true) (hR false) hw hwb

/-- In the literal high modular cusp, the two fields used above are exactly
the original full angular response and its particular-plus-native split. -/
theorem fullAngularField_high_cusp_decomposition (q : XiZeroCopy) (b : Bool)
    {x y : ℝ} (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) (hy : 3 < y) :
    fullAngularField q b ![x,y] =
      cutoffResponse q b ![x,y] + responsePlanar q b (point x y) := by
  let z : UpperHalfPlane := ⟨point x y,by simp [point]; linarith⟩
  have hcoord : coordinates z=![x,y] := by
    ext j
    fin_cases j <;> simp [coordinates,z,point]
  have hfd : z ∈ fd := by
    constructor
    · change 1 ≤ Complex.normSq (point x y)
      simp only [Complex.normSq_apply,point,Complex.add_re,Complex.add_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
      nlinarith [sq_nonneg x]
    · change |(point x y).re| ≤ 1/2
      simpa [point] using abs_le.mpr ⟨by simpa only [neg_div] using hx.1.le,hx.2⟩
  have hfield : fullAngularField q b (coordinates z) = fullAngular q b z := by
    change fullAngular q b (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ)))) = _
    rw [angularCoordinates.symm_apply_apply,ofComplex_apply]
  rw [← hcoord,hfield,fullAngular,globalCuspCutoff_eq_on_fd q b z hfd,hcoord]
  congr 1
  change globalResponse q b z=globalResponse q b (ofComplex (z:ℂ))
  rw [ofComplex_apply]

end
end RHTower.D4BMPWCrossClockActualError
