import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.PoleTrace

/-! # Native reference additions and the pole reading -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

/-- Coherently add a calibrated amplitude at a known occupation. -/
def addNative (v : MissingWave) (k : ℕ) (c : ℂ) : MissingWave :=
  ⟨v.val+c • modeWave (number k),fun h => v.property (by
    have hs := (LinearMap.range criticalOperator.toLinearMap).sub_mem h
      ((LinearMap.range criticalOperator.toLinearMap).smul_mem c (modeWave_mem_range (number k)))
    simpa only [add_sub_cancel_right] using hs)⟩

theorem addNative_zero (v : MissingWave) (k : ℕ) : addNative v k 0 = v := by
  apply Subtype.ext
  change v.val+0 • modeWave (number k) = _
  rw [zero_smul,add_zero]

theorem addNative_off (v : MissingWave) {k j : ℕ} (h : j ≠ k) (c : ℂ) :
    (addNative v k c).val (number j) = v.val (number j) := by
  change v.val (number j)+c*modeWave (number k) (number j) = _
  rw [modeWave,lp.single_apply,Pi.single_eq_of_ne (number_injective.ne h),mul_zero,add_zero]

/-- Change of squared norm when the amplitude in a single coordinate is displaced by `c`. -/
def probeIncrement (z c : ℂ) := c.re^2+c.im^2+2*(c.re*z.re+c.im*z.im)

private theorem norm_native_add (f : Gas) (k : ℕ+) (c : ℂ) :
    ‖f+c • modeWave k‖^2 = ‖f‖^2+probeIncrement (f k) c := by
  have h : inner ℂ f (modeWave k) = (starRingEnd ℂ) (f k) := by
    rw [modeWave,lp.inner_single_right,RCLike.inner_apply,one_mul]
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_right,h,norm_smul,modeWave_norm,mul_one]
  change ‖f‖^2+2*(c*(starRingEnd ℂ) (f k)).re+‖c‖^2 = _
  simp only [probeIncrement,Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem addNative_norm_sq (v : MissingWave) (k : ℕ) (c : ℂ) :
    ‖(addNative v k c).val‖^2 = ‖v.val‖^2+probeIncrement (v.val (number k)) c := norm_native_add _ _ _

private theorem probeIncrement_scaled (z c : ℂ) (r : ℝ) :
    probeIncrement ((r:ℂ)*z) (c*(r:ℂ)) = r^2*probeIncrement z c := by
  simp only [probeIncrement,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem addNative_heat_norm_sq (v : MissingWave) (k : ℕ) (c : ℂ) :
    ‖criticalOperator (addNative v k c).val‖^2 =
      ‖criticalOperator v.val‖^2+occupationWeight k*probeIncrement (v.val (number k)) c := by
  change ‖criticalOperator (v.val+c • modeWave (number k))‖^2 = _
  rw [map_add,map_smul,heat_modeWave,smul_smul,norm_native_add,critical_apply,probeIncrement_scaled]
  rfl

/-- The single real reading at the pole. -/
def poleReading (v : MissingWave) := (omissionPartition v 1).re

theorem poleReading_energy (v : MissingWave) : poleReading v*‖v.val‖^2 = ‖criticalOperator v.val‖^2 := by
  rw [poleReading,omissionPartition_pole,Complex.ofReal_re,firstMoment,div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))]

/-- Reference addition preserves the signed displacement from the target level after weighting by total mass. -/
theorem poleReading_displacement (v : MissingWave) (k : ℕ) (c : ℂ) :
    (poleReading (addNative v k c)-occupationWeight k)*‖(addNative v k c).val‖^2 =
      (poleReading v-occupationWeight k)*‖v.val‖^2 := by
  rw [sub_mul,sub_mul,poleReading_energy,poleReading_energy,addNative_heat_norm_sq,addNative_norm_sq]
  ring

theorem probe_blind_iff (v : MissingWave) (k : ℕ) (c : ℂ) :
    poleReading (addNative v k c) = occupationWeight k ↔ poleReading v = occupationWeight k := by
  have h := poleReading_displacement v k c
  have hp (w : MissingWave) : ‖w.val‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero w))
  constructor
  · intro he
    rw [he,sub_self,zero_mul] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right (hp _))
  · intro he
    rw [he,sub_self,zero_mul] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (hp _))

#print axioms addNative_zero
#print axioms addNative_off
#print axioms addNative_norm_sq
#print axioms addNative_heat_norm_sq
#print axioms poleReading_energy
#print axioms poleReading_displacement
#print axioms probe_blind_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
