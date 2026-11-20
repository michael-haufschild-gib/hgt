import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.FastPhaseMixingLeavesASquaredEnergyDefect

/-!
# Resonance of two simultaneous receiver sweeps

Two scalar tail-energy sweeps retain a correlation exactly through their
zero difference or zero sum frequency. Equal nonzero speeds measure the
Hermitian product of the cross energies; opposite speeds measure their
ordinary product. Distinct absolute speeds have zero limiting correlation.
-/

noncomputable section
open Complex MeasureTheory Filter Topology
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Addition of sweep frequencies multiplies their phases. -/
theorem phaseSweepCarrier_add (a b t : ℝ) :
    phaseSweepCarrier (a+b) t=phaseSweepCarrier a t*phaseSweepCarrier b t := by
  unfold phaseSweepCarrier
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Reversing a sweep conjugates its phase. -/
theorem phaseSweepCarrier_neg (a t : ℝ) :
    phaseSweepCarrier (-a) t=(starRingEnd ℂ) (phaseSweepCarrier a t) := by
  unfold phaseSweepCarrier
  rw [←Complex.exp_conj,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring_nf

private theorem carrier_product (a b n t : ℝ) (w : ℝ) (C D : ℂ) :
    2*((phaseSweepCarrier ((a+b)*n) t*((w:ℂ)*(C*D))).re+
      (phaseSweepCarrier ((a-b)*n) t*((w:ℂ)*(C*(starRingEnd ℂ) D))).re) =
      w*(2*(phaseSweepCarrier (a*n) t*C).re)*(2*(phaseSweepCarrier (b*n) t*D).re) := by
  let X := phaseSweepCarrier (a*n) t*C
  let Y := phaseSweepCarrier (b*n) t*D
  have hplus : phaseSweepCarrier ((a+b)*n) t*((w:ℂ)*(C*D))=(w:ℂ)*(X*Y) := by
    rw [add_mul,phaseSweepCarrier_add]
    dsimp only [X,Y]
    ring
  have hminus : phaseSweepCarrier ((a-b)*n) t*((w:ℂ)*(C*(starRingEnd ℂ) D)) =
      (w:ℂ)*(X*(starRingEnd ℂ) Y) := by
    rw [sub_mul,sub_eq_add_neg,phaseSweepCarrier_add,phaseSweepCarrier_neg]
    dsimp only [X,Y]
    rw [map_mul]
    ring
  rw [hplus,hminus]
  change _=w*(2*X.re)*(2*Y.re)
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  ring

/-- The limiting covariance of the two measured scalar errors includes
exactly the static terms at the sum and difference frequencies. -/
theorem joint_phase_sweep_covariance (g h k l : CompactPulse) (a b : ℝ)
    {w : ℝ → ℝ} (hw : Continuous w) (hk : HasCompactSupport w) :
    Tendsto (fun n : ℝ => ∫ t : ℝ,
      w t*phaseSweepError g h (a*n) t*phaseSweepError k l (b*n) t) atTop
      (𝓝 (2*((if a+b=0 then ∫ t : ℝ, w t*(tailCrossEnergy g h t*tailCrossEnergy k l t).re else 0)+
        (if a-b=0 then ∫ t : ℝ, w t*(tailCrossEnergy g h t*(starRingEnd ℂ) (tailCrossEnergy k l t)).re
          else 0)))) := by
  let C := tailCrossEnergy g h
  let D := tailCrossEnergy k l
  let F (t : ℝ) := (w t:ℂ)*(C t*D t)
  let G (t : ℝ) := (w t:ℂ)*(C t*(starRingEnd ℂ) (D t))
  have hc := continuous_tailCrossEnergy g h
  have hd := continuous_tailCrossEnergy k l
  have hF : Continuous F := (Complex.continuous_ofReal.comp hw).mul (hc.mul hd)
  have hG : Continuous G := (Complex.continuous_ofReal.comp hw).mul (hc.mul (Complex.continuous_conj.comp hd))
  have hkw := hk.comp_left (g:=fun x : ℝ => (x:ℂ)) (by simp)
  have hkF : HasCompactSupport F := hkw.mul_right
  have hkG : HasCompactSupport G := hkw.mul_right
  have h := ((signed_phase_sweep_integral hF hkF (a+b)).add
    (signed_phase_sweep_integral hG hkG (a-b))).const_mul 2
  have fRe (t : ℝ) : (F t).re=w t*(C t*D t).re := by simp [F,Complex.mul_re]
  have gRe (t : ℝ) : (G t).re=w t*(C t*(starRingEnd ℂ) (D t)).re := by simp [G,Complex.mul_re]
  simp only [fRe,gRe] at h
  apply h.congr
  intro n
  have hi {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (v : ℝ) :
      Integrable (fun t => (phaseSweepCarrier v t*f t).re) :=
    (Complex.continuous_re.comp ((continuous_phaseSweepCarrier v).mul hf)).integrable_of_hasCompactSupport
      ((hs.mul_left).comp_left (g:=Complex.re) rfl)
  rw [←integral_add (hi hF hkF _) (hi hG hkG _),←integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [phaseSweepError_eq_carrier,phaseSweepError_eq_carrier]
  exact carrier_product a b n t (w t) (C t) (D t)

/-- Distinct absolute speeds completely remove the cross covariance
for every continuous compactly supported time weight. -/
theorem unequal_sweep_speeds_decorrelate (g h k l : CompactPulse) {a b : ℝ}
    (hab : |a|≠|b|) {w : ℝ → ℝ} (hw : Continuous w) (hk : HasCompactSupport w) :
    Tendsto (fun n : ℝ => ∫ t : ℝ,
      w t*phaseSweepError g h (a*n) t*phaseSweepError k l (b*n) t) atTop (𝓝 0) := by
  have hp : a+b≠0 := fun he => hab (by rw [eq_neg_of_add_eq_zero_left he,abs_neg])
  have hm : a-b≠0 := fun he => hab (congrArg abs (sub_eq_zero.mp he))
  simpa only [if_neg hp,if_neg hm,add_zero,mul_zero] using joint_phase_sweep_covariance g h k l a b hw hk

#print axioms joint_phase_sweep_covariance
#print axioms unequal_sweep_speeds_decorrelate
end GaloisForLFunctions.BlackHoleRingdown
