import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ResonancesOfTwoSimultaneousReceiverSweeps
import Mathlib.Data.Nat.Choose.Sum

/-!
# All moments of a rapidly wound receiver

The microscopic fluctuation at cutoff t has the moments of
2 |C(t)| cos θ with uniform phase θ. All odd powers disappear against
compactly supported continuous weights. The even power 2k retains the
central binomial coefficient times the weighted cross energy to power 2k.
This extends the quadratic defect of weak phase mixing to polynomial tests.
-/

noncomputable section
open Complex Filter Topology MeasureTheory
namespace GaloisForLFunctions.BlackHoleRingdown

private theorem sweep_nat_mul (i : ℕ) (n t : ℝ) :
    phaseSweepCarrier ((i:ℝ)*n) t=phaseSweepCarrier n t^i := by
  induction i with
  | zero => simp [phaseSweepCarrier]
  | succ i ih => rw [Nat.cast_succ,add_mul,one_mul,phaseSweepCarrier_add,ih,pow_succ]

private def coefficient (g h : CompactPulse) (w : ℝ → ℝ) (m i : ℕ) (t : ℝ) :=
  (w t:ℂ)*((tailCrossEnergy g h t)^i*((starRingEnd ℂ) (tailCrossEnergy g h t))^(m-i)*(m.choose i:ℂ))

private theorem continuous_coefficient (g h : CompactPulse) {w : ℝ → ℝ} (hw : Continuous w) (m i : ℕ) :
    Continuous (coefficient g h w m i) :=
  (Complex.continuous_ofReal.comp hw).mul ((((continuous_tailCrossEnergy g h).pow i).mul
    ((Complex.continuous_conj.comp (continuous_tailCrossEnergy g h)).pow (m-i))).mul continuous_const)

private theorem compact_coefficient (g h : CompactPulse) {w : ℝ → ℝ} (hw : HasCompactSupport w) (m i : ℕ) :
    HasCompactSupport (coefficient g h w m i) :=
  (hw.comp_left (g:=fun x : ℝ => (x:ℂ)) (by simp)).mul_right

private theorem binomial_reading (g h : CompactPulse) (w : ℝ → ℝ) (m : ℕ) (n t : ℝ) :
    (∑ i ∈ Finset.range (m+1),
      (phaseSweepCarrier (((i:ℝ)-((m-i:ℕ):ℝ))*n) t*coefficient g h w m i t).re) =
      w t*(phaseSweepError g h n t)^m := by
  let Z := phaseSweepCarrier n t*tailCrossEnergy g h t
  have he : (∑ i ∈ Finset.range (m+1),
      phaseSweepCarrier (((i:ℝ)-((m-i:ℕ):ℝ))*n) t*coefficient g h w m i t) =
      (w t:ℂ)*(Z+(starRingEnd ℂ) Z)^m := by
    rw [add_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [sub_mul,sub_eq_add_neg,phaseSweepCarrier_add,phaseSweepCarrier_neg,sweep_nat_mul,sweep_nat_mul,map_pow]
    dsimp only [Z,coefficient]
    rw [map_mul,mul_pow,mul_pow]
    ring
  have hr := congrArg Complex.re he
  rw [Complex.add_conj,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re] at hr
  simpa only [Complex.re_sum,phaseSweepError_eq_carrier,Z] using hr

private theorem power_limit (g h : CompactPulse) {w : ℝ → ℝ}
    (hw : Continuous w) (hk : HasCompactSupport w) (m : ℕ) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, w t*(phaseSweepError g h n t)^m) atTop
      (𝓝 (∑ i ∈ Finset.range (m+1), if i=m-i then ∫ t : ℝ, (coefficient g h w m i t).re else 0)) := by
  have hi (i : ℕ) := signed_phase_sweep_integral (continuous_coefficient g h hw m i)
    (compact_coefficient g h hk m i) ((i:ℝ)-((m-i:ℕ):ℝ))
  have hsum := tendsto_finsetSum (Finset.range (m+1)) (fun i _ => hi i)
  simp only [sub_eq_zero,Nat.cast_inj] at hsum
  apply hsum.congr
  intro n
  have hi' (i : ℕ) (_ : i∈Finset.range (m+1)) : Integrable (fun t : ℝ =>
      (phaseSweepCarrier (((i:ℝ)-((m-i:ℕ):ℝ))*n) t*coefficient g h w m i t).re) :=
    (Complex.continuous_re.comp ((continuous_phaseSweepCarrier _).mul
      (continuous_coefficient g h hw m i))).integrable_of_hasCompactSupport
        (((compact_coefficient g h hk m i).mul_left).comp_left (g:=Complex.re) rfl)
  rw [←integral_finsetSum _ hi']
  exact integral_congr_ae (Eventually.of_forall (binomial_reading g h w m n))

/-- The mean of every odd power vanishes, including in overlapping channels. -/
theorem odd_phase_sweep_moment (g h : CompactPulse) {w : ℝ → ℝ} (hw : Continuous w)
    (hk : HasCompactSupport w) (k : ℕ) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, w t*(phaseSweepError g h n t)^(2*k+1)) atTop (𝓝 0) := by
  have h := power_limit g h hw hk (2*k+1)
  have he (i : ℕ) (hi : i∈Finset.range (2*k+1+1)) : i≠2*k+1-i := by
    have := Finset.mem_range.mp hi
    omega
  rwa [Finset.sum_eq_zero (fun i hi => if_neg (he i hi))] at h

private theorem central_coefficient (g h : CompactPulse) (w : ℝ → ℝ) (t : ℝ) (k : ℕ) :
    (coefficient g h w (2*k) k t).re =
      ((2*k).choose k:ℝ)*(w t*‖tailCrossEnergy g h t‖^(2*k)) := by
  have h := Complex.mul_conj (tailCrossEnergy g h t)
  rw [Complex.normSq_eq_norm_sq] at h
  unfold coefficient
  rw [show 2*k-k=k by omega,←mul_pow,h,←Complex.ofReal_pow,←pow_mul,
    ←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.ofReal_re]
  ring

/-- The surviving even moments measure the complete sequence of local
cross powers. For k=2 the fourth moment has coefficient six. -/
theorem even_phase_sweep_moment (g h : CompactPulse) {w : ℝ → ℝ} (hw : Continuous w)
    (hk : HasCompactSupport w) (k : ℕ) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, w t*(phaseSweepError g h n t)^(2*k)) atTop
      (𝓝 (((2*k).choose k:ℝ)*∫ t : ℝ, w t*‖tailCrossEnergy g h t‖^(2*k))) := by
  have h := power_limit g h hw hk (2*k)
  have he (i : ℕ) (hi : i∈Finset.range (2*k+1)) (hn : i≠k) : i≠2*k-i := by
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_eq_single k (fun i hi hn => if_neg (he i hi hn))
    (fun hn => (hn (Finset.mem_range.mpr (by omega))).elim),if_pos (show k=2*k-k by omega)] at h
  simpa only [central_coefficient,integral_const_mul] using h

#print axioms odd_phase_sweep_moment
#print axioms even_phase_sweep_moment
end GaloisForLFunctions.BlackHoleRingdown
