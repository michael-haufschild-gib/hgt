import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence

/-!
# Reading a compact pulse from the energy of its derivative

The far reflected field tends to zero. Integrate its exact time
derivative over successive unit intervals. The energy of the derivative
pulse prices each interval, and the geometric series preserves the full
exponential rate in the pointwise reading of the original pulse.
-/

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Every reflected field tends to zero in the late-time direction. -/
theorem reflected_field_tends_to_zero (h : CompactPulse) :
    Tendsto (pulseReflected h) atTop (𝓝 0) := by
  have H := ((tendsto_tailEnergy_atTop h).const_mul 4).mul (tendsto_tailEnergy_atTop h.D)
  rw [mul_zero,mul_zero] at H
  have hp := squeeze_zero (show ∀ T : ℝ, 0≤‖pulseReflected h T‖^4 from fun _ => by positivity)
    (norm_pulseReflected_pow_four_le h) H
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs := hp.sqrt.sqrt
  rw [Real.sqrt_zero,Real.sqrt_zero] at hs
  apply hs.congr
  intro t
  change Real.sqrt (Real.sqrt (‖pulseReflected h t‖^4))=_
  rw [show ‖pulseReflected h t‖^4=(‖pulseReflected h t‖^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]

private theorem unit_field_change (h : CompactPulse) {C σ t : ℝ} (ht : 0≤t)
    (hE : ∀ u : ℝ, 0≤u → tailEnergy h.D u ≤ C*Real.exp (-2*σ*u)) :
    ‖pulseReflected h (t+1)-pulseReflected h t‖ ≤ ((1+C)/2)*Real.exp (-σ*t) := by
  let L := Real.exp (-σ*t)
  have hp : 0<L := Real.exp_pos _
  have hle : t≤t+1 := by linarith
  have hcont := (continuous_pulseReflected h.D).norm
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=t) (b:=t+1)
    (fun u _ => hasDerivAt_pulseReflected h u) ((continuous_pulseReflected h.D).intervalIntegrable ..)
  rw [←ft]
  apply (intervalIntegral.norm_integral_le_integral_norm hle).trans
  have hpt (u : ℝ) : (2*L)*‖pulseReflected h.D u‖ ≤ L^2+‖pulseReflected h.D u‖^2 :=
    by nlinarith only [sq_nonneg (L-‖pulseReflected h.D u‖)]
  have hi := intervalIntegral.integral_mono_on hle ((continuous_const.mul hcont).intervalIntegrable ..)
    ((continuous_const.add (hcont.pow 2)).intervalIntegrable ..) (fun u _ => hpt u)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const
    ((hcont.pow 2).intervalIntegrable ..),intervalIntegral.integral_const,smul_eq_mul,
    show t+1-t=1 by ring,one_mul] at hi
  have he := hE t ht
  have hs : stepDecrement h.D t 1 ≤ tailEnergy h.D t := by
    have hh := tailEnergy_sub_step h.D t (L:=1) zero_le_one
    linarith only [hh,tailEnergy_nonneg h.D (t+1)]
  unfold stepDecrement at hs
  rw [←intervalIntegral.integral_of_le hle] at hs
  have hL : Real.exp (-2*σ*t)=L^2 := by
    rw [show -2*σ*t=(-σ*t)+(-σ*t) by ring,Real.exp_add]; ring
  rw [hL] at he
  apply le_of_mul_le_mul_left (a:=2*L) _ (by positivity)
  change 2*L*(∫ u in t..t+1, ‖pulseReflected h.D u‖) ≤ 2*L*((1+C)/2*L)
  linarith only [hi,hs,he]

/-- Energy decay of one derivative pulse implies pointwise reflected
decay of its primitive at precisely the same rate. -/
theorem reflected_decay_from_derivative_energy (h : CompactPulse) {σ C : ℝ} (hσ : 0<σ)
    (hE : ∀ T : ℝ, 0≤T → tailEnergy h.D T ≤ C*Real.exp (-2*σ*T)) :
    ∃ A : ℝ, 0≤A ∧ ∀ T : ℝ, 0≤T → ‖pulseReflected h T‖ ≤ A*Real.exp (-σ*T) := by
  let q := Real.exp (-σ)
  have hq : 0<q := Real.exp_pos _
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hσ)
  have hC : 0≤C := (tailEnergy_nonneg h.D 0).trans (by simpa using hE 0 le_rfl)
  let A := (1+C)/2
  have hA : 0≤A := by dsimp only [A]; positivity
  refine ⟨A*(1-q)⁻¹,mul_nonneg hA (inv_nonneg.mpr (sub_nonneg.mpr hq1.le)),fun T ht => ?_⟩
  let f := fun j : ℕ => pulseReflected h (T+j)
  have hdiff (j : ℕ) : ‖f (j+1)-f j‖ ≤ A*Real.exp (-σ*T)*q^j := by
    have H := unit_field_change h (t:=T+j) (add_nonneg ht (Nat.cast_nonneg _)) hE
    rw [show -σ*(T+j)=-(σ*T)+(j:ℝ)*(-σ) by ring,Real.exp_add,Real.exp_nat_mul] at H
    simpa only [f,A,q,Nat.cast_succ,←add_assoc,neg_mul,mul_assoc] using H
  have part (n : ℕ) : ‖f n-f 0‖ ≤ A*Real.exp (-σ*T)*∑ j ∈ range n,q^j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show f (n+1)-f 0=(f (n+1)-f n)+(f n-f 0) by abel,sum_range_succ,mul_add]
      exact (norm_add_le _ _).trans (by linarith only [ih,hdiff n])
  have hg := hasSum_geometric_of_lt_one hq.le hq1
  have uniform (n : ℕ) : ‖f n-f 0‖ ≤ (A*(1-q)⁻¹)*Real.exp (-σ*T) := by
    have hs := hg.summable.sum_le_tsum (range n) (fun j _ => pow_nonneg hq.le j)
    rw [hg.tsum_eq] at hs
    exact (part n).trans ((mul_le_mul_of_nonneg_left hs (mul_nonneg hA (Real.exp_pos _).le)).trans_eq (by ring))
  have htime : Tendsto (fun j : ℕ => T+(j:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T tendsto_natCast_atTop_atTop
  have lim := (((reflected_field_tends_to_zero h).comp htime).sub_const (f 0)).norm
  rw [zero_sub,norm_neg] at lim
  simpa only [f,Nat.cast_zero,add_zero] using le_of_tendsto lim (Eventually.of_forall uniform)

#print axioms reflected_field_tends_to_zero
#print axioms reflected_decay_from_derivative_energy
end GaloisForLFunctions.BlackHoleRingdown
