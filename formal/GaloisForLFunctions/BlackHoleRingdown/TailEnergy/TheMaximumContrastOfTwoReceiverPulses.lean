import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PolarizationAndPositivity

/-!
# Extreme energy contrast of two receiver pulses

The normalized difference of two densities is the Atwood number
in Giri (arXiv:2611.23171, Eq. 2). For two receiver channels it
depends on the input basis. Optimizing over unitary mixtures gives
the length of the three real polarization readings divided by the
total energy. Partial dephasing gives an exactly linear splitting
at equal diagonal energies and a quadratic shift away from equality.
This distinguishes the two powers of the weak coupling observed in
Perez-Obiol et al. (arXiv:2611.08168, §III) in a receiver model.
-/

noncomputable section
open Complex Filter Topology
namespace GaloisForLFunctions.BlackHoleRingdown

private def mix (g h : CompactPulse) (a b : ℂ) :=
  (CompactPulse.smul a g).add (CompactPulse.smul b h)

/-- Average over the two phases differing by π. For |r|≤1 the
coefficients are probabilities; r=1 retains full coherence. -/
def partiallyCoherentTail (g h : CompactPulse) (T r : ℝ) (a b : ℂ) : ℝ :=
  ((1+r)/2)*tailEnergy (mix g h a b) T + ((1-r)/2)*tailEnergy (mix g h a (-b)) T

/-- Separation between the largest and smallest unit-input energies. -/
def receiverSplitting (g h : CompactPulse) (T r : ℝ) : ℝ :=
  Real.sqrt ((tailEnergy g T-tailEnergy h T)^2+4*r^2*‖tailCrossEnergy g h T‖^2)

private theorem readings (g h : CompactPulse) (T r : ℝ) (a b : ℂ)
    (hn : ‖a‖^2+‖b‖^2=1) :
    2*partiallyCoherentTail g h T r a b-(tailEnergy g T+tailEnergy h T) =
      (2*(a*(starRingEnd ℂ) b).re)*(2*r*(tailCrossEnergy g h T).re) +
      (-(2*(a*(starRingEnd ℂ) b).im))*(2*r*(tailCrossEnergy g h T).im) +
      (‖a‖^2-‖b‖^2)*(tailEnergy g T-tailEnergy h T) := by
  simp only [partiallyCoherentTail,mix,tailEnergy_linComb,norm_neg,map_neg,mul_neg,neg_mul,
    Complex.neg_re,Complex.mul_re]
  linear_combination (tailEnergy g T+tailEnergy h T)*hn

private theorem spin_sphere (a b : ℂ) (h : ‖a‖^2+‖b‖^2=1) :
    (2*(a*(starRingEnd ℂ) b).re)^2+(-(2*(a*(starRingEnd ℂ) b).im))^2+
      (‖a‖^2-‖b‖^2)^2=1 := by
  have hn := Complex.normSq_eq_norm_sq (a*(starRingEnd ℂ) b)
  rw [Complex.normSq_apply,norm_mul,RCLike.norm_conj,mul_pow] at hn
  calc _ = (‖a‖^2+‖b‖^2)^2 := by linear_combination 4*hn
       _ = 1 := by rw [h,one_pow]

private theorem spin_lift {x y z : ℝ} (h : x^2+y^2+z^2=1) :
    ∃ a b : ℂ, ‖a‖^2+‖b‖^2=1 ∧ 2*(a*(starRingEnd ℂ) b).re=x ∧
      -(2*(a*(starRingEnd ℂ) b).im)=y ∧ ‖a‖^2-‖b‖^2=z := by
  have hbound : -1≤z := by nlinarith only [h,sq_nonneg x,sq_nonneg y,sq_nonneg (z+1)]
  rcases eq_or_lt_of_le hbound with hz|hz
  · have hx : x=0 := by rw [←hz] at h; nlinarith only [h,sq_nonneg y,sq_nonneg x]
    have hy : y=0 := by rw [←hz,hx] at h; nlinarith only [h,sq_nonneg y]
    exact ⟨0,1,by simp,by simp [hx],by simp [hy],by simp [←hz]⟩
  let s := Real.sqrt ((1+z)/2)
  have hs : 0<s := Real.sqrt_pos.mpr (by linarith only [hz])
  have hsq : s^2=(1+z)/2 := Real.sq_sqrt (by linarith only [hz])
  let b : ℂ := ⟨x/(2*s),y/(2*s)⟩
  have hb : ‖b‖^2=(1-z)/2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    change x/(2*s)*(x/(2*s))+y/(2*s)*(y/(2*s))=(1-z)/2
    field_simp [hs.ne']
    nlinarith only [h,hsq,congrArg (fun v : ℝ => v*z) hsq]
  have ha : ‖(s:ℂ)‖^2=(1+z)/2 := by rw [Complex.norm_real,Real.norm_of_nonneg hs.le,hsq]
  refine ⟨s,b,by rw [ha,hb]; ring,?_,?_,by rw [ha,hb]; ring⟩ <;>
    simp only [b,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] <;> field_simp

private theorem radius_sq (g h : CompactPulse) (T r : ℝ) :
    (2*r*(tailCrossEnergy g h T).re)^2+(2*r*(tailCrossEnergy g h T).im)^2+
      (tailEnergy g T-tailEnergy h T)^2=(receiverSplitting g h T r)^2 := by
  rw [receiverSplitting,Real.sq_sqrt (by positivity),←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

/-- Every unit input lies between the two extremal readings. -/
theorem receiver_energy_contrast_bound (g h : CompactPulse) (T r : ℝ) {a b : ℂ}
    (hunit : ‖a‖^2+‖b‖^2=1) :
    |2*partiallyCoherentTail g h T r a b-(tailEnergy g T+tailEnergy h T)| ≤
      receiverSplitting g h T r := by
  rw [readings _ _ _ _ _ _ hunit]
  have cs (x y z p q k : ℝ) : (x*p+y*q+z*k)^2≤(x^2+y^2+z^2)*(p^2+q^2+k^2) := by
    nlinarith only [sq_nonneg (x*q-y*p),sq_nonneg (x*k-z*p),sq_nonneg (y*k-z*q)]
  have hnonneg : 0≤receiverSplitting g h T r := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
  rw [sq_abs,←radius_sq g h T r]
  exact (cs _ _ _ _ _ _).trans_eq (by rw [spin_sphere a b hunit,one_mul])

/-- Both endpoints are attained even if the cross energy vanishes. -/
theorem receiver_energy_contrast_attained (g h : CompactPulse) (T r : ℝ) (sign : ℝ) (hs : sign^2=1) :
    ∃ a b : ℂ, ‖a‖^2+‖b‖^2=1 ∧
      2*partiallyCoherentTail g h T r a b-(tailEnergy g T+tailEnergy h T)=
        sign*receiverSplitting g h T r := by
  let D := receiverSplitting g h T r
  by_cases hn : D=0
  · have hu : ‖(1:ℂ)‖^2+‖(0:ℂ)‖^2=1 := by simp
    have hb := receiver_energy_contrast_bound g h T r hu
    change abs _ ≤ D at hb
    rw [hn,abs_nonpos_iff] at hb
    exact ⟨1,0,hu,hb.trans (by change 0=sign*D; simp [hn])⟩
  let p := 2*r*(tailCrossEnergy g h T).re
  let q := 2*r*(tailCrossEnergy g h T).im
  let k := tailEnergy g T-tailEnergy h T
  have hD : p^2+q^2+k^2=D^2 := radius_sq g h T r
  have hu : (sign*p/D)^2+(sign*q/D)^2+(sign*k/D)^2=1 := by
    simp only [div_pow, mul_pow sign, hs, one_mul]
    rw [←add_div, ←add_div, hD, div_self (pow_ne_zero _ hn)]
  obtain ⟨a,b,hab,hp,hq,hk⟩ := spin_lift hu
  refine ⟨a,b,hab,?_⟩
  rw [readings _ _ _ _ _ _ hab,hp,hq,hk]
  change sign*p/D*p+sign*q/D*q+sign*k/D*k=sign*D
  field_simp [hn]
  linear_combination sign*hD

/-- The two orthogonal settings exhaust the original total energy. -/
theorem orthogonal_receiver_sum (g h : CompactPulse) (T r : ℝ) {a b : ℂ}
    (hu : ‖a‖^2+‖b‖^2=1) :
    partiallyCoherentTail g h T r a b +
      partiallyCoherentTail g h T r (-(starRingEnd ℂ) b) ((starRingEnd ℂ) a) =
      tailEnergy g T+tailEnergy h T := by
  have hu' : ‖-(starRingEnd ℂ) b‖^2+‖(starRingEnd ℂ) a‖^2=1 := by
    simpa only [norm_neg,RCLike.norm_conj,add_comm] using hu
  have h₁ := readings g h T r a b hu
  have h₂ := readings g h T r _ _ hu'
  have he : (-(starRingEnd ℂ) b)*(starRingEnd ℂ) ((starRingEnd ℂ) a) =
      -(a*(starRingEnd ℂ) b) := by simp [mul_comm]
  rw [he,Complex.neg_re,Complex.neg_im,norm_neg,RCLike.norm_conj,RCLike.norm_conj] at h₂
  linarith only [h₁,h₂]

/-- Normalized difference of the two orthogonal receiver energies. -/
def receiverAtwoodContrast (g h : CompactPulse) (T r : ℝ) (a b : ℂ) :=
  let E := partiallyCoherentTail g h T r a b
  let F := partiallyCoherentTail g h T r (-(starRingEnd ℂ) b) ((starRingEnd ℂ) a)
  (E-F)/(E+F)

/-- The largest absolute Atwood contrast over all orthogonal input bases
is the splitting divided by the trace. One basis attains the positive endpoint. -/
theorem maximum_receiver_atwood_contrast (g h : CompactPulse) (T r : ℝ) :
    (∀ a b : ℂ, ‖a‖^2+‖b‖^2=1 →
      |receiverAtwoodContrast g h T r a b| ≤
        receiverSplitting g h T r/(tailEnergy g T+tailEnergy h T)) ∧
    ∃ a b : ℂ, ‖a‖^2+‖b‖^2=1 ∧ receiverAtwoodContrast g h T r a b =
      receiverSplitting g h T r/(tailEnergy g T+tailEnergy h T) := by
  have he (a b : ℂ) (hu : ‖a‖^2+‖b‖^2=1) :
      receiverAtwoodContrast g h T r a b =
        (2*partiallyCoherentTail g h T r a b-(tailEnergy g T+tailEnergy h T))/
          (tailEnergy g T+tailEnergy h T) := by
    unfold receiverAtwoodContrast
    dsimp only
    have hs := orthogonal_receiver_sum g h T r hu
    rw [hs]
    congr 1
    linarith only [hs]
  constructor
  · intro a b hu
    have ht := add_nonneg (tailEnergy_nonneg g T) (tailEnergy_nonneg h T)
    rw [he a b hu,abs_div,abs_of_nonneg ht]
    exact div_le_div_of_nonneg_right (receiver_energy_contrast_bound g h T r hu) ht
  · obtain ⟨a,b,hu,hpos⟩ := receiver_energy_contrast_attained g h T r 1 (by norm_num)
    exact ⟨a,b,hu,by rw [he a b hu,hpos,one_mul]⟩

/-- Independent nonzero inputs never attain unit normalized Atwood
contrast, even after changing the coherent input basis. -/
theorem independent_pulse_splitting_lt_trace (g h : CompactPulse)
    (hind : ∀ a b : ℂ, (∀ t : ℝ, a*g t+b*h t=0) → a=0 ∧ b=0) (T : ℝ) :
    receiverSplitting g h T 1 < tailEnergy g T+tailEnergy h T := by
  have hcross := norm_tailCrossEnergy_sq_lt_mul g h hind T
  have hp := tailEnergy_nonneg g T
  have hq := tailEnergy_nonneg h T
  have hnonneg : 0≤receiverSplitting g h T 1 := Real.sqrt_nonneg _
  apply (sq_lt_sq₀ hnonneg (add_nonneg hp hq)).mp
  unfold receiverSplitting
  rw [Real.sq_sqrt (by positivity)]
  nlinarith only [hcross]

/-- Equal diagonal energies split linearly in the coherence. -/
theorem receiver_splitting_at_balance (g h : CompactPulse) (T : ℝ)
    (he : tailEnergy g T=tailEnergy h T) (r : ℝ) :
    receiverSplitting g h T r=2 * |r| * ‖tailCrossEnergy g h T‖ := by
  unfold receiverSplitting
  rw [he,sub_self,zero_pow (by decide : 2≠0),zero_add,
    show 4*r^2*‖tailCrossEnergy g h T‖^2=(2*r*‖tailCrossEnergy g h T‖)^2 by ring,
    Real.sqrt_sq_eq_abs,abs_mul,abs_mul,abs_of_nonneg (norm_nonneg _)]
  norm_num

/-- With unequal diagonal energies, the increase of the splitting is
second order and its coefficient is twice the cross power divided by
the diagonal separation. -/
theorem receiver_splitting_quadratic_at_imbalance (g h : CompactPulse) (T : ℝ)
    (he : tailEnergy g T ≠ tailEnergy h T) :
    Tendsto (fun r : ℝ => (receiverSplitting g h T r-|tailEnergy g T-tailEnergy h T|)/r^2)
      (𝓝[≠] 0) (𝓝 (2*‖tailCrossEnergy g h T‖^2/|tailEnergy g T-tailEnergy h T|)) := by
  let d := tailEnergy g T-tailEnergy h T
  let c := ‖tailCrossEnergy g h T‖
  have dp : 0 < |d| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hD : Continuous (receiverSplitting g h T) := by unfold receiverSplitting; fun_prop
  have h₀ : receiverSplitting g h T 0 = |d| := by simp [receiverSplitting,d,Real.sqrt_sq_eq_abs]
  have hx := hD.tendsto (0:ℝ)
  rw [h₀] at hx
  have hl := (tendsto_const_nhds (x:=(4*c^2))).div (hx.add_const |d|) (by positivity)
  rw [show 4*c^2/(|d|+|d|)=2*c^2/|d| by field_simp; ring] at hl
  apply (hl.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : r≠0 := hr
  have hsum : 0<receiverSplitting g h T r+|d| := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) dp
  have hsq : (receiverSplitting g h T r)^2=d^2+4*r^2*c^2 := Real.sq_sqrt (by positivity)
  change 4*c^2/(receiverSplitting g h T r+|d|)=(receiverSplitting g h T r-|d|)/r^2
  field_simp [hsum.ne',hr']
  nlinarith only [hsq,sq_abs d]

#print axioms receiver_energy_contrast_bound
#print axioms receiver_energy_contrast_attained
#print axioms maximum_receiver_atwood_contrast
#print axioms independent_pulse_splitting_lt_trace
#print axioms receiver_splitting_at_balance
#print axioms receiver_splitting_quadratic_at_imbalance
end GaloisForLFunctions.BlackHoleRingdown
