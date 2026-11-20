import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ASingleCompactPulseDetectsEveryStrip

/-!
# Tail energy of one pulse forces its own blind frequencies

Integrating a compact pulse over a forward unit interval gives a compact
primitive of its first translation difference. This difference costs at
most four times the original tail energy. Its frequency multiplier has
no nonreal zero. Applying the pole obstruction to the averaged pulse
therefore recovers the obstruction from the original transmission alone.
-/

noncomputable section
open Complex Filter Set MeasureTheory Topology
open scoped ContDiff
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Moving unit integral of a pulse. -/
private def movingIntegral (h : CompactPulse) (x : ℝ) := ∫ u in x..x+1, h u

private theorem moving_hasDeriv (h : CompactPulse) (x : ℝ) :
    HasDerivAt (movingIntegral h) (h (x+1)-h x) x := by
  let F (x : ℝ) := ∫ u in (0:ℝ)..x, h u
  have hF (x : ℝ) : HasDerivAt F (h x) x :=
    (h.continuous_toFun.integral_hasStrictDerivAt 0 x).hasDerivAt
  have he : movingIntegral h = fun x => F (x+1)-F x := by
    funext x
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (h.continuous_toFun.intervalIntegrable 0 x) (h.continuous_toFun.intervalIntegrable x (x+1))
    exact eq_sub_of_add_eq' hh
  rw [he]
  exact ((hF (x+1)).comp_add_const x 1).sub (hF x)

/-- Unit box average, still in the space of compact smooth pulses. -/
def forwardBoxPulse (h : CompactPulse) : CompactPulse where
  toFun := movingIntegral h
  smooth := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (moving_hasDeriv h x).differentiableAt,?_⟩
    rw [show deriv (movingIntegral h)=(fun x : ℝ => h (x+1)-h x) from
      funext fun x => (moving_hasDeriv h x).deriv]
    exact (h.smooth.comp (contDiff_id.add contDiff_const)).sub h.smooth
  compact := by
    obtain ⟨R,_,hR⟩ := h.exists_support_bound
    apply HasCompactSupport.intro (isCompact_Icc (a:= -R-1) (b:=R))
    intro x hx
    have hn : x < -R-1 ∨ R<x := by simpa only [mem_Icc,not_and_or,not_le] using hx
    have hz (u : ℝ) (hu : u∈uIcc x (x+1)) : h u=(0:ℂ) := by
      rw [uIcc_of_le (by linarith)] at hu
      apply hR
      rcases hn with hl|hr
      · exact (show R < -u by linarith only [hl,hu.2]).trans_le (neg_le_abs u)
      · exact (hr.trans_le hu.1).trans_le (le_abs_self u)
    rw [movingIntegral,intervalIntegral.integral_congr hz,intervalIntegral.integral_zero]

private def advanceDifference (h : CompactPulse) :=
  (CompactPulse.smul 1 (h.delay (-1))).add (CompactPulse.smul (-1) h)

private theorem box_derivative (h : CompactPulse) :
    (forwardBoxPulse h).D.toFun=(advanceDifference h).toFun := by
  funext x
  change deriv (movingIntegral h) x=1*h (x-(-1))+(-1)*h x
  rw [(moving_hasDeriv h x).deriv,sub_neg_eq_add,one_mul,neg_one_mul,sub_eq_add_neg]

/-- Translation of the pulse translates its full tail-energy curve. -/
theorem tail_energy_delay (h : CompactPulse) (d T : ℝ) :
    tailEnergy (h.delay d) T=tailEnergy h (T-d) := by
  let f (u : ℝ) := ‖pulseReflected h u‖^2
  have he : (Ioi T).indicator (fun u => ‖pulseReflected (h.delay d) u‖^2) =
      fun u => (Ioi (T-d)).indicator f (u-d) := by
    funext u
    by_cases hu : T<u
    · rw [indicator_of_mem (show u ∈ Ioi T from hu),
        indicator_of_mem (show u-d ∈ Ioi (T-d) from sub_lt_sub_right hu d),pulseReflected_delay]
    · rw [indicator_of_notMem (show u ∉ Ioi T from hu),indicator_of_notMem (show u-d∉Ioi (T-d) from
        not_lt.mpr (sub_le_sub_right (le_of_not_gt hu) d))]
  unfold tailEnergy
  rw [←integral_indicator measurableSet_Ioi,he,integral_sub_right_eq_self,integral_indicator measurableSet_Ioi]

/-- First translation differences preserve every upper tail-energy
rate with an absolute loss of at most four in energy. -/
theorem forward_box_derivative_energy_le (h : CompactPulse) (T : ℝ) :
    tailEnergy (forwardBoxPulse h).D T≤4*tailEnergy h T := by
  change tailEnergy (forwardBoxPulse h).D.toFun T≤_
  rw [box_derivative]
  let g := h.delay (-1)
  have hm := tailEnergy_linComb 1 (-1) g h T
  have hp := tailEnergy_linComb 1 1 g h T
  have hn := tailEnergy_nonneg ((CompactPulse.smul 1 g).add (CompactPulse.smul 1 h)) T
  simp only [norm_one,norm_neg,one_pow,one_mul,map_neg,map_one,neg_one_mul,Complex.neg_re] at hm hp
  have hbound : tailEnergy g T≤tailEnergy h T := by
    rw [show tailEnergy g T=tailEnergy h (T-(-1)) from tail_energy_delay h (-1) T]
    exact tailEnergy_anti h (by linarith)
  change tailEnergy ((CompactPulse.smul 1 g).add (CompactPulse.smul (-1) h)) T≤_
  linarith only [hm,hp,hn,hbound]

/-- Every pole to the right of the strip seen by an individual energy
curve forces a zero of that very pulse's amplitude. -/
theorem single_pulse_fast_energy_forces_blind_frequency (h : CompactPulse) {δ : ℝ}
    (hdec : pulseDecayThrough h δ) {ρ : ℂ} (hρ : riemannZeta ρ=0)
    (hpos : 0<ρ.re) (hright : 1-2*δ<ρ.re) : pulseAmplitude h (-I*((ρ-1)/2))=0 := by
  have hbox : pulseDecayThrough (forwardBoxPulse h).D δ := by
    intro σ hσ hσδ
    obtain ⟨C,hC⟩ := hdec σ hσ hσδ
    exact ⟨4*C,fun T ht => (forward_box_derivative_energy_le h T).trans
      ((mul_le_mul_of_nonneg_left (hC T ht) (by norm_num : (0:ℝ)≤4)).trans_eq (mul_assoc ..).symm)⟩
  let w := -I*((ρ-1)/2)
  have hblind : pulseAmplitude (forwardBoxPulse h) w=0 :=
    fast_derivative_hides_zeta_zero _ hbox hρ hpos hright
  have hD := (forwardBoxPulse h).amplitude_D w
  change pulseAmplitude (forwardBoxPulse h).D.toFun w=_ at hD
  rw [box_derivative,hblind,mul_zero] at hD
  change pulseAmplitude ((CompactPulse.smul 1 (h.delay (-1))).add (CompactPulse.smul (-1) h)) w=0 at hD
  rw [pulseAmplitude_add,pulseAmplitude_smul,pulseAmplitude_smul,pulseAmplitude_delay] at hD
  simp only [Complex.ofReal_neg,Complex.ofReal_one,mul_neg,mul_one,neg_neg,one_mul,neg_one_mul] at hD
  have hprod : (Complex.exp (I*w)-1)*pulseAmplitude h w=0 := by linear_combination hD
  have hlt : ρ.re<1 := lt_of_not_ge fun hge => riemannZeta_ne_zero_of_one_le_re hge hρ
  have he : I*w=(ρ-1)/2 := by dsimp [w]; linear_combination -((ρ-1)/2)*I_sq
  have hnorm : ‖Complex.exp (I*w)‖<1 := by
    rw [Complex.norm_exp,Real.exp_lt_one_iff,he]
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.one_re]
    linarith only [hlt]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr fun h => by
    rw [h,norm_one] at hnorm; exact (lt_irrefl _ hnorm))

/-- A specified pulse that sees every scattering frequency tests all
positive strip widths through its own unmodified energy curve. -/
theorem single_pulse_energy_strip {h : CompactPulse}
    (hvis : ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → pulseAmplitude h (-I*((ρ-1)/2))≠0)
    {δ : ℝ} (hd : 0<δ) (hq : δ≤1/4) :
    pulseDecayThrough h δ ↔ ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  constructor
  · intro he ρ hz hp
    exact le_of_not_gt fun hr => hvis ρ hz hp (single_pulse_fast_energy_forces_blind_frequency h he hz hp hr)
  · intro hz σ hs hsd
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hd hq).2.2.1.mp hz
      (δ-σ) (sub_pos.mpr hsd) h
    exact ⟨C,fun T ht => by simpa only [sub_sub_cancel] using hC T ht⟩

#print axioms forward_box_derivative_energy_le
#print axioms single_pulse_fast_energy_forces_blind_frequency
#print axioms single_pulse_energy_strip
end GaloisForLFunctions.BlackHoleRingdown
