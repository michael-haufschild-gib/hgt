import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.CarrierFrequenciesThatMissNoResonance
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ReadingAPulseFromItsDerivativeEnergy
import Mathlib.Analysis.Real.Cardinality

/-!
# A single compact pulse detects every zero-free strip

Fix one carrier outside the countable exceptional set and transmit the
derivative of the modulated unit bump. Its tail energy controls the
undifferentiated receiver at the full decay rate. The amplitude at each
pole is nonzero, so this same pulse tests every strip and the RH endpoint.
-/

noncomputable section
open Complex Set
open _root_.RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Open exponential rates observed on one compact pulse. -/
def pulseDecayThrough (h : CompactPulse) (δ : ℝ) : Prop :=
  ∀ σ : ℝ, 0<σ → σ<δ → ∃ C : ℝ, ∀ T : ℝ, 0≤T → tailEnergy h T ≤ C*Real.exp (-2*σ*T)

/-- The fixed pulse associated to a carrier of the unit bump. -/
def carrierDerivativePulse (ω : ℝ) := ((excitingPulse 0).modulate ω).D

/-- A zero beyond the proposed strip forces every sufficiently fast
derivative pulse to have a blind frequency at its associated pole. -/
theorem fast_derivative_hides_zeta_zero (h : CompactPulse) {δ : ℝ} (hdec : pulseDecayThrough h.D δ)
    {ρ : ℂ} (hρ : riemannZeta ρ=0) (hρ0 : 0<ρ.re) (hright : 1-2*δ<ρ.re) :
    pulseAmplitude h (-I*((ρ-1)/2))=0 := by
  have hρ1 : ρ.re<1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
  have hne : ρ≠1 := by intro he; rw [he,Complex.one_re] at hρ1; exact lt_irrefl _ hρ1
  let p := (ρ-1)/2
  have hpρ : 1+2*p=ρ := by dsimp only [p]; ring
  have hp : xi (1+2*p)=0 := by rw [hpρ]; exact (xi_eq_zero_iff hρ0 hne).mpr hρ
  have hre : p.re=(ρ.re-1)/2 := by simp [p]
  have hp0 : p.re<0 := by linarith only [hre,hρ1]
  have hcut : -p.re<δ := by linarith only [hre,hright]
  obtain ⟨σ,hσ,hσδ⟩ := exists_between hcut
  have hσ0 := (neg_pos.mpr hp0).trans hσ
  obtain ⟨C,hE⟩ := hdec σ hσ0 hσδ
  obtain ⟨A,_,hA⟩ := reflected_decay_from_derivative_energy h hσ0 hE
  exact pulseAmplitude_eq_zero_of_pulseReflected_decay _ hσ0 hA hp
    (by linarith only [hre,hρ0]) hp0 (by linarith only [hσ])

/-- One admissible carrier simultaneously tests every intermediate
strip and the critical-line endpoint. -/
theorem single_carrier_strip {ω : ℝ} (hω : ω ∉ missedCarriers (excitingPulse 0) poleFrequencies)
    {δ : ℝ} (hδ : 0<δ) (hquarter : δ≤1/4) :
    pulseDecayThrough (carrierDerivativePulse ω) δ ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  constructor
  · intro h ρ hρ hρ0
    by_contra! hright
    let p := (ρ-1)/2
    have hp : xi (1+2*p)=0 := by
      rw [show 1+2*p=ρ by dsimp only [p]; ring]
      exact (xi_eq_zero_iff hρ0 (fun he => riemannZeta_ne_zero_of_one_le_re
        (by rw [he,Complex.one_re]) hρ)).mpr hρ
    exact hω ⟨-I*p,⟨p,hp,rfl⟩,fast_derivative_hides_zeta_zero _ h hρ hρ0 hright⟩
  · intro h σ hσ hσδ
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hδ hquarter).2.2.1.mp h
      (δ-σ) (sub_pos.mpr hσδ) (carrierDerivativePulse ω)
    exact ⟨C,fun T ht => by simpa only [sub_sub_cancel] using hC T ht⟩

/-- Every carrier interval contains one fixed compact pulse testing
RH and all intermediate strip widths. -/
theorem single_pulse_in_every_carrier_interval {a b : ℝ} (hab : a<b) :
    ∃ ω ∈ Ioo a b,
      (∀ δ : ℝ, 0<δ → δ≤1/4 → (pulseDecayThrough (carrierDerivativePulse ω) δ ↔
        ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ)) ∧
      (pulseDecayThrough (carrierDerivativePulse ω) (1/4) ↔ RiemannHypothesis) := by
  have hnot : ¬Ioo a b ⊆ missedCarriers (excitingPulse 0) poleFrequencies :=
    fun h => hab.not_ge (Cardinal.Real.Ioo_countable_iff.mp (almost_all_unit_window_carriers_detect_all_poles.mono h))
  obtain ⟨ω,hω,hgood⟩ := not_subset.mp hnot
  refine ⟨ω,hω,fun _ hd hq => single_carrier_strip hgood hd hq,?_⟩
  have hquarter := zeroFreeStrip_tailEnergy_equivalences (δ:=1/4) (by norm_num) le_rfl
  exact (single_carrier_strip hgood (by norm_num) le_rfl).trans
    (hquarter.1.trans RingdownRate.riemannHypothesis_iff_pulse_ringdown.symm)

#print axioms single_carrier_strip
#print axioms single_pulse_in_every_carrier_interval
end GaloisForLFunctions.BlackHoleRingdown
