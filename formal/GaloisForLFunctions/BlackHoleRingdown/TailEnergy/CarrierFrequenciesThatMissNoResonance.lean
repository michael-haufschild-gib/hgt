import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.FixedStepContractionFalsification
import GaloisForLFunctions.HTGeometry.EntireNonzeroPathConnected

/-!
# Carrier frequencies that miss no resonance

The amplitude of a compact pulse is entire; a nonzero amplitude has
countably many zeros. Modulation translates this set. Only countably
many carriers can hide any member of a prescribed countable census.
Two copies with a generic relative carrier have no common blind
frequency anywhere in the complex plane.
-/

noncomputable section
open Complex Set
open _root_.RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Exceptional carriers for a prescribed set of complex frequencies. -/
def missedCarriers (h : CompactPulse) (S : Set ℂ) :=
  {ω : ℝ | ∃ w ∈ S, pulseAmplitude (h.modulate ω) w=0}

/-- A generic translate of one nonzero entire amplitude sees every
member of any countable census simultaneously. -/
theorem missed_carriers_countable (h : CompactPulse) {w₀ : ℂ} (hne : pulseAmplitude h w₀ ≠ 0)
    {S : Set ℂ} (hS : S.Countable) : (missedCarriers h S).Countable := by
  let Z := {w : ℂ | pulseAmplitude h w=0}
  have hZ : Z.Countable := HTGeometry.countable_zeros_of_entire_nonzero h.differentiable_amplitude hne
  have hinj (w : ℂ) : Function.Injective (fun ω : ℝ => w-(ω:ℂ)) :=
    fun _ _ he => Complex.ofReal_injective (sub_right_inj.mp he)
  have hc := hS.biUnion (fun w _ => hZ.preimage (hinj w))
  apply hc.mono
  rintro ω ⟨w,hw,hω⟩
  rw [pulseAmplitude_modulate] at hω
  exact mem_iUnion.mpr ⟨w,mem_iUnion.mpr ⟨hw,hω⟩⟩

/-- Two copies at a generic relative carrier have no common amplitude
zero at any complex frequency, independently of the resonance set. -/
theorem common_blind_carriers_countable (h : CompactPulse) {w₀ : ℂ} (hne : pulseAmplitude h w₀ ≠ 0) :
    {ω : ℝ | ∃ w : ℂ, pulseAmplitude h w=0 ∧ pulseAmplitude (h.modulate ω) w=0}.Countable :=
  missed_carriers_countable h hne (HTGeometry.countable_zeros_of_entire_nonzero h.differentiable_amplitude hne)

/-- Complex frequencies of the poles tested by reflected pulse decay. -/
def poleFrequencies : Set ℂ := (fun p : ℂ => -I*p) '' {p : ℂ | xi (1+2*p)=0}

theorem pole_frequencies_countable : poleFrequencies.Countable := by
  have hd : Differentiable ℂ (fun z : ℂ => xi (1+2*z)) :=
    xi_differentiable.comp (by fun_prop)
  have hn : xi (1+2*(1:ℂ)) ≠ 0 := xi_ne_zero_of_one_lt_re (by norm_num)
  exact (HTGeometry.countable_zeros_of_entire_nonzero hd hn).image _

/-- Outside a countable exceptional set, one modulated unit-window
pulse has nonzero amplitude at every scattering pole. -/
theorem almost_all_unit_window_carriers_detect_all_poles :
    (missedCarriers (excitingPulse 0) poleFrequencies).Countable :=
  missed_carriers_countable _ (pulseAmplitude_excitingPulse_ne_zero 0) pole_frequencies_countable

#print axioms missed_carriers_countable
#print axioms almost_all_unit_window_carriers_detect_all_poles
#print axioms common_blind_carriers_countable
end GaloisForLFunctions.BlackHoleRingdown
