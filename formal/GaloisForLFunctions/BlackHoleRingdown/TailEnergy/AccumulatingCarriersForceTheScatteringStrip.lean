import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ASingleCompactPulseDetectsEveryStrip
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Accumulating carriers force the scattering strip

A forbidden zeta zero allows only finitely many fast carriers in any
bounded frequency window. Thus any preassigned infinite compact
census suffices, with independent constants for each of its receivers.
An arbitrarily sparse subsequence of reciprocal integer carriers works.
-/

noncomputable section
open Complex Set Filter Topology
open _root_.RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- The carriers missing a single prescribed frequency form a finite
set on every compact window. -/
theorem compact_blind_carriers_finite (h : CompactPulse) {z₀ : ℂ} (hz₀ : pulseAmplitude h z₀ ≠ 0)
    (w : ℂ) {K : Set ℝ} (hK : IsCompact K) :
    {ω ∈ K | pulseAmplitude (h.modulate ω) w=0}.Finite := by
  let F := pulseAmplitude h
  let shift := fun u : ℝ => w-(u:ℂ)
  have inj : Function.Injective shift := fun u v he => Complex.ofReal_injective (sub_right_inj.mp he)
  have ha : AnalyticOnNhd ℂ F univ := fun z _ => h.differentiable_amplitude.analyticAt z
  have hi : ∀ z ∈ (univ : Set ℂ), ¬(∀ᶠ v in 𝓝 z, F v=0) := by
    intro z _ hv
    have hh := ha.eq_of_eventuallyEq (g:=fun _ => (0:ℂ)) analyticOnNhd_const hv
    exact hz₀ (congrFun hh z₀)
  have hf := HTGeometry.finite_zeros_of_isCompact isOpen_univ h.differentiable_amplitude.differentiableOn hi
    (hK.image (show Continuous shift from continuous_const.sub Complex.continuous_ofReal)) (subset_univ _)
  apply (hf.preimage inj.injOn).subset
  intro ω hh
  obtain ⟨hω,hz⟩ := hh
  rw [pulseAmplitude_modulate] at hz
  exact ⟨⟨ω,hω,rfl⟩,hz⟩

/-- A forbidden pole makes the fast carriers locally finite. -/
theorem fast_carriers_finite_of_zero {δ : ℝ} {ρ : ℂ} (hρ : riemannZeta ρ=0)
    (hρ0 : 0<ρ.re) (hbad : 1-2*δ<ρ.re) {K : Set ℝ} (hK : IsCompact K) :
    {ω ∈ K | pulseDecayThrough (carrierDerivativePulse ω) δ}.Finite := by
  apply (compact_blind_carriers_finite (excitingPulse 0) (pulseAmplitude_excitingPulse_ne_zero 0)
    (-I*((ρ-1)/2)) hK).subset
  intro ω hω
  exact ⟨hω.1,fast_derivative_hides_zeta_zero _ hω.2 hρ hρ0 hbad⟩

/-- Infinitely many fast carriers from any one infinite compact
carrier set are equivalent to the zero strip. -/
theorem accumulating_carriers_strip {δ : ℝ} (hd : 0<δ) (hd1 : δ≤1/4) {K : Set ℝ}
    (hK : IsCompact K) (hinf : K.Infinite) :
    {ω ∈ K | pulseDecayThrough (carrierDerivativePulse ω) δ}.Infinite ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  constructor
  · intro h ρ hz hp
    exact le_of_not_gt fun hb => h (fast_carriers_finite_of_zero hz hp hb hK)
  · intro hs
    apply hinf.mono
    intro ω hω
    refine ⟨hω,fun σ hσ hσδ => ?_⟩
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hd hd1).2.2.1.mp hs
      (δ-σ) (sub_pos.mpr hσδ) (carrierDerivativePulse ω)
    exact ⟨C,fun T ht => by simpa only [sub_sub_cancel] using hC T ht⟩

/-- A pole can hide at only finitely many of the explicit carriers
1/(n+1), without any density or spacing assumption on the observed n. -/
theorem reciprocal_carriers_strip {δ : ℝ} (hd : 0<δ) (hd1 : δ≤1/4) :
    (∃ᶠ n : ℕ in atTop, pulseDecayThrough (carrierDerivativePulse (((n:ℝ)+1)⁻¹)) δ) ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  let c := fun n : ℕ => ((n:ℝ)+1)⁻¹
  have inj : Function.Injective c := by
    intro n m he
    have h := inv_injective he
    exact Nat.cast_injective ((add_left_inj _).mp h)
  constructor
  · intro hf ρ hz hp
    by_contra! hb
    have hfin := fast_carriers_finite_of_zero hz hp hb (isCompact_Icc (a:=(0:ℝ)) (b:=1))
    have hf' := hfin.preimage (f:=c) inj.injOn
    obtain ⟨M,hM⟩ := hf'.bddAbove
    obtain ⟨n,hn,hfast⟩ := frequently_atTop.mp hf (M+1)
    have hc : c n∈Icc (0:ℝ) 1 := ⟨by dsimp only [c]; positivity,inv_le_one_of_one_le₀
      (le_add_of_nonneg_left (Nat.cast_nonneg n))⟩
    have hi := hM (show n∈c ⁻¹' {ω ∈ Icc (0:ℝ) 1 | pulseDecayThrough (carrierDerivativePulse ω) δ}
      from ⟨hc,hfast⟩)
    omega
  · intro hs
    apply (Eventually.of_forall (fun n => ?_)).frequently
    intro σ hσ hσδ
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hd hd1).2.2.1.mp hs (δ-σ) (sub_pos.mpr hσδ)
      (carrierDerivativePulse (((n:ℝ)+1)⁻¹))
    exact ⟨C,fun T ht => by simpa only [sub_sub_cancel] using hC T ht⟩

#print axioms fast_carriers_finite_of_zero
#print axioms accumulating_carriers_strip
#print axioms reciprocal_carriers_strip
end GaloisForLFunctions.BlackHoleRingdown
