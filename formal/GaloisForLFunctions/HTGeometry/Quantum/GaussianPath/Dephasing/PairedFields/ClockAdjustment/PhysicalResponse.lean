import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail

/-! # A frozen chain has angular response at every edge after retiming -/

open Filter MeasureTheory Set Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open SpectralEdge
open private continuous_edgeResponse from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- The bound applies after an observer chooses both time and phase corrections from all
the couplings. Spectral energies in the denominator belong to the original frozen prefix. -/
theorem physical_retimed_response (n : ℕ) (e : Fin (n+1)) (a b : Fin 3) (r : ℝ) (hr : 0<r) :
    let D := (2:ℝ)^(n+2)
    pathPauliDisorderLaw.real {ω |
      let h : Coeff n := fun i => pathPauliDisorderShell ω n i
      let E := (generator h).2.isHermitian.eigenvalues
      let g := pairField h (leftSite e a) (rightSite e b)
      ∃ t φ : ℝ, (∑ j, E j^4)*(∑ j, (localSlope h g j+t*E j+φ)^2) < (2*D*r^3)^2} ≤ 6*r := by
  intro D
  let X (ω) : Coeff n := fun i => pathPauliDisorderShell ω n i
  let S := {h : Coeff n | |edgeResponse h e a b|<2*D*r^3}
  have hm : MeasurableSet S := measurableSet_lt (continuous_edgeResponse e a b).abs.measurable measurable_const
  have hcut : 0≤2*D*r^3 := by dsimp only [D]; positivity
  refine le_trans (measureReal_mono (s₂ := X ⁻¹' S) ?_ (measure_ne_top _ _)) ?_
  · rintro ω ⟨t,φ,hw⟩
    change |edgeResponse (X ω) e a b| < _
    by_contra! he
    have hsq := pow_le_pow_left₀ hcut he 2
    rw [sq_abs] at hsq
    exact hw.not_ge (hsq.trans (retimed_pair_response (X ω) (leftSite e a) (rightSite e b) t φ))
  · rw [(BlockDilations.prefix_measure n).measureReal_preimage hm.nullMeasurableSet]
    exact gaussian_edge_response e a b r hr

/-- On one chain, at every prefix and every edge and pair of axes, some energy level
responds to the onsite rotation after any correction of clock and phase. -/
theorem frozen_angular_response :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (e : Fin (n+1)) (a b : Fin 3) (t φ : ℝ),
      let h : Coeff n := fun i => pathPauliDisorderShell ω n i
      let E := (generator h).2.isHermitian.eigenvalues
      let g := pairField h (leftSite e a) (rightSite e b)
      ∃ j, localSlope h g j+t*E j+φ≠0 := by
  refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun e => ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => ?_
  let X (ω) : Coeff n := fun i => pathPauliDisorderShell ω n i
  let Z := {ω : PathPauliDisorder | edgeResponse (X ω) e a b=0}
  have hzero : pathPauliDisorderLaw.real Z=0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! hp
    let r := pathPauliDisorderLaw.real Z/12
    have hr : 0<r := div_pos hp (by norm_num)
    let D := (2:ℝ)^(n+2)
    let B := {h : Coeff n | |edgeResponse h e a b|<2*D*r^3}
    have hB : MeasurableSet B := measurableSet_lt (continuous_edgeResponse e a b).abs.measurable measurable_const
    have hsub : Z ⊆ X ⁻¹' B := by
      intro ω hω
      change |edgeResponse (X ω) e a b|<2*D*r^3
      rw [show edgeResponse (X ω) e a b=0 from hω,abs_zero]
      dsimp only [D]; positivity
    have hle := measureReal_mono (μ:=pathPauliDisorderLaw) hsub (measure_ne_top _ _)
    rw [(BlockDilations.prefix_measure n).measureReal_preimage hB.nullMeasurableSet] at hle
    have hsmall := hle.trans (gaussian_edge_response e a b r hr)
    dsimp only [r] at hsmall
    linarith only [hp,hsmall]
  have hnon : ∀ᵐ ω ∂pathPauliDisorderLaw, ω∉Z := by
    apply ae_iff.mpr
    simpa only [not_not,setOf_mem_eq] using (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hzero
  filter_upwards [hnon] with ω hω t φ
  let h := X ω
  let E := (generator h).2.isHermitian.eigenvalues
  let g := pairField h (leftSite e a) (rightSite e b)
  change ∃ j, localSlope h g j+t*E j+φ≠0
  by_contra! hall
  have hdet : edgeResponse (X ω) e a b≠0 := hω
  have hh := retimed_pair_response (X ω) (leftSite e a) (rightSite e b) t φ
  change (edgeResponse (X ω) e a b)^2 ≤ (∑ j, E j^4)*∑ j, (localSlope h g j+t*E j+φ)^2 at hh
  simp only [hall,zero_pow (by decide : 2≠0),sum_const_zero,mul_zero] at hh
  exact (sq_pos_of_ne_zero hdet).not_ge hh

#print axioms physical_retimed_response
#print axioms frozen_angular_response
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
