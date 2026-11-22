import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity

/-! # Empty-return frequency and mean residence from the first crossing -/
open Real Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- The same two constants control the spectral prefactors of entry
frequency and mean occupied time per entry, at every physical tolerance. -/
theorem gaussian_crossing_rate_and_residence :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ε∈Ioo (0:ℝ) (sqrt 2), let x := physicalArc ε
          let F := entriesAfter E x σ
          let rate := x^(D-2)*pairTurnRate E
          let L := (D:ℝ)*x/pairTurnRate E
          Tendsto (fun T : ℝ => ((F T).card:ℝ)/(T-σ)) atTop (𝓝 rate) ∧
          rate ∈ Icc (x^(D-2)*(c*(D:ℝ)^2*sqrt N)) (x^(D-2)*(C*(D:ℝ)^2*sqrt N)) ∧
          Tendsto (fun T : ℝ => volume.real (visitSet H 0 ε ∩ Icc σ T)/(F T).card) atTop (𝓝 L) ∧
          L∈Icc (x/(C*(D:ℝ)*sqrt N)) (x/(c*(D:ℝ)*sqrt N)) := by
  obtain ⟨c,C,hc,hC,hg⟩ := gaussian_pair_rate_scale
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hg,gaussian_first_crossing_flux,gaussian_path_all_prefixes_maximally_projective] with ω hg hσ hi
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hg,hσ] with k hg hσ
  intro N D H P E
  obtain ⟨σ,hσ,he,hbefore,hflux⟩ := hσ
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro ε hε x F rate L
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hD : 0<(D:ℝ) := by dsimp only [D]; positivity
  have hroot := sqrt_pos.mpr hN
  have hx : 0<x := (physicalArc_spec hε.1 hε.2).1.1
  have hd : 2≤D := by
    simpa only [D,N,pow_one] using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤k+3 by omega)
  have hd' : (D:ℝ)=(2:ℝ)^N := by simp only [D,Nat.cast_pow,Nat.cast_ofNat]
  have hg' : pairTurnRate E∈Icc (c*(D:ℝ)^2*sqrt N) (C*(D:ℝ)^2*sqrt N) := by
    rw [hd']
    exact hg
  have hR : 0<pairTurnRate E := (mul_pos (mul_pos hc (pow_pos hD 2)) hroot).trans_le hg'.1
  have hrate : 0<rate := mul_pos (pow_pos hx _) hR
  have hf := (hflux ε hε.1 hε.2).2
  refine ⟨hf,⟨mul_le_mul_of_nonneg_left hg'.1 (pow_pos hx _).le,
    mul_le_mul_of_nonneg_left hg'.2 (pow_pos hx _).le⟩,?_,?_⟩
  · have hp := ShortTimeProducts.scalar_fraction H (hi k) hε.1 hε.2 σ
    have hl := hp.div hf hrate.ne'
    have hpow : x^(D-1)=x*x^(D-2) := by rw [show D-1=D-2+1 by omega,pow_succ']
    have heq : (D:ℝ)*x^(D-1)/rate=L := by
      dsimp only [rate,L]
      rw [hpow]
      field_simp [hR.ne',(pow_pos hx (D-2)).ne']
    change Tendsto (fun T : ℝ => visitFraction H 0 ε σ T / (((F T).card:ℝ)/(T-σ))) atTop
      (𝓝 ((D:ℝ)*x^(D-1)/rate)) at hl
    rw [heq] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop σ] with T hT
    exact div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _
  · constructor
    · apply (div_le_div_iff₀ (mul_pos (mul_pos hC hD) hroot) hR).mpr
      calc x*pairTurnRate E ≤ x*(C*(D:ℝ)^2*sqrt N) := mul_le_mul_of_nonneg_left hg'.2 hx.le
           _ = (D:ℝ)*x*(C*D*sqrt N) := by ring
    · apply (div_le_div_iff₀ hR (mul_pos (mul_pos hc hD) hroot)).mpr
      calc (D:ℝ)*x*(c*D*sqrt N) = x*(c*(D:ℝ)^2*sqrt N) := by ring
           _ ≤ x*pairTurnRate E := mul_le_mul_of_nonneg_left hg'.1 hx.le

#print axioms gaussian_crossing_rate_and_residence
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass
