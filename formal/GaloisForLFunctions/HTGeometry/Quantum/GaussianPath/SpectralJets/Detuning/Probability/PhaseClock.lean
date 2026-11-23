import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.MarginGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # A phase-filling horizon outside disorder of mass at most 3·2⁻ᴰ -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Every sliding window of length 2 to a fixed power of D in the
exponent visits every phase cube, except on a common set of Gaussian
samples with an explicit bound on its mass. -/
theorem gaussian_exponential_confidence_clock :
    ∃ c : ℕ, ∀ k : ℕ,
      let N := k+3
      let D : ℕ := 2^N
      ∃ B : Set PathPauliDisorder, pathPauliDisorderLaw B ≤ ENNReal.ofReal (3*(1/2:ℝ)^D) ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω ∉ B →
          let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
          ∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ u : ℝ, ∀ z : Fin (D-1) → ℝ,
            ∃ t ∈ Icc u (u+(2:ℝ)^(D^c)), ∀ j, turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-z j)<1/80 := by
  let D (k : ℕ) := 2^(k+3)
  let S (k : ℕ) := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  let F (k : ℕ) := nonconstantPacketIndexSet (phaseCubeFourierCutoff (D k-1) (1/80)) (D k-1)
  have hh := LogPolynomialInDimension.twoPow ((PolynomialInDimension.const 128).mul PolynomialInDimension.dim.square)
  have hc (k : ℕ) := fixed_radius_phase_packet_envelope (D:=D k)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0))) (prefixPhaseEnergyEquiv k)
  have hS := hh.mono (f:=fun k => ((S k).card:ℝ)) (fun k => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hc k).2.1)
  have hF := hh.mono (f:=fun k => ((F k).card:ℝ)) (fun k => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hc k).1)
  obtain ⟨b,hb⟩ := gaussian_exponential_confidence_margin S hS
  let G (k : ℕ) := (2:ℝ)^((D k)^b)
  have hG : LogPolynomialInDimension G := LogPolynomialInDimension.twoPow ⟨b,fun _ => le_rfl⟩
  obtain ⟨c,hc'⟩ := (((LogPolynomialInDimension.const 8).mul (hF.add (LogPolynomialInDimension.const 1))).mul hG).bound
  refine ⟨c,fun k => ?_⟩
  intro N D₀
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let A := smallBalancedMode N (S k) (G k)⁻¹
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  refine ⟨X ⁻¹' A,((Measure.le_map_apply hmp.measurable.aemeasurable A).trans ?_),?_⟩
  · rw [hmp.map_eq]; exact hb k
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω hx
  intro E
  let f := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) (X ω)
  let e := prefixPhaseEnergyEquiv k
  obtain ⟨p,hp⟩ := physical_sorted_order k ω (hω k).injective
  refine ⟨p.trans e,?_⟩
  have he : E ∘ (p.trans e).symm = f ∘ e.symm := by
    funext j
    simpa only [Function.comp_apply,Equiv.symm_trans_apply,p.apply_symm_apply] using hp (p.symm (e.symm j))
  rw [he]
  have hpos : 0<(G k)⁻¹ := by dsimp only [G]; positivity
  have hmode (v) (hv : v∈F k) : (G k)⁻¹≤|packetFreq (RHTower.zeroProjectiveFrequency (f ∘ e.symm)) v| := by
    obtain ⟨m,hm,hn,hbal,heq⟩ := balanced_mode_of_retained_phase_frequency (ρ:=1/80) e f v hv
    rw [←heq]
    exact le_of_not_gt fun hs => hx ⟨m,hm,hn,hbal,hs⟩
  intro u z
  obtain ⟨t,ht,hz⟩ := phaseCube_hit_at_calibrated_cutoff (by norm_num : (0:ℝ)<1/80)
    (by linarith only [pi_gt_three]) hpos (RHTower.zeroProjectiveFrequency (f ∘ e.symm)) hmode u z
  have htime : 8*(((F k).card:ℝ)+1)/(G k)⁻¹ ≤ (2:ℝ)^(D₀^c) := by
    rw [div_inv_eq_mul]; exact hc' k
  exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl htime)⟩,hz⟩

#print axioms gaussian_exponential_confidence_clock
end
end GaloisForLFunctions.HTGeometry.SpectralJets
