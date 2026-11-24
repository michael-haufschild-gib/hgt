import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.MarginGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.PhaseWitness

/-! # A phase-filling horizon outside disorder of mass at most 3·2⁻ᴰ -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

private theorem retained_clock_growth :
    LogPolynomialInDimension (fun k => ((retainedClockModes k).card:ℝ)) ∧
      LogPolynomialInDimension phaseClockPrice := by
  let D (k : ℕ) := 2^(k+3)
  let S (k : ℕ) := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  let F (k : ℕ) := nonconstantPacketIndexSet (phaseCubeFourierCutoff (D k-1) (1/80)) (D k-1)
  have hh := LogPolynomialInDimension.twoPow ((PolynomialInDimension.const 128).mul PolynomialInDimension.dim.square)
  have hc (k : ℕ) := fixed_radius_phase_packet_envelope (D:=D k)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0))) (prefixPhaseEnergyEquiv k)
  have hS := hh.mono (f:=fun k => ((S k).card:ℝ)) (fun k => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hc k).2.1)
  have hF := hh.mono (f:=fun k => ((F k).card:ℝ)) (fun k => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hc k).1)
  refine ⟨hS,?_⟩
  change LogPolynomialInDimension (fun k => 8*(((F k).card:ℝ)+1))
  simpa only [Nat.cast_ofNat,Nat.cast_one] using
    (LogPolynomialInDimension.const 8).mul (hF.add (LogPolynomialInDimension.const 1))

/-- The exact finite-mode deadline at failure parameter 2⁻ᴰ has a
logarithm bounded by a fixed polynomial in Hilbert dimension. -/
theorem calibrated_confidence_horizon :
    ∃ c : ℕ, ∀ k : ℕ, let D : ℕ := 2^(k+3)
      phaseClockPrice k / confidenceMargin k (retainedClockModes k).card (confidenceBox k)
        ((1/2:ℝ)^D) ≤ (2:ℝ)^(D^c) := by
  obtain ⟨hs,hp⟩ := retained_clock_growth
  simpa only [div_eq_mul_inv] using
    (hp.mul (high_confidence_margin (fun k => (retainedClockModes k).card) hs)).bound

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
  let S := retainedClockModes
  obtain ⟨hS,hprice⟩ := retained_clock_growth
  obtain ⟨b,hb⟩ := gaussian_exponential_confidence_margin S hS
  let G (k : ℕ) := (2:ℝ)^((D k)^b)
  have hG : LogPolynomialInDimension G := LogPolynomialInDimension.twoPow ⟨b,fun _ => le_rfl⟩
  obtain ⟨c,hc'⟩ := (hprice.mul hG).bound
  refine ⟨c,fun k => ?_⟩
  intro N D₀
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let A := smallBalancedMode N (S k) (G k)⁻¹
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  refine ⟨X ⁻¹' A,((Measure.le_map_apply hmp.measurable.aemeasurable A).trans ?_),?_⟩
  · rw [hmp.map_eq]; exact hb k
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω hx
  intro E
  have hpos : 0<(G k)⁻¹ := by dsimp only [G]; positivity
  obtain ⟨e,he⟩ := phase_cover_of_margin k ω hpos (hω k).injective hx
  refine ⟨e,fun u z => ?_⟩
  obtain ⟨t,ht,hz⟩ := he u z
  have htime : phaseClockPrice k/(G k)⁻¹ ≤ (2:ℝ)^(D₀^c) := by
    rw [div_inv_eq_mul]; exact hc' k
  exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl htime)⟩,hz⟩

#print axioms gaussian_exponential_confidence_clock
end
end GaloisForLFunctions.HTGeometry.SpectralJets
