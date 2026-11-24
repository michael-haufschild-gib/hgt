import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.VariablePrecision.MarginGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.VariablePrecision.PhaseWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.Cutoff
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Reflections.VariablePrecision

/-! # Finite confidence for a scalar return at prescribed precision -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Polynomially many accuracy bits and confidence bits can be prescribed
independently. One exceptional set controls all time windows at that prefix. -/
theorem gaussian_scalar_confidence_bits (b q : ℕ → ℕ) (hb : PolynomialInDimension b)
    (hq : PolynomialInDimension q) :
    ∃ c : ℕ, ∀ k : ℕ,
      let N := k+3
      let D : ℕ := 2^N
      ∃ B : Set PathPauliDisorder, pathPauliDisorderLaw B ≤ ENNReal.ofReal (3*(1/2:ℝ)^(q k)) ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω ∉ B →
          let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
          ∀ a : ℝ, ∃ t ∈ Icc a (a+(2:ℝ)^(D^c)),
            HasProjectiveCircuitApproximation N (1/(2:ℝ)^(b k)) 0 (unitaryEvolution H t) := by
  let D (k : ℕ) := 2^(k+3)
  let ρ (k : ℕ) := 1/(2:ℝ)^(b k)
  let S (k : ℕ) := precisionModes k (ρ k)
  have hp k : 0 < ρ k := by dsimp only [ρ]; positivity
  have hπ k : ρ k ≤ π := (div_le_self zero_le_one (one_le_pow₀ (by norm_num))).trans (by linarith only [pi_gt_three])
  have hρ : LogPolynomialInDimension (fun k => (ρ k)⁻¹) := by
    simpa only [ρ,one_div,inv_inv] using LogPolynomialInDimension.twoPow hb
  obtain ⟨hF,hS⟩ := HighPrecision.growing_packet_size ρ hp hρ
  obtain ⟨d,hd⟩ := gaussian_bit_confidence_margin q hq S hS
  let G (k : ℕ) := (2:ℝ)^((D k)^d)
  have hG : LogPolynomialInDimension G := LogPolynomialInDimension.twoPow ⟨d,fun _ => le_rfl⟩
  have hprice : LogPolynomialInDimension (fun k => precisionPrice k (ρ k)) := by
    simpa only [precisionPrice,Nat.cast_one,Nat.cast_ofNat] using
      (LogPolynomialInDimension.const 8).mul (hF.add (LogPolynomialInDimension.const 1))
  obtain ⟨c,hc⟩ := (hprice.mul hG).bound
  refine ⟨c,fun k => ?_⟩
  intro N D₀
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let A := smallBalancedMode N (S k) (G k)⁻¹
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  refine ⟨X ⁻¹' A,((Measure.le_map_apply hmp.measurable.aemeasurable A).trans ?_),?_⟩
  · rw [hmp.map_eq]; exact hd k
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω hx
  intro H
  let H' : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  have hpos : 0<(G k)⁻¹ := by dsimp only [G]; positivity
  obtain ⟨e,he⟩ := precision_cover_of_margin k ω (hp k) (hπ k) hpos (hω k).injective hx
  intro a
  obtain ⟨t,ht,hs⟩ := phase_interval_zero_gate_at_error (hp k).le e H' a _ (he a)
  have htime : precisionPrice k (ρ k)/(G k)⁻¹ ≤ (2:ℝ)^(D₀^c) := by
    rw [div_inv_eq_mul]; exact hc k
  exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl htime)⟩,hs⟩

#print axioms gaussian_scalar_confidence_bits
end
end GaloisForLFunctions.HTGeometry.SpectralJets
