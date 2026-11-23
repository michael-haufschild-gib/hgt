import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.HorizonGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.Growth

/-! # Fourier packet size at growing angular precision -/
open Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
noncomputable section

private theorem cutoff_bound (d : ℕ) {ρ : ℝ} (hp : 0 < ρ) :
    (phaseCubeFourierCutoff d ρ:ℝ) ≤ (128*ρ⁻¹*(16*ρ⁻¹)^d)^2+1 := by
  let v := 2*π/(ρ*((ρ/(4*π))^d/16))
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have h : v = 32*π*ρ⁻¹*(4*π*ρ⁻¹)^d := by
    dsimp only [v]
    simp only [div_eq_mul_inv,mul_inv_rev,←inv_pow,inv_inv]
    ring
  have hv' : v ≤ 128*ρ⁻¹*(16*ρ⁻¹)^d := by
    rw [h]
    have h₁ := mul_le_mul_of_nonneg_right (show 32*π ≤ 128 by linarith only [pi_lt_four]) (inv_nonneg.mpr hp.le)
    have h₂ := mul_le_mul_of_nonneg_right (show 4*π ≤ 16 by linarith only [pi_lt_four]) (inv_nonneg.mpr hp.le)
    exact mul_le_mul h₁ (pow_le_pow_left₀ (by positivity) h₂ d) (by positivity) (by positivity)
  exact (Nat.ceil_lt_add_one (sq_nonneg v)).le.trans (add_le_add_left (pow_le_pow_left₀ hv hv' 2) 1)

/-- When inverse accuracy has logarithm polynomial in Hilbert dimension,
the entire finite Fourier packet also has polynomial logarithmic size. -/
theorem growing_packet_size (ρ : ℕ → ℝ) (hp : ∀ k, 0 < ρ k)
    (hρ : LogPolynomialInDimension fun k => (ρ k)⁻¹) :
    let M (k : ℕ) := phaseCubeFourierCutoff (2^(k+3)-1) (ρ k)
    LogPolynomialInDimension (fun k => ((nonconstantPacketIndexSet (M k) (2^(k+3)-1)).card:ℝ)) ∧
      LogPolynomialInDimension (fun k => ((phaseClockModes (prefixPhaseEnergyEquiv k) (ρ k)).card:ℝ)) := by
  intro M
  let d (k : ℕ) := 2^(k+3)-1
  let F (k : ℕ) := nonconstantPacketIndexSet (M k) (d k)
  have hd : PolynomialInDimension d := PolynomialInDimension.dim.mono fun _ => Nat.sub_le _ _
  have hb := ((((LogPolynomialInDimension.const 128).mul hρ).mul
    (((LogPolynomialInDimension.const 16).mul hρ).pow hd)).pow (PolynomialInDimension.const 2)).add
    (LogPolynomialInDimension.const 1)
  have hM : LogPolynomialInDimension (fun k => (M k:ℝ)) :=
    hb.mono (fun _ => Nat.cast_nonneg _) (fun k => cutoff_bound _ (hp k))
  have hh := (hM.add (LogPolynomialInDimension.const 1)).pow ((PolynomialInDimension.const 2).mul hd)
  have hF : LogPolynomialInDimension (fun k => ((F k).card:ℝ)) :=
    hh.mono (fun _ => Nat.cast_nonneg _) (fun k => by exact_mod_cast nonconstant_phase_packet_card_le (M k) (d k))
  exact ⟨hF,hF.mono (fun _ => Nat.cast_nonneg _) (fun k => by
    exact_mod_cast (Finset.card_image_le : (phaseClockModes (prefixPhaseEnergyEquiv k) (ρ k)).card ≤ (F k).card))⟩

#print axioms growing_packet_size
end
end GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
