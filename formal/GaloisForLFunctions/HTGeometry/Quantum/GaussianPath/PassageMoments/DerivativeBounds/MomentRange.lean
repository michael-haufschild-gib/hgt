import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.DyadicTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.GeometricTail

/-! # Inverse-cubic positive moment orders for physical first excursions -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
open PrescribedTimes SpectralJets
noncomputable section

/-- On the same frozen Gaussian chain, the maximum of the first robust
crossing and its first return wait has finite p-th moment at every gate
budget for p below 1/(B+L), where B=2D(1+2LD) and L=D-2. -/
theorem gaussian_derivative_first_passage_moments :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ p : ℝ, 0<p → p<1/(marginOrder k:ℝ) →
      Integrable (fun x => (passageMax k s x)^p)
        (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1) := by
  filter_upwards [gaussian_derivative_survival] with k hk s p hp hq
  let d := marginOrder k
  let B := (2:ℝ)^d
  have hd : 0<d := by dsimp only [d,marginOrder,prefixDetectorDegree]; positivity
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hB : 1<B := one_lt_pow₀ (by norm_num) hd.ne'
  have hBp : B^p<2 := by
    change ((2:ℝ)^d)^p<2
    rw [←Real.rpow_natCast_mul (by norm_num : 0≤(2:ℝ))]
    apply (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1<(2:ℝ)) _).trans_eq (Real.rpow_one 2)
    simpa only [mul_comm] using (lt_div_iff₀ hd').mp hq
  apply integrable_rpow_of_geometric_tail _ _ (measurable_passageMax k s) (passageMax_nonneg k s)
    (boxDeadline_pos k (confidenceBox k)) hB (by norm_num : 0≤(1/2:ℝ)) hp
    (by linarith only [hBp] : B^p*(1/2)<1) (C:=8/3)
  intro u
  have h := hk s ((1/2:ℝ)^u) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  rwa [dyadic_margin_inverse] at h

#print axioms gaussian_derivative_first_passage_moments
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
