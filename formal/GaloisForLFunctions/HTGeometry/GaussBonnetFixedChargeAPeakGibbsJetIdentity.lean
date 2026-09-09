import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsSmooth

/-!
# Exact all-order identity for the actual aligned Gibbs jet

At every physical state, differentiating the exact smooth force
identity gives the correction to every positive derivative order of
the actual normalized Gibbs energy. The derivative order is arbitrary
natural data, and every regularity fact is proved within the corpus.
-/
noncomputable section
open Real Filter Set
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_correction (w φ τ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ) :
    (iteratedDeriv (n + 1) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv (n + 1) (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ =
      iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l₂)) ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hV : deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) = egbFixedChargeAPeakNormalizedGibbsForce w φ τ l₂ :=
    funext (egbFixedChargeAPeakNormalizedGibbs_derivative w φ τ l₁ l₂)
  have hQ : deriv (fun x : ℝ => cos x ^ 4) = fun x => -4 * sin x * cos x ^ 3 :=
    funext (fun x => (egbFixedChargeAQuarticProfile_hasDerivAt x).deriv)
  have hF : egbFixedChargeAPeakNormalizedGibbsForce w φ τ l₂ = fun x =>
      deriv (fun y : ℝ => cos y ^ 4) x +
      egbCoexistenceASymmetricRatio τ * egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l₂) x := by
    funext x
    rw [hQ]
    exact egbFixedChargeAPeakNormalizedGibbsForce_decomposition w φ τ l₂ x
  have hQc : ContDiff ℝ ∞ (deriv (fun x : ℝ => cos x ^ 4)) := by rw [hQ]; fun_prop
  have hAc : ContDiff ℝ ∞ (fun x => egbCoexistenceASymmetricRatio τ *
      egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l₂) x) := by
    have ha := egbFixedChargeAAlignedAngularCorrection_actual_contDiff w φ τ l₂
    fun_prop
  have hQn : ContDiffAt ℝ n (deriv (fun x : ℝ => cos x ^ 4)) ψ := (hQc.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
  have hAn : ContDiffAt ℝ n (fun x => egbCoexistenceASymmetricRatio τ *
      egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l₂) x) ψ :=
    (hAc.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
  simp only [iteratedDeriv_succ']
  have hsum := iteratedDeriv_add hQn hAn
  change iteratedDeriv n (fun x => deriv (fun y : ℝ => cos y ^ 4) x +
    egbCoexistenceASymmetricRatio τ * egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l₂) x) ψ = _ at hsum
  rw [hV, hF, hsum, _root_.iteratedDeriv_const_mul_field]
  field_simp [hd.ne'] <;> ring

end GaloisForLFunctions.HTGeometry
