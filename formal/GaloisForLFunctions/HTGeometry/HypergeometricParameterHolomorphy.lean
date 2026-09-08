import GaloisForLFunctions.HTGeometry.HypergeometricParameterMajorant
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-! Parameter holomorphy of the original Gauss sum, including terminating numerator parameters. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The denominator prefix stays nonzero under the actual uniform pole separation. -/
theorem pochhammer_ne_zero_of_separated {c : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ j : ℕ, δ ≤ ‖c+j‖) (n : ℕ) : (ascPochhammer ℂ n).eval c ≠ 0 := by
  exact norm_pos_iff.mp ((pow_pos hδ n).trans_le (pochhammer_norm_lower hδ hc n))

/-- Local uniform estimates prove holomorphy of the original sum, without excluding terminating numerators. -/
theorem hypergeometric_family_differentiableAt
    (a b c : ℂ → ℂ) (w z : ℂ) (R B δ : ℝ) (hR : 0 < R) (hB : 0 < B) (hδ : 0 < δ)
    (ha : ∀ u ∈ Metric.ball w R, DifferentiableAt ℂ a u)
    (hb : ∀ u ∈ Metric.ball w R, DifferentiableAt ℂ b u)
    (hc : ∀ u ∈ Metric.ball w R, DifferentiableAt ℂ c u)
    (hbound : ∀ u ∈ Metric.ball w R, ‖a u‖ ≤ B ∧ ‖b u‖ ≤ B ∧ ‖c u‖ ≤ B)
    (hsep : ∀ u ∈ Metric.ball w R, ∀ j : ℕ, δ ≤ ‖c u+j‖)
    (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun u => ordinaryHypergeometric (a u) (b u) (c u) z) w := by
  obtain ⟨N,hN⟩ := exists_nat_ge (B+1)
  have hdiff (n : ℕ) : DifferentiableOn ℂ
      (fun u => ordinaryHypergeometricCoefficient (a u) (b u) (c u) n*z^n) (Metric.ball w R) := by
    intro u hu
    have hpa := (ascPochhammer ℂ n).differentiable.differentiableAt.comp u (ha u hu)
    have hpb := (ascPochhammer ℂ n).differentiable.differentiableAt.comp u (hb u hu)
    have hpc := (ascPochhammer ℂ n).differentiable.differentiableAt.comp u (hc u hu)
    have hn := pochhammer_ne_zero_of_separated hδ (hsep u hu) n
    exact (((((differentiableAt_const ((n.factorial : ℂ)⁻¹)).mul hpa).mul hpb).mul
      (hpc.inv hn)).mul_const (z^n)).differentiableWithinAt
  have hmaj (n : ℕ) (u : ℂ) (hu : u ∈ Metric.ball w R) :
      ‖ordinaryHypergeometricCoefficient (a u) (b u) (c u) n*z^n‖ ≤
        gaussParameterMajorant B δ N n*‖z‖^n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right (gaussParameterMajorant_bound hB hδ
      (hbound u hu).1 (hbound u hu).2.1 (hbound u hu).2.2 (hsep u hu) N hN n) (pow_nonneg (norm_nonneg _) _)
  have he := differentiableAt_tsum_of_cauchy_dominated hR hdiff hmaj
    (gaussParameterMajorant_summable (δ := δ) hB (norm_nonneg z) hz N)
  simpa only [ordinaryHypergeometric,ordinaryHypergeometric_sum_eq,smul_eq_mul] using he

end
end GaloisForLFunctions.HTGeometry
