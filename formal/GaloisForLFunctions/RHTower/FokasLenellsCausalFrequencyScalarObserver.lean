import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCompletedObservability
import GaloisForLFunctions.HTGeometry.HardyDiskLineCayleyUnitary
import Mathlib.Analysis.InnerProductSpace.Dual
open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem upper_feature_inner_ne_zero (z w : UpperHalfPlanePoint) :
    inner ℂ (lowerCauchyFeatureAt z.val z.property)
      (lowerCauchyFeatureAt w.val w.property) ≠ 0 := by
  have hd : z.val - (starRingEnd ℂ) w.val ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    linarith [z.property, w.property]
  rw [inner_lowerCauchyFeatureAt_cross]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) (inv_ne_zero hd)

/-- Two actual rational Cauchy eigenvectors are never orthogonal, for arbitrary
native upper-half-plane poles. -/
theorem causalCauchyEigenvector_inner_ne_zero
    (z w : {z : ℂ // 0 < z.im}) :
    inner ℂ (causalCauchyEigenvector z) (causalCauchyEigenvector w) ≠ 0 := by
  change inner ℂ (causalHardyConjugation (lowerCauchyFeatureAt z.val z.property))
    (causalHardyConjugation (lowerCauchyFeatureAt w.val w.property)) ≠ 0
  rw [causalHardyConjugation_inner]
  intro h
  apply upper_feature_inner_ne_zero z w
  have hc := congrArg (starRingEnd ℂ) h
  simpa only [Complex.conj_conj, map_zero] using hc

private theorem normalized_inner_ne_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v w : H) (hv : v ≠ 0) (hw : w ≠ 0) (hi : inner ℂ v w ≠ 0) :
    inner ℂ ((‖v‖ : ℂ)⁻¹ • v) ((‖w‖ : ℂ)⁻¹ • w) ≠ 0 := by
  rw [inner_smul_left, inner_smul_right]
  apply mul_ne_zero
  · simpa only [map_inv₀, Complex.conj_ofReal, ne_eq, inv_eq_zero,
      Complex.ofReal_eq_zero, norm_eq_zero] using hv
  · exact mul_ne_zero
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))) hi

/-- Unit normalization preserves the nonzero Cauchy pairing of every two
actual frequency modes in one chart. -/
theorem causalUnitBoundaryEigenvector_inner_ne_zero (b η ω : ℝ) :
    inner ℂ (causalUnitBoundaryEigenvector b η).val
      (causalUnitBoundaryEigenvector b ω).val ≠ 0 :=
  normalized_inner_ne_zero
    (causalCauchyEigenvector (causalEigenPole (causalUnitBoundaryRate b η)))
    (causalCauchyEigenvector (causalEigenPole (causalUnitBoundaryRate b ω)))
    (causalCauchyEigenvector_ne_zero _) (causalCauchyEigenvector_ne_zero _)
    (causalCauchyEigenvector_inner_ne_zero _ _)

section ScalarObservation
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def scalarObservation (q : E →L[ℂ] H) (h : H) : E →L[ℂ] ℂ :=
  (innerSL ℂ h).comp q

private theorem scalarObservation_mode_ne_zero {I : Type*}
    (q : E →L[ℂ] H) (v : I → E) (h : I → H)
    (hq : ∀ i, q (v i) = h i) (hinner : ∀ i j, inner ℂ (h i) (h j) ≠ 0)
    (i j : I) : scalarObservation q (h i) (v j) ≠ 0 := by
  change inner ℂ (h i) (q (v j)) ≠ 0
  rw [hq]
  exact hinner i j

private theorem scalarObservation_norm_one
    (q : E →L[ℂ] H) (hq : ∀ u, ‖q u‖ ≤ ‖u‖)
    (h : H) (hh : ‖h‖ = 1) (v : E) (hv : ‖v‖ = 1) (hqv : q v = h) :
    ‖scalarObservation q h‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    change ‖inner ℂ h (q u)‖ ≤ 1 * ‖u‖
    simpa only [hh, one_mul] using (norm_inner_le_norm h (q u)).trans
      (mul_le_mul_of_nonneg_left (hq u) (norm_nonneg h))
  · have he : scalarObservation q h v = 1 := by
      change inner ℂ h (q v) = 1
      rw [hqv]
      exact inner_self_eq_one_of_norm_eq_one hh
    have hb := (scalarObservation q h).le_opNorm v
    simpa only [he, norm_one, hv, mul_one] using hb
end ScalarObservation

/-- A concrete scalar sensor: pair the original derivative coordinate with
one fixed actual normalized rational mode. -/
def causalFrequencyScalarObserver (b η : ℝ) : causalFrequencySpace b →L[ℂ] ℂ :=
  scalarObservation
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (causalUnitBoundaryEigenvector b η).val

/-- This single scalar sensor sees every actual frequency mode, without an
additional nonvanishing or genericity assumption. -/
theorem causalFrequencyScalarObserver_mode_ne_zero (b η ω : ℝ) :
    causalFrequencyScalarObserver b η (causalFrequencyMode b ω) ≠ 0 :=
  scalarObservation_mode_ne_zero
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (causalFrequencyMode b) (fun ξ => (causalUnitBoundaryEigenvector b ξ).val)
    (causalBoundedUnitEigenchain_zero b) (causalUnitBoundaryEigenvector_inner_ne_zero b) η ω

/-- The scalar sensor is bounded with sharp operator norm one. -/
theorem norm_causalFrequencyScalarObserver (b η : ℝ) :
    ‖causalFrequencyScalarObserver b η‖ = 1 :=
  scalarObservation_norm_one
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (fun u => causalBoundedChainCoordinate_norm_le 0 u.val)
    (causalUnitBoundaryEigenvector b η).val (norm_causalUnitBoundaryEigenvector b η)
    (causalFrequencyMode b η) (norm_causalBoundedUnitEigenchain b η)
    (causalBoundedUnitEigenchain_zero b η)

/-- The long-run squared output of one explicit norm-one scalar sensor
detects every nonzero vector in the actual completed frequency space. -/
theorem causalFrequencyScalarObserver_mean_zero_iff (b η : ℝ) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖causalFrequencyScalarObserver b η (((causalFrequencyShift b) ^ n) u)‖ ^ 2)
      atTop (𝓝 0) ↔ u = 0 :=
  ((causalFrequencyShift_completed_hilbert_observable_iff b (causalFrequencyScalarObserver b η)).2
    (causalFrequencyScalarObserver_mode_ne_zero b η)) u

end RHTower.FokasLenells
