import GaloisForLFunctions.RHTower.FokasLenellsCausalHardyConjugation
import GaloisForLFunctions.RHTower.FokasLenellsCauchyCoreRange

/-!
# Actual rational eigenvectors of completed causal Cauchy evolution

The conjugated Hardy evaluation features are literal upper-pole rational
boundary functions. Each is a nonzero eigenvector of every causal operator,
with the actual analytic phase as eigenvalue. Their complex span is dense in
the full lower Hardy space, while the existing pole probes lie outside the
encoded analytic range.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance fokasLenellsCausalRationalEigenvectorsInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalRationalEigenvectorsInst2 : CompleteSpace UpperHardyL2 := isClosed_hardyL2.completeSpace_coe

/-- An actual lower Hardy rational vector with its pole at the supplied upper point. -/
def causalCauchyEigenvector (w : {z : ℂ // 0 < z.im}) : hardyL2ᗮ :=
  causalHardyConjugation (lowerCauchyFeatureAt w.val w.property)

/-- The actual eigenvector is literally the reciprocal upper-pole boundary function almost everywhere. -/
theorem causalCauchyEigenvector_ae (w : {z : ℂ // 0 < z.im}) :
    (causalCauchyEigenvector w).val =ᵐ[volume] fun x : ℝ => ((x:ℂ)-w.val)⁻¹ := by
  filter_upwards [Lp.coeFn_star (lowerCauchyFeatureAt w.val w.property).val,
    coe_lowerCauchyFeatureAt w.property] with x hs hf
  change (star (lowerCauchyFeatureAt w.val w.property).val : SoninL2) x = _
  rw [hs]
  simp only [Pi.star_apply,hf,RCLike.star_def,map_inv₀,map_sub,Complex.conj_ofReal,Complex.conj_conj]

/-- Every actual rational eigenvector is nonzero in the completed lower Hardy norm. -/
theorem causalCauchyEigenvector_ne_zero (w : {z : ℂ // 0 < z.im}) : causalCauchyEigenvector w ≠ 0 := by
  intro h
  apply lowerCauchyFeatureAt_ne_zero w.property
  apply causalHardyConjugation.injective
  exact h.trans (map_zero causalHardyConjugation).symm

/-- The completed causal operator acts on every rational probe by its exact analytic phase value. -/
theorem causalLowerCauchyEvolution_eigenvector (t : ℝ≥0) (w : {z : ℂ // 0 < z.im}) :
    causalLowerCauchyEvolution t (causalCauchyEigenvector w) =
      causalAnalyticPhase t w.val • causalCauchyEigenvector w := by
  rw [causalCauchyEigenvector,causalLowerCauchyEvolution_conjugation,adjoint_causalHardyEvolution_feature,
    map_smulₛₗ,Complex.conj_conj]

/-- Rational eigenvectors have the exact original Cauchy-kernel norm. -/
theorem norm_causalCauchyEigenvector_sq (w : {z : ℂ // 0 < z.im}) :
    ‖causalCauchyEigenvector w‖^(2 : ℕ) = Real.pi/w.val.im := by
  change ‖causalHardyConjugation (lowerCauchyFeatureAt w.val w.property)‖^(2 : ℕ) = _
  rw [causalHardyConjugation.norm_map]
  have h := congrArg Complex.re (inner_lowerCauchyFeatureAt_self w.property)
  calc
    ‖lowerCauchyFeatureAt w.val w.property‖^(2 : ℕ) =
        (inner ℂ (lowerCauchyFeatureAt w.val w.property) (lowerCauchyFeatureAt w.val w.property)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = Real.pi/w.val.im := by simpa only [Complex.ofReal_re] using h

/-- The actual rational causal eigenvectors have dense complex span in the completed data space. -/
theorem topologicalClosure_span_causalCauchyEigenvector_eq_top :
    (Submodule.span ℂ (Set.range causalCauchyEigenvector)).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro f hf
  obtain ⟨u,rfl⟩ := causalHardyConjugation_surjective f
  have hu : u = 0 := by
    apply ((RHTower.topologicalClosure_span_eq_top_iff (Set.range (fun w : {z : ℂ // 0 < z.im} =>
      lowerCauchyFeatureAt w.val w.property))).1 topologicalClosure_span_lowerCauchyFeatureAt_eq_top) u
    rintro g ⟨w,rfl⟩
    have h := hf (causalCauchyEigenvector w) ⟨w,rfl⟩
    change inner ℂ (causalHardyConjugation u)
      (causalHardyConjugation (lowerCauchyFeatureAt w.val w.property)) = 0 at h
    rw [causalHardyConjugation_inner] at h
    have hc := congrArg (starRingEnd ℂ) h
    simpa only [Complex.conj_conj,map_zero] using hc
  rw [hu,map_zero]

/-- The actual upper pole associated with the corpus's existing rational probe coordinates. -/
def causalUpperPolePoint (r a : ℝ) : {z : ℂ // 0 < z.im} :=
  ⟨(r:ℂ)+(Real.exp a:ℂ)*I,by
    simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_add,add_zero] using Real.exp_pos a⟩

/-- The causal rational eigenvectors are exactly the corpus's previously constructed upper-pole probes. -/
theorem causalCauchyEigenvector_upperPole (r a : ℝ) :
    (causalCauchyEigenvector (causalUpperPolePoint r a)).val = upperPoleProbe r a := by
  apply Lp.ext
  have hp : (upperPoleProbe r a : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => ((x:ℂ)-(causalUpperPolePoint r a).val)⁻¹ :=
    (memLp_cauchyKernel (w := (causalUpperPolePoint r a).val)
      (ne_of_gt (causalUpperPolePoint r a).property)).coeFn_toLp
  exact (causalCauchyEigenvector_ae (causalUpperPolePoint r a)).trans hp.symm

end
end RHTower.FokasLenells
