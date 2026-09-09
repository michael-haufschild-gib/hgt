import GaloisForLFunctions.RHTower.FokasLenellsCausalCoisometry
import GaloisForLFunctions.HTGeometry.FokasLenellsCausalHardyOrientation

/-!
# Actual Hardy conjugation of the completed causal semigroup

Pointwise conjugation exchanges the two Hardy halves and reverses the raw
phase. The completed lower Hardy coisometry is therefore the conjugate of
the upper Hardy semigroup adjoint. This connects the existing reproducing
feature eigenformula to actual lower Hardy dynamics.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace UpperHardyL2 := isClosed_hardyL2.completeSpace_coe

/-- Pointwise conjugation reverses the actual real spectral phase, including zero frequency. -/
theorem star_phase (t x : ℝ) : (starRingEnd ℂ) (phase t x) = phase (-t) x := by
  simp only [phase,← Complex.exp_conj,map_neg,map_mul,Complex.conj_ofReal,Complex.conj_I,
    neg_div,Complex.ofReal_neg,neg_mul,mul_neg,neg_neg]

/-- Pointwise conjugation reverses the actual raw unitary evolution on whole-line L². -/
theorem star_evolution (t : ℝ) (u : SoninL2) : star (evolution t u) = evolution (-t) (star u) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (evolution t u),evolution_ae t u,
    evolution_ae (-t) (star u),Lp.coeFn_star u] with x h0 h1 h2 h3
  rw [h0,h2]
  simp only [Pi.star_apply,h1,h3,star_mul]
  rw [show star (phase t x) = phase (-t) x from star_phase t x]
  ring

private theorem norm_star_L2 (u : SoninL2) : ‖star u‖ = ‖u‖ := by
  have h : ‖star u‖^2 = ‖u‖^2 := by
    calc
      ‖star u‖^2 = (inner ℂ (star u) (star u)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (inner ℂ u u).re := by rw [inner_star_star_realLineL2,Complex.conj_re]
      _ = ‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  nlinarith [norm_nonneg u,norm_nonneg (star u)]

/-- Literal conjugation as an anti-linear isometry from upper to lower Hardy data. -/
def causalHardyConjugation : UpperHardyL2 →ₛₗᵢ[starRingEnd ℂ] hardyL2ᗮ where
  toLinearMap := {
    toFun u := ⟨star u.val,by rw [← map_star_hardyL2]; exact ⟨u.val,u.property,rfl⟩⟩
    map_add' u v := by apply Subtype.ext; exact lpStar_add _ _
    map_smul' c u := by apply Subtype.ext; exact lpStar_smul _ _ }
  norm_map' u := norm_star_L2 u.val

/-- Actual conjugation covers the whole lower Hardy completion. -/
theorem causalHardyConjugation_surjective : Function.Surjective causalHardyConjugation := by
  intro u
  have h := (congrArg (fun S : Submodule ℂ SoninL2 => u.val ∈ S) map_star_hardyL2).mpr u.property
  obtain ⟨v,hv,he⟩ := h
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩

/-- Conjugation preserves the inner product with precisely complex conjugation of its value. -/
theorem causalHardyConjugation_inner (u v : UpperHardyL2) :
    inner ℂ (causalHardyConjugation u) (causalHardyConjugation v) =
      (starRingEnd ℂ) (inner ℂ u v) := inner_star_star_realLineL2 u.val v.val

/-- Opposite-time lower Hardy recovery is the conjugate of actual upper Hardy forward evolution. -/
theorem causalLowerRecovery_conjugation (t : ℝ≥0) (u : UpperHardyL2) :
    causalLowerRecovery t (causalHardyConjugation u) =
      causalHardyConjugation (causalHardyEvolution t u) := by
  apply Subtype.ext
  exact (star_evolution (t:ℝ) u.val).symm

/-- The completed lower coisometry is exactly the conjugate upper Hardy adjoint action. -/
theorem causalLowerCauchyEvolution_conjugation (t : ℝ≥0) (u : UpperHardyL2) :
    causalLowerCauchyEvolution t (causalHardyConjugation u) =
      causalHardyConjugation ((causalHardyEvolution t).toContinuousLinearMap.adjoint u) := by
  apply ext_inner_right ℂ
  intro y
  obtain ⟨v,rfl⟩ := causalHardyConjugation_surjective y
  rw [← ContinuousLinearMap.adjoint_inner_right,causalLowerCauchyEvolution_adjoint]
  change inner ℂ (causalHardyConjugation u) (causalLowerRecovery t (causalHardyConjugation v)) = _
  rw [causalLowerRecovery_conjugation,causalHardyConjugation_inner,causalHardyConjugation_inner,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

end
end RHTower.FokasLenells
