import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorGraph
import GaloisForLFunctions.RHTower.FokasLenellsCausalInformationLoss
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Generator dissipation and positive shift stability

The contraction law forces a nonpositive real generator pairing on its entire
maximal domain. Differentiating the exact retained/lost energy identity then
identifies the initial information-loss rate. Every strictly positive shift
has a quantitative lower bound, hence is injective, in the original data norm.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : InnerProductSpace ℝ (hardyL2ᗮ) := InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)

/-- The completed orbit energy has its exact right derivative on the maximal domain. -/
theorem causalGenerator_energy_hasRightDeriv (u : causalGeneratorDomain) :
    HasDerivWithinAt (fun r : ℝ => ‖causalForwardOrbit u.val r‖^2)
      (2 * inner ℝ u.val (causalGenerator u)) (Ioi 0) 0 := by
  simpa only [causalForwardOrbit_zero] using (causalGenerator_hasRightDeriv u).norm_sq

/-- The actual maximal generator is dissipative for the original Hilbert inner product. -/
theorem causalGenerator_dissipative (u : causalGeneratorDomain) :
    inner ℝ u.val (causalGenerator u) ≤ 0 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).1
    (causalGenerator_energy_hasRightDeriv u)
  have he : 2 * inner ℝ u.val (causalGenerator u) ≤ 0 := by
    apply le_of_tendsto ht
    have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
    filter_upwards [hpos] with r hr
    simp only [slope_def_module,sub_zero,causalForwardOrbit_zero,smul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hr.le)
    have hb := causalLowerCauchyEvolution_norm_le r.toNNReal u.val
    change ‖causalForwardOrbit u.val r‖ ≤ ‖u.val‖ at hb
    nlinarith [norm_nonneg (causalForwardOrbit u.val r),norm_nonneg u.val]
  linarith

/-- The actual initial information-loss rate, with no externally chosen dissipation data. -/
def causalDissipationRate (u : causalGeneratorDomain) : ℝ :=
  -2 * inner ℝ u.val (causalGenerator u)

/-- The generator's actual information-loss rate is nonnegative. -/
theorem causalDissipationRate_nonneg (u : causalGeneratorDomain) : 0 ≤ causalDissipationRate u := by
  unfold causalDissipationRate
  have h := causalGenerator_dissipative u
  linarith

/-- The actual lost energy has the rate supplied by the maximal generator. -/
theorem causalLossProjection_energy_hasRightDeriv (u : causalGeneratorDomain) :
    HasDerivWithinAt (fun r : ℝ => ‖causalLossProjection r.toNNReal u.val‖^2)
      (causalDissipationRate u) (Ioi 0) 0 := by
  have hd := (hasDerivWithinAt_const (0:ℝ) (Ioi 0) (‖u.val‖^2)).sub
    (causalGenerator_energy_hasRightDeriv u)
  have he (r : ℝ) : ‖causalLossProjection r.toNNReal u.val‖^2 =
      ‖u.val‖^2-‖causalForwardOrbit u.val r‖^2 := by
    have h := causalLowerCauchyEvolution_energy_decomposition r.toNNReal u.val
    change ‖u.val‖^2 = ‖causalForwardOrbit u.val r‖^2+‖causalLossProjection r.toNNReal u.val‖^2 at h
    linarith
  have hd' : HasDerivWithinAt (fun r : ℝ => ‖u.val‖^2-‖causalForwardOrbit u.val r‖^2)
      (causalDissipationRate u) (Ioi 0) 0 := by
    simpa only [Pi.sub_apply,zero_sub,causalDissipationRate,neg_mul] using! hd
  exact hd'.congr (fun r _ => he r) (he 0)

/-- The finite-time lost-energy quotient converges to the actual nonnegative generator rate. -/
theorem causalLossProjection_energy_quotient_tendsto (u : causalGeneratorDomain) :
    Tendsto (fun r : ℝ => r⁻¹ * ‖causalLossProjection r.toNNReal u.val‖^2)
      (𝓝[>] 0) (𝓝 (causalDissipationRate u)) := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).1
    (causalLossProjection_energy_hasRightDeriv u)
  have hz : ‖causalLossProjection 0 u.val‖^2 = 0 := by
    have h := causalLowerCauchyEvolution_energy_decomposition 0 u.val
    rw [causalLowerCauchyEvolution_zero] at h
    linarith
  change Tendsto (fun r : ℝ => slope (fun s : ℝ => ‖causalLossProjection s.toNNReal u.val‖^2) 0 r)
    (𝓝[>] 0) (𝓝 (causalDissipationRate u)) at ht
  simpa only [slope_def_module,sub_zero,Real.toNNReal_zero,hz,smul_eq_mul] using ht

/-- A strictly positive scalar shift of the actual generator on its unchanged maximal domain. -/
def causalGeneratorShift (a : ℝ) : causalGeneratorDomain →ₗ[ℂ] hardyL2ᗮ :=
  ((Real.exp a : ℝ) : ℂ) • causalGeneratorDomain.subtype - causalGenerator

/-- Every positive shift is bounded below quantitatively in the original data norm. -/
theorem causalGeneratorShift_norm_lowerBound (a : ℝ) (u : causalGeneratorDomain) :
    Real.exp a * ‖u.val‖ ≤ ‖causalGeneratorShift a u‖ := by
  have he := norm_sub_sq_real ((Real.exp a) • u.val) (causalGenerator u)
  have hi : inner ℝ ((Real.exp a) • u.val) (causalGenerator u) =
      Real.exp a * inner ℝ u.val (causalGenerator u) := by
    exact real_inner_smul_left _ _ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos a),hi] at he
  have hd := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos a).le (causalGenerator_dissipative u)
  have hn : ‖causalGeneratorShift a u‖ = ‖(Real.exp a) • u.val-causalGenerator u‖ := by
    change ‖((Real.exp a : ℝ):ℂ) • u.val-causalGenerator u‖ = _
    change ‖(algebraMap ℝ ℂ (Real.exp a)) • u.val-causalGenerator u‖ = _
    rw [algebraMap_smul]
  rw [hn]
  nlinarith [sq_nonneg ‖causalGenerator u‖,norm_nonneg ((Real.exp a) • u.val-causalGenerator u),
    mul_nonneg (Real.exp_pos a).le (norm_nonneg u.val)]

/-- Every strictly positive shift of the maximal generator is injective. -/
theorem causalGeneratorShift_injective (a : ℝ) : Function.Injective (causalGeneratorShift a) := by
  intro u v h
  have hb := causalGeneratorShift_norm_lowerBound a (u-v)
  rw [map_sub,h,sub_self,norm_zero] at hb
  have hn : ‖u.val-v.val‖ = 0 := by
    have hn0 : 0 ≤ ‖u.val-v.val‖ := norm_nonneg _
    change Real.exp a * ‖u.val-v.val‖ ≤ 0 at hb
    nlinarith [Real.exp_pos a]
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end
end RHTower.FokasLenells
