import GaloisForLFunctions.HTGeometry.CompactAbelianConvolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The convolution operator on `L²` of a compact abelian group

Convolution with a continuous kernel is a bounded operator on `L²(G)`.  Because the group carries a
probability measure, the `L¹` size of a function is dominated by its `L²` norm, and the convolution
of an `L²` function is a *continuous* function with sup norm at most `‖k‖_∞ ‖u‖₂`.  So the operator
factors through the continuous functions,

`L²(G) → C(G) → L²(G)`,

which is the factorization that makes it compact.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
theorem integrable_lp (u : Lp ℂ 2 (haarProb G)) : Integrable (fun y => u y) (haarProb G) :=
  (Lp.memLp u).integrable one_le_two

omit [T2Space G] in
/-- On a probability space the `L¹` size of a function is at most its `L²` norm. -/
theorem integral_norm_le_norm (u : Lp ℂ 2 (haarProb G)) :
    ∫ y, ‖u y‖ ∂(haarProb G) ≤ ‖u‖ := by
  have hint : Integrable (fun y => u y) (haarProb G) := integrable_lp u
  have hcoe : (fun y => (hint.toL1 _) y) =ᵐ[haarProb G] fun y => u y := hint.coeFn_toL1
  have h1 : ‖hint.toL1 (fun y => u y)‖ = ∫ y, ‖u y‖ ∂(haarProb G) := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (by filter_upwards [hcoe] with y hy; rw [hy])
  have h2 : ‖hint.toL1 (fun y => u y)‖ = (eLpNorm (fun y => u y) 1 (haarProb G)).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hcoe)
  have h3 : eLpNorm (fun y => u y) 1 (haarProb G) ≤ eLpNorm (fun y => u y) 2 (haarProb G) :=
    eLpNorm_le_eLpNorm_of_exponent_le one_le_two (Lp.aestronglyMeasurable u)
  have h4 : eLpNorm (fun y => u y) 2 (haarProb G) ≠ ⊤ := (Lp.memLp u).eLpNorm_ne_top
  rw [← h1, h2, Lp.norm_def]
  exact ENNReal.toReal_mono h4 h3

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

include hk hC in
/-- The convolution of an `L²` function, as a continuous function. -/
def convC (u : Lp ℂ 2 (haarProb G)) : C(G, ℂ) :=
  ⟨convFun k (fun y => u y), continuous_convFun hk hC (integrable_lp u)⟩

omit [T2Space G] in
include hk hC in
@[simp] theorem convC_apply (u : Lp ℂ 2 (haarProb G)) (x : G) :
    convC k hk hC u x = convFun k (fun y => u y) x := rfl

omit [T2Space G] in
include hk hC in
theorem convC_add (u v : Lp ℂ 2 (haarProb G)) :
    convC k hk hC (u + v) = convC k hk hC u + convC k hk hC v := by
  ext x
  have hco : (fun y => (u + v) y) =ᵐ[haarProb G] fun y => u y + v y := Lp.coeFn_add u v
  have h1 : convFun k (fun y => (u + v) y) x
      = ∫ y, (u y + v y) * k (x - y) ∂(haarProb G) := by
    refine integral_congr_ae ?_
    filter_upwards [hco] with y hy
    rw [hy]
  have hgoal : (convC k hk hC u + convC k hk hC v) x
      = convFun k (fun y => u y) x + convFun k (fun y => v y) x := rfl
  have hsplit : ∀ y : G, (u y + v y) * k (x - y) = u y * k (x - y) + v y * k (x - y) := by
    intro y; ring
  rw [convC_apply, hgoal, h1, integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add (integrable_mul_kernel hk hC (integrable_lp u) x)
      (integrable_mul_kernel hk hC (integrable_lp v) x)]
  rfl

omit [T2Space G] in
include hk hC in
theorem convC_smul (c : ℂ) (u : Lp ℂ 2 (haarProb G)) :
    convC k hk hC (c • u) = c • convC k hk hC u := by
  ext x
  have hco : (fun y => (c • u) y) =ᵐ[haarProb G] fun y => c • u y := Lp.coeFn_smul c u
  have h1 : convFun k (fun y => (c • u) y) x
      = ∫ y, c * (u y * k (x - y)) ∂(haarProb G) := by
    refine integral_congr_ae ?_
    filter_upwards [hco] with y hy
    rw [hy]
    simp [smul_eq_mul, mul_assoc]
  have hgoal : (c • convC k hk hC u) x = c * convFun k (fun y => u y) x := rfl
  rw [convC_apply, hgoal, h1, integral_const_mul]
  rfl

omit [T2Space G] in
include hk hC in
theorem norm_convC_le (u : Lp ℂ 2 (haarProb G)) : ‖convC k hk hC u‖ ≤ C * ‖u‖ := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  calc ‖convC k hk hC u x‖ ≤ C * ∫ y, ‖u y‖ ∂(haarProb G) :=
        norm_convFun_le hk hC (integrable_lp u) x
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_left (integral_norm_le_norm u) hCnonneg

include hk hC in
/-- Convolution as a continuous linear map into the continuous functions. -/
def convCLM : Lp ℂ 2 (haarProb G) →L[ℂ] C(G, ℂ) :=
  LinearMap.mkContinuous
    { toFun := convC k hk hC
      map_add' := convC_add k hk hC
      map_smul' := convC_smul k hk hC } C (norm_convC_le k hk hC)

omit [T2Space G] in
include hk hC in
@[simp] theorem convCLM_apply (u : Lp ℂ 2 (haarProb G)) : convCLM k hk hC u = convC k hk hC u := rfl

include hk hC in
/-- **The convolution operator on `L²`.** -/
def convOp : Lp ℂ 2 (haarProb G) →L[ℂ] Lp ℂ 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) ℂ).comp (convCLM k hk hC)

omit [T2Space G] in
include hk hC in
theorem convOp_apply (u : Lp ℂ 2 (haarProb G)) :
    convOp k hk hC u = ContinuousMap.toLp 2 (haarProb G) ℂ (convC k hk hC u) := rfl

omit [T2Space G] in
include hk hC in
theorem convOp_coeFn (u : Lp ℂ 2 (haarProb G)) :
    (fun x => (convOp k hk hC u) x) =ᵐ[haarProb G] fun x => convC k hk hC u x :=
  ContinuousMap.coeFn_toLp (haarProb G) (convC k hk hC u)

end

end CompactAbelian

end GaloisForLFunctions
