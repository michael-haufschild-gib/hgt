import GaloisForLFunctions.HTGeometry.BistochasticMixingMajorization
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral bounds on the finite zero-sum subspace

A symmetric bistochastic kernel preserves zero-sum functions. Restricting to that
subspace and applying the Rayleigh characterization converts its quadratic bound
into a Euclidean norm bound.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace GaloisForLFunctions.HTGeometry
variable {ι : Type*} [Fintype ι]

/-- The zero-sum subspace of a finite real Euclidean space. -/
def finiteZeroSum : Submodule ℝ (EuclideanSpace ℝ ι) where
  carrier := {f | ∑ i, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, PiLp.add_apply, Finset.sum_add_distrib]
    rw [hf, hg, add_zero]
  smul_mem' := by
    intro c f hf
    change ∑ i, f i = 0 at hf
    simp only [Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf,
      mul_zero]


/-- A symmetric real operator is bounded by any uniform absolute quadratic-form bound. -/
theorem symmetric_norm_le_of_quadratic_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, |inner ℝ (T x) x| ≤ c * ‖x‖ ^ 2) : ‖T‖ ≤ c := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hc
  · rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr (h x)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric bistochastic kernel's zero-sum quadratic bound controls its Euclidean norm. -/
theorem bistochastic_zeroSum_norm_le (M : doublyStochastic ℝ ι)
    (hM : ∀ i j, M.val i j = M.val j i) (c : ℝ) (hc : 0 ≤ c)
    (hquad : ∀ f : ι → ℝ, (∑ i, f i) = 0 →
      |∑ i, f i * (M.val *ᵥ f) i| ≤ c * ∑ i, f i ^ 2)
    (f : EuclideanSpace ℝ ι) (hf : ∑ i, f i = 0) :
    ‖Matrix.toEuclideanLin M.val f‖ ≤ c * ‖f‖ := by
  let L := Matrix.toEuclideanLin M.val
  have hmean (x : finiteZeroSum (ι := ι)) : L x ∈ finiteZeroSum (ι := ι) := by
    change (∑ i, (M.val *ᵥ (fun j => (x : EuclideanSpace ℝ ι) j)) i) = 0
    rw [sum_mulVec_of_mem_doublyStochastic M.property]
    exact x.property
  let A : finiteZeroSum (ι := ι) →ₗ[ℝ] finiteZeroSum (ι := ι) :=
    { toFun := fun x => ⟨L x, hmean x⟩
      map_add' := fun x y => Subtype.ext (L.map_add x y)
      map_smul' := fun c x => Subtype.ext (L.map_smul c x) }
  let T := A.toContinuousLinearMap
  have hT : T.IsSymmetric := by
    intro x y
    change inner ℝ (L x) (y : EuclideanSpace ℝ ι) =
      inner ℝ (x : EuclideanSpace ℝ ι) (L y)
    simp only [PiLp.inner_apply, Real.inner_apply]
    change (∑ i, (M.val *ᵥ (fun j => (x : EuclideanSpace ℝ ι) j)) i * y.val i) =
      ∑ i, x.val i * (M.val *ᵥ (fun j => (y : EuclideanSpace ℝ ι) j)) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j i]
    ring
  have hbound (x : finiteZeroSum (ι := ι)) :
      |inner ℝ (T x) x| ≤ c * ‖x‖ ^ 2 := by
    change |inner ℝ (L x) (x : EuclideanSpace ℝ ι)| ≤
      c * ‖(x : EuclideanSpace ℝ ι)‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.inner_apply, Real.inner_apply]
    change |∑ i, (M.val *ᵥ (fun j => x.val j)) i * x.val i| ≤ c * ∑ i, x.val i ^ 2
    simpa only [mul_comm] using hquad (fun i => x.val i) x.property
  have hnorm := symmetric_norm_le_of_quadratic_le T hT c hc hbound
  have h := (T.le_opNorm (⟨f, hf⟩ : finiteZeroSum (ι := ι))).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  exact h

end GaloisForLFunctions.HTGeometry
