import GaloisForLFunctions.HTGeometry.CompactConfigurationBaire
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Dense subspaces preserve finite negative index

Strict negativity on a finite coefficient sphere is an open condition.
Density therefore transfers every finite negative subspace to a prescribed
dense linear subspace, including polynomial test spaces for bounded
signed multiplication operators.
-/

open Set
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HilbertMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The quadratic form of a finite linear combination, for a bounded operator. -/
def finiteFamilyQuadratic (B : E →L[ℝ] E) (v : Fin n → E) (c : Fin n → ℝ) : ℝ :=
  inner ℝ (∑ i, c i • v i) (B (∑ i, c i • v i))

private theorem finiteFamilyQuadratic_smul (B : E →L[ℝ] E) (v : Fin n → E)
    (c : Fin n → ℝ) (r : ℝ) :
    finiteFamilyQuadratic B v (r • c) = r ^ 2 * finiteFamilyQuadratic B v c := by
  have h : (∑ i, (r • c) i • v i) = r • ∑ i, c i • v i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  rw [finiteFamilyQuadratic, h, map_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [finiteFamilyQuadratic]
  ring

/-- A strictly negative family has no nontrivial linear relation. -/
theorem finiteFamilyNegative_injective (B : E →L[ℝ] E) (v : Fin n → E)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 → finiteFamilyQuadratic B v c < 0) :
    Function.Injective (fun c : Fin n → ℝ => ∑ i, c i • v i) := by
  intro c d he
  by_contra hne
  have h := hv (c - d) (sub_ne_zero.mpr hne)
  have hs : (∑ i, (c - d) i • v i) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, he, sub_self]
  rw [finiteFamilyQuadratic, hs, map_zero] at h
  simp at h

/-- Every finite strictly negative family can be replaced by one in any dense linear subspace. -/
theorem exists_negative_family_in_dense_submodule (B : E →L[ℝ] E)
    (S : Submodule ℝ E) (hS : Dense (S : Set E)) (v : Fin n → E)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 → finiteFamilyQuadratic B v c < 0) :
    ∃ w : Fin n → E, (∀ i, w i ∈ S) ∧
      (∀ c : Fin n → ℝ, c ≠ 0 → finiteFamilyQuadratic B w c < 0) ∧
        Function.Injective (fun c : Fin n → ℝ => ∑ i, c i • w i) := by
  classical
  let F : (Fin n → E) × (Fin n → ℝ) → ℝ :=
    fun z => finiteFamilyQuadratic B z.1 z.2
  have hsum : Continuous (fun z : (Fin n → E) × (Fin n → ℝ) => ∑ i, z.2 i • z.1 i) := by
    fun_prop
  have hF : Continuous F := hsum.inner (B.continuous.comp hsum)
  let U := HTGeometry.compactConfigurationAvoidance F (Ici (0 : ℝ)) (Metric.sphere 0 1)
  have hU : IsOpen U := HTGeometry.compactConfigurationAvoidance_isOpen F hF
    (Ici (0 : ℝ)) isClosed_Ici (Metric.sphere 0 1) (isCompact_sphere 0 1)
  have hvU : v ∈ U := by
    intro c hc
    have hcn : ‖c‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hc
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hcn
      exact zero_ne_one hcn
    exact not_le_of_gt (hv c hc0)
  have hdense : Dense (Set.pi Set.univ (fun _ : Fin n => (S : Set E))) :=
    dense_pi Set.univ (fun _ _ => hS)
  obtain ⟨w, hwU, hwS⟩ := (mem_closure_iff.mp (hdense v)) U hU hvU
  have hw : ∀ c : Fin n → ℝ, c ≠ 0 → finiteFamilyQuadratic B w c < 0 := by
    intro c hc
    let d : Fin n → ℝ := ‖c‖⁻¹ • c
    have hdn : ‖d‖ = 1 := by
      dsimp only [d]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg c)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]
    have hd : d ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hdn
    have hneg : finiteFamilyQuadratic B w d < 0 := lt_of_not_ge (hwU d hd)
    rw [show d = ‖c‖⁻¹ • c from rfl, finiteFamilyQuadratic_smul] at hneg
    apply lt_of_not_ge
    intro hnonneg
    exact (not_le_of_gt hneg) (mul_nonneg (sq_nonneg _) hnonneg)
  exact ⟨w, fun i => hwS i (mem_univ i), hw, finiteFamilyNegative_injective B w hw⟩

#print axioms exists_negative_family_in_dense_submodule
end GaloisForLFunctions.HilbertMetric
