import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

/-!
# Subgroup indicators and one-square jumps

Every subgroup indicator is positive definite. Subtracting its identity value
gives a zero-diagonal kernel with exactly one negative square when the subgroup
is proper. Positive real rescaling preserves this index.
-/

open Complex Finset Matrix
open scoped ComplexConjugate Classical
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- The constant unit kernel is the coefficient of the trivial representation. -/
theorem positive_constant_one : IsPosDefKernel (fun _ : G => (1 : ℂ)) := by
  refine ⟨fun _ => by simp only [map_one], ?_⟩
  intro n x c
  rw [hermQuad_gram]
  have he : (∑ a : Fin n, ∑ b : Fin n, conj (c a) * 1 * c b) =
      conj (∑ a, c a) * ∑ b, c b := by
    rw [map_sum, Finset.sum_mul_sum]
    simp only [mul_one]
  rw [he, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The positive kernel obtained by extending the constant unit kernel from a subgroup. -/
def subgroupIndicatorKernel (H : Subgroup G) : G → ℂ :=
  extendFromSubgroup H (fun _ => 1)

theorem subgroupIndicatorKernel_apply (H : Subgroup G) (g : G) :
    subgroupIndicatorKernel H g = if g ∈ H then 1 else 0 := by
  by_cases hg : g ∈ H
  · simp only [subgroupIndicatorKernel, extendFromSubgroup, dif_pos hg, if_pos hg]
  · simp only [subgroupIndicatorKernel, extendFromSubgroup, dif_neg hg, if_neg hg]

theorem subgroupIndicatorKernel_posDef (H : Subgroup G) :
    IsPosDefKernel (subgroupIndicatorKernel H) :=
  isPosDefKernel_iff_isPosDefOnGroup.mpr
    (isPosDefOnGroup_extendFromSubgroup
      (isPosDefKernel_iff_isPosDefOnGroup.mp positive_constant_one))

/-- The kernel vanishing on a subgroup and equal to minus one on its complement. -/
def subgroupJumpKernel (H : Subgroup G) (g : G) : ℂ := subgroupIndicatorKernel H g - 1

theorem subgroupJumpKernel_apply (H : Subgroup G) (g : G) :
    subgroupJumpKernel H g = if g ∈ H then 0 else -1 := by
  rw [subgroupJumpKernel, subgroupIndicatorKernel_apply]
  split_ifs <;> ring

theorem subgroupJumpKernel_one (H : Subgroup G) : subgroupJumpKernel H 1 = 0 := by
  rw [subgroupJumpKernel_apply, if_pos H.one_mem]

theorem subgroupJumpKernel_hermitian (H : Subgroup G) : IsHermKernel (subgroupJumpKernel H) := by
  intro g
  change subgroupIndicatorKernel H g⁻¹ - 1 =
    (starRingEnd ℂ) (subgroupIndicatorKernel H g - 1)
  rw [(subgroupIndicatorKernel_posDef H).1, map_sub, map_one]

private theorem negIndex_negative_one_le_one : negIndex (fun _ : G => (-1 : ℂ)) ≤ 1 := by
  refine negIndex_le_of_rank (m := 1) (fun _ _ => (1 : ℂ)) ?_
  intro n x c
  simp only [Fin.sum_univ_one, mul_one]
  have he : (∑ i : Fin n, ∑ j : Fin n, conj (c i) * (-1) * c j) =
      -(conj (∑ i, c i) * ∑ j, c j) := by
    rw [map_sum, Finset.sum_mul_sum]
    simp only [mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib]
  rw [hermQuad_gram, he, ← Complex.normSq_eq_conj_mul_self, Complex.neg_re, Complex.ofReal_re]
  simp only [neg_add_cancel, le_refl]

/-- Subtracting the constant unit kernel costs at most one square. -/
theorem negIndex_subgroupJumpKernel_le_one (H : Subgroup G) :
    negIndex (subgroupJumpKernel H) ≤ 1 := by
  have h := negIndex_add_posDef_le (p := subgroupIndicatorKernel H)
    (k := fun _ => (-1 : ℂ)) (subgroupIndicatorKernel_posDef H)
  have he : (fun g => subgroupIndicatorKernel H g + -1) = subgroupJumpKernel H := by
    funext g
    exact (sub_eq_add_neg _ _).symm
  rw [he] at h
  exact h.trans negIndex_negative_one_le_one

/-- A nonzero zero-diagonal subgroup jump has exactly one negative square. -/
theorem negIndex_subgroupJumpKernel (H : Subgroup G) (hH : H ≠ ⊤) :
    negIndex (subgroupJumpKernel H) = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra! h
    apply hH
    ext g
    exact ⟨fun _ => trivial, fun _ => h g⟩
  have hne : negIndex (subgroupJumpKernel H) ≠ 0 := by
    intro hz
    have hp := (isPosDefKernel_iff (subgroupJumpKernel_hermitian H)).mpr hz
    have hb := hp.norm_le g
    have hgval : subgroupJumpKernel H g = -1 := by
      rw [subgroupJumpKernel_apply, if_neg hg]
    rw [hgval, subgroupJumpKernel_one, Complex.zero_re, norm_neg, norm_one] at hb
    norm_num at hb
  exact le_antisymm (negIndex_subgroupJumpKernel_le_one H) (Order.one_le_iff_ne_zero.mpr hne)

/-- Positive real rescaling preserves a group kernel's entire negative index. -/
theorem negIndex_mul_pos_real {a : ℝ} (ha : 0 < a) (k : G → ℂ) :
    negIndex (fun g => (a : ℂ) * k g) = negIndex k := by
  unfold negIndex
  apply iSup_congr
  intro n
  apply iSup_congr
  intro x
  congr 1
  change hermNegIndex ((a : ℂ) • gram k x) = hermNegIndex (gram k x)
  exact negIndex_smul_pos ha _

/-- Every positive multiple of a proper-subgroup jump still costs exactly one square. -/
theorem negIndex_scaled_subgroupJumpKernel (H : Subgroup G) (hH : H ≠ ⊤)
    {a : ℝ} (ha : 0 < a) : negIndex (fun g => (a : ℂ) * subgroupJumpKernel H g) = 1 := by
  rw [negIndex_mul_pos_real ha, negIndex_subgroupJumpKernel H hH]

#print axioms subgroupIndicatorKernel_posDef
#print axioms negIndex_subgroupJumpKernel
#print axioms negIndex_scaled_subgroupJumpKernel
end GaloisForLFunctions.HeckeKreinToeplitz
