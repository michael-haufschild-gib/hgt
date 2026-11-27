import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-! # Product overlap of an approximate eigenvector with a separated local spectrum -/
open Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section

private theorem restricted_overlap {X : Type*} (S : Finset X) (u v : X → ℂ)
    {b c : ℝ} (hb : 0≤b) (hc : 0≤c) (hu : ∑ x∈S, ‖u x‖^2≤b^2)
    (hv : ∑ x∈S, ‖v x‖^2≤c^2) :
    ‖∑ x∈S, conj (u x)*v x‖ ≤ b*c := by
  have ht : ‖∑ x∈S, conj (u x)*v x‖ ≤ ∑ x∈S, ‖u x‖*‖v x‖ :=
    (norm_sum_le _ _).trans_eq (by simp only [norm_mul,Complex.norm_conj])
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb hc)).mp
  rw [mul_pow]
  exact ((pow_le_pow_left₀ (norm_nonneg _) ht 2).trans (sum_mul_sq_le_sq_mul_sq S _ _)).trans
    (mul_le_mul hu hv (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))

/-- In a unit energy band there is at most one local level per
spectator level. The possible product overlap costs the largest local
amplitude plus the norm of the energy residual. -/
theorem resonant_slice {I J : Type*} [Fintype I] [Fintype J] [Nonempty I]
    (E : I → ℝ) (F : J → ℝ) (λ₀ : ℝ) (hgap : ∀ i l, i≠l → 2≤|E i-E l|)
    (u : I → ℂ) (v : J → ℂ) (ψ : J × I → ℂ) {b δ : ℝ}
    (hb : 0≤b) (hδ : 0≤δ) (hu : ∑ i, ‖u i‖^2=1) (hv : ∑ j, ‖v j‖^2=1)
    (hψ : ∑ x, ‖ψ x‖^2=1) (hmax : ∀ i, ‖u i‖≤b)
    (herr : ∑ x : J × I, (E x.2+F x.1-λ₀)^2*‖ψ x‖^2 ≤ δ^2) :
    ‖∑ x : J × I, conj (v x.1*u x.2)*ψ x‖ ≤ b+δ := by
  classical
  let a (j : J) : I := if h : ∃ i, |E i+F j-λ₀|<1 then h.choose else Classical.choice inferInstance
  have hfar (j : J) (i : I) (hne : i≠a j) : 1 ≤ |E i+F j-λ₀| := by
    by_contra! hn
    have hex : ∃ l, |E l+F j-λ₀|<1 := ⟨i,hn⟩
    have hsel : |E (a j)+F j-λ₀|<1 := by simpa only [a,dif_pos hex] using hex.choose_spec
    rcases abs_lt.mp hsel with ⟨hl,hr⟩
    rcases abs_lt.mp hn with ⟨hi,hj⟩
    exact (hgap i (a j) hne).not_gt (abs_lt.mpr ⟨by linarith only [hi,hr],by linarith only [hj,hl]⟩)
  let S := univ.image (fun j : J => (j,a j))
  let w (x : J × I) := v x.1*u x.2
  have hw : ∑ x, ‖w x‖^2=1 := by
    rw [Fintype.sum_prod_type]
    simp only [w,norm_mul,mul_pow,←mul_sum,hu,mul_one,hv]
  have hgood : ∑ x∈S, ‖w x‖^2 ≤ b^2 := by
    rw [Finset.sum_image (fun j _ l _ h => congrArg Prod.fst h)]
    calc _ ≤ ∑ j, ‖v j‖^2*b^2 := sum_le_sum fun j _ => by
           dsimp only [w]
           rw [norm_mul,mul_pow]
           exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hmax _) _) (sq_nonneg _)
         _ = _ := by rw [←sum_mul,hv,one_mul]
  have hbad : ∑ x∈Sᶜ, ‖ψ x‖^2 ≤ δ^2 := by
    apply le_trans _ herr
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (subset_univ Sᶜ)
      (fun x _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg ‖ψ x‖)))
    apply sum_le_sum
    intro x hx
    have hne : x.2≠a x.1 := by
      intro he
      exact (mem_compl.mp hx) (mem_image.mpr ⟨x.1,mem_univ _,Prod.ext rfl he.symm⟩)
    have hsq := pow_le_pow_left₀ zero_le_one (hfar x.1 x.2 hne) 2
    rw [one_pow,sq_abs] at hsq
    exact le_mul_of_one_le_left (sq_nonneg _) hsq
  have hG := restricted_overlap S w ψ hb zero_le_one hgood (by
    rw [one_pow,←hψ]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _))
  have hB := restricted_overlap Sᶜ w ψ zero_le_one hδ (by
    rw [one_pow,←hw]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)) hbad
  rw [mul_one] at hG
  rw [one_mul] at hB
  rw [←sum_add_sum_compl S]
  exact (norm_add_le _ _).trans (add_le_add hG hB)

#print axioms resonant_slice
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
