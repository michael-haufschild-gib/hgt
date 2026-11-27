import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Transverse

/-! # The fourteen transverse coordinates at an interior spin -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section
variable {n : ℕ}

private def xy := (univ : Finset (Fin 3)).erase 2

/-- Two onsite coefficients and six coefficients on each incident edge. -/
def transverseLabels (a b : Fin (n+1)) : Finset (PathLabel n) :=
  (xy.image fun p => Sum.inl (a.succ,p)) ∪
  ((univ ×ˢ xy).image fun p => Sum.inr (a,p)) ∪
  ((xy ×ˢ univ).image fun p => Sum.inr (b,p))

theorem transverseLabels_card (a b : Fin (n+1)) : (transverseLabels a b).card≤14 := by
  have hxy : xy.card=2 := by simp [xy]
  unfold transverseLabels
  apply (card_union_le ..).trans
  apply (Nat.add_le_add (card_union_le ..) Finset.card_image_le).trans
  apply (Nat.add_le_add_right (Nat.add_le_add Finset.card_image_le Finset.card_image_le) _).trans
  rw [card_product,card_product,hxy,card_univ,Fintype.card_fin]

theorem transverseLabels_axial {a b : Fin (n+1)} (hab : a.succ=b.castSucc) (l : PathLabel n)
    (hl : l∉transverseLabels a b) : axial a.succ l := by
  rcases l with ⟨i,p⟩|⟨e,p,r⟩
  · by_cases hi : a.succ=i
    · subst i
      have hp : p=2 := by
        by_contra h
        exact hl (mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨p,mem_erase.mpr ⟨h,mem_univ _⟩,rfl⟩)))
      simp [axial,pathWord,onsiteWord,hp]
    · simp [axial,pathWord,onsiteWord,hi]
  · by_cases h₁ : a.succ=e.castSucc
    · have he : b=e := Fin.castSucc_injective _ (hab.symm.trans h₁)
      subst e
      have hp : p=2 := by
        by_contra h
        exact hl (mem_union_right _ (mem_image.mpr
          ⟨(p,r),mem_product.mpr ⟨mem_erase.mpr ⟨h,mem_univ _⟩,mem_univ _⟩,rfl⟩))
      simp [axial,pathWord,couplingWord,hab,hp]
    · by_cases h₂ : a.succ=e.succ
      · have he : a=e := Fin.succ_injective _ h₂
        subst e
        have hr : r=2 := by
          by_contra h
          exact hl (mem_union_left _ (mem_union_right _ (mem_image.mpr
            ⟨(p,r),mem_product.mpr ⟨mem_univ _,mem_erase.mpr ⟨h,mem_univ _⟩⟩,rfl⟩)))
        simp [axial,pathWord,couplingWord,h₁,hr]
      · simp [axial,pathWord,couplingWord,h₁,h₂]

/-- A coordinate box of radius δ contributes at most 14δ in operator norm. -/
theorem offAxis_norm {a b : Fin (n+1)} (hab : a.succ=b.castSucc) (u : PathShell n)
    {δ : ℝ} (hδ : 0≤δ) (hu : ∀ l∈transverseLabels a b, |u l|≤δ) :
    ‖pathHamiltonian (offAxis a.succ u)‖≤14*δ := by
  classical
  rw [pathHamiltonian_eq_sum]
  apply (norm_sum_le ..).trans
  let S := transverseLabels a b
  calc
    _ ≤ ∑ l : PathLabel n, if l∈S then δ else 0 := by
      apply sum_le_sum
      intro l _
      rw [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
      by_cases h : l∈S
      · rw [if_pos h]
        by_cases hx : axial a.succ l
        · rw [restricted_zero (P:=fun x => ¬axial a.succ x) u (not_not_intro hx),abs_zero]
          exact hδ
        · rw [restricted_eq (P:=fun x => ¬axial a.succ x) u hx]
          exact hu l h
      · rw [if_neg h,restricted_zero (P:=fun x => ¬axial a.succ x) u
          (not_not_intro (transverseLabels_axial hab l h)),abs_zero]
    _ = (S.card:ℝ)*δ := by simp [sum_ite_mem,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast transverseLabels_card a b) hδ

#print axioms offAxis_norm
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
