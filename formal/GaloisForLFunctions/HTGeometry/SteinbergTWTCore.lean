import GaloisForLFunctions.HTGeometry.SteinbergFinFourUpperNormalForm
import GaloisForLFunctions.HTGeometry.SteinbergWeylWordNormalForm

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n] [LinearOrder n]

def steinbergTWT : Set (SteinbergGroup F n) :=
  {g | ∃ t₁ w t₂, t₁ ∈ upperSteinbergSubgroup (F := F) n
    ∧ w ∈ steinbergWeylWordSubgroup (F := F) (n := n)
    ∧ t₂ ∈ upperSteinbergSubgroup (F := F) n ∧ g = t₁ * w * t₂}

omit [DecidableEq n] in
theorem upper_mem_steinbergTWT {t : SteinbergGroup F n}
    (ht : t ∈ upperSteinbergSubgroup (F := F) n) : t ∈ steinbergTWT (F := F) (n := n) :=
  ⟨t, 1, 1, ht, Subgroup.one_mem _, Subgroup.one_mem _, by simp⟩

omit [DecidableEq n] in
theorem weyl_mem_steinbergTWT {w : SteinbergGroup F n}
    (hw : w ∈ steinbergWeylWordSubgroup (F := F) (n := n)) :
    w ∈ steinbergTWT (F := F) (n := n) :=
  ⟨1, w, 1, Subgroup.one_mem _, hw, Subgroup.one_mem _, by simp⟩

omit [DecidableEq n] in
theorem steinbergTWT_inv {g : SteinbergGroup F n} (hg : g ∈ steinbergTWT (F := F) (n := n)) :
    g⁻¹ ∈ steinbergTWT (F := F) (n := n) := by
  rcases hg with ⟨t₁, w, t₂, ht₁, hw, ht₂, rfl⟩
  refine ⟨t₂⁻¹, w⁻¹, t₁⁻¹, (upperSteinbergSubgroup (F := F) n).inv_mem ht₂,
    (steinbergWeylWordSubgroup (F := F) (n := n)).inv_mem hw,
    (upperSteinbergSubgroup (F := F) n).inv_mem ht₁, ?_⟩
  group

theorem weyl_conj_upper_root_mem_TWT {w : SteinbergGroup F n}
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    (hw : w ∈ steinbergWeylWordSubgroup (F := F) (n := n))
    {p q : n} (hpq : p ≠ q) (a : F) :
    w * steinbergX hpq a * w⁻¹ ∈ steinbergTWT (F := F) (n := n) := by
  obtain ⟨σ, c, haction⟩ := exists_signed_root_action_of_mem hspare hw
  rw [haction p q hpq a]
  by_cases horder : σ p < σ q
  · exact upper_mem_steinbergTWT
      (Subgroup.subset_closure ⟨σ p, σ q, σ.injective.ne_iff.mpr hpq,
        ((c p : F) * ((c q)⁻¹ : F) * a), horder, rfl⟩)
  · have hreverse : σ q < σ p := lt_of_le_of_ne (le_of_not_gt horder)
      (Ne.symm (σ.injective.ne_iff.mpr hpq))
    set d : F := (c p : F) * ((c q)⁻¹ : F) * a
    by_cases hd : d = 0
    · rw [hd, steinbergX_zero]
      exact upper_mem_steinbergTWT (Subgroup.one_mem _)
    · let b : Fˣ := Units.mk0 d hd
      have hfactor := steinbergX_lower_eq_upper_weyl_upper
        (σ.injective.ne_iff.mpr hpq) b
      rw [← show (b : F) = d by simp [b], hfactor]
      refine ⟨(steinbergX (Ne.symm (σ.injective.ne_iff.mpr hpq))
          ((-b⁻¹ : Fˣ) : F))⁻¹, steinbergWeyl (Ne.symm (σ.injective.ne_iff.mpr hpq)) (-b⁻¹),
        (steinbergX (Ne.symm (σ.injective.ne_iff.mpr hpq)) ((-b⁻¹ : Fˣ) : F))⁻¹, ?_, ?_, ?_, rfl⟩
      · exact (upperSteinbergSubgroup (F := F) n).inv_mem
          (Subgroup.subset_closure ⟨σ q, σ p, Ne.symm (σ.injective.ne_iff.mpr hpq),
            ((-b⁻¹ : Fˣ) : F), hreverse, rfl⟩)
      · exact Subgroup.subset_closure
          ⟨σ q, σ p, Ne.symm (σ.injective.ne_iff.mpr hpq), -b⁻¹, rfl⟩
      · exact (upperSteinbergSubgroup (F := F) n).inv_mem
          (Subgroup.subset_closure ⟨σ q, σ p, Ne.symm (σ.injective.ne_iff.mpr hpq),
            ((-b⁻¹ : Fˣ) : F), hreverse, rfl⟩)

end GaloisForLFunctions.HTGeometry
