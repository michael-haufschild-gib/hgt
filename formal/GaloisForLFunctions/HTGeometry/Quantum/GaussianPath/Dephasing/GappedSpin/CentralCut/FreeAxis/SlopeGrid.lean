import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.CentralCones

/-! # A quadratic packing of distinct physical spin directions -/
open Real Matrix Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
noncomputable section

private def slope {N : ℕ} (i : Fin N) : ℝ := 1+(i.val:ℝ)/(N:ℝ)

private theorem slope_range {N : ℕ} (i : Fin N) : slope i ∈ Icc (1:ℝ) 2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val:ℝ) ≤ N := Nat.cast_le.mpr i.isLt.le
  exact ⟨le_add_of_nonneg_right (by positivity),by
    dsimp only [slope]; linarith only [(div_le_one hn).mpr hi]⟩

private theorem slope_separation {N : ℕ} {i j : Fin N} (hne : i≠j) : 1/(N:ℝ) ≤ |slope i-slope j| := by
  have hn := (Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt) : (0:ℝ)<N)
  have inc {a b : Fin N} (h : a<b) : 1/(N:ℝ) ≤ slope b-slope a := by
    have hb : (a.val:ℝ)+1 ≤ b.val := by exact_mod_cast (show a.val+1≤b.val from h)
    rw [slope,slope,add_sub_add_left_eq_sub,←sub_div]
    exact div_le_div_of_nonneg_right (by linarith only [hb]) hn.le
  rcases lt_or_gt_of_ne hne with h|h
  · rw [abs_sub_comm]; exact (inc h).trans (le_abs_self _)
  · exact (inc h).trans (le_abs_self _)

/-- At least T directions fit in the positive octant, and their observable
central-field cones of transverse width 1/(3600√T) are pairwise disjoint. -/
theorem packed_directions (T : ℝ) (hT : 1≤T) :
    ∃ N : ℕ, T ≤ (N:ℝ)^2 ∧ ∃ p : Fin N→ℝ, (∀ i, p i∈Icc (1:ℝ) 2) ∧
      ∀ a b : Fin N×Fin N, a≠b → ∀ v, SlopeCone (p a.1) (p a.2) (1/(3600*sqrt T)) v →
        ¬SlopeCone (p b.1) (p b.2) (1/(3600*sqrt T)) v := by
  let N := ⌊sqrt T⌋₊+1
  have hs := one_le_sqrt.mpr hT
  have hs₀ := zero_lt_one.trans_le hs
  have hl : sqrt T < (N:ℝ) := by simpa only [N,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (sqrt T)
  have hu : (N:ℝ) ≤ 2*sqrt T := by
    have he := Nat.floor_le (sqrt_nonneg T)
    simp only [N,Nat.cast_add,Nat.cast_one]
    linarith only [he,hs]
  have hN := hs₀.trans hl
  have hsep : 96*(1/(3600*sqrt T)) < 1/(N:ℝ) := by
    rw [mul_one_div,div_lt_div_iff₀ (by positivity) hN]
    linarith only [hu,hs₀]
  refine ⟨N,?_,slope,slope_range,?_⟩
  · have hh := pow_le_pow_left₀ hs₀.le hl.le 2
    rwa [sq_sqrt (zero_le_one.trans hT)] at hh
  · intro a b hab v ha hb
    obtain ⟨hx,hy⟩ := common_cone_slopes ha hb
    apply hab
    exact Prod.ext (by by_contra h; exact (slope_separation h).not_gt (hx.trans_lt hsep))
      (by by_contra h; exact (slope_separation h).not_gt (hy.trans_lt hsep))

#print axioms packed_directions
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
