import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.GibbsRange
import GaloisForLFunctions.RHTower.EvenSectorAbelRigidity
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusDivergence

/-! # Thermal transition across all finite omission dimensions

Every finite-rank cost stays finite. Their collective range is bounded
precisely in the half-plane of absolute convergence of the Gibbs partition.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

theorem shellPower_pos (β : GibbsExponent) (n : ℕ) : 0 < shellPower β n :=
  one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

theorem summable_shellPower_iff (β : GibbsExponent) : Summable (shellPower β) ↔ 1 < β.val := by
  rw [← Real.summable_one_div_nat_rpow,← summable_nat_add_iff 1 (f := fun n : ℕ => 1/(n:ℝ)^β.val)]
  change Summable (fun n : ℕ => 1/((n:ℝ)+1)^β.val) ↔ _
  simp only [Nat.cast_add,Nat.cast_one]

theorem hasSum_shellPower {β : GibbsExponent} (hβ : 1 < β.val) :
    HasSum (shellPower β) (riemannZeta (β.val:ℂ)).re := by
  have h := (Real.summable_one_div_nat_rpow.mpr hβ).sum_add_tsum_nat_add 1
  have hz := _root_.RHTower.EvenSector.tsum_one_div_rpow_eq_re_riemannZeta (s := β.val-1) (sub_pos.mpr hβ)
  have e₁ : 1+(β.val-1) = β.val := by ring
  have e₂ : (1:ℂ)+((β.val-1:ℝ):ℂ) = (β.val:ℂ) := by push_cast; ring
  rw [e₁,e₂] at hz
  have e : (∑' n, shellPower β n) = (riemannZeta (β.val:ℂ)).re := by
    simpa only [Finset.sum_range_one,Nat.cast_zero,Real.zero_rpow β.property.ne',div_zero,zero_add,
      Nat.cast_add,Nat.cast_one,shellPower] using h.trans hz
  exact e ▸ ((summable_shellPower_iff β).mpr hβ).hasSum

private theorem gibbsHead_lt_total {β : GibbsExponent} (hβ : 1 < β.val) (r : ℕ) :
    gibbsHead β r < (riemannZeta (β.val:ℂ)).re := by
  have h := (hasSum_shellPower hβ).summable.sum_le_tsum (Finset.range (r+1)) (fun i _ => (shellPower_pos β i).le)
  rw [(hasSum_shellPower hβ).tsum_eq,Finset.sum_range_succ] at h
  exact (lt_add_of_pos_right _ (shellPower_pos β r)).trans_le h

theorem finiteGibbsLosses_convergent {β : GibbsExponent} (hβ : 1 < β.val) :
    finiteGibbsLosses β = Ico 0 (riemannZeta (β.val:ℂ)).re := by
  ext y
  rw [finiteGibbsLosses_iff]
  constructor
  · rintro (rfl | ⟨hy,r,h⟩)
    · exact ⟨le_rfl,by simpa [gibbsHead] using gibbsHead_lt_total hβ 0⟩
    · exact ⟨hy.le,h.trans (gibbsHead_lt_total hβ _)⟩
  · rintro ⟨hy,hu⟩
    rcases hy.eq_or_lt with e | hy
    · exact Or.inl e.symm
    have ht : Tendsto (gibbsHead β) atTop (𝓝 (riemannZeta (β.val:ℂ)).re) :=
      (hasSum_shellPower hβ).tendsto_sum_nat
    exact Or.inr ⟨hy,((ht.comp (tendsto_add_atTop_nat 1)).eventually_const_lt hu).exists⟩

/-- At the pole and throughout the positive subcritical interval every nonnegative finite cost occurs. -/
theorem finiteGibbsLosses_divergent {β : GibbsExponent} (hβ : β.val ≤ 1) :
    finiteGibbsLosses β = Ici 0 := by
  have hns : ¬ Summable (shellPower β) := fun h => hβ.not_gt ((summable_shellPower_iff β).mp h)
  have ht : Tendsto (gibbsHead β) atTop atTop :=
    (HTGeometry.tendsto_finsetSum_atTop_of_not_summable (fun n => (shellPower_pos β n).le) hns).comp tendsto_finset_range
  ext y
  rw [finiteGibbsLosses_iff,mem_Ici]
  constructor
  · rintro (rfl | ⟨h,_⟩)
    · exact le_rfl
    · exact h.le
  · intro hy
    rcases hy.eq_or_lt with he | h
    · exact Or.inl he.symm
    exact Or.inr ⟨h,((ht.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop y).exists⟩

theorem finiteGibbsLosses_bounded_iff (β : GibbsExponent) :
    BddAbove (finiteGibbsLosses β) ↔ 1 < β.val := by
  rcases lt_or_ge 1 β.val with h | h
  · rw [finiteGibbsLosses_convergent h]
    exact iff_of_true bddAbove_Ico h
  · rw [finiteGibbsLosses_divergent h]
    exact iff_of_false (not_bddAbove_Ici (a := (0 : ℝ))) h.not_gt

#print axioms hasSum_shellPower
#print axioms finiteGibbsLosses_convergent
#print axioms finiteGibbsLosses_divergent
#print axioms finiteGibbsLosses_bounded_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
