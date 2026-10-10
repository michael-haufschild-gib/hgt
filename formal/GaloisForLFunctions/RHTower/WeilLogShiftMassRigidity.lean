import GaloisForLFunctions.RHTower.WeilLogShiftMomentProbabilities

/-! Equality in the zero-sum absolute-mass bound forces a single exceptional sign. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeil_positive_pair_le_mass {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hzero : ∑ i, c i = 0) (i j : ι) (hij : i ≠ j) :
    (|c i| + c i) + (|c j| + c j) ≤ finiteWeilAbsMass c := by
  have hn (l : ι) : 0 ≤ |c l| + c l := by
    have := neg_abs_le (c l)
    linarith
  have hj : |c j| + c j ≤ ∑ l ∈ Finset.univ.erase i, (|c l| + c l) :=
    Finset.single_le_sum (fun l _ => hn l)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  have hs := Finset.sum_erase_add Finset.univ (fun l => |c l| + c l) (Finset.mem_univ i)
  have hsum : (∑ l, (|c l| + c l)) = ∑ l, |c l| := by
    rw [Finset.sum_add_distrib, hzero, add_zero]
  rw [hsum] at hs
  change (|c i| + c i) + (|c j| + c j) ≤ ∑ l, |c l|
  linarith only [hj, hs]

/-- At minimal mass, every other coordinate has the opposite weak sign to a
coordinate attaining the unit sup norm. -/
theorem finiteWeil_mass_two_sign_rigidity {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ‖c‖ = 1) (hzero : ∑ i, c i = 0)
    (hmass : finiteWeilAbsMass c = 2) :
    ∃ i, |c i| = 1 ∧ ∀ j, j ≠ i → c i * c j ≤ 0 := by
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|)
    Finset.univ_nonempty
  have htop : ‖c‖ ≤ |c i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => by
    simpa only [Real.norm_eq_abs] using hmax j (Finset.mem_univ j)
  have hi : |c i| = 1 := le_antisymm
    (by simpa only [Real.norm_eq_abs, hc] using norm_le_pi_norm c i)
    (by simpa only [hc] using htop)
  refine ⟨i, hi, fun j hji => ?_⟩
  rcases abs_eq_abs.mp (show |c i| = |(1 : ℝ)| by simpa using hi) with hi | hi
  · have hp := finiteWeil_positive_pair_le_mass c hzero i j hji.symm
    rw [hi, abs_one, hmass] at hp
    rw [hi, one_mul]
    have := le_abs_self (c j)
    linarith
  · have hz : ∑ j, -c j = 0 := by rw [Finset.sum_neg_distrib, hzero, neg_zero]
    have hm : finiteWeilAbsMass (fun j => -c j) = 2 := by
      simpa only [finiteWeilAbsMass, abs_neg] using hmass
    have hp := finiteWeil_positive_pair_le_mass (fun j => -c j) hz i j hji.symm
    simp only [hi, neg_neg, abs_one, abs_neg, hm] at hp
    rw [hi, neg_one_mul]
    have := neg_abs_le (c j)
    linarith

end RHTower
