import GaloisForLFunctions.RHTower.WeilLogShiftBandedCut

/-! Exact reconstruction of ordered node distances from elementary prefix cuts. -/

open scoped BigOperators
namespace RHTower

theorem finiteWeilCutIndicator_antitone {n : ℕ} (i : Fin n) :
    Antitone (finiteWeilCutIndicator i) := by
  intro u v huv
  have huv' : (u : ℕ) ≤ (v : ℕ) := huv
  by_cases hv : (v : ℕ) ≤ (i : ℕ)
  · have hu : (u : ℕ) ≤ (i : ℕ) := le_trans huv' hv
    simp [finiteWeilCutIndicator, hu, hv]
  · by_cases hu : (u : ℕ) ≤ (i : ℕ) <;> simp [finiteWeilCutIndicator, hu, hv]

theorem finiteWeil_cut_reconstruction {n : ℕ} (x : Fin (n + 1) → ℝ) (u v : Fin (n + 1)) :
    x u - x v = ∑ i : Fin n,
      (finiteWeilCutIndicator i u - finiteWeilCutIndicator i v) * (x i.castSucc - x i.succ) := by
  let c : Fin (n + 1) → ℝ := fun j => (if j = u then 1 else 0) - (if j = v then 1 else 0)
  have hc : (∑ j, c j) = 0 := by simp [c, Finset.sum_sub_distrib]
  have hp := finiteWeil_prefix_pairing_zero c x hc
  have hl : (∑ j, c j * x j) = x u - x v := by
    simp [c, sub_mul, ite_mul, Finset.sum_sub_distrib]
  have hprefix (i : Fin n) : (∑ j ∈ Finset.Iic i.castSucc, c j) =
      finiteWeilCutIndicator i u - finiteWeilCutIndicator i v := by
    simp [c, Finset.sum_sub_distrib, finiteWeilCutIndicator]
    rfl
  rw [hl] at hp
  simp_rw [hprefix] at hp
  exact hp

theorem finiteWeil_ordered_distance_eq_cuts {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hmono : Monotone x) (u v : Fin (n + 1)) :
    |x u - x v| = ∑ i : Fin n,
      (x i.succ - x i.castSucc) * |finiteWeilCutIndicator i u - finiteWeilCutIndicator i v| := by
  have hord (a b : Fin (n + 1)) (hab : a ≤ b) :
      |x a - x b| = ∑ i : Fin n,
        (x i.succ - x i.castSucc) * |finiteWeilCutIndicator i a - finiteWeilCutIndicator i b| := by
    have hI (i : Fin n) : 0 ≤ finiteWeilCutIndicator i a - finiteWeilCutIndicator i b :=
      sub_nonneg.mpr (finiteWeilCutIndicator_antitone i hab)
    have hx : x a - x b ≤ 0 := sub_nonpos.mpr (hmono hab)
    rw [abs_of_nonpos hx]
    simp_rw [abs_of_nonneg (hI _)]
    have hp := finiteWeil_cut_reconstruction x a b
    have hs : (∑ i : Fin n, (x i.succ - x i.castSucc) *
        (finiteWeilCutIndicator i a - finiteWeilCutIndicator i b)) = -(x a - x b) := by
      calc
        _ = -(∑ i : Fin n, (finiteWeilCutIndicator i a - finiteWeilCutIndicator i b) *
            (x i.castSucc - x i.succ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := congrArg Neg.neg hp.symm
    exact hs.symm
  rcases le_total u v with h | h
  · exact hord u v h
  · simpa only [abs_sub_comm] using hord v u h

end RHTower
