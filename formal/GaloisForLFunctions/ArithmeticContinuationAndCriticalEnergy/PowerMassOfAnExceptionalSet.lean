import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent

/-!
# Power mass of an exceptional set

A decreasing power has maximal mass when indices are packed against
one. For growing powers at least half the indices carry weight
comparable to the cardinality raised to that power.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticPowerMass

/-- The reciprocal power mass of m distinct positive indices is largest at the first m. -/
theorem packed_power {v : ℝ} (hv : 0<v) (hv1 : v ≤ 1)
    (S : Finset ℕ) (hs : ∀ k ∈ S, 1 ≤ k) :
    (∑ k ∈ S, (k:ℝ)^(v-1)) ≤ (1+1/v)*((S.card:ℝ)+1)^v := by
  have sep (k l : ℕ) (hne : k ≠ l) : 1 ≤ |(-(k:ℝ)) - (-(l:ℝ))| := by
    rw [show -(k:ℝ) - -(l:ℝ) = l-k by ring]
    rcases lt_or_gt_of_ne hne with h|h
    · have h' : (k:ℝ)+1 ≤ l := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h' : (l:ℝ)+1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
  have h := ZeroConfigurationGeometry.sum_le_sum_range_of_sep (fun k : ℕ => -(k:ℝ))
    (μ:=1) zero_le_one S.card S 0 (fun t => t^(v-1)) rfl
    (fun t ht => Real.rpow_nonneg (zero_le_one.trans ht) _)
    (fun x y hx hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (sub_nonpos.mpr hv1))
    (fun k _ l _ => sep k l) (fun k hk => by simpa using (Nat.one_le_cast (α:=ℝ)).mpr (hs k hk))
  simp only [zero_sub,neg_neg,mul_one] at h
  exact h.trans (ArithmeticGaugeTheory.sum_rpow_sub_one_le hv _)

/-- A set of m distinct nonnegative integers has shifted v-th power
mass at least (m/2)^(1+v), uniformly for every real v ≥ 0. -/
theorem cardinal_power_le_mass (S : Finset ℕ) {v : ℝ} (hv : 0≤v) :
    (S.card:ℝ)^(1+v) ≤ 2^(1+v)*∑ k ∈ S, ((k:ℝ)+1)^v := by
  classical
  rcases S.eq_empty_or_nonempty with hh|hne
  · subst S
    simp [Real.zero_rpow (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hv))]
  have hm := (Nat.cast_pos (α:=ℝ)).mpr (card_pos.mpr hne)
  let T := S.filter (· < S.card/2)
  let H := S \ T
  have ht : T ⊆ S := filter_subset _ _
  have hl : T.card ≤ S.card/2 := by
    have h := card_le_card (show T ⊆ range (S.card/2) from fun _ hk => mem_range.mpr (mem_filter.mp hk).2)
    simpa only [card_range] using h
  have hcard : (S.card:ℝ) ≤ 2*(H.card:ℝ) := by
    have h := card_sdiff_of_subset ht
    change (S.card:ℝ) ≤ 2*((S \ T).card:ℝ)
    exact_mod_cast (show S.card ≤ 2*(S \ T).card by omega)
  have hw (k : ℕ) (hk : k ∈ H) : (S.card:ℝ)^v ≤ 2^v*((k:ℝ)+1)^v := by
    have hks := mem_sdiff.mp hk
    have hk' : S.card/2 ≤ k := le_of_not_gt fun hh => hks.2 (mem_filter.mpr ⟨hks.1,hh⟩)
    have h : (S.card:ℝ) ≤ 2*((k:ℝ)+1) := by exact_mod_cast (show S.card ≤ 2*(k+1) by omega)
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : 0≤(k:ℝ)+1)] using
      Real.rpow_le_rpow hm.le h hv
  have hsum := sum_le_sum (s:=H) (fun k hk => hw k hk)
  rw [sum_const,nsmul_eq_mul,←mul_sum] at hsum
  have hall : (∑ k ∈ H,((k:ℝ)+1)^v) ≤ ∑ k ∈ S,((k:ℝ)+1)^v :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun k _ _ => Real.rpow_nonneg (by positivity) _)
  rw [Real.rpow_add hm,Real.rpow_one,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
  linarith only [mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hm.le v),hsum,
    mul_le_mul_of_nonneg_left hall (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) v)]

#print axioms packed_power
#print axioms cardinal_power_le_mass
end GaloisForLFunctions.ArithmeticPowerMass
