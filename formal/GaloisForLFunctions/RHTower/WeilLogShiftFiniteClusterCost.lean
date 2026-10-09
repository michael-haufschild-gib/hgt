import GaloisForLFunctions.RHTower.WeilLogShiftSeparationEnvelope
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth

/-!
# Finite-support Gram cost controlled by index separation

Signed coordinate differences inside any finite support expose a logarithmic
resolution cost. Their arithmetic-gap consequence gives a cubic cost obstruction
for every normalized certificate on a full arithmetic cutoff.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private def finiteWeilDifference (s : Finset ℕ) (i j : s) : s → ℝ :=
  Pi.single i 1 - Pi.single j 1

private theorem finiteWeilDifference_norm (s : Finset ℕ) (i j : s) (hij : i ≠ j) :
    ‖finiteWeilDifference s i j‖ = 1 := by
  classical
  have hi : finiteWeilDifference s i j i = 1 := by
    simp only [finiteWeilDifference, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, sub_zero]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro z
    by_cases hzi : z = i
    · subst z
      rw [hi, norm_one]
    by_cases hzj : z = j
    · subst z
      simp only [finiteWeilDifference, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij.symm, zero_sub, norm_neg, norm_one, le_refl]
    · simp only [finiteWeilDifference, Pi.sub_apply, Pi.single_eq_of_ne hzi,
        Pi.single_eq_of_ne hzj, sub_zero, norm_zero, zero_le_one]
  · have h := norm_le_pi_norm (finiteWeilDifference s i j) i
    rwa [hi, norm_one] at h

private theorem finiteWeilPotential_single_one (s : Finset ℕ) (i : s) (y : ℝ) :
    finiteWeilPotential s (Pi.single i 1) y = pairedLogKernel y ((i : ℕ) + 2) := by
  classical
  unfold finiteWeilPotential
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private theorem finiteWeilDifference_potential (s : Finset ℕ) (i j : s) (y : ℝ) :
    finiteWeilPotential s (finiteWeilDifference s i j) y =
      pairedLogKernel y ((i : ℕ) + 2) - pairedLogKernel y ((j : ℕ) + 2) := by
  have hsub (c d : s → ℝ) : finiteWeilPotential s (c - d) y =
      finiteWeilPotential s c y - finiteWeilPotential s d y := by
    simp only [finiteWeilPotential, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [finiteWeilDifference, hsub, finiteWeilPotential_single_one, finiteWeilPotential_single_one]

private theorem abs_finiteWeilDifference_gram_le {B : ℝ}
    (hK : ∀ (y : ℝ) (n m : ℕ), 1 ≤ n → n ≤ m →
      |pairedLogKernel y m - pairedLogKernel y n| ≤
        (B * Real.exp (2 * |y|)) * ((Real.log m - Real.log n) * ((n : ℝ) ^ 2)⁻¹))
    (s : Finset ℕ) (i j : s) (hij : (i : ℕ) ≤ j) (w : FiniteWeilGramTest) :
    |finiteWeilGramForm s w (finiteWeilDifference s i j)| ≤
      finiteWeilGramTailCost B w *
        ((Real.log ((j : ℕ) + 2 : ℕ) - Real.log ((i : ℕ) + 2 : ℕ)) *
          ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)⁻¹) := by
  let q := (Real.log ((j : ℕ) + 2 : ℕ) - Real.log ((i : ℕ) + 2 : ℕ)) *
    ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)⁻¹
  have hp (y : ℝ) : |finiteWeilPotential s (finiteWeilDifference s i j) y| ≤
      (B * Real.exp (2 * |y|)) * q := by
    rw [finiteWeilDifference_potential, abs_sub_comm]
    exact hK y ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega)
  rcases w with ⟨N, x, u, a⟩
  let M := ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))
  have hsum : |∑ i', ∑ j', (u i' * u j') *
      finiteWeilPotential s (finiteWeilDifference s i j) (x j' - x i')| ≤ M * q := by
    calc
      _ ≤ ∑ i', |∑ j', (u i' * u j') *
          finiteWeilPotential s (finiteWeilDifference s i j) (x j' - x i')| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i', ∑ j', |(u i' * u j') *
          finiteWeilPotential s (finiteWeilDifference s i j) (x j' - x i')| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i', ∑ j', |u i' * u j'| * ((B * Real.exp (2 * |x j' - x i'|)) * q) := by
        apply Finset.sum_le_sum
        intro i' _
        apply Finset.sum_le_sum
        intro j' _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
      _ = _ := by simp only [M, Finset.sum_mul, mul_assoc]
  rw [finiteWeilGramForm_apply, abs_mul, abs_neg]
  have haabs : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg a.property
  rw [haabs]
  calc
    _ ≤ (a : ℝ) * (M * q) := mul_le_mul_of_nonneg_left hsum a.property
    _ = _ := by dsimp only [finiteWeilGramTailCost, M, q]; ring

private theorem clusterGramCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

private theorem finiteWeilGram_logGap_cost_bound {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ (y : ℝ) (n m : ℕ), 1 ≤ n → n ≤ m →
      |pairedLogKernel y m - pairedLogKernel y n| ≤
        (B * Real.exp (2 * |y|)) * ((Real.log m - Real.log n) * ((n : ℝ) ^ 2)⁻¹))
    (s : Finset ℕ) (tests : Finset FiniteWeilGramTest)
    (ht : FiniteWeilGramNormCertificate s tests) (i j : s) (hij : (i : ℕ) < j) :
    2 * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2) <
      (Real.log ((j : ℕ) + 2 : ℕ) - Real.log ((i : ℕ) + 2 : ℕ)) *
        ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  have hneij : i ≠ j := fun h => (ne_of_lt hij) (congrArg Subtype.val h)
  let e := finiteWeilDifference s i j
  let q := ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)
  let δ := Real.log ((j : ℕ) + 2 : ℕ) - Real.log ((i : ℕ) + 2 : ℕ)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hδ : 0 ≤ δ := by
    apply sub_nonneg.mpr
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show (i : ℕ) + 2 ≤ (j : ℕ) + 2 by omega)
  have he : ‖e‖ = 1 := finiteWeilDifference_norm s i j hneij
  have hne : e ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at he
  obtain ⟨wp, hwp, hp⟩ := ht e hne
  obtain ⟨wm, hwm, hm⟩ := ht (-e) (neg_ne_zero.mpr hne)
  rw [he] at hp
  rw [map_neg, norm_neg, he] at hm
  have hcost (w : FiniteWeilGramTest) (hw : 1 < |finiteWeilGramForm s w e|) :
      q < finiteWeilGramTailCost B w * δ := by
    have h := abs_finiteWeilDifference_gram_le hK s i j hij.le w
    change |finiteWeilGramForm s w e| ≤ finiteWeilGramTailCost B w * (δ * q⁻¹) at h
    have hmul := mul_lt_mul_of_pos_right (hw.trans_le h) hq
    simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] using hmul
  have hcp := hcost wp (by linarith [neg_le_abs (finiteWeilGramForm s wp e)])
  have hcm := hcost wm (by linarith [le_abs_self (finiteWeilGramForm s wm e)])
  have hne_tests : wp ≠ wm := by intro h; rw [h] at hp; linarith
  have hsubset : ({wp, wm} : Finset FiniteWeilGramTest) ⊆ tests := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hwp
    · exact hwm
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun w _ _ => clusterGramCost_nonneg hB w)
  rw [Finset.sum_pair hne_tests] at hpair
  have hweighted := mul_le_mul_of_nonneg_left hpair hδ
  change 2 * q < δ * _
  nlinarith

/-- Every ordered pair inside any finite support forces both a logarithmic-gap
cost and its arithmetic-gap consequence, in one universal normalization. -/
theorem exists_finiteWeilGram_separation_cost_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Finset ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate s tests → ∀ i j : s, (i : ℕ) < j →
        (2 * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2) <
          (Real.log ((j : ℕ) + 2 : ℕ) - Real.log ((i : ℕ) + 2 : ℕ)) *
            ∑ w ∈ tests, finiteWeilGramTailCost B w) ∧
        (2 * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 3) <
          (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * ∑ w ∈ tests, finiteWeilGramTailCost B w) := by
  classical
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_logSeparation_envelope
  refine ⟨B, hB, ?_⟩
  intro s tests ht i j hij
  have hlog := finiteWeilGram_logGap_cost_bound hB.le hK s tests ht i j hij
  refine ⟨hlog, ?_⟩
  let n : ℝ := ((i : ℕ) + 2 : ℕ)
  let m : ℝ := ((j : ℕ) + 2 : ℕ)
  let δ := Real.log m - Real.log n
  let T := ∑ w ∈ tests, finiteWeilGramTailCost B w
  have hn : 0 < n := by dsimp only [n]; positivity
  have hm : 0 < m := by dsimp only [m]; positivity
  have hT : 0 ≤ T := Finset.sum_nonneg fun w _ => clusterGramCost_nonneg hB.le w
  have hgap : δ ≤ (m - n) / n := by
    calc
      δ = Real.log (m / n) := by rw [Real.log_div hm.ne' hn.ne']
      _ ≤ m / n - 1 := Real.log_le_sub_one_of_pos (div_pos hm hn)
      _ = _ := by field_simp
  have hmul := mul_lt_mul_of_pos_right hlog hn
  have hbound := mul_le_mul_of_nonneg_right hgap (mul_nonneg hT hn.le)
  have heq : ((m - n) / n) * (T * n) = (m - n) * T := by field_simp
  rw [heq] at hbound
  change 2 * n ^ 2 * n < (δ * T) * n at hmul
  calc
    2 * n ^ 3 < (m - n) * T := by nlinarith
    _ = _ := by
      congr 1
      dsimp only [m, n]
      push_cast
      ring

/-- Full arithmetic cutoffs inherit the cubic obstruction from their last
adjacent pair; additional coordinates cannot remove that cost. -/
theorem exists_finiteWeilGram_cutoff_cubic_cost_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate (Finset.range (n + 2)) tests →
        2 * (((n + 2 : ℕ) : ℝ) ^ 3) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, hB, h⟩ := exists_finiteWeilGram_separation_cost_bounds
  refine ⟨B, hB, ?_⟩
  intro n tests ht
  have hp := (h (Finset.range (n + 2)) tests ht
    ⟨n, Finset.mem_range.mpr (by omega)⟩
    ⟨n + 1, Finset.mem_range.mpr (by omega)⟩ (by simp)).2
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul] using hp

end RHTower
