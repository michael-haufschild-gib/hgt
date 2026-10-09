import GaloisForLFunctions.RHTower.WeilLogShiftTripleCancellation
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth

/-!
# Quartic Gram cost from three consecutive arithmetic indices

A logarithmically balanced coefficient triple has norm one and an inverse-fourth
potential envelope. Zero extension transports its obstruction to every finite
support containing the triple, including every full arithmetic cutoff.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private def finiteWeilTriple (s : Finset ℕ) (i j l : s) (a : ℝ) : s → ℝ :=
  Pi.single i a - Pi.single j 1 + Pi.single l (1 - a)

private theorem finiteWeilTriple_norm (s : Finset ℕ) (i j l : s) (a : ℝ)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖finiteWeilTriple s i j l a‖ = 1 := by
  classical
  have hj : finiteWeilTriple s i j l a j = -1 := by
    simp only [finiteWeilTriple, Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hij.symm,
      Pi.single_eq_same, Pi.single_eq_of_ne hjl, zero_sub, add_zero]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro z
    by_cases hzi : z = i
    · subst z
      simpa only [finiteWeilTriple, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hil, sub_zero, add_zero,
        Real.norm_eq_abs, abs_of_nonneg ha] using ha1
    by_cases hzj : z = j
    · subst z
      rw [hj, norm_neg, norm_one]
    by_cases hzl : z = l
    · subst z
      simp only [finiteWeilTriple, Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hil.symm,
        Pi.single_eq_of_ne hjl.symm, Pi.single_eq_same, sub_zero, zero_add,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha1)]
      linarith
    · simp only [finiteWeilTriple, Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hzi,
        Pi.single_eq_of_ne hzj, Pi.single_eq_of_ne hzl, sub_zero, add_zero, norm_zero, zero_le_one]
  · have h := norm_le_pi_norm (finiteWeilTriple s i j l a) j
    rwa [hj, norm_neg, norm_one] at h

private theorem finiteWeilPotential_single_value (s : Finset ℕ) (i : s) (a y : ℝ) :
    finiteWeilPotential s (Pi.single i a) y = a * pairedLogKernel y ((i : ℕ) + 2) := by
  classical
  unfold finiteWeilPotential
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private theorem finiteWeilTriple_potential (s : Finset ℕ) (i j l : s) (a y : ℝ) :
    finiteWeilPotential s (finiteWeilTriple s i j l a) y =
      a * pairedLogKernel y ((i : ℕ) + 2) + (1 - a) * pairedLogKernel y ((l : ℕ) + 2) -
        pairedLogKernel y ((j : ℕ) + 2) := by
  have hadd (c d : s → ℝ) : finiteWeilPotential s (c + d) y =
      finiteWeilPotential s c y + finiteWeilPotential s d y := by
    simp only [finiteWeilPotential, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsub (c d : s → ℝ) : finiteWeilPotential s (c - d) y =
      finiteWeilPotential s c y - finiteWeilPotential s d y := by
    simp only [finiteWeilPotential, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [finiteWeilTriple, hadd, hsub, finiteWeilPotential_single_value,
    finiteWeilPotential_single_value, finiteWeilPotential_single_value, one_mul]
  ring

private theorem abs_tripleGramForm_le_of_potential_bound (s : Finset ℕ) (c : s → ℝ)
    (B q : ℝ) (hp : ∀ y : ℝ, |finiteWeilPotential s c y| ≤ (B * Real.exp (2 * |y|)) * q)
    (w : FiniteWeilGramTest) :
    |finiteWeilGramForm s w c| ≤ finiteWeilGramTailCost B w * q := by
  rcases w with ⟨N, x, u, a⟩
  let M := ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))
  have hsum : |∑ i, ∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i)| ≤ M * q := by
    calc
      _ ≤ ∑ i, |∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(u i * u j) * finiteWeilPotential s c (x j - x i)| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u i * u j| * ((B * Real.exp (2 * |x j - x i|)) * q) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
      _ = _ := by simp only [M, Finset.sum_mul, mul_assoc]
  rw [finiteWeilGramForm_apply, abs_mul, abs_neg]
  have haabs : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg a.property
  rw [haabs]
  calc
    _ ≤ (a : ℝ) * (M * q) := mul_le_mul_of_nonneg_left hsum a.property
    _ = _ := by dsimp only [finiteWeilGramTailCost, M]; ring

private theorem quarticGramCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

/-- Any finite support containing three consecutive indices forces quartic
normalized Gram cost, under one universal positive normalization. -/
theorem exists_finiteWeilGram_triple_quartic_cost_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Finset ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate s tests → ∀ k : ℕ,
        k ∈ s → k + 1 ∈ s → k + 2 ∈ s →
          2 * (((k + 2 : ℕ) : ℝ) ^ 4) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_triple_inverseFourth_envelope
  refine ⟨B, hB, ?_⟩
  intro s tests ht k hk hk1 hk2
  obtain ⟨a, ha, ha1, hkernel⟩ := hK (k + 2) (by omega)
  let i : s := ⟨k, hk⟩
  let j : s := ⟨k + 1, hk1⟩
  let l : s := ⟨k + 2, hk2⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Subtype.val h
    dsimp only [i, j] at hv
    omega
  have hil : i ≠ l := by
    intro h
    have hv := congrArg Subtype.val h
    dsimp only [i, l] at hv
    omega
  have hjl : j ≠ l := by
    intro h
    have hv := congrArg Subtype.val h
    dsimp only [j, l] at hv
    omega
  let e := finiteWeilTriple s i j l a
  let q := (((k + 2 : ℕ) : ℝ) ^ 4)
  have hq : 0 < q := by dsimp only [q]; positivity
  have he : ‖e‖ = 1 := finiteWeilTriple_norm s i j l a hij hil hjl ha ha1
  have hne : e ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at he
  have hpotential (y : ℝ) : |finiteWeilPotential s e y| ≤
      (B * Real.exp (2 * |y|)) * q⁻¹ := by
    dsimp only [e]
    rw [finiteWeilTriple_potential]
    simpa only [i, j, l, q, Nat.add_assoc] using hkernel y
  obtain ⟨wp, hwp, hp⟩ := ht e hne
  obtain ⟨wm, hwm, hm⟩ := ht (-e) (neg_ne_zero.mpr hne)
  rw [he] at hp
  rw [map_neg, norm_neg, he] at hm
  have hcost (w : FiniteWeilGramTest) (hw : 1 < |finiteWeilGramForm s w e|) :
      q < finiteWeilGramTailCost B w := by
    have h := abs_tripleGramForm_le_of_potential_bound s e B q⁻¹ hpotential w
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
    (fun w _ _ => quarticGramCost_nonneg hB.le w)
  rw [Finset.sum_pair hne_tests] at hpair
  change 2 * q < _
  linarith

/-- Full arithmetic cutoffs inherit the quartic obstruction from their last
three consecutive indices. -/
theorem exists_finiteWeilGram_cutoff_quartic_cost_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate (Finset.range (n + 3)) tests →
        2 * (((n + 2 : ℕ) : ℝ) ^ 4) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, hB, h⟩ := exists_finiteWeilGram_triple_quartic_cost_bound
  refine ⟨B, hB, ?_⟩
  intro n tests ht
  exact h (Finset.range (n + 3)) tests ht n
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))
    (Finset.mem_range.mpr (by omega))

end RHTower
