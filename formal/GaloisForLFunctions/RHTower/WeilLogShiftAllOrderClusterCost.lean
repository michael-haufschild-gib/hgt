import GaloisForLFunctions.RHTower.WeilLogShiftAllOrderCancellation
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth

/-!
# Arbitrary polynomial lower bounds for finite Gram certificate cost

Extend a normalized cluster direction by zero. The two signed certificate
witnesses are distinct, and each must pay the reciprocal sensitivity cost.
-/

open scoped BigOperators

namespace RHTower

private theorem allOrder_extend_norm {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (c : ι → ℝ) :
    ‖Function.extend e c (fun _ => 0)‖ = ‖c‖ := by
  classical
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg c)).mpr
    intro j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [he.extend_apply]
      exact norm_le_pi_norm c i
    · rw [Function.extend_apply' c (fun _ => 0) j hj, norm_zero]
      exact norm_nonneg c
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← he.extend_apply c (fun _ => 0) i]
    exact norm_le_pi_norm _ (e i)

private theorem allOrder_gram_cost_nonneg {B : ℝ} (hB : 0 ≤ B) (w : FiniteWeilGramTest) :
    0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp [finiteWeilGramTailCost]
  positivity

private theorem allOrder_gram_sensitivity {s : Finset ℕ} {c : s → ℝ} {B q : ℝ}
    (hq : 0 < q)
    (hc : ∀ y, |finiteWeilPotential s c y| ≤ B * Real.exp (2 * |y|) * q⁻¹)
    (w : FiniteWeilGramTest) :
    |finiteWeilGramForm s w c| * q ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  have ha : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg a.property
  have hsum : |∑ i, ∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| ≤
      (∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
    calc
      |∑ i, ∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| ≤
          ∑ i, |∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (|u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| ≤
              ∑ j, |u i * u j * finiteWeilPotential s c (x j - x i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, (|u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hc _) (abs_nonneg _)
      _ = (∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
        simp only [Finset.sum_mul]
  have hb : |finiteWeilGramForm s ⟨N, x, u, a⟩ c| ≤
      finiteWeilGramTailCost B ⟨N, x, u, a⟩ * q⁻¹ := by
    rw [finiteWeilGramForm_apply, abs_mul, abs_neg, ha]
    convert mul_le_mul_of_nonneg_left hsum a.property using 1
    · rfl
    · rfl
    · dsimp [finiteWeilGramTailCost]
      ring
  exact (le_div_iff₀ hq).mp (by simpa only [div_eq_mul_inv] using hb)

private theorem allOrder_certificate_cost {s : Finset ℕ} {tests : Finset FiniteWeilGramTest}
    (hcert : FiniteWeilGramNormCertificate s tests) {c : s → ℝ} (hnorm : ‖c‖ = 1)
    {B q : ℝ} (hB : 0 < B) (hq : 0 < q)
    (hc : ∀ y, |finiteWeilPotential s c y| ≤ B * Real.exp (2 * |y|) * q⁻¹) :
    2 * q < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  have hc0 : c ≠ 0 := by intro hz; simp only [hz, norm_zero] at hnorm; norm_num at hnorm
  obtain ⟨wp, hwp, hp⟩ := hcert c hc0
  obtain ⟨wm, hwm, hm⟩ := hcert (-c) (neg_ne_zero.mpr hc0)
  rw [hnorm] at hp
  simp only [map_neg, norm_neg, hnorm] at hm
  have hneq : wp ≠ wm := by intro heq; rw [heq] at hp; linarith
  have hcp := allOrder_gram_sensitivity hq hc wp
  have hcm := allOrder_gram_sensitivity hq hc wm
  have hpabs : 1 < |finiteWeilGramForm s wp c| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hmabs : 1 < |finiteWeilGramForm s wm c| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hpq : q < finiteWeilGramTailCost B wp := by nlinarith
  have hmq : q < finiteWeilGramTailCost B wm := by nlinarith
  have hsub : {wp, wm} ⊆ tests := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hwp
    · exact hwm
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun w _ _ => allOrder_gram_cost_nonneg hB.le w)
  rw [Finset.sum_pair hneq] at hpair
  linarith

/-- Every containing support inherits the all-order cost obstruction, with
one normalization constant for each cancellation order. -/
theorem finiteWeilGram_cluster_cost_of_paired_bound (r : ℕ)
    (s : Finset ℕ) (tests : Finset FiniteWeilGramTest)
    (hcert : FiniteWeilGramNormCertificate s tests) (k : ℕ)
    (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s)
    {B q : ℝ} (hB : 0 < B) (hq : 0 < q)
    (hbound : ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
      |∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
        B * Real.exp (2 * |y|) * q⁻¹) :
    2 * q < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  obtain ⟨c, hc, hpot⟩ := hbound
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let d : s → ℝ := Function.extend e c (fun _ => 0)
  have hd : ‖d‖ = 1 := (allOrder_extend_norm e he c).trans hc
  have hpotential (y : ℝ) : finiteWeilPotential s d y =
      ∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ)) := by
    unfold finiteWeilPotential
    symm
    apply Fintype.sum_of_injective e he
    · intro j hj
      dsimp [d]
      rw [Function.extend_apply' c (fun _ => 0) j hj, zero_mul]
    · intro i
      dsimp [d]
      rw [he.extend_apply]
      congr 2
      dsimp [e]
      omega
  apply allOrder_certificate_cost hcert hd hB hq
  intro y
  rw [hpotential]
  exact hpot y

theorem exists_finiteWeilGram_allOrder_cluster_cost_bound (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Finset ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate s tests → ∀ k : ℕ, r + 1 ≤ k + 2 →
      (∀ i : Fin (r + 2), k + (i : ℕ) ∈ s) →
      2 * (((k + 2 : ℕ) : ℝ) ^ (r + 3)) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, hB, hbound⟩ := exists_pairedLogKernel_allOrder_cluster_envelope r
  refine ⟨B, hB, ?_⟩
  intro s tests hcert k hk hmem
  exact finiteWeilGram_cluster_cost_of_paired_bound r s tests hcert k hmem hB
    (by positivity) (hbound (k + 2) hk)

theorem exists_finiteWeilGram_allOrder_cutoff_cost_bound (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (tests : Finset FiniteWeilGramTest),
      r + 1 ≤ n + 2 → FiniteWeilGramNormCertificate (Finset.range (n + r + 2)) tests →
      2 * (((n + 2 : ℕ) : ℝ) ^ (r + 3)) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, hB, hbound⟩ := exists_finiteWeilGram_allOrder_cluster_cost_bound r
  refine ⟨B, hB, ?_⟩
  intro n tests hn hcert
  apply hbound _ tests hcert n hn
  intro i
  apply Finset.mem_range.mpr
  have := i.isLt
  omega

end RHTower
