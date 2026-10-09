import GaloisForLFunctions.RHTower.WeilLogShiftFiniteTailCompensation

/-!
# Quadratic cost growth of normalized finite Weil Gram certificates

Every finite support admits a certificate. Detecting both signs at an
arithmetic index n requires distinct tests, whose total explicit cost exceeds
2n². Thus finite feasibility does not give a support-uniform cost budget.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The coefficient weight associated with the inverse-square envelope. -/
def finiteWeilCoefficientWeight (s : Finset ℕ) (c : s → ℝ) : ℝ :=
  ∑ i : s, |c i| * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)⁻¹

/-- The normalization already supplied by the finite Gram certificate. -/
def FiniteWeilGramNormCertificate (s : Finset ℕ) (tests : Finset FiniteWeilGramTest) : Prop :=
  ∀ c : s → ℝ, c ≠ 0 → ∃ w ∈ tests, finiteWeilGramForm s w c < -‖c‖

private theorem finiteWeilCoefficientWeight_single (s : Finset ℕ) (i : s) (a : ℝ) :
    finiteWeilCoefficientWeight s (Pi.single i a) =
      |a| * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
  classical
  unfold finiteWeilCoefficientWeight
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, abs_zero, zero_mul]
  · simp

private theorem finiteWeilGramTailCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

private theorem abs_finiteWeilGramForm_le
    {B : ℝ} (hK : ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      pairedLogKernel y n ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹)
    (s : Finset ℕ) (w : FiniteWeilGramTest) (c : s → ℝ) :
    |finiteWeilGramForm s w c| ≤ finiteWeilGramTailCost B w * finiteWeilCoefficientWeight s c := by
  have hp (y : ℝ) : |finiteWeilPotential s c y| ≤
      (B * Real.exp (2 * |y|)) * finiteWeilCoefficientWeight s c := by
    calc
      _ ≤ ∑ i : s, |c i * pairedLogKernel y ((i : ℕ) + 2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : s, |c i| *
          (B * Real.exp (2 * |y|) * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (pairedLogKernel_pos y ((i : ℕ) + 2))]
        exact mul_le_mul_of_nonneg_left (hK y ((i : ℕ) + 2) (by omega)) (abs_nonneg _)
      _ = _ := by
        simp only [finiteWeilCoefficientWeight, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rcases w with ⟨N, x, u, a⟩
  let M := ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))
  have hsum : |∑ i, ∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i)| ≤
      M * finiteWeilCoefficientWeight s c := by
    calc
      _ ≤ ∑ i, |∑ j, (u i * u j) * finiteWeilPotential s c (x j - x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(u i * u j) * finiteWeilPotential s c (x j - x i)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u i * u j| *
          ((B * Real.exp (2 * |x j - x i|)) * finiteWeilCoefficientWeight s c) := by
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
    _ ≤ (a : ℝ) * (M * finiteWeilCoefficientWeight s c) :=
      mul_le_mul_of_nonneg_left hsum a.property
    _ = _ := by dsimp only [finiteWeilGramTailCost, M]; ring

private theorem finiteWeilGram_cost_gt_twice_square
    {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      pairedLogKernel y n ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹)
    (s : Finset ℕ) (tests : Finset FiniteWeilGramTest)
    (htests : FiniteWeilGramNormCertificate s tests) (i : s) :
    2 * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  let e : s → ℝ := Pi.single i 1
  let q : ℝ := (((i : ℕ) + 2 : ℕ) : ℝ) ^ 2
  have hq : 0 < q := by dsimp only [q]; positivity
  have he : ‖e‖ = 1 := by simp only [e, Pi.norm_single, norm_one]
  have hne : e ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at he
  have hw : finiteWeilCoefficientWeight s e = q⁻¹ := by
    simp only [e, finiteWeilCoefficientWeight_single, abs_one, one_mul, q]
  obtain ⟨wp, hwp, hp⟩ := htests e hne
  obtain ⟨wm, hwm, hm⟩ := htests (-e) (neg_ne_zero.mpr hne)
  rw [he] at hp
  rw [map_neg, norm_neg, he] at hm
  have hcost (w : FiniteWeilGramTest) (hw1 : 1 < |finiteWeilGramForm s w e|) :
      q < finiteWeilGramTailCost B w := by
    have h := abs_finiteWeilGramForm_le hK s w e
    rw [hw] at h
    have hmul := mul_lt_mul_of_pos_right (hw1.trans_le h) hq
    simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] using hmul
  have hcp := hcost wp (by linarith [neg_le_abs (finiteWeilGramForm s wp e)])
  have hcm := hcost wm (by linarith [le_abs_self (finiteWeilGramForm s wm e)])
  have hne_tests : wp ≠ wm := by
    intro h
    rw [h] at hp
    linarith
  have hsubset : ({wp, wm} : Finset FiniteWeilGramTest) ⊆ tests := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hwp
    · exact hwm
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun w _ _ => finiteWeilGramTailCost_nonneg hB w)
  rw [Finset.sum_pair hne_tests] at hpair
  change 2 * q < _
  linarith

/-- One universal envelope gives weighted sensitivity and the two-sign
quadratic lower bound for every certificate, while every finite support
still admits a certificate. -/
theorem exists_finiteWeilGram_cost_bounds :
    ∃ B : ℝ, 0 < B ∧
      (∀ (s : Finset ℕ) (w : FiniteWeilGramTest) (c : s → ℝ),
        |finiteWeilGramForm s w c| ≤
          finiteWeilGramTailCost B w * finiteWeilCoefficientWeight s c) ∧
      (∀ (s : Finset ℕ) (tests : Finset FiniteWeilGramTest),
        FiniteWeilGramNormCertificate s tests → ∀ i : s,
          2 * ((((i : ℕ) + 2 : ℕ) : ℝ) ^ 2) <
            ∑ w ∈ tests, finiteWeilGramTailCost B w) ∧
      ∀ s : Finset ℕ, ∃ tests : Finset FiniteWeilGramTest,
        FiniteWeilGramNormCertificate s tests := by
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_inverseSquare_envelope
  exact ⟨B, hB, abs_finiteWeilGramForm_le hK,
    finiteWeilGram_cost_gt_twice_square hB.le hK, exists_finiteWeilGram_norm_certificate⟩

/-- Along increasing arithmetic cutoffs, every normalized Gram certificate
eventually exceeds each fixed explicit cost budget. -/
theorem exists_finiteWeilGram_cost_escape :
    ∃ B : ℝ, 0 < B ∧ ∀ A : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ tests : Finset FiniteWeilGramTest,
        FiniteWeilGramNormCertificate (Finset.range (n + 1)) tests →
          A < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  obtain ⟨B, hB, _, hcost, _⟩ := exists_finiteWeilGram_cost_bounds
  refine ⟨B, hB, ?_⟩
  intro A
  obtain ⟨N, hN⟩ := exists_nat_gt A
  refine ⟨N, ?_⟩
  intro n hn tests htests
  have hindex : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h := hcost (Finset.range (n + 1)) tests htests ⟨n, hindex⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlarge : A < 2 * (((n + 2 : ℕ) : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (n : ℝ)]
  exact hlarge.trans h

end RHTower
