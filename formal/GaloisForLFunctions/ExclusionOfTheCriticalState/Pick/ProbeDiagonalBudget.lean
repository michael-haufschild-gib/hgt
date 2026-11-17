import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TwoSupportProbeRigidity

/-!
# Sharp diagonal budget for aligned arithmetic probes

The deficit from cardinality times diagonal energy is half the sum of
antisymmetric pair energies. Saturation forces either the zero family
or total node collision with equal coefficient magnitudes.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick

/-- The arithmetic diagonal energy of prescribed coefficient magnitudes. -/
def probeDiagonalEnergy {n : ℕ} (p a : Fin n → ℝ) : ℝ :=
  ∑ i, |a i| ^ 2 * safeProbeEntry (p i) (p i)

theorem probeDiagonalEnergy_nonneg {n : ℕ} (p a : Fin n → ℝ) :
    0 ≤ probeDiagonalEnergy p a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (probeEntry_pos _ _).le

private theorem pair_diagonal_bound {n : ℕ} (p a : Fin n → ℝ) (i j : Fin n) :
    2 * |a i| * |a j| * safeProbeEntry (p i) (p j) ≤
      |a i| ^ 2 * safeProbeEntry (p i) (p i) +
        |a j| ^ 2 * safeProbeEntry (p j) (p j) := by
  have h := twoProbeQuadratic_nonneg (p i) (p j) |a i| (-|a j|)
  unfold twoProbeQuadratic at h
  nlinarith only [h]

/-- Pairwise arithmetic positivity bounds the fully aligned energy by cardinality times its diagonal. -/
theorem alignedEnergy_le_card_diagonal {n : ℕ} (p a : Fin n → ℝ) :
    alignedEnergy p a ≤ (n : ℝ) * probeDiagonalEnergy p a := by
  have h := Finset.sum_le_sum fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun (j : Fin n) (_ : j ∈ Finset.univ) => pair_diagonal_bound p a i j
  have hl : (∑ i, ∑ j, 2 * |a i| * |a j| * safeProbeEntry (p i) (p j)) =
      2 * alignedEnergy p a := by
    unfold alignedEnergy sourceQuadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change 2 * |a i| * |a j| * safeProbeEntry (p i) (p j) =
      2 * (|a i| * |a j| * safeProbeEntry (p i) (p j))
    ring
  have hr : (∑ i : Fin n, ∑ j : Fin n,
      (|a i| ^ 2 * safeProbeEntry (p i) (p i) +
        |a j| ^ 2 * safeProbeEntry (p j) (p j))) =
      2 * (n : ℝ) * probeDiagonalEnergy p a := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    unfold probeDiagonalEnergy
    ring
  rw [hl, hr] at h
  linarith only [h]

/-- Removing all diagonal terms leaves a bounded nonnegative aligned cross energy. -/
theorem aligned_cross_energy_bounds {n : ℕ} (p a : Fin (n + 1) → ℝ) :
    0 ≤ alignedEnergy p a - probeDiagonalEnergy p a ∧
      alignedEnergy p a - probeDiagonalEnergy p a ≤ (n : ℝ) * probeDiagonalEnergy p a := by
  constructor
  · have hdiag : probeDiagonalEnergy p a ≤ alignedEnergy p a := by
      unfold probeDiagonalEnergy alignedEnergy sourceQuadratic
      apply Finset.sum_le_sum
      intro i _
      have hn (j : Fin (n + 1)) : 0 ≤
          |a i| * |a j| * bareMixedEnergy (probe (node (p i))) (probe (node (p j))) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (probeEntry_pos _ _).le
      have h := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      simpa only [pow_two, safeProbeEntry] using h
    exact sub_nonneg.mpr hdiag
  · have h := alignedEnergy_le_card_diagonal p a
    simp only [Nat.cast_add, Nat.cast_one] at h
    linarith only [h]

/-- The diagonal-budget defect is exactly the sum of antisymmetric two-probe energies. -/
theorem diagonal_budget_defect {n : ℕ} (p a : Fin n → ℝ) :
    (n : ℝ) * probeDiagonalEnergy p a - alignedEnergy p a =
      (1 / 2 : ℝ) * ∑ i, ∑ j, twoProbeQuadratic (p i) (p j) |a i| (-|a j|) := by
  have he (i j : Fin n) : twoProbeQuadratic (p i) (p j) |a i| (-|a j|) =
      |a i| ^ 2 * safeProbeEntry (p i) (p i) +
        |a j| ^ 2 * safeProbeEntry (p j) (p j) -
          2 * (|a i| * |a j| * safeProbeEntry (p i) (p j)) := by
    unfold twoProbeQuadratic
    ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  change (n : ℝ) * probeDiagonalEnergy p a - alignedEnergy p a =
    (1 / 2 : ℝ) * ((n : ℝ) * probeDiagonalEnergy p a +
      (n : ℝ) * probeDiagonalEnergy p a - 2 * alignedEnergy p a)
  ring

private theorem alignedEnergy_eq_card_diagonal_iff_pairs {n : ℕ} (p a : Fin n → ℝ) :
    alignedEnergy p a = (n : ℝ) * probeDiagonalEnergy p a ↔
      ∀ i j, twoProbeQuadratic (p i) (p j) |a i| (-|a j|) = 0 := by
  have hn (i j : Fin n) := twoProbeQuadratic_nonneg (p i) (p j) |a i| (-|a j|)
  constructor
  · intro h i j
    have hs := diagonal_budget_defect p a
    rw [h, sub_self] at hs
    have hsum : (∑ i, ∑ j, twoProbeQuadratic (p i) (p j) |a i| (-|a j|)) = 0 := by
      linarith only [hs]
    have hij := Finset.single_le_sum (fun j _ => hn i j) (Finset.mem_univ j)
    have hi := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hn i j)) (Finset.mem_univ i)
    rw [hsum] at hi
    exact le_antisymm (hij.trans hi) (hn i j)
  · intro h
    have hs := diagonal_budget_defect p a
    simp only [h, Finset.sum_const_zero, mul_zero] at hs
    exact (sub_eq_zero.mp hs).symm

/-- Saturation is either the zero family or total node collision with equal coefficient magnitudes. -/
theorem alignedEnergy_eq_card_diagonal_iff {n : ℕ} (p a : Fin n → ℝ) :
    alignedEnergy p a = (n : ℝ) * probeDiagonalEnergy p a ↔
      (∀ i, a i = 0) ∨ (∀ i j, node (p i) = node (p j) ∧ |a i| = |a j|) := by
  rw [alignedEnergy_eq_card_diagonal_iff_pairs]
  constructor
  · intro h
    by_cases ha : ∀ i, a i = 0
    · exact Or.inl ha
    · right
      push_neg at ha
      obtain ⟨i, hi⟩ := ha
      have hall (j : Fin n) : node (p i) = node (p j) ∧ |a i| = |a j| := by
        have hz := (twoProbeQuadratic_zero_iff (p i) (p j) |a i| (-|a j|)).mp (h i j)
        by_cases hp : node (p i) = node (p j)
        · rw [if_pos hp] at hz
          exact ⟨hp, by linarith only [hz]⟩
        · rw [if_neg hp] at hz
          exact (hi (abs_eq_zero.mp hz.1)).elim
      intro j k
      exact ⟨(hall j).1.symm.trans (hall k).1, (hall j).2.symm.trans (hall k).2⟩
  · rintro (ha | ha) i j
    · simp only [ha, abs_zero, neg_zero, twoProbeQuadratic,
        zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    · apply (twoProbeQuadratic_zero_iff (p i) (p j) |a i| (-|a j|)).mpr
      rw [if_pos (ha i j).1, (ha i j).2, add_neg_cancel]

#print axioms alignedEnergy_le_card_diagonal
#print axioms aligned_cross_energy_bounds
#print axioms diagonal_budget_defect
#print axioms alignedEnergy_eq_card_diagonal_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
