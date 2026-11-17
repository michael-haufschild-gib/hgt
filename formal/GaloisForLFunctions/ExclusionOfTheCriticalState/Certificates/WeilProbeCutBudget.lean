import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.SchurRadialRegularization

/-!
# Finite Weil sign tests are weighted cut budgets

Every entry of the safe real probe kernel is strictly positive.
Separating coefficient magnitudes from signs expresses the full Weil
quadratic form as its aligned value minus four times a positive cut
weight. Thus a negative finite sign test is exactly a cut exceeding one
quarter of the aligned value. This supplies the exact finite objective
for the Bellman sign-selection mechanism of arXiv:2611.16663.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick
noncomputable section

/-- Safe probe pairs have positive entries even when their full matrix is indefinite. -/
theorem probeEntry_pos (s t : ℝ) :
    0 < bareMixedEnergy (probe (node s)) (probe (node t)) := by
  have hs : (1 / 2 : ℝ) < node s := by unfold node; linarith only [abs_nonneg s]
  have ht : (1 / 2 : ℝ) < node t := by unfold node; linarith only [abs_nonneg t]
  rw [bareMixedEnergy_probe hs ht]
  exact div_pos (add_pos (symbol_pos s) (symbol_pos t)) (by linarith only [hs, ht])

/-- Edge weight determined by the actual Weil kernel and coefficient magnitudes. -/
def weight {n : ℕ} (p a : Fin n → ℝ) (i j : Fin n) : ℝ :=
  |a i| * |a j| * bareMixedEnergy (probe (node (p i))) (probe (node (p j)))

theorem weight_nonneg {n : ℕ} (p a : Fin n → ℝ) (i j : Fin n) : 0 ≤ weight p a i j :=
  mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (probeEntry_pos _ _).le

/-- Half the ordered weight crossing a binary partition. -/
def cutWeight {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, if σ i = σ j then 0 else weight p a i j

/-- Coefficients with prescribed magnitudes and selected signs. -/
def signedCoefficients {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) (i : Fin n) : ℝ :=
  |a i| * if σ i then 1 else -1

/-- The reference energy with all signs aligned. -/
def alignedEnergy {n : ℕ} (p a : Fin n → ℝ) : ℝ := sourceQuadratic n p (fun i => |a i|)

theorem cutWeight_nonneg {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) :
    0 ≤ cutWeight p a σ := by
  unfold cutWeight
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact weight_nonneg p a i j

/-- The exact identity retains every diagonal and cross term of the Weil form. -/
theorem signed_energy_eq_aligned_sub_cut {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) :
    sourceQuadratic n p (signedCoefficients a σ) = alignedEnergy p a - 4 * cutWeight p a σ := by
  have hterm (i j : Fin n) :
      signedCoefficients a σ i * signedCoefficients a σ j *
          bareMixedEnergy (probe (node (p i))) (probe (node (p j))) =
        weight p a i j - 2 * (if σ i = σ j then 0 else weight p a i j) := by
    cases hi : σ i <;> cases hj : σ j <;> simp [signedCoefficients, hi, hj, weight] <;> ring
  unfold alignedEnergy cutWeight sourceQuadratic
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ i, ∑ j, weight p a i j) - 2 * (∑ i, ∑ j,
    if σ i = σ j then 0 else weight p a i j) = _
  unfold weight
  ring

/-- A negative sign test is precisely an excessive positive cut. -/
theorem negative_signed_energy_iff {n : ℕ} (p a : Fin n → ℝ) (σ : Fin n → Bool) :
    sourceQuadratic n p (signedCoefficients a σ) < 0 ↔
      alignedEnergy p a / 4 < cutWeight p a σ := by
  rw [signed_energy_eq_aligned_sub_cut]
  constructor <;> intro h <;> linarith only [h]

private theorem signedCoefficients_reconstruct {n : ℕ} (c : Fin n → ℝ) :
    signedCoefficients c (fun i => decide (0 ≤ c i)) = c := by
  funext i
  by_cases h : 0 ≤ c i
  · simp [signedCoefficients, h, abs_of_nonneg h]
  · simp [signedCoefficients, h, abs_of_neg (lt_of_not_ge h)]

/-- Arbitrary real negative witnesses are exhausted by positive magnitudes and binary cuts. -/
theorem negative_probe_form_iff_excessive_cut (n : ℕ) (p : Fin n → ℝ) :
    (∃ c : Fin n → ℝ, sourceQuadratic n p c < 0) ↔
      ∃ (a : Fin n → ℝ) (σ : Fin n → Bool), alignedEnergy p a / 4 < cutWeight p a σ := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => decide (0 ≤ c i), (negative_signed_energy_iff _ _ _).mp ?_⟩
    rwa [signedCoefficients_reconstruct]
  · rintro ⟨a, σ, h⟩
    exact ⟨signedCoefficients a σ, (negative_signed_energy_iff _ _ _).mpr h⟩

/-- Positive semidefiniteness is an exact uniform cut-capacity bound. -/
theorem probe_form_nonnegative_iff_cut_budget (n : ℕ) (p : Fin n → ℝ) :
    (∀ c : Fin n → ℝ, 0 ≤ sourceQuadratic n p c) ↔
      ∀ (a : Fin n → ℝ) (σ : Fin n → Bool), cutWeight p a σ ≤ alignedEnergy p a / 4 := by
  constructor
  · intro h a σ
    have hs := h (signedCoefficients a σ)
    rw [signed_energy_eq_aligned_sub_cut] at hs
    linarith only [hs]
  · intro h c
    have hs := h c (fun i => decide (0 ≤ c i))
    have he := signed_energy_eq_aligned_sub_cut p c (fun i => decide (0 ≤ c i))
    rw [signedCoefficients_reconstruct] at he
    linarith only [hs, he]

#print axioms probeEntry_pos
#print axioms signed_energy_eq_aligned_sub_cut
#print axioms negative_probe_form_iff_excessive_cut
#print axioms probe_form_nonnegative_iff_cut_budget
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
