import GaloisForLFunctions.BiScaleUncertainty.QuadraticPerturbedNodes
import GaloisForLFunctions.BiScaleUncertainty.IntegerLinearVariance
import GaloisForLFunctions.BiScaleUncertainty.FiniteWindowVariance

/-!
# Exact doubling incidence and its discontinuous coercivity constant

The graph is defined from actual physical positions. It equals integer
doubling on the integer grid, but vanishes for the explicit quadratic
perturbation. The linear signal then forces the exact additive-only ratio.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- All ordered pairs satisfying literal physical doubling contribute an edge. -/
def exactDoublingEnergy (N : ℕ) (x f : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    if x j = 2 * x i then (f j - f i) ^ 2 else 0

theorem exactDoublingEnergy_nonneg (N : ℕ) (x f : ℕ → ℝ) :
    0 ≤ exactDoublingEnergy N x f := by
  classical
  unfold exactDoublingEnergy
  apply sum_nonneg
  intro i _
  apply sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- Exclusion of every actual incidence makes the complete graph energy zero. -/
theorem exactDoublingEnergy_eq_zero_of_no_incidence (N : ℕ) (x f : ℕ → ℝ)
    (hx : ∀ i ∈ Icc 1 N, ∀ j ∈ Icc 1 N, x j ≠ 2 * x i) :
    exactDoublingEnergy N x f = 0 := by
  classical
  unfold exactDoublingEnergy
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  exact if_neg (hx i hi j hj)

/-- The actual integer incidences give exactly the original doubling energy. -/
theorem exactDoublingEnergy_integer (N : ℕ) (f : ℕ → ℝ) :
    exactDoublingEnergy N (fun n : ℕ => (n : ℝ)) f = multiplicativeScaleEnergy 2 N f := by
  classical
  have hsub : Icc 1 (N / 2) ⊆ Icc 1 N := by
    intro i hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans (Nat.div_le_self N 2)⟩
  have hne (i j : ℕ) (hji : j ≠ 2 * i) : (j : ℝ) ≠ 2 * (i : ℝ) := by
    intro he
    apply hji
    exact_mod_cast he
  have hout (i : ℕ) (hi : i ∈ Icc 1 N) (hout : i ∉ Icc 1 (N / 2)) :
      (∑ j ∈ Icc 1 N, if (j : ℝ) = 2 * (i : ℝ) then (f j - f i) ^ 2 else 0) = 0 := by
    apply sum_eq_zero
    intro j hj
    apply if_neg
    apply hne
    intro he
    apply hout
    have hi' := mem_Icc.mp hi
    have hj' := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨hi'.1, by omega⟩
  unfold exactDoublingEnergy
  simp only [multiplicativeScaleEnergy, Icc_self, sum_singleton]
  calc
    _ = ∑ i ∈ Icc 1 (N / 2), ∑ j ∈ Icc 1 N,
        if (j : ℝ) = 2 * (i : ℝ) then (f j - f i) ^ 2 else 0 := (sum_subset hsub hout).symm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_Icc.mp hi
      have h2i : 2 * i ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
      rw [sum_eq_single (2 * i)]
      · simp only [Nat.cast_mul, Nat.cast_ofNat, ite_true]
      · intro j _ hji
        exact if_neg (hne i j hji)
      · exact fun hn => (hn h2i).elim

/-- Before perturbation, the actual graph has the stated linear coercivity bound. -/
theorem exactDoubling_integer_coercivity (N : ℕ) (f : ℕ → ℝ) :
    integerWindowVariance N f ≤ 24 * (N : ℝ) *
      (additiveStepEnergy N f + exactDoublingEnergy N (fun n : ℕ => (n : ℝ)) f) := by
  rw [exactDoublingEnergy_integer]
  have hb := (integerWindowVariance_le_centered N f (f 1)).trans (doubling_window_coercivity N f)
  have he := biScaleJointEnergy_nonneg 2 N f
  change integerWindowVariance N f ≤ 24 * (N : ℝ) * biScaleJointEnergy 2 N f
  exact hb.trans (mul_le_mul_of_nonneg_right
    (by have hN := Nat.cast_nonneg (α := ℝ) N; linarith only [hN]) he)

/-- Every signal loses all exact-doubling energy on the specified perturbed nodes. -/
theorem exactDoublingEnergy_quadraticPerturbedNode {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) (N : ℕ) (f : ℕ → ℝ) :
    exactDoublingEnergy N (quadraticPerturbedNode δ N) f = 0 :=
  exactDoublingEnergy_eq_zero_of_no_incidence N _ f
    (fun _ hi _ hj => quadraticPerturbedNode_ne_double hδ hδ1 hi hj)

/-- The exact perturbed graph requires the full quadratic additive-only ratio. -/
theorem exactDoubling_quadratic_coercivity_lower {δ C : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) {N : ℕ} (hN : 2 ≤ N)
    (hC : ∀ f : ℕ → ℝ, integerWindowVariance N f ≤ C *
      (additiveStepEnergy N f + exactDoublingEnergy N (quadraticPerturbedNode δ N) f)) :
    (N : ℝ) * ((N : ℝ) + 1) / 12 ≤ C := by
  apply additive_coercivity_constant_linear_lower_bound hN
  intro f
  refine ⟨integerWindowMean N f, ?_⟩
  have h := hC f
  simpa only [integerWindowVariance, exactDoublingEnergy_quadraticPerturbedNode hδ hδ1,
    add_zero] using h

/-- Arbitrarily small strictly ordered perturbations destroy every exact doubling incidence. -/
theorem exists_small_incidence_free_grid (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
      StrictMono (quadraticPerturbedNode δ N) ∧
      (∀ n ∈ Icc 1 N, |quadraticPerturbedNode δ N n - (n : ℝ)| < ε) ∧
      (∀ f : ℕ → ℝ, exactDoublingEnergy N (quadraticPerturbedNode δ N) f = 0) := by
  let δ := min (ε / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδ, hδ1, strictMono_quadraticPerturbedNode hδ.le N, ?_,
    fun f => exactDoublingEnergy_quadraticPerturbedNode hδ hδ1 N f⟩
  intro n hn
  have hd := quadraticPerturbedNode_displacement hδ (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  rw [abs_of_pos hd.1]
  exact hd.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
