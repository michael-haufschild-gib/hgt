import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPurityJet
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Global triangular chart for scale-covariant Bernstein purity

The coefficient jet of the degree-`N` scale-purity polynomial gives global coordinates on the
pointed moment prefix `m 0, ..., m N`.  This file constructs the inverse recursively.  The
construction is genuinely global: every real target jet with positive constant coordinate has a
unique pointed moment prefix.
-/

namespace RHTower

noncomputable section

/-- Successive reconstruction of a moment sequence from a proposed purity jet.  Stage zero fixes
the positive orientation, and stage `r+1` solves the triangular coefficient identity for the next
moment. -/
def bernsteinPurityJetInverseStage (N : ℕ) (y : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => Function.update (fun _ => 0) 0 (Real.sqrt (y 0))
  | r + 1 =>
      let prev := bernsteinPurityJetInverseStage N y r
      Function.update prev (r + 1)
        ((y (r + 1) - bernsteinScalePurityLower prev N (r + 1)) /
          (2 * (-1 : ℝ) ^ (r + 1) * N.choose (r + 1) * prev 0))

/-- The reconstructed sequence after the final relevant stage. -/
def bernsteinPurityJetInverse (N : ℕ) (y : ℕ → ℝ) : ℕ → ℝ :=
  bernsteinPurityJetInverseStage N y N

@[simp] theorem bernsteinPurityJetInverseStage_zero_apply_zero (N : ℕ) (y : ℕ → ℝ) :
    bernsteinPurityJetInverseStage N y 0 0 = Real.sqrt (y 0) := by
  simp [bernsteinPurityJetInverseStage]

/-- Passing to the next stage does not change any already reconstructed coordinate. -/
  theorem bernsteinPurityJetInverseStage_succ_apply_of_le
    (N : ℕ) (y : ℕ → ℝ) {r j : ℕ} (hj : j ≤ r) :
    bernsteinPurityJetInverseStage N y (r + 1) j =
      bernsteinPurityJetInverseStage N y r j := by
  rw [bernsteinPurityJetInverseStage]
  simp [Nat.ne_of_lt (Nat.lt_succ_of_le hj)]

/-- A reconstructed prefix is stable at all later stages. -/
theorem bernsteinPurityJetInverseStage_stable
    (N : ℕ) (y : ℕ → ℝ) {r s j : ℕ} (hrs : r ≤ s) (hj : j ≤ r) :
    bernsteinPurityJetInverseStage N y s j =
      bernsteinPurityJetInverseStage N y r j := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
      rw [bernsteinPurityJetInverseStage_succ_apply_of_le N y (hj.trans hrs), ih]

/-- The pointed mass remains the positive square root throughout the recursion. -/
theorem bernsteinPurityJetInverseStage_apply_zero
    (N : ℕ) (y : ℕ → ℝ) (r : ℕ) :
    bernsteinPurityJetInverseStage N y r 0 = Real.sqrt (y 0) := by
  exact bernsteinPurityJetInverseStage_stable N y (Nat.zero_le r) (Nat.zero_le 0)

theorem bernsteinPurityJetInverse_apply_zero
    (N : ℕ) (y : ℕ → ℝ) :
    bernsteinPurityJetInverse N y 0 = Real.sqrt (y 0) := by
  exact bernsteinPurityJetInverseStage_apply_zero N y N

theorem bernsteinPurityJetInverse_zero_pos
    (N : ℕ) {y : ℕ → ℝ} (hy : 0 < y 0) :
    0 < bernsteinPurityJetInverse N y 0 := by
  rw [bernsteinPurityJetInverse_apply_zero]
  exact Real.sqrt_pos.2 hy

/-- At stage `r+1`, the newly reconstructed coordinate is the explicit triangular quotient. -/
theorem bernsteinPurityJetInverseStage_succ_apply_self
    (N : ℕ) (y : ℕ → ℝ) (r : ℕ) :
    bernsteinPurityJetInverseStage N y (r + 1) (r + 1) =
      ((y (r + 1) -
          bernsteinScalePurityLower (bernsteinPurityJetInverseStage N y r) N (r + 1)) /
        (2 * (-1 : ℝ) ^ (r + 1) * N.choose (r + 1) *
          bernsteinPurityJetInverseStage N y r 0)) := by
  simp [bernsteinPurityJetInverseStage]

/-- The recursive inverse realizes every prescribed positive purity jet through degree `N`. -/
theorem coeff_bernsteinScalePurityPolynomial_inverse
    (N : ℕ) {y : ℕ → ℝ} (hy : 0 < y 0) {r : ℕ} (hr : r ≤ N) :
    (bernsteinScalePurityPolynomial (bernsteinPurityJetInverse N y) N).coeff r = y r := by
  cases r with
  | zero =>
      rw [coeff_zero_bernsteinScalePurityPolynomial,
        bernsteinPurityJetInverse_apply_zero, Real.sq_sqrt hy.le]
  | succ r =>
      have hrN : r + 1 ≤ N := hr
      have hr0 : 0 < r + 1 := Nat.zero_lt_succ r
      have hchooseNat : 0 < N.choose (r + 1) := Nat.choose_pos hrN
      have hchoose : (N.choose (r + 1) : ℝ) ≠ 0 := by
        exact_mod_cast hchooseNat.ne'
      have hroot : 0 < Real.sqrt (y 0) := Real.sqrt_pos.2 hy
      have hden :
          2 * (-1 : ℝ) ^ (r + 1) * N.choose (r + 1) *
            bernsteinPurityJetInverseStage N y r 0 ≠ 0 := by
        rw [bernsteinPurityJetInverseStage_apply_zero]
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hchoose)
          hroot.ne'
      have hprev0 : bernsteinPurityJetInverseStage N y r 0 ≠ 0 := by
        rw [bernsteinPurityJetInverseStage_apply_zero]
        exact hroot.ne'
      have hcoord : bernsteinPurityJetInverse N y (r + 1) =
          ((y (r + 1) -
              bernsteinScalePurityLower (bernsteinPurityJetInverseStage N y r) N (r + 1)) /
            (2 * (-1 : ℝ) ^ (r + 1) * N.choose (r + 1) *
              bernsteinPurityJetInverseStage N y r 0)) := by
        rw [bernsteinPurityJetInverse]
        exact (bernsteinPurityJetInverseStage_stable N y hrN (le_refl (r + 1))).trans
          (bernsteinPurityJetInverseStage_succ_apply_self N y r)
      have hzero : bernsteinPurityJetInverse N y 0 =
          bernsteinPurityJetInverseStage N y r 0 := by
        rw [bernsteinPurityJetInverse_apply_zero,
          bernsteinPurityJetInverseStage_apply_zero]
      have hlower :
          bernsteinScalePurityLower (bernsteinPurityJetInverse N y) N (r + 1) =
            bernsteinScalePurityLower
              (bernsteinPurityJetInverseStage N y r) N (r + 1) := by
        apply bernsteinScalePurityLower_congr N
        intro j hj
        exact bernsteinPurityJetInverseStage_stable N y
          ((Nat.le_succ r).trans hrN) (Nat.le_of_lt_succ hj)
      rw [coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower
          (bernsteinPurityJetInverse N y) N hr0 hrN,
        hcoord, hzero, hlower]
      field_simp [hden, hprev0]
      ring

/-- Every target prefix with positive constant coordinate has a pointed preimage. -/
theorem exists_pointed_moment_of_positive_bernsteinPurityJet
    (N : ℕ) {y : ℕ → ℝ} (hy : 0 < y 0) :
    ∃ m : ℕ → ℝ, 0 < m 0 ∧
      ∀ r ≤ N, (bernsteinScalePurityPolynomial m N).coeff r = y r := by
  exact ⟨bernsteinPurityJetInverse N y,
    bernsteinPurityJetInverse_zero_pos N hy,
    fun r hr => coeff_bernsteinScalePurityPolynomial_inverse N hy hr⟩

/-- The explicit inverse is a left inverse on every pointed moment prefix. -/
theorem bernsteinPurityJetInverse_leftInverse_prefix
    (N : ℕ) {m : ℕ → ℝ} (hm : 0 < m 0) :
    ∀ r ≤ N,
      bernsteinPurityJetInverse N
        (fun j => (bernsteinScalePurityPolynomial m N).coeff j) r = m r := by
  let y : ℕ → ℝ := fun j => (bernsteinScalePurityPolynomial m N).coeff j
  have hy : 0 < y 0 := by
    dsimp only [y]
    rw [coeff_zero_bernsteinScalePurityPolynomial]
    positivity
  have hinv0 := bernsteinPurityJetInverse_zero_pos N hy
  apply bernsteinScalePurityJet_injectiveOn_pointed hinv0 hm
  intro r hr
  exact coeff_bernsteinScalePurityPolynomial_inverse N hy hr

/-- Global pointed chart theorem: a positive purity jet has one and only one moment prefix. -/
theorem bernsteinPurityJet_global_pointed_chart
    (N : ℕ) {y : ℕ → ℝ} (hy : 0 < y 0) :
    ∃ m : ℕ → ℝ,
      0 < m 0 ∧
      (∀ r ≤ N, (bernsteinScalePurityPolynomial m N).coeff r = y r) ∧
      ∀ m' : ℕ → ℝ, 0 < m' 0 →
        (∀ r ≤ N, (bernsteinScalePurityPolynomial m' N).coeff r = y r) →
        ∀ r ≤ N, m' r = m r := by
  refine ⟨bernsteinPurityJetInverse N y,
    bernsteinPurityJetInverse_zero_pos N hy,
    fun r hr => coeff_bernsteinScalePurityPolynomial_inverse N hy hr, ?_⟩
  intro m' hm' hjet
  apply bernsteinScalePurityJet_injectiveOn_pointed hm'
    (bernsteinPurityJetInverse_zero_pos N hy)
  intro r hr
  rw [hjet r hr, coeff_bernsteinScalePurityPolynomial_inverse N hy hr]

end

end RHTower
