import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters
import GaloisForLFunctions.HTGeometry.HorizonScalingSymmetry

/-!
# Quadratic cost of a word of Euler filters

Normalize a positive Euler multiplier by its constant and linear terms,
using scalar multiplication and a positive change of variable. Its
multiplier in degree `j` is the probability of at most one success in
`j` Bernoulli trials of parameter `1/(s+2)`. Telescoping successive
multipliers bounds the loss by the sum of the pair-collision probabilities.
This quadratic estimate applies to arbitrary words with nonuniform weights.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-- Retained degree multiplier after normalizing the constant and linear terms. -/
def eulerRetention (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => (1-u)^j*(1+(j : ℝ)*u)

private theorem keep_drop (u : ℝ) (j : ℕ) :
    eulerRetention u (j+1) - eulerRetention u (j+2) = ((j : ℝ)+1)*u^2*(1-u)^j := by
  simp only [eulerRetention, Nat.cast_succ, pow_succ]
  ring

private theorem keep_unit {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) (j : ℕ) :
    0 ≤ eulerRetention u j ∧ eulerRetention u j ≤ 1 := by
  have hbase : 0 ≤ 1-u := sub_nonneg.mpr hu'
  induction j with
  | zero => simp [eulerRetention]
  | succ j ih =>
    refine ⟨mul_nonneg (pow_nonneg hbase _) (by positivity), ?_⟩
    cases j with
    | zero => simp [eulerRetention]
    | succ j =>
      have H := keep_drop u j
      linarith only [ih.2, H, mul_nonneg (mul_nonneg (by positivity : 0 ≤ (j : ℝ)+1)
        (sq_nonneg u)) (pow_nonneg hbase j)]

private theorem keep_loss {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) (j : ℕ) :
    1 - eulerRetention u j ≤ (j.choose 2 : ℝ)*u^2 := by
  induction j with
  | zero => simp [eulerRetention]
  | succ j ih =>
    cases j with
    | zero => simp [eulerRetention]
    | succ j =>
      have hpow : (1-u)^j ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hu') (by linarith) _
      have hdrop := keep_drop u j
      have hle := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (by positivity : 0 ≤ (j : ℝ)+1) (sq_nonneg u))
      rw [Nat.choose_succ_succ (j+1) 1, Nat.choose_one, Nat.cast_add, Nat.cast_succ]
      linarith only [ih, hdrop, hle]

/-- Reciprocal of the linear eigenvalue of one positive Euler filter. -/
def eulerTrialRate (s : ℕ) : ℝ := ((s : ℝ)+2)⁻¹

private theorem rate_bounds (s : ℕ) : 0 ≤ eulerTrialRate s ∧ eulerTrialRate s ≤ 1 :=
  ⟨by unfold eulerTrialRate; positivity, by unfold eulerTrialRate; rw [inv_le_one₀ (by positivity)]; positivity⟩

private theorem normalized_eigenvalue (s j : ℕ) :
    ((s : ℝ)+1)⁻¹ * ((s : ℝ)+1+j) * (((s : ℝ)+1)/((s : ℝ)+2))^j = eulerRetention (eulerTrialRate s) j := by
  have h₁ : (s : ℝ)+1 ≠ 0 := by positivity
  have h₂ : (s : ℝ)+2 ≠ 0 := by positivity
  cases j with
  | zero => simp [eulerRetention, h₁]
  | succ j =>
    rw [eulerRetention, eulerTrialRate, show 1-((s : ℝ)+2)⁻¹ = ((s : ℝ)+1)/((s : ℝ)+2) by field_simp; ring,
      pow_succ, Nat.cast_succ]
    field_simp [h₁, h₂]
    <;> ring

/-- Pair-collision budget of a word. -/
def eulerCollisionCost (w : List ℕ) : ℝ := (w.map fun s => eulerTrialRate s ^ 2).sum

/-- Scalar and dilation normalization preserving splitting and both lowest coefficients. -/
def normalizedEulerWord (w : List ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((w.map fun s : ℕ => ((s : ℝ)+1)⁻¹).prod) * (eulerWord w p).comp
    (C ((w.map fun s : ℕ => ((s : ℝ)+1)/((s : ℝ)+2)).prod) * X)

private theorem normalized_product (w : List ℕ) (j : ℕ) :
    (w.map (fun s : ℕ => ((s : ℝ)+1)⁻¹)).prod *
      (w.map (fun s : ℕ => (s : ℝ)+1+j)).prod *
      (w.map (fun s : ℕ => ((s : ℝ)+1)/((s : ℝ)+2))).prod^j =
    (w.map (fun s => eulerRetention (eulerTrialRate s) j)).prod := by
  induction w with
  | nil => simp
  | cons s w ih =>
    simp only [List.map_cons, List.prod_cons, mul_pow]
    rw [← normalized_eigenvalue, ← ih]
    ring

theorem normalizedEulerWord_coeff (w : List ℕ) (p : ℝ[X]) (j : ℕ) :
    (normalizedEulerWord w p).coeff j = (w.map (fun s => eulerRetention (eulerTrialRate s) j)).prod*p.coeff j := by
  rw [normalizedEulerWord, coeff_C_mul, horizonScalingCoeff_comp_C_mul_X, eulerWord_coeff,
    ← normalized_product]
  ring

private theorem joint_loss (w : List ℕ) (j : ℕ) :
    let F := (w.map (fun s => eulerRetention (eulerTrialRate s) j)).prod
    0 ≤ F ∧ F ≤ 1 ∧ 1-F ≤ (j.choose 2 : ℝ)*eulerCollisionCost w := by
  induction w with
  | nil => simp [eulerCollisionCost]
  | cons s w ih =>
    dsimp only [List.map_cons, List.prod_cons] at ih ⊢
    obtain ⟨hlo,hhi,hloss⟩ := ih
    obtain ⟨hr,hr'⟩ := rate_bounds s
    obtain ⟨hk,hk'⟩ := keep_unit hr hr' j
    refine ⟨mul_nonneg hk hlo, (mul_le_mul_of_nonneg_right hk' hlo).trans (by simpa using hhi), ?_⟩
    change _ ≤ (j.choose 2 : ℝ)*(eulerTrialRate s^2+eulerCollisionCost w)
    have hprod := mul_nonneg (sub_nonneg.mpr hk') (sub_nonneg.mpr hhi)
    nlinarith only [hprod, hloss, keep_loss hr hr' j]

/-- Sharp pair-count constant controls every coefficient of the normalized operator. -/
theorem normalizedEulerWord_error (w : List ℕ) (p : ℝ[X]) (j : ℕ) :
    |(normalizedEulerWord w p).coeff j - p.coeff j| ≤
      |p.coeff j| * (j.choose 2 : ℝ) * eulerCollisionCost w := by
  have H := joint_loss w j
  rw [normalizedEulerWord_coeff, ← sub_one_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr H.2.1)]
  have h := mul_le_mul_of_nonneg_right H.2.2 (abs_nonneg (p.coeff j))
  linarith only [h]

theorem normalizedEulerWord_splits (w : List ℕ) (p : ℝ[X]) :
    (eulerWord w p).Splits → (normalizedEulerWord w p).Splits := by
  intro hs
  apply (Polynomial.Splits.C _).mul
  exact hs.comp_of_natDegree_le_one ((natDegree_C_mul_le _ _).trans natDegree_X.le)

#print axioms normalizedEulerWord_error
#print axioms normalizedEulerWord_splits

end

end FiniteFreeProbability
