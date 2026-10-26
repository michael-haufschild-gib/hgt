import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity

/-!
# Comparable logarithmic spacing without exact doubling incidence

The explicit quadratic perturbation is arbitrarily small and strictly ordered.
Its logarithmic gaps stay quantitatively comparable to the integer grid, but
no two positive window nodes have exact physical doubling incidence.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- The specified quadratic displacement of the integer nodes. -/
def quadraticPerturbedNode (δ : ℝ) (N n : ℕ) : ℝ :=
  (n : ℝ) + δ * (n : ℝ) ^ 2 / (N : ℝ) ^ 2

/-- Actual logarithmic coordinates of the perturbed physical nodes. -/
def quadraticPerturbedLogNode (δ : ℝ) (N n : ℕ) : ℝ :=
  Real.log (quadraticPerturbedNode δ N n)

/-- The displacement lies strictly above zero and at most the prescribed radius. -/
theorem quadraticPerturbedNode_displacement {δ : ℝ} (hδ : 0 < δ) {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    0 < quadraticPerturbedNode δ N n - (n : ℝ) ∧
      quadraticPerturbedNode δ N n - (n : ℝ) ≤ δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hle : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith only [hle, hnR]
  have he : quadraticPerturbedNode δ N n - (n : ℝ) = δ * (n : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    unfold quadraticPerturbedNode
    ring
  rw [he]
  refine ⟨div_pos (mul_pos hδ (sq_pos_of_pos hnR)) (sq_pos_of_pos hN), ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
  exact mul_le_mul_of_nonneg_left hsq hδ.le

/-- The actual nodes remain strictly increasing on the whole natural ray. -/
theorem strictMono_quadraticPerturbedNode {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    StrictMono (quadraticPerturbedNode δ N) := by
  intro i j hij
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hsq : (i : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by nlinarith only [hijR, hiR]
  have hpert := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hδ)
    (sq_nonneg (N : ℝ))
  unfold quadraticPerturbedNode
  linarith only [hijR, hpert]

/-- Every adjacent physical gap has its exact polynomial expression. -/
theorem quadraticPerturbedNode_succ_sub (δ : ℝ) (N n : ℕ) :
    quadraticPerturbedNode δ N (n + 1) - quadraticPerturbedNode δ N n =
      1 + δ * (2 * (n : ℝ) + 1) / (N : ℝ) ^ 2 := by
  unfold quadraticPerturbedNode
  push_cast
  ring

/-- On integer doubling labels the perturbed nodes have a strictly positive mismatch. -/
theorem quadraticPerturbedNode_double_sub (δ : ℝ) (N i : ℕ) :
    quadraticPerturbedNode δ N (2 * i) - 2 * quadraticPerturbedNode δ N i =
      2 * δ * (i : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  unfold quadraticPerturbedNode
  push_cast
  ring

/-- The perturbation of any window doubling mismatch has absolute value at most twice its radius. -/
theorem abs_quadratic_doubling_perturbation_le {δ : ℝ} (hδ : 0 < δ) {N i j : ℕ}
    (hi : i ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    |(quadraticPerturbedNode δ N j - 2 * quadraticPerturbedNode δ N i) -
      ((j : ℝ) - 2 * (i : ℝ))| ≤ 2 * δ := by
  have hdi := quadraticPerturbedNode_displacement hδ (mem_Icc.mp hi).1 (mem_Icc.mp hi).2
  have hdj := quadraticPerturbedNode_displacement hδ (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  apply abs_le.mpr
  constructor <;> linarith only [hdi.1, hdi.2, hdj.1, hdj.2, hδ]

/-- No pair of positive window nodes has exact doubling incidence. -/
theorem quadraticPerturbedNode_ne_double {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    {N i j : ℕ} (hi : i ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    quadraticPerturbedNode δ N j ≠ 2 * quadraticPerturbedNode δ N i := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast (mem_Icc.mp hi).1
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by have hb := mem_Icc.mp hi; omega)
  intro he
  by_cases hji : j = 2 * i
  · subst j
    have hp : 0 < 2 * δ * (i : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
      div_pos (mul_pos (mul_pos (by norm_num) hδ) (sq_pos_of_pos hiR)) (sq_pos_of_pos hN)
    rw [← quadraticPerturbedNode_double_sub, he, sub_self] at hp
    exact (lt_irrefl 0) hp
  · have hb := abs_quadratic_doubling_perturbation_le hδ hi hj
    rw [he, sub_self, zero_sub, abs_neg] at hb
    rcases lt_or_gt_of_ne hji with hji | hji
    · have hg : (j : ℝ) + 1 ≤ 2 * (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ 2 * i by omega)
      have hlo := neg_le_abs ((j : ℝ) - 2 * (i : ℝ))
      linarith only [hb, hg, hlo, hδ1]
    · have hg : 2 * (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show 2 * i + 1 ≤ j by omega)
      have hlo := le_abs_self ((j : ℝ) - 2 * (i : ℝ))
      linarith only [hb, hg, hlo, hδ1]

private theorem quadraticNode_log_split {δ : ℝ} (hδ : 0 ≤ δ) {N n : ℕ} (hn : 1 ≤ n) :
    quadraticPerturbedLogNode δ N n =
      Real.log (n : ℝ) + Real.log (1 + δ * (n : ℝ) / (N : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < 1 + δ * (n : ℝ) / (N : ℝ) ^ 2 := by
    have hh := div_nonneg (mul_nonneg hδ hnR.le) (sq_nonneg (N : ℝ))
    linarith only [hh]
  unfold quadraticPerturbedLogNode quadraticPerturbedNode
  rw [show (n : ℝ) + δ * (n : ℝ) ^ 2 / (N : ℝ) ^ 2 =
    (n : ℝ) * (1 + δ * (n : ℝ) / (N : ℝ) ^ 2) by ring,
    Real.log_mul hnR.ne' hp.ne']

/-- Logarithmic displacements are bounded by the stated radius divided by the horizon. -/
theorem quadraticPerturbedLogNode_displacement {δ : ℝ} (hδ : 0 ≤ δ) {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    0 ≤ quadraticPerturbedLogNode δ N n - Real.log (n : ℝ) ∧
      quadraticPerturbedLogNode δ N n - Real.log (n : ℝ) ≤ δ / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hle : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have he0 : 0 ≤ δ * (n : ℝ) / (N : ℝ) ^ 2 := by positivity
  rw [quadraticNode_log_split hδ hn, add_sub_cancel_left]
  refine ⟨Real.log_nonneg (by linarith only [he0]), ?_⟩
  have hb := Real.log_le_sub_one_of_pos (by linarith only [he0] :
    0 < 1 + δ * (n : ℝ) / (N : ℝ) ^ 2)
  have he : δ * (n : ℝ) / (N : ℝ) ^ 2 ≤ δ / (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hle hδ
    apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hh hN.le]
  linarith only [hb, he]

private theorem log_one_add_step_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.log (1 + a + b) - Real.log (1 + a) ∧
      Real.log (1 + a + b) - Real.log (1 + a) ≤ b := by
  have ha1 : 0 < 1 + a := by linarith only [ha]
  have hab1 : 0 < 1 + a + b := by linarith only [ha1, hb]
  refine ⟨sub_nonneg.mpr (Real.log_le_log ha1 (by linarith only [hb])), ?_⟩
  calc
    _ = Real.log ((1 + a + b) / (1 + a)) := (Real.log_div hab1.ne' ha1.ne').symm
    _ ≤ (1 + a + b) / (1 + a) - 1 := Real.log_le_sub_one_of_pos (div_pos hab1 ha1)
    _ = b / (1 + a) := by field_simp [ha1.ne']; ring
    _ ≤ b := (div_le_iff₀ ha1).mpr (by nlinarith only [mul_nonneg ha hb])

/-- The additional logarithmic gap lies between zero and the exact displacement increment. -/
theorem quadraticPerturbedLogNode_extra_gap {δ : ℝ} (hδ : 0 ≤ δ) (N n : ℕ) :
    0 ≤ Real.log (1 + δ * ((n + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2) -
        Real.log (1 + δ * (n : ℝ) / (N : ℝ) ^ 2) ∧
      Real.log (1 + δ * ((n + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2) -
        Real.log (1 + δ * (n : ℝ) / (N : ℝ) ^ 2) ≤ δ / (N : ℝ) ^ 2 := by
  have he : 1 + δ * ((n + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2 =
      1 + δ * (n : ℝ) / (N : ℝ) ^ 2 + δ / (N : ℝ) ^ 2 := by push_cast; ring
  rw [he]
  exact log_one_add_step_bounds (by positivity) (by positivity)

/-- Consecutive logarithmic gaps retain the precise relative factor one plus radius over horizon. -/
theorem quadraticPerturbedLogNode_gap_bounds {δ : ℝ} (hδ : 0 ≤ δ) {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n < N) :
    Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
        quadraticPerturbedLogNode δ N (n + 1) - quadraticPerturbedLogNode δ N n ∧
      quadraticPerturbedLogNode δ N (n + 1) - quadraticPerturbedLogNode δ N n ≤
        (1 + δ / (N : ℝ)) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnext : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show n + 1 ≤ N by omega)
  have he := quadraticPerturbedLogNode_extra_gap hδ N n
  have hgap : quadraticPerturbedLogNode δ N (n + 1) - quadraticPerturbedLogNode δ N n =
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) +
        (Real.log (1 + δ * ((n + 1 : ℕ) : ℝ) / (N : ℝ) ^ 2) -
          Real.log (1 + δ * (n : ℝ) / (N : ℝ) ^ 2)) := by
    rw [quadraticNode_log_split hδ (by omega : 1 ≤ n + 1), quadraticNode_log_split hδ hn,
      Real.log_div hn1R.ne' hnR.ne']
    ring
  have hbase : 1 / ((n + 1 : ℕ) : ℝ) ≤ Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    have hb := Real.one_sub_inv_le_log_of_pos (div_pos hn1R hnR)
    have hid : 1 - (((n + 1 : ℕ) : ℝ) / (n : ℝ))⁻¹ = 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp [hnR.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]
      ring
    rwa [hid] at hb
  have hinv : 1 / (N : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
    (div_le_div_iff₀ hN hn1R).mpr (by simpa only [one_mul] using hnext)
  have hrelative : δ / (N : ℝ) ^ 2 ≤
      (δ / (N : ℝ)) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    calc
      _ = (δ / (N : ℝ)) * (1 / (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hinv.trans hbase) (div_nonneg hδ hN.le)
  rw [hgap]
  constructor <;> linarith only [he.1, he.2, hrelative]

/-- Exact logarithmic separation by log two is excluded on the same actual node set. -/
theorem quadraticPerturbedLogNode_sub_ne_log_two {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    {N i j : ℕ} (hi : i ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    quadraticPerturbedLogNode δ N j - quadraticPerturbedLogNode δ N i ≠ Real.log 2 := by
  have hip : 0 < quadraticPerturbedNode δ N i := by
    have hd := (quadraticPerturbedNode_displacement hδ (mem_Icc.mp hi).1 (mem_Icc.mp hi).2).1
    have hn := Nat.cast_nonneg (α := ℝ) i
    linarith only [hd, hn]
  have hjp : 0 < quadraticPerturbedNode δ N j := by
    have hd := (quadraticPerturbedNode_displacement hδ (mem_Icc.mp hj).1 (mem_Icc.mp hj).2).1
    have hn := Nat.cast_nonneg (α := ℝ) j
    linarith only [hd, hn]
  intro he
  have hh := congrArg Real.exp he
  simp only [quadraticPerturbedLogNode, Real.exp_sub, Real.exp_log hip, Real.exp_log hjp,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  exact quadraticPerturbedNode_ne_double hδ hδ1 hi hj ((div_eq_iff hip.ne').mp hh)

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
