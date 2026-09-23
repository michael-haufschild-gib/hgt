import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Fixed-rank Hankel tests do not imply Stieltjes positivity

Fix `r ≥ 1` and pairwise distinct nodes `x j > 1`.  Put

`m n = (∑ j, x j ^ n) - ε`,

so that the quadratic form of the shifted Hankel block `[m (N + i + j)]` of size `k` at a
coefficient vector `c` is

`∑ j, x j ^ N * p(x j) ^ (2 : ℕ) - ε * p(1) ^ (2 : ℕ)`,  `p = ∑ i, c i X ^ i`.

For `k ≤ r` the Lagrange formula `p(1) = ∑ j (L j).eval 1 * p(x j)` and Cauchy–Schwarz make the
subtracted term strictly smaller than the bulk term once `ε` is below the reciprocal Lagrange
budget, so every such block is positive definite at every shift.  At size `r + 1` the coefficient
vector of `∏ j (X - x j)` kills the bulk term and leaves `-ε * (∏ j (1 - x j)) ^ (2 : ℕ) < 0`.
-/

noncomputable section

namespace RHTower

open scoped BigOperators Matrix
open Polynomial

variable {r : ℕ}

/-- The polynomial attached to a finite coefficient vector. -/
def coeffPoly {k : ℕ} (c : Fin k → ℝ) : Polynomial ℝ :=
  ∑ i : Fin k, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem eval_coeffPoly {k : ℕ} (c : Fin k → ℝ) (t : ℝ) :
    (coeffPoly c).eval t = ∑ i : Fin k, c i * t ^ (i : ℕ) := by
  simp [coeffPoly, Polynomial.eval_finsetSum]

/-- The signed atomic moment sequence: a positive bulk minus one unit atom at `1`. -/
def signedAtomMoment (x : Fin r → ℝ) (ε : ℝ) (n : ℕ) : ℝ := (∑ j, x j ^ n) - ε

/-- The shifted Hankel block of a moment sequence. -/
def shiftedHankel (m : ℕ → ℝ) (N k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => m (N + (i : ℕ) + (j : ℕ))

theorem hankelBilinear_pow {k : ℕ} (c : Fin k → ℝ) (N : ℕ) (t : ℝ) :
    (∑ i : Fin k, ∑ i' : Fin k, c i * t ^ (N + (i : ℕ) + (i' : ℕ)) * c i')
      = t ^ N * (∑ i : Fin k, c i * t ^ (i : ℕ)) ^ (2 : ℕ) := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [pow_add, pow_add]
  ring

theorem hankelBilinear_const {k : ℕ} (c : Fin k → ℝ) (ε : ℝ) :
    (∑ i : Fin k, ∑ i' : Fin k, c i * ε * c i') = ε * (∑ i : Fin k, c i) ^ (2 : ℕ) := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- **Quadratic-form identity.**  The shifted block splits into a positive bulk term and one
negative rank-one term. -/
theorem quadForm_shiftedHankel_signedAtom (x : Fin r → ℝ) (ε : ℝ) (N k : ℕ) (c : Fin k → ℝ) :
    c ⬝ᵥ ((shiftedHankel (signedAtomMoment x ε) N k) *ᵥ c) =
      (∑ j, x j ^ N * ((coeffPoly c).eval (x j)) ^ (2 : ℕ)) - ε * ((coeffPoly c).eval 1) ^ (2 : ℕ) := by
  have hexpand : c ⬝ᵥ ((shiftedHankel (signedAtomMoment x ε) N k) *ᵥ c)
      = ∑ i : Fin k, ∑ i' : Fin k,
        ((∑ j, c i * x j ^ (N + (i : ℕ) + (i' : ℕ)) * c i') - c i * ε * c i') := by
    simp only [dotProduct, Matrix.mulVec, shiftedHankel, signedAtomMoment]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    have hmul : (∑ j, c i * x j ^ (N + (i : ℕ) + (i' : ℕ)) * c i')
        = c i * (∑ j, x j ^ (N + (i : ℕ) + (i' : ℕ))) * c i' := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hmul]
    ring
  rw [hexpand]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    Finset.sum_sub_distrib (f := fun i' : Fin k =>
      ∑ j, c i * x j ^ (N + (i : ℕ) + (i' : ℕ)) * c i')
      (g := fun i' : Fin k => c i * ε * c i'))]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      Finset.sum_comm (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset (Fin r)))
        (f := fun i' j => c i * x j ^ (N + (i : ℕ) + (i' : ℕ)) * c i'))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hankelBilinear_pow c N (x j), eval_coeffPoly]
  · rw [hankelBilinear_const c ε, eval_coeffPoly]
    simp

/-! ### The Lagrange budget and fixed-rank positivity -/

theorem coeffPoly_coeff {k : ℕ} (c : Fin k → ℝ) (i : Fin k) :
    (coeffPoly c).coeff (i : ℕ) = c i := by
  classical
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hEq
    exact hb (Fin.ext hEq.symm)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem coeffPoly_ne_zero {k : ℕ} {c : Fin k → ℝ} (hc : c ≠ 0) : coeffPoly c ≠ 0 := by
  intro h
  apply hc
  funext i
  have := coeffPoly_coeff c i
  rw [h] at this
  simpa using this.symm

theorem degree_coeffPoly_lt {k : ℕ} (c : Fin k → ℝ) : (coeffPoly c).degree < (k : ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
  intro i _
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) (by exact_mod_cast i.2)

/-- The Lagrange evaluation weight at `1`. -/
def lagrangeWeight (x : Fin r → ℝ) (j : Fin r) : ℝ :=
  (Lagrange.basis (Finset.univ : Finset (Fin r)) x j).eval 1

/-- The Lagrange budget of the node family. -/
def lagrangeBudget (x : Fin r → ℝ) : ℝ := ∑ j, (lagrangeWeight x j) ^ (2 : ℕ)

/-- The admissible negative-atom weight. -/
def signedAtomWeight (x : Fin r → ℝ) : ℝ := 1 / (1 + lagrangeBudget x)

theorem lagrangeBudget_nonneg (x : Fin r → ℝ) : 0 ≤ lagrangeBudget x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem signedAtomWeight_pos (x : Fin r → ℝ) : 0 < signedAtomWeight x := by
  have h := lagrangeBudget_nonneg x
  unfold signedAtomWeight
  positivity

/-- **Lagrange evaluation.**  A polynomial of degree below the number of nodes is reconstructed at
`1` from its values at the nodes. -/
theorem eval_one_eq_lagrange (x : Fin r → ℝ) (hx : Function.Injective x)
    {p : Polynomial ℝ} (hp : p.degree < (r : ℕ)) :
    p.eval 1 = ∑ j, lagrangeWeight x j * p.eval (x j) := by
  classical
  have hcard : ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) = (r : ℕ) := by
    simp
  have hvs : Set.InjOn x ↑(Finset.univ : Finset (Fin r)) := fun a _ b _ h => hx h
  have hdeg : p.degree < ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) := by
    rw [hcard]; exact hp
  have hinterp := Lagrange.eq_interpolate (v := x) hvs hdeg
  conv_lhs => rw [hinterp]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, lagrangeWeight]
  ring

/-- A nonzero polynomial of degree below the number of nodes has a nonzero value at some node. -/
theorem sum_sq_eval_pos (x : Fin r → ℝ) (hx : Function.Injective x)
    {p : Polynomial ℝ} (hp : p.degree < (r : ℕ)) (hp0 : p ≠ 0) :
    0 < ∑ j, (p.eval (x j)) ^ (2 : ℕ) := by
  classical
  have hvs : Set.InjOn x ↑(Finset.univ : Finset (Fin r)) := fun a _ b _ h => hx h
  have hcard : ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) = (r : ℕ) := by simp
  have hdeg : p.degree < ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) := by
    rw [hcard]; exact hp
  have hex : ∃ j : Fin r, p.eval (x j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hp0 (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs hdeg
      fun j _ => hcon j)
  obtain ⟨j, hj⟩ := hex
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
  positivity

/-- Cauchy–Schwarz against the Lagrange weights. -/
theorem sq_eval_one_le (x : Fin r → ℝ) (hx : Function.Injective x)
    {p : Polynomial ℝ} (hp : p.degree < (r : ℕ)) :
    (p.eval 1) ^ (2 : ℕ) ≤ lagrangeBudget x * ∑ j, (p.eval (x j)) ^ (2 : ℕ) := by
  rw [eval_one_eq_lagrange x hx hp, lagrangeBudget]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### Fixed-rank positivity and the failure one step higher -/

/-- **Every shifted block of size at most `r` is positive definite.** -/
theorem quadForm_pos_of_le (x : Fin r → ℝ) (hx : Function.Injective x) (hx1 : ∀ j, 1 ≤ x j)
    (N k : ℕ) (hk : k ≤ r) {c : Fin k → ℝ} (hc : c ≠ 0) :
    0 < c ⬝ᵥ ((shiftedHankel (signedAtomMoment x (signedAtomWeight x)) N k) *ᵥ c) := by
  have hp0 : coeffPoly c ≠ 0 := coeffPoly_ne_zero hc
  have hdeg : (coeffPoly c).degree < (r : ℕ) :=
    lt_of_lt_of_le (degree_coeffPoly_lt c) (by exact_mod_cast hk)
  have hpos : 0 < ∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ) := sum_sq_eval_pos x hx hdeg hp0
  have hbulk : (∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ))
      ≤ ∑ j, x j ^ N * ((coeffPoly c).eval (x j)) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hpow : (1 : ℝ) ≤ x j ^ N := one_le_pow₀ (hx1 j)
    nlinarith [sq_nonneg ((coeffPoly c).eval (x j))]
  have hcs := sq_eval_one_le x hx hdeg
  have hB := lagrangeBudget_nonneg x
  rw [quadForm_shiftedHankel_signedAtom]
  have hkey : signedAtomWeight x * ((coeffPoly c).eval 1) ^ (2 : ℕ)
      < ∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ) := by
    have h1 : signedAtomWeight x * ((coeffPoly c).eval 1) ^ (2 : ℕ)
        ≤ signedAtomWeight x * (lagrangeBudget x * ∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcs (le_of_lt (signedAtomWeight_pos x))
    have h2 : signedAtomWeight x * (lagrangeBudget x * ∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ))
        < ∑ j, ((coeffPoly c).eval (x j)) ^ (2 : ℕ) := by
      unfold signedAtomWeight
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [hpos, hB]
    linarith
  linarith

/-- The monic node polynomial. -/
def nodePoly (x : Fin r → ℝ) : Polynomial ℝ := ∏ j, (Polynomial.X - Polynomial.C (x j))

theorem monic_nodePoly (x : Fin r → ℝ) : (nodePoly x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (x j)

theorem nodePoly_ne_zero (x : Fin r → ℝ) : nodePoly x ≠ 0 := (monic_nodePoly x).ne_zero

theorem natDegree_nodePoly (x : Fin r → ℝ) : (nodePoly x).natDegree = r := by
  rw [nodePoly, Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero (x j))]
  simp

theorem eval_nodePoly_node (x : Fin r → ℝ) (j : Fin r) : (nodePoly x).eval (x j) = 0 := by
  rw [nodePoly, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  simp

theorem eval_nodePoly_one_ne_zero (x : Fin r → ℝ) (hx1 : ∀ j, 1 < x j) :
    (nodePoly x).eval 1 ≠ 0 := by
  rw [nodePoly, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  have := hx1 j
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  intro hzero
  linarith [sub_eq_zero.mp hzero]

/-- The coefficient vector of the node polynomial, of length `r + 1`. -/
def nodeCoeffVector (x : Fin r → ℝ) : Fin (r + 1) → ℝ := fun i => (nodePoly x).coeff (i : ℕ)

theorem coeffPoly_nodeCoeffVector (x : Fin r → ℝ) :
    coeffPoly (nodeCoeffVector x) = nodePoly x := by
  have hlt : (nodePoly x).natDegree < r + 1 := by
    rw [natDegree_nodePoly]
    omega
  have hsum : coeffPoly (nodeCoeffVector x)
      = ∑ i ∈ Finset.range (r + 1), Polynomial.C ((nodePoly x).coeff i) * Polynomial.X ^ i := by
    rw [coeffPoly]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => Polynomial.C ((nodePoly x).coeff i) * Polynomial.X ^ i) (r + 1)
  rw [hsum]
  conv_rhs => rw [Polynomial.as_sum_range' (nodePoly x) (r + 1) hlt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]

theorem nodeCoeffVector_ne_zero (x : Fin r → ℝ) : nodeCoeffVector x ≠ 0 := by
  intro h
  apply nodePoly_ne_zero x
  rw [← coeffPoly_nodeCoeffVector x, h]
  simp [coeffPoly]

/-- **Failure one step higher.**  At size `r + 1` the node coefficient vector makes the shifted
block indefinite. -/
theorem quadForm_neg_at_succ (x : Fin r → ℝ) (hx1 : ∀ j, 1 < x j) (N : ℕ) :
    (nodeCoeffVector x) ⬝ᵥ
        ((shiftedHankel (signedAtomMoment x (signedAtomWeight x)) N (r + 1)) *ᵥ
          (nodeCoeffVector x)) < 0 := by
  rw [quadForm_shiftedHankel_signedAtom, coeffPoly_nodeCoeffVector]
  have hbulk : (∑ j, x j ^ N * ((nodePoly x).eval (x j)) ^ (2 : ℕ)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [eval_nodePoly_node]
    ring
  rw [hbulk]
  have hne := eval_nodePoly_one_ne_zero x hx1
  have hsq : 0 < ((nodePoly x).eval 1) ^ (2 : ℕ) := by positivity
  have hw := signedAtomWeight_pos x
  nlinarith

/-- **Fixed-rank Hankel tests are not the Stieltjes cone.**  For every `r` there is a moment
sequence whose shifted Hankel blocks are positive definite at every shift up to size `r`, and
indefinite at size `r + 1`. -/
theorem fixedRank_hankel_not_stieltjes (x : Fin r → ℝ) (hx : Function.Injective x)
    (hx1 : ∀ j, 1 < x j) :
    (∀ N k : ℕ, k ≤ r → ∀ c : Fin k → ℝ, c ≠ 0 →
        0 < c ⬝ᵥ ((shiftedHankel (signedAtomMoment x (signedAtomWeight x)) N k) *ᵥ c)) ∧
      (∀ N : ℕ, ∃ c : Fin (r + 1) → ℝ, c ≠ 0 ∧
        c ⬝ᵥ ((shiftedHankel (signedAtomMoment x (signedAtomWeight x)) N (r + 1)) *ᵥ c) < 0) :=
  ⟨fun N k hk c hc => quadForm_pos_of_le x hx (fun j => le_of_lt (hx1 j)) N k hk (c := c) hc,
    fun N => ⟨nodeCoeffVector x, nodeCoeffVector_ne_zero x, quadForm_neg_at_succ x hx1 N⟩⟩

end RHTower
