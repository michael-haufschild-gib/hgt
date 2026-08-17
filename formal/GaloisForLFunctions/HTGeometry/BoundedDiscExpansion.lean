import GaloisForLFunctions.HTGeometry.DiscExpansionExponential

/-!
# Bounded truncated expansions on a disc

Combining expansions of several factors needs, alongside each expansion, a bound for the factor on
the disc; the bound for the truncating polynomial is then automatic.  Carrying the bound alongside
the approximant turns the product, sum and truncation rules into closure properties of a single
predicate, so an expansion for a long product is assembled without tracking any constant by hand,
while the approximant itself stays explicit.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Extras

/-- A monomial is its own expansion, with no error. -/
theorem hasPolyExpansion_monomial (r : ℝ) (n k : ℕ) :
    HasPolyExpansion r n 0 (fun w => w ^ k) (Polynomial.X ^ k) := by
  intro w _
  simp

/-- The truncating polynomial inherits the bound of the function it expands. -/
theorem HasPolyExpansion.norm_poly_le {r C Bf : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ Bf) (hC : 0 ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ r) : ‖P.eval w‖ ≤ Bf + C * r ^ n := by
  have hrn : ‖w‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg w) hw n
  have h1 := hf w hw
  have h2 := hfb w hw
  have h3 := norm_sub_norm_le (P.eval w) (f w)
  rw [norm_sub_rev] at h3
  nlinarith [h1, h2, h3, hC, hrn]

/-- Finite sums of expansions. -/
theorem HasPolyExpansion.finsetSum {ι : Type*} {r : ℝ} {n : ℕ} (s : Finset ι)
    {f : ι → ℂ → ℂ} {P : ι → Polynomial ℂ} {C : ι → ℝ}
    (h : ∀ i ∈ s, HasPolyExpansion r n (C i) (f i) (P i)) :
    HasPolyExpansion r n (∑ i ∈ s, C i) (fun w => ∑ i ∈ s, f i w) (∑ i ∈ s, P i) := by
  intro w hw
  have heval : (∑ i ∈ s, P i).eval w = ∑ i ∈ s, (P i).eval w := by
    rw [Polynomial.eval_finsetSum]
  rw [heval, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => h i hi w hw

/-- An expansion of order `n` is an expansion of every lower order, at the cost of a power of the
radius in the constant. -/
theorem HasPolyExpansion.mono {r C : ℝ} {n n' : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hC : 0 ≤ C) (hn : n' ≤ n) :
    HasPolyExpansion r n' (C * r ^ (n - n')) f P := by
  intro w hw
  refine le_trans (hf w hw) ?_
  have hsplit : ‖w‖ ^ n = ‖w‖ ^ n' * ‖w‖ ^ (n - n') := by
    rw [← pow_add]
    congr 1
    omega
  have hle : ‖w‖ ^ (n - n') ≤ r ^ (n - n') := pow_le_pow_left₀ (norm_nonneg w) hw _
  have h1 : (0 : ℝ) ≤ ‖w‖ ^ n' := pow_nonneg (norm_nonneg w) n'
  rw [hsplit]
  nlinarith [mul_nonneg (mul_nonneg hC h1) (sub_nonneg.mpr hle)]

/-- Truncating below degree `n` leaves only coefficients below `n`. -/
theorem coeff_truncBelow_of_le (n : ℕ) (P : Polynomial ℂ) {j : ℕ} (hj : n ≤ j) :
    (truncBelow n P).coeff j = 0 := by
  classical
  rw [truncBelow, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hne : ¬ (j = k) := by
    have := Finset.mem_range.mp hk
    omega
  simp [hne]

/-- The truncated polynomial is the corresponding partial sum. -/
theorem eval_truncBelow (n : ℕ) (P : Polynomial ℂ) (w : ℂ) :
    (truncBelow n P).eval w = ∑ j ∈ Finset.range n, P.coeff j * w ^ j := by
  rw [truncBelow, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Below the truncation degree the coefficients are unchanged. -/
theorem coeff_truncBelow_of_lt (n : ℕ) (P : Polynomial ℂ) {j : ℕ} (hj : j < n) :
    (truncBelow n P).coeff j = P.coeff j := by
  classical
  rw [truncBelow, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro k _ hkj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hkj), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr hj) hnot

end Extras

section Bounded

/-- `f` has the truncated expansion `P` of order `n` on the disc of radius `r`, and is bounded
there.  The constant and the bound are existential; the approximant is not. -/
def BddPolyExpansionAt (r : ℝ) (n : ℕ) (f : ℂ → ℂ) (P : Polynomial ℂ) : Prop :=
  ∃ C B : ℝ, 0 ≤ C ∧ (∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ B) ∧ HasPolyExpansion r n C f P

theorem BddPolyExpansionAt.add {r : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ}
    (hf : BddPolyExpansionAt r n f P) (hg : BddPolyExpansionAt r n g Q) :
    BddPolyExpansionAt r n (fun w => f w + g w) (P + Q) := by
  obtain ⟨C, B, hC, hB, hP⟩ := hf
  obtain ⟨D, E, hD, hE, hQ⟩ := hg
  refine ⟨C + D, B + E, by linarith, fun w hw => ?_, hP.add hQ⟩
  exact le_trans (norm_add_le _ _) (add_le_add (hB w hw) (hE w hw))

theorem BddPolyExpansionAt.const_mul {r : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (c : ℂ)
    (hf : BddPolyExpansionAt r n f P) :
    BddPolyExpansionAt r n (fun w => c * f w) (Polynomial.C c * P) := by
  obtain ⟨C, B, hC, hB, hP⟩ := hf
  refine ⟨‖c‖ * C, ‖c‖ * B, mul_nonneg (norm_nonneg c) hC, fun w hw => ?_, hP.const_mul c⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB w hw) (norm_nonneg c)

theorem BddPolyExpansionAt.mul {r : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hf : BddPolyExpansionAt r n f P) (hg : BddPolyExpansionAt r n g Q) :
    BddPolyExpansionAt r n (fun w => f w * g w) (P * Q) := by
  obtain ⟨C, B, hC, hB, hP⟩ := hf
  obtain ⟨D, E, hD, hE, hQ⟩ := hg
  have hzero : ‖(0 : ℂ)‖ ≤ r := by simpa using hr0
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hE 0 hzero)
  have hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ B + C * r ^ n := fun w hw =>
    hP.norm_poly_le hB hC hw
  have hBp0 : 0 ≤ B + C * r ^ n := le_trans (norm_nonneg _) (hPb 0 hzero)
  refine ⟨C * E + (B + C * r ^ n) * D, B * E,
    add_nonneg (mul_nonneg hC hE0) (mul_nonneg hBp0 hD), fun w hw => ?_,
    hP.mul hQ hE hPb hC⟩
  rw [norm_mul]
  exact mul_le_mul (hB w hw) (hE w hw) (norm_nonneg _) (le_trans (norm_nonneg _) (hB w hw))

theorem BddPolyExpansionAt.finsetSum {ι : Type*} {r : ℝ} {n : ℕ} (s : Finset ι) {f : ι → ℂ → ℂ}
    {P : ι → Polynomial ℂ} (h : ∀ i ∈ s, BddPolyExpansionAt r n (f i) (P i)) :
    BddPolyExpansionAt r n (fun w => ∑ i ∈ s, f i w) (∑ i ∈ s, P i) := by
  classical
  revert h
  induction s using Finset.cons_induction with
  | empty =>
      intro _
      exact ⟨0, 0, le_rfl, fun w _ => by simp, fun w _ => by simp⟩
  | cons a s ha ih =>
      intro h
      have hfun : (fun w : ℂ => ∑ i ∈ Finset.cons a s ha, f i w)
          = fun w : ℂ => f a w + ∑ i ∈ s, f i w := by
        funext w
        rw [Finset.sum_cons]
      rw [hfun, Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem BddPolyExpansionAt.mono {r : ℝ} {n n' : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hn : n' ≤ n) (hf : BddPolyExpansionAt r n f P) : BddPolyExpansionAt r n' f P := by
  obtain ⟨C, B, hC, hB, hP⟩ := hf
  exact ⟨C * r ^ (n - n'), B, mul_nonneg hC (pow_nonneg hr0 _), hB, hP.mono hC hn⟩

/-- **The assembled expansion, truncated to degree below the order.** -/
theorem BddPolyExpansionAt.trunc {r : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (hr1 : r ≤ 1)
    (hf : BddPolyExpansionAt r n f P) :
    ∃ C : ℝ, 0 ≤ C ∧ HasPolyExpansion r n C f (truncBelow n P) := by
  obtain ⟨C, B, hC, hB, hP⟩ := hf
  exact ⟨C + polyAbsSum P, by linarith [polyAbsSum_nonneg P], hP.trunc hr1⟩

/-- The exponential of a small expandable function is a bounded expansion. -/
theorem bddPolyExpansionAt_cexp {r C M K : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ M) (hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ M)
    (hM1 : 1 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsmall : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ K * ‖w‖)
    (htiny : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ / ((n : ℝ) + 1) ≤ 1 / 2) :
    BddPolyExpansionAt r n (fun w => Complex.exp (f w))
      (∑ j ∈ Finset.range n, Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹) * P ^ j) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hfacn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  refine ⟨2 * K ^ n / (Nat.factorial n : ℝ)
      + ∑ j ∈ Finset.range n, C * (j : ℝ) * M ^ j / (Nat.factorial j : ℝ),
    Real.exp M, ?_, ?_, hf.cexp hfb hPb hM1 hC hsmall htiny⟩
  · have h1 : (0 : ℝ) ≤ 2 * K ^ n / (Nat.factorial n : ℝ) :=
      div_nonneg (by nlinarith [pow_nonneg hK n]) (le_of_lt hfacn)
    have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, C * (j : ℝ) * M ^ j / (Nat.factorial j : ℝ) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have hfacj : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have hMj : (0 : ℝ) ≤ M ^ j := pow_nonneg hM0 j
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      exact div_nonneg (mul_nonneg (mul_nonneg hC hj) hMj) (le_of_lt hfacj)
    linarith
  · intro w hw
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) (hfb w hw))

end Bounded

end

end GaloisForLFunctions.HTGeometry
