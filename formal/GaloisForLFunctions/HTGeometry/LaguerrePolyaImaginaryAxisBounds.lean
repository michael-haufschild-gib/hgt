import GaloisForLFunctions.HTGeometry.LaguerrePolyaLocallyUniformLimit

/-!
# Real-rooted polynomials on the imaginary axis

For a real polynomial `q` that splits over `ℝ`:

* `‖q(iy)‖ ≥ |q(0)|` (`norm_polyEvalC_I_mul_ge`), since every factor satisfies `|iy − r| ≥ |r|`;
  hence `‖F(iy)‖ ≥ |F(0)|` for every Laguerre–Pólya `F` (`LaguerrePolya.norm_I_mul_ge`);
* if `q(0) ≠ 0`, the Gaussian bound
  `‖q(iy)‖² ≤ q(0)² exp(y² Λ(q)/q(0)²)`, `Λ(q) = q′(0)² − q(0)q″(0)`
  (`norm_sq_polyEvalC_I_mul_le`). The proof peels one root at a time:
  `Λ((X − a)Q) = Q(0)² + a²Λ(Q)` (`lagAtZero_X_sub_C_mul`) and `y² + a² ≤ a² e^{y²/a²}`.
  For real-rooted `q = q(0)∏(1 − z/a_j)` this is `∏(1 + y²/a_j²) ≤ exp(y²Σ1/a_j²)`, since
  `Λ(q)/q(0)² = Σ1/a_j²`.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `Λ(q) = q′(0)² − q(0)q″(0)`, the first Laguerre expression at the origin. -/
def lagAtZero (q : ℝ[X]) : ℝ :=
  ((derivative q).eval 0) ^ 2 - q.eval 0 * (derivative (derivative q)).eval 0

theorem lagAtZero_X_sub_C_mul (a : ℝ) (q : ℝ[X]) :
    lagAtZero ((X - C a) * q) = q.eval 0 ^ 2 + a ^ 2 * lagAtZero q := by
  unfold lagAtZero
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    derivative_add, derivative_one, zero_mul, zero_add, eval_add, eval_mul, eval_sub, eval_X,
    eval_C]
  ring

theorem lagAtZero_C_mul (c : ℝ) (q : ℝ[X]) : lagAtZero (C c * q) = c ^ 2 * lagAtZero q := by
  unfold lagAtZero
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  ring

theorem polyEvalC_mul (p q : ℝ[X]) (z : ℂ) :
    polyEvalC (p * q) z = polyEvalC p z * polyEvalC q z := by
  simp [polyEvalC]

theorem polyEvalC_X_sub_C (a : ℝ) (z : ℂ) : polyEvalC (X - C a) z = z - a := by
  simp [polyEvalC]

theorem polyEvalC_C (c : ℝ) (z : ℂ) : polyEvalC (C c) z = c := by
  simp [polyEvalC]

theorem polyEvalC_zero_eq (q : ℝ[X]) : polyEvalC q 0 = ((q.eval 0 : ℝ) : ℂ) := by
  rw [polyEvalC_zero, Polynomial.coeff_zero_eq_eval_zero]

theorem norm_I_mul_sub_sq (y a : ℝ) : ‖Complex.I * y - a‖ ^ 2 = y ^ 2 + a ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- Monic real-rooted products on the imaginary axis. -/
theorem norm_prod_I_mul_sub_ge (s : Multiset ℝ) (y : ℝ) :
    |((s.map fun a => X - C a).prod).eval 0| ≤
      ‖polyEvalC ((s.map fun a => X - C a).prod) (Complex.I * y)‖ := by
  induction s using Multiset.induction with
  | empty => simp [polyEvalC]
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, polyEvalC_mul, abs_mul, norm_mul,
      polyEvalC_X_sub_C]
    refine mul_le_mul ?_ ih (abs_nonneg _) (norm_nonneg _)
    have h := norm_I_mul_sub_sq y a
    simp only [eval_sub, eval_X, eval_C, zero_sub, abs_neg]
    have h2 : a ^ 2 ≤ ‖Complex.I * y - a‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg y]
    rw [← Real.sqrt_sq (abs_nonneg a), ← Real.sqrt_sq (norm_nonneg (Complex.I * y - a)), sq_abs]
    exact Real.sqrt_le_sqrt h2

theorem norm_polyEvalC_I_mul_ge {q : ℝ[X]} (hq : q.Splits) (y : ℝ) :
    |q.eval 0| ≤ ‖polyEvalC q (Complex.I * y)‖ := by
  rw [hq.eq_prod_roots, eval_mul, eval_C, polyEvalC_mul, polyEvalC_C, abs_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_prod_I_mul_sub_ge _ y) (abs_nonneg _)

/-- **Laguerre–Pólya functions grow along the imaginary axis.** -/
theorem LaguerrePolya.norm_I_mul_ge {F : ℂ → ℂ} (hF : LaguerrePolya F) (y : ℝ) :
    ‖F 0‖ ≤ ‖F (Complex.I * y)‖ := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  have h0 := (TendstoLocallyUniformlyOn.tendsto_at (tendstoLocallyUniformlyOn_univ.2 hconv)
    (Set.mem_univ (0 : ℂ)))
  have hy := (TendstoLocallyUniformlyOn.tendsto_at (tendstoLocallyUniformlyOn_univ.2 hconv)
    (Set.mem_univ (Complex.I * y)))
  refine le_of_tendsto_of_tendsto' ((continuous_norm.tendsto _).comp h0)
    ((continuous_norm.tendsto _).comp hy) fun m => ?_
  simp only [Function.comp_apply]
  rw [polyEvalC_zero_eq, Complex.norm_real, Real.norm_eq_abs]
  exact norm_polyEvalC_I_mul_ge (hsplit m) y

/-- The Gaussian bound for monic real-rooted products with nonzero roots. -/
theorem norm_sq_prod_I_mul_le (s : Multiset ℝ) (hs : ∀ a ∈ s, a ≠ 0) (y : ℝ) :
    ‖polyEvalC ((s.map fun a => X - C a).prod) (Complex.I * y)‖ ^ 2 ≤
      (((s.map fun a => X - C a).prod).eval 0) ^ 2 *
        Real.exp (y ^ 2 * lagAtZero ((s.map fun a => X - C a).prod) /
          (((s.map fun a => X - C a).prod).eval 0) ^ 2) := by
  induction s using Multiset.induction with
  | empty => simp [polyEvalC, lagAtZero]
  | cons a t ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a t)
    have ih' := ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    set Q := (t.map fun a => X - C a).prod with hQ
    have hQ0 : Q.eval 0 ≠ 0 := by
      rw [hQ, eval_multiset_prod, Multiset.map_map]
      refine Multiset.prod_ne_zero ?_
      intro h0
      obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub, neg_eq_zero] at hb0
      exact hs b (Multiset.mem_cons_of_mem hb) hb0
    rw [Multiset.map_cons, Multiset.prod_cons, ← hQ, polyEvalC_mul, norm_mul, mul_pow,
      polyEvalC_X_sub_C, norm_I_mul_sub_sq, lagAtZero_X_sub_C_mul, eval_mul]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    have hpos : 0 < Q.eval 0 ^ 2 := by positivity
    have ha2 : 0 < a ^ 2 := by positivity
    have e : y ^ 2 * (Q.eval 0 ^ 2 + a ^ 2 * lagAtZero Q) / (-a * Q.eval 0) ^ 2 =
        y ^ 2 / a ^ 2 + y ^ 2 * lagAtZero Q / Q.eval 0 ^ 2 := by
      field_simp
    rw [e, Real.exp_add]
    have h1 : y ^ 2 + a ^ 2 ≤ a ^ 2 * Real.exp (y ^ 2 / a ^ 2) := by
      have := Real.add_one_le_exp (y ^ 2 / a ^ 2)
      have e2 : a ^ 2 * (y ^ 2 / a ^ 2 + 1) = y ^ 2 + a ^ 2 := by field_simp
      nlinarith
    calc (y ^ 2 + a ^ 2) * ‖polyEvalC Q (Complex.I * y)‖ ^ 2
        ≤ (a ^ 2 * Real.exp (y ^ 2 / a ^ 2)) *
            (Q.eval 0 ^ 2 * Real.exp (y ^ 2 * lagAtZero Q / Q.eval 0 ^ 2)) :=
          mul_le_mul h1 ih' (sq_nonneg _) (by positivity)
      _ = (-a * Q.eval 0) ^ 2 *
            (Real.exp (y ^ 2 / a ^ 2) * Real.exp (y ^ 2 * lagAtZero Q / Q.eval 0 ^ 2)) := by ring

/-- **Gaussian bound on the imaginary axis.** For real-rooted `q` with `q(0) ≠ 0`,
`‖q(iy)‖² ≤ q(0)² exp(y² Λ(q)/q(0)²)`. -/
theorem norm_sq_polyEvalC_I_mul_le {q : ℝ[X]} (hq : q.Splits) (h0 : q.eval 0 ≠ 0) (y : ℝ) :
    ‖polyEvalC q (Complex.I * y)‖ ^ 2 ≤
      q.eval 0 ^ 2 * Real.exp (y ^ 2 * lagAtZero q / q.eval 0 ^ 2) := by
  have hfac := hq.eq_prod_roots
  set P := (q.roots.map fun a => X - C a).prod with hP
  have hroots : ∀ a ∈ q.roots, a ≠ 0 := by
    intro a ha h
    rw [h] at ha
    exact h0 ((mem_roots (by rintro rfl; simp at h0)).mp ha)
  have hb := norm_sq_prod_I_mul_le q.roots hroots y
  rw [← hP] at hb
  have hlc : q.eval 0 = q.leadingCoeff * P.eval 0 := by
    conv_lhs => rw [hfac]
    rw [eval_mul, eval_C]
  have hP0 : P.eval 0 ≠ 0 := by
    intro h; rw [hlc, h, mul_zero] at h0; exact h0 rfl
  have hlc0 : q.leadingCoeff ≠ 0 := by
    intro h; rw [hlc, h, zero_mul] at h0; exact h0 rfl
  have hL : lagAtZero q = q.leadingCoeff ^ 2 * lagAtZero P := by
    conv_lhs => rw [hfac]
    exact lagAtZero_C_mul _ _
  have hE : y ^ 2 * lagAtZero q / q.eval 0 ^ 2 = y ^ 2 * lagAtZero P / P.eval 0 ^ 2 := by
    rw [hL, hlc]; field_simp
  rw [hE]
  conv_lhs => rw [hfac]
  rw [polyEvalC_mul, polyEvalC_C, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    hlc, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

end

end GaloisForLFunctions.HTGeometry
