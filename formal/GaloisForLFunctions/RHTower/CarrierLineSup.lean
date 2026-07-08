/-
Closed-form line sup for the completed carrier.

The square-root telescope `n^{−1/2} ≤ 2(√n − √(n−1))` bounds the coefficient sum of the
Dirichlet part by `2√N`; χ is unimodular on the line and the reflected part is a conjugate,
so `‖g_N‖ ≤ 4√N` there.  Combining with the Euler-integral envelope sup gives the explicit
line sup for the completed carrier, `|Re Φ̃_N(linePt u)| ≤ (¼+u²)/2·π^{−1/4}Γ(¼)·4√N` — the
`M_line` face of the sign-bracket certificate is a closed-form function of height and length.
-/
import GaloisForLFunctions.RHTower.ResonanceClosedForm

open Complex Metric

namespace RHTower

/-- Square-root telescope: `Σ_{n≤N} n^{−1/2} ≤ 2√N`. -/
theorem sum_rpow_neg_half_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℝ)) ^ (-(1 / 2 : ℝ))) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hkey : ((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ)) := by
      have hpos : (0 : ℝ) < Real.sqrt ((N : ℝ) + 1) :=
        Real.sqrt_pos.mpr (by positivity)
      have hrw : ((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
          1 / Real.sqrt ((N : ℝ) + 1) := by
        push_cast
        rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow, inv_eq_one_div]
      have hs : Real.sqrt (N : ℝ) * Real.sqrt ((N : ℝ) + 1) ≤ (N : ℝ) + 1 / 2 := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
        calc Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))
            ≤ Real.sqrt (((N : ℝ) + 1 / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = (N : ℝ) + 1 / 2 := Real.sqrt_sq (by positivity)
      have hself : Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) = (N : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      rw [hrw, div_le_iff₀ hpos]
      nlinarith
    have hcast : Real.sqrt ((N + 1 : ℕ) : ℝ) = Real.sqrt ((N : ℝ) + 1) := by
      push_cast
      ring_nf
    rw [hcast]
    linarith

/-- Termwise line bound for the Dirichlet part: `‖h_N(linePt u)‖ ≤ 2√N`. -/
private theorem norm_dirichletPoly_line_le (N : ℕ) (u : ℝ) :
    ‖dirichletPoly N (linePt u)‖ ≤ 2 * Real.sqrt N := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(n : ℂ) ^ (-(linePt u))‖ = ((n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    rw [Complex.neg_re, linePt_re]
  unfold dirichletPoly
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(linePt u))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-(linePt u))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ ≤ 2 * Real.sqrt N := sum_rpow_neg_half_le N

/-- Line sup for the symmetrized carrier: `‖g_N(linePt u)‖ ≤ 4√N` — the reflected part is a
conjugate and χ is unimodular on the line. -/
private theorem norm_gN_line_le (N : ℕ) (u : ℝ) :
    ‖gN N (linePt u)‖ ≤ 4 * Real.sqrt N := by
  have hrefl : ‖dirichletPoly N (1 - linePt u)‖ = ‖dirichletPoly N (linePt u)‖ := by
    rw [← conj_linePt, dirichletPoly_conj, Complex.norm_conj]
  have hd := norm_dirichletPoly_line_le N u
  calc ‖gN N (linePt u)‖
      = ‖dirichletPoly N (linePt u) +
          zetaChi (linePt u) * dirichletPoly N (1 - linePt u)‖ := rfl
    _ ≤ ‖dirichletPoly N (linePt u)‖ +
          ‖zetaChi (linePt u) * dirichletPoly N (1 - linePt u)‖ := norm_add_le _ _
    _ = ‖dirichletPoly N (linePt u)‖ + ‖dirichletPoly N (linePt u)‖ := by
        rw [norm_mul, norm_zetaChi_line, one_mul, hrefl]
    _ ≤ 4 * Real.sqrt N := by linarith

/-- **Closed-form line sup for the completed carrier**: the `M_line` face of the
sign-bracket certificates is `(¼+u²)/2 · π^{−1/4}Γ(¼) · 4√N`. -/
private theorem abs_re_completedGN_line_le (N : ℕ) (u : ℝ) :
    |(completedGN N (linePt u)).re| ≤
      (1 / 4 + u ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
        (4 * Real.sqrt N) := by
  have hM₀ : (0 : ℝ) ≤
      (1 / 4 + u ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) :=
    mul_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
        (Real.Gamma_pos_of_pos (by norm_num)).le)
  refine le_trans (Complex.abs_re_le_norm _) ?_
  calc ‖completedGN N (linePt u)‖
      = ‖archFactor (linePt u)‖ * ‖gN N (linePt u)‖ := norm_mul _ _
    _ ≤ (1 / 4 + u ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
          (4 * Real.sqrt N) :=
        mul_le_mul (norm_archFactor_line_le u) (norm_gN_line_le N u)
          (norm_nonneg _) hM₀

/-- Closed-form scalar budget for `|(completedGN N (linePt u)).re|` up to height `B`. -/
noncomputable def completedGNLineSupBudget (N : ℕ) (B : ℝ) : ℝ :=
  (1 / 4 + B ^ 2) / 2 * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
    (4 * Real.sqrt N)

/-- The closed-form completed-carrier line-sup budget is nonnegative. -/
theorem completedGNLineSupBudget_nonneg (N : ℕ) (B : ℝ) :
    0 ≤ completedGNLineSupBudget N B := by
  dsimp [completedGNLineSupBudget]
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
        (Real.Gamma_pos_of_pos (by norm_num)).le))
    (by positivity)

/-- On nonnegative heights, the closed-form completed-carrier line-sup budget is monotone. -/
theorem completedGNLineSupBudget_mono_nonneg (N : ℕ) {B₁ B₂ : ℝ}
    (hB₁0 : 0 ≤ B₁) (hB₁B₂ : B₁ ≤ B₂) :
    completedGNLineSupBudget N B₁ ≤ completedGNLineSupBudget N B₂ := by
  have hB₂0 : 0 ≤ B₂ := le_trans hB₁0 hB₁B₂
  have hsqu : B₁ ^ 2 ≤ B₂ ^ 2 := by
    have hmul := mul_le_mul hB₁B₂ hB₁B₂ hB₁0 hB₂0
    simpa [pow_two] using hmul
  have hfactor : (1 / 4 + B₁ ^ 2) / 2 ≤ (1 / 4 + B₂ ^ 2) / 2 := by
    nlinarith
  have hC0 : 0 ≤ Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) :=
    mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have hN0 : 0 ≤ 4 * Real.sqrt N := by positivity
  dsimp [completedGNLineSupBudget]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor hC0) hN0

/-- The pointwise line-sup theorem in named-budget form. -/
private theorem abs_re_completedGN_line_le_budget (N : ℕ) (u : ℝ) :
    |(completedGN N (linePt u)).re| ≤ completedGNLineSupBudget N u := by
  simpa [completedGNLineSupBudget] using abs_re_completedGN_line_le N u

/-- On a nonnegative segment `[α, β]`, the right endpoint controls the completed-carrier
line-sup budget. -/
theorem abs_re_completedGN_line_le_segment_budget
    (N : ℕ) {α β u : ℝ} (hα0 : 0 ≤ α) (hu : u ∈ Set.Icc α β) :
    |(completedGN N (linePt u)).re| ≤ completedGNLineSupBudget N β := by
  have hu0 : 0 ≤ u := le_trans hα0 hu.1
  exact le_trans (abs_re_completedGN_line_le_budget N u)
    (completedGNLineSupBudget_mono_nonneg N hu0 hu.2)

end RHTower
