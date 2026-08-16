import GaloisForLFunctions.RHTower.DirichletCoeffBound

/-!
# Absolute convergence, uniform convergence, and the width-one bound

Two classical comparisons between the abscissas of an ordinary Dirichlet series.

* A summable majorant gives uniform convergence: `σ_u ≤ σ_a`.
* Convergence at a point bounds the coefficients: `‖a_n‖ ≤ C (n+1)^{Re s₀}`, which is the
  ingredient of Bohr's width-one inequality `σ_a ≤ σ_c + 1`.

The first is the Weierstrass test; the second is nothing more than the vanishing of the terms of a
convergent series, read against the kernel.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- Each term is bounded by its majorant on the closed half-plane. -/
theorem norm_dirichletTerm_le (a : ℕ → ℂ) {x : ℝ} (n : ℕ) {s : ℂ} (hs : x ≤ s.re) :
    ‖a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖a n‖ * ((n : ℝ) + 1) ^ (-x) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hexp : ((-s).re) ≤ -x := by
    rw [Complex.neg_re]
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hone hexp) (norm_nonneg _)

/-- **A summable majorant gives uniform convergence.** -/
theorem uniformlyConvergesOn_of_summable {a : ℕ → ℂ} {x : ℝ}
    (h : Summable (fun n : ℕ => ‖a n‖ * ((n : ℝ) + 1) ^ (-x))) :
    DirichletUniformlyConvergesOn a x := by
  refine ⟨fun s => ∑' n : ℕ, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s), ?_⟩
  exact tendstoUniformlyOn_tsum_nat h fun n s hs => norm_dirichletTerm_le a n hs

/-- **`σ_u ≤ σ_a`.**  The abscissa of uniform convergence is at most the abscissa of absolute
convergence. -/
theorem abscissaOfUnifConv_le_of_summable {a : ℕ → ℂ} {x : ℝ}
    (h : Summable (fun n : ℕ => ‖a n‖ * ((n : ℝ) + 1) ^ (-x))) :
    abscissaOfUnifConv a ≤ (x : EReal) :=
  sInf_le ⟨x, uniformlyConvergesOn_of_summable h, rfl⟩

/-- **Convergence at a point bounds the coefficients.**  The terms of a convergent series tend to
zero, so they are bounded, and dividing by the kernel gives the coefficient bound. -/
theorem exists_norm_coeff_le_of_convergesAt {a : ℕ → ℂ} {s₀ : ℂ}
    (h : DirichletConvergesAt a s₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ s₀.re := by
  obtain ⟨L, hL⟩ := h
  have hterm : Tendsto (fun n : ℕ => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₀)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun N : ℕ => dirichletPartialSum a (N + 1) s₀) atTop (𝓝 L) :=
      hL.comp (Filter.tendsto_add_atTop_nat 1)
    have hdiff := hshift.sub hL
    rw [sub_self] at hdiff
    refine hdiff.congr fun N => ?_
    rw [dirichletPartialSum, dirichletPartialSum, Finset.sum_range_succ]
    ring
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
    (hterm.cauchySeq.isBounded_range)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (Set.mem_range_self 0))
  refine ⟨C, hC0, fun n => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb := hC _ (Set.mem_range_self n)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos] at hb
  have hker : ((n : ℝ) + 1) ^ ((-s₀).re) = (((n : ℝ) + 1) ^ (s₀.re))⁻¹ := by
    rw [Complex.neg_re, Real.rpow_neg hpos.le]
  rw [hker] at hb
  have hkpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (s₀.re) := Real.rpow_pos_of_pos hpos _
  rw [mul_inv_le_iff₀ hkpos] at hb
  linarith [hb]

end GaloisForLFunctions.RHTower

end
