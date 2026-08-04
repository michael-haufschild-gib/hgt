import GaloisForLFunctions.HTGeometry.TwoVariableDecomposition

/-!
# Explicit growth bounds for polynomials

A polynomial is bounded by the sum of its coefficient norms times `(1 + ‖z‖)` to its degree.  This is
the elementary input to every comparison between an algebraic relation and the growth of its
solutions: the coefficients of an order-zero equation are polynomials, so the bound they impose on a
solution is polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The sum of the norms of a polynomial's coefficients. -/
noncomputable def coeffNormSum (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖

theorem coeffNormSum_nonneg (p : Polynomial ℂ) : 0 ≤ coeffNormSum p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **An explicit polynomial growth bound.** -/
theorem norm_eval_le_coeffNormSum (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖ ≤ coeffNormSum p * (1 + ‖z‖) ^ p.natDegree := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
  have hzz : ‖z‖ ≤ 1 + ‖z‖ := by linarith
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [coeffNormSum, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hkle : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ p.natDegree := by
    calc ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) hzz k
      _ ≤ (1 + ‖z‖) ^ p.natDegree := pow_le_pow_right₀ hz1 hkle
  calc ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ ‖p.coeff k‖ * (1 + ‖z‖) ^ p.natDegree :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

/-- **A uniform bound for a finite family of polynomials.** -/
theorem norm_eval_le_of_family {ι : Type*} (s : Finset ι) (a : ι → Polynomial ℂ) (D : ℕ)
    (hD : ∀ i ∈ s, (a i).natDegree ≤ D) (z : ℂ) (i : ι) (hi : i ∈ s) :
    ‖(a i).eval z‖ ≤ coeffNormSum (a i) * (1 + ‖z‖) ^ D := by
  have hz : (1 : ℝ) ≤ 1 + ‖z‖ := by
    have := norm_nonneg z
    linarith
  refine le_trans (norm_eval_le_coeffNormSum (a i) z) ?_
  refine mul_le_mul_of_nonneg_left ?_ (coeffNormSum_nonneg _)
  exact pow_le_pow_right₀ hz (hD i hi)

/-! ## Lower bounds far from the roots

A nonzero polynomial eventually dominates half its leading term.  This is the denominator bound the
algebraic root estimate needs: away from a computable radius the normalised coefficients are
polynomially bounded. -/

/-- **A polynomial dominates half its leading term far out.** -/
theorem norm_eval_ge_of_large {p : Polynomial ℂ} (hp : p ≠ 0) {z : ℂ}
    (hz1 : (1 : ℝ) ≤ ‖z‖)
    (hz2 : 2 * coeffNormSum p.eraseLead * 2 ^ (p.natDegree - 1) ≤ ‖p.leadingCoeff‖ * ‖z‖) :
    ‖p.leadingCoeff‖ / 2 * ‖z‖ ^ p.natDegree ≤ ‖p.eval z‖ := by
  classical
  set d : ℕ := p.natDegree with hd
  set c : ℂ := p.leadingCoeff with hc
  set S : ℝ := coeffNormSum p.eraseLead with hS
  have hS0 : 0 ≤ S := coeffNormSum_nonneg _
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hcpos : 0 < ‖c‖ := by
    rw [hc]
    exact norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  -- the tail is small
  have hsplit : p.eval z = c * z ^ d + p.eraseLead.eval z := by
    conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  have htail : ‖p.eraseLead.eval z‖ ≤ S * (2 * ‖z‖) ^ (d - 1) := by
    refine le_trans (norm_eval_le_coeffNormSum p.eraseLead z) ?_
    have hdeg : p.eraseLead.natDegree ≤ d - 1 := Polynomial.eraseLead_natDegree_le p
    have hbase : 1 + ‖z‖ ≤ 2 * ‖z‖ := by linarith
    have hb0 : (0 : ℝ) ≤ 1 + ‖z‖ := by linarith
    have h1 : (1 + ‖z‖) ^ p.eraseLead.natDegree ≤ (1 + ‖z‖) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) hdeg
    have h2 : (1 + ‖z‖) ^ (d - 1) ≤ (2 * ‖z‖) ^ (d - 1) := pow_le_pow_left₀ hb0 hbase _
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hS0
    exact this
  have hpow : (2 * ‖z‖) ^ (d - 1) = 2 ^ (d - 1) * ‖z‖ ^ (d - 1) := by
    rw [mul_pow]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- constant case
    have hz' : ‖z‖ ^ d = 1 := by rw [hd0, pow_zero]
    have hdeg0 : p.natDegree = 0 := by rw [← hd]; exact hd0
    have hera : p.eraseLead = 0 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
      simp
    rw [hsplit, hera, Polynomial.eval_zero, add_zero, norm_mul, norm_pow, hz']
    linarith
  · -- the leading term dominates
    have hzd : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rw [← pow_succ]
      congr 1
      omega
    have hzd1 : (0 : ℝ) < ‖z‖ ^ (d - 1) := by positivity
    have hkey : S * (2 ^ (d - 1) * ‖z‖ ^ (d - 1)) ≤ ‖c‖ / 2 * ‖z‖ ^ d := by
      rw [hzd]
      have hstep : S * 2 ^ (d - 1) * 2 ≤ ‖c‖ * ‖z‖ := by linarith
      nlinarith [hzd1, hstep]
    have hlead : ‖c * z ^ d‖ = ‖c‖ * ‖z‖ ^ d := by rw [norm_mul, norm_pow]
    have htri : ‖c * z ^ d‖ - ‖p.eraseLead.eval z‖ ≤ ‖p.eval z‖ := by
      have h := norm_sub_le (c * z ^ d + p.eraseLead.eval z) (p.eraseLead.eval z)
      rw [add_sub_cancel_right] at h
      rw [hsplit]
      linarith
    rw [hpow] at htail
    rw [hlead] at htri
    linarith

/-- **A quotient of polynomials is polynomially bounded far out.**  The denominator's lower bound
loses only the factor `‖z‖^{deg r} ≥ 1`, so the quotient is bounded by a constant times
`(1 + ‖z‖)^{deg q}`. -/
theorem norm_div_le_of_large {q r : Polynomial ℂ} (hr : r ≠ 0) {z : ℂ}
    (hz1 : (1 : ℝ) ≤ ‖z‖)
    (hz2 : 2 * coeffNormSum r.eraseLead * 2 ^ (r.natDegree - 1) ≤ ‖r.leadingCoeff‖ * ‖z‖) :
    ‖q.eval z / r.eval z‖
      ≤ (2 * coeffNormSum q / ‖r.leadingCoeff‖) * (1 + ‖z‖) ^ q.natDegree := by
  have hlc : 0 < ‖r.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hr)
  have hzpow : (1 : ℝ) ≤ ‖z‖ ^ r.natDegree := one_le_pow₀ hz1
  have hlow := norm_eval_ge_of_large hr hz1 hz2
  have hden : ‖r.leadingCoeff‖ / 2 ≤ ‖r.eval z‖ := by
    have hstep : ‖r.leadingCoeff‖ / 2 * 1 ≤ ‖r.leadingCoeff‖ / 2 * ‖z‖ ^ r.natDegree :=
      mul_le_mul_of_nonneg_left hzpow (by linarith)
    linarith
  have hden0 : 0 < ‖r.eval z‖ := lt_of_lt_of_le (by linarith) hden
  have hnum := norm_eval_le_coeffNormSum q z
  have hL : ‖r.leadingCoeff‖ ≠ 0 := ne_of_gt hlc
  rw [norm_div, div_le_iff₀ hden0]
  have hK0 : 0 ≤ 2 * coeffNormSum q / ‖r.leadingCoeff‖ * (1 + ‖z‖) ^ q.natDegree := by
    have := coeffNormSum_nonneg q
    positivity
  have hstep : (2 * coeffNormSum q / ‖r.leadingCoeff‖ * (1 + ‖z‖) ^ q.natDegree)
        * (‖r.leadingCoeff‖ / 2)
      ≤ (2 * coeffNormSum q / ‖r.leadingCoeff‖ * (1 + ‖z‖) ^ q.natDegree) * ‖r.eval z‖ :=
    mul_le_mul_of_nonneg_left hden hK0
  have heq : (2 * coeffNormSum q / ‖r.leadingCoeff‖ * (1 + ‖z‖) ^ q.natDegree)
        * (‖r.leadingCoeff‖ / 2)
      = coeffNormSum q * (1 + ‖z‖) ^ q.natDegree
          * (‖r.leadingCoeff‖ / ‖r.leadingCoeff‖) := by
    ring
  rw [div_self hL, mul_one] at heq
  rw [heq] at hstep
  linarith

/-! ## An explicit radius

Packaging the two hypotheses of the lower bound into a single radius makes the estimates composable:
beyond `growthRadius p` the polynomial does not vanish and every quotient by it is polynomially
bounded. -/

/-- A radius beyond which a nonzero polynomial dominates half its leading term. -/
noncomputable def growthRadius (p : Polynomial ℂ) : ℝ :=
  max 1 (2 * coeffNormSum p.eraseLead * 2 ^ (p.natDegree - 1) / ‖p.leadingCoeff‖)

theorem one_le_growthRadius (p : Polynomial ℂ) : (1 : ℝ) ≤ growthRadius p := le_max_left _ _

theorem growthRadius_nonneg (p : Polynomial ℂ) : 0 ≤ growthRadius p := by
  have := one_le_growthRadius p
  linarith

/-- Beyond the radius, both hypotheses of the lower bound hold. -/
theorem hyps_of_growthRadius_le {p : Polynomial ℂ} (hp : p ≠ 0) {z : ℂ}
    (hz : growthRadius p ≤ ‖z‖) :
    (1 : ℝ) ≤ ‖z‖ ∧
      2 * coeffNormSum p.eraseLead * 2 ^ (p.natDegree - 1) ≤ ‖p.leadingCoeff‖ * ‖z‖ := by
  have hlc : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  refine ⟨le_trans (le_max_left _ _) hz, ?_⟩
  have hdiv : 2 * coeffNormSum p.eraseLead * 2 ^ (p.natDegree - 1) / ‖p.leadingCoeff‖ ≤ ‖z‖ :=
    le_trans (le_max_right _ _) hz
  rw [div_le_iff₀ hlc] at hdiv
  linarith [hdiv]

/-- **A nonzero polynomial does not vanish beyond its growth radius.** -/
theorem eval_ne_zero_of_growthRadius_le {p : Polynomial ℂ} (hp : p ≠ 0) {z : ℂ}
    (hz : growthRadius p ≤ ‖z‖) : p.eval z ≠ 0 := by
  obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hp hz
  have hlc : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hlow := norm_eval_ge_of_large hp hz1 hz2
  have hpow : (0 : ℝ) < ‖z‖ ^ p.natDegree := by
    have : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  intro hcon
  rw [hcon, norm_zero] at hlow
  nlinarith [hlow, hlc, hpow]

/-- **The quotient bound, in radius form.** -/
theorem norm_div_le_of_growthRadius_le {q r : Polynomial ℂ} (hr : r ≠ 0) {z : ℂ}
    (hz : growthRadius r ≤ ‖z‖) :
    ‖q.eval z / r.eval z‖
      ≤ (2 * coeffNormSum q / ‖r.leadingCoeff‖) * (1 + ‖z‖) ^ q.natDegree := by
  obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hr hz
  exact norm_div_le_of_large hr hz1 hz2

end GaloisForLFunctions.HTGeometry
