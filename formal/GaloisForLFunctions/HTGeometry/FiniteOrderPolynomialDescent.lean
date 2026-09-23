import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# Finite order descends through a polynomial outer factor

If `P ∘ g` has a finite-order growth envelope and `P` is a nonconstant polynomial, then so does
`g`.  The mechanism is the elementary lower bound `‖w‖ ≤ R + c ‖P w‖`, valid globally once the
constants are chosen from the coefficients of `P`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Polynomial

/-- **A nonconstant polynomial dominates its argument.**  There are constants `R ≥ 0` and `c > 0`
with `‖w‖ ≤ R + c ‖P w‖` for every `w`. -/
theorem exists_norm_le_of_natDegree_pos {P : Polynomial ℂ} (hP : 1 ≤ P.natDegree) :
    ∃ R c : ℝ, 0 ≤ R ∧ 0 < c ∧ ∀ w : ℂ, ‖w‖ ≤ R + c * ‖P.eval w‖ := by
  classical
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hP
    omega
  set n : ℕ := P.natDegree with hn
  set Lc : ℝ := ‖P.coeff n‖ with hLc
  have hLpos : 0 < Lc := by
    rw [hLc, norm_pos_iff, hn, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  set M : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set R : ℝ := max 1 (2 * M / Lc) with hR
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  refine ⟨R, 2 / Lc, by linarith, by positivity, fun w => ?_⟩
  by_cases hw : ‖w‖ ≤ R
  · have : 0 ≤ 2 / Lc * ‖P.eval w‖ := by positivity
    linarith
  push Not at hw
  -- far from the origin the leading term dominates
  have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans hR1 hw.le
  have hw0 : (0 : ℝ) < ‖w‖ := by linarith
  have hlow : ‖P.eval w - P.coeff n * w ^ n‖ ≤ M * ‖w‖ ^ (n - 1) := by
    have hsplit : P.eval w - P.coeff n * w ^ n
        = ∑ i ∈ Finset.range n, P.coeff i * w ^ i := by
      rw [Polynomial.eval_eq_sum_range, ← hn, Finset.sum_range_succ]
      ring
    rw [hsplit, hM, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine pow_le_pow_right₀ hw1 ?_
    have := Finset.mem_range.mp hi
    omega
  have hlead : Lc * ‖w‖ ^ n ≤ ‖P.eval w‖ + M * ‖w‖ ^ (n - 1) := by
    have hnorm : ‖P.coeff n * w ^ n‖ = Lc * ‖w‖ ^ n := by
      rw [norm_mul, norm_pow, hLc]
    have := norm_sub_norm_le (P.coeff n * w ^ n) (P.eval w)
    have htri : ‖P.coeff n * w ^ n‖ - ‖P.eval w‖ ≤ ‖P.coeff n * w ^ n - P.eval w‖ := this
    rw [hnorm] at htri
    have hsymm : ‖P.coeff n * w ^ n - P.eval w‖ = ‖P.eval w - P.coeff n * w ^ n‖ :=
      norm_sub_rev _ _
    rw [hsymm] at htri
    linarith
  -- absorb the lower-order tail
  have hMw : M * ‖w‖ ^ (n - 1) ≤ Lc * ‖w‖ ^ n / 2 := by
    have hpow : ‖w‖ ^ (n - 1) * ‖w‖ = ‖w‖ ^ n := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    have hbig : 2 * M / Lc ≤ ‖w‖ := le_trans (le_max_right _ _) hw.le
    have h2M : 2 * M ≤ Lc * ‖w‖ := by
      rw [div_le_iff₀ hLpos] at hbig
      linarith
    have hppos : (0 : ℝ) ≤ ‖w‖ ^ (n - 1) := by positivity
    nlinarith [hppos]
  have hhalf : Lc * ‖w‖ ^ n / 2 ≤ ‖P.eval w‖ := by linarith
  have hwn : ‖w‖ ≤ ‖w‖ ^ n := by
    calc ‖w‖ = ‖w‖ ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ‖w‖ ^ n := pow_le_pow_right₀ hw1 hP
  have hfinal : ‖w‖ ≤ 2 / Lc * ‖P.eval w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
    nlinarith
  linarith [le_max_left (1:ℝ) (2 * M / Lc)]

/-- **Finite order descends through a polynomial outer factor.** -/
theorem finiteOrderEnvelope_of_comp_polynomial {P : Polynomial ℂ} (hP : 1 ≤ P.natDegree)
    {g : ℂ → ℂ} (henv : FiniteOrderEnvelope (fun z => P.eval (g z))) :
    FiniteOrderEnvelope g := by
  obtain ⟨R, c, hR, hc, hbound⟩ := exists_norm_le_of_natDegree_pos hP
  obtain ⟨C, d, hC, hgrow⟩ := henv
  refine ⟨C + |Real.log (R + c)|, d, by positivity, fun z => ?_⟩
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith)
  have hu : (0 : ℝ) ≤ C * (1 + ‖z‖) ^ d := by positivity
  have hexp1 : (1 : ℝ) ≤ Real.exp (C * (1 + ‖z‖) ^ d) := Real.one_le_exp hu
  have hRc : 0 < R + c := by linarith
  calc ‖g z‖ ≤ R + c * ‖P.eval (g z)‖ := hbound (g z)
    _ ≤ R + c * Real.exp (C * (1 + ‖z‖) ^ d) := by
        have := hgrow z
        nlinarith [hc.le]
    _ ≤ (R + c) * Real.exp (C * (1 + ‖z‖) ^ d) := by nlinarith
    _ = Real.exp (Real.log (R + c)) * Real.exp (C * (1 + ‖z‖) ^ d) := by
        rw [Real.exp_log hRc]
    _ = Real.exp (Real.log (R + c) + C * (1 + ‖z‖) ^ d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C + |Real.log (R + c)|) * (1 + ‖z‖) ^ d) := by
        refine Real.exp_le_exp.mpr ?_
        have habs : Real.log (R + c) ≤ |Real.log (R + c)| := le_abs_self _
        have habs0 : 0 ≤ |Real.log (R + c)| := abs_nonneg _
        nlinarith

end GaloisForLFunctions.HTGeometry
