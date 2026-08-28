import GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlinePhaseWindow

/-!
# Quadrant surjectivity of the FZZ parity Krein eigenline

The balanced positive-imaginary literal FZZ source eigenline was known to lie in the strict
upper-left unit quadrant at every positive physical scale. This module computes its full scale
image.

The squared negative real coordinate is the source Fermi ratio

`P(beta) P(4 beta) / P(2 beta)^2`.

After writing `a = exp(beta)`, this is the rational function

`(a^2 + 1)^2 / ((a + 1)(a^4 + 1))`.

It equals one at `a=1`, is bounded by `4/a` for `a>=1`, and is continuous. Exact intermediate
value therefore realizes every negative real coordinate between zero and one. Unit norm and
positive imaginary part then identify the whole complex coordinate.

Consequently positive scale fills the entire strict upper-left unit quadrant, not merely an
unknown subset. The prior cofinal two-line obstruction is exactly a missing-half-circle
obstruction. This supplies the analytic input for nonlinear conjugate-pair phase completion.

`[NEW] [EXACT SCALE IMAGE] [QUADRANT SURJECTIVITY] [LEAN-PROVED]`
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Algebraic form of the squared radial coordinate after `a = exp(beta)`. -/
def fzzCigarParityKreinEigenlineAlgebraicRadialSq (a : ℝ) : ℝ :=
  (a ^ 2 + 1) ^ 2 / ((a + 1) * (a ^ 4 + 1))

/-- The squared negative real coordinate of the balanced source eigenline is the multiplicative
three-scale Fermi ratio. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_neg_re_sq
    {beta : ℝ} (hbeta : 0 < beta) :
    (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re) ^ 2 =
      fzzKreinPAt beta * fzzKreinRAt beta / fzzKreinQAt beta ^ 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re]
  have hs := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hp := (fzzKreinPAt_pos hbeta).ne'
  have hq := (fzzKreinQAt_pos hbeta).ne'
  have hneg :
      -(-fzzCigarParitySourceMetricReflectionScale beta * fzzKreinPAt beta /
          fzzKreinQAt beta) =
        fzzCigarParitySourceMetricReflectionScale beta * fzzKreinPAt beta /
          fzzKreinQAt beta := by ring
  rw [hneg, div_pow, mul_pow, hs]
  field_simp

/-- Exact rational Fermi form in the exponential scale coordinate. -/
theorem fzzCigarParityKreinFermiRatio_log_eq_algebraic
    {a : ℝ} (ha : 1 < a) :
    fzzKreinPAt (Real.log a) * fzzKreinRAt (Real.log a) /
        fzzKreinQAt (Real.log a) ^ 2 =
      fzzCigarParityKreinEigenlineAlgebraicRadialSq a := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hlog : 0 < Real.log a := Real.log_pos ha
  have he2 : Real.exp (2 * Real.log a) = a ^ 2 := by
    rw [show 2 * Real.log a = Real.log a + Real.log a by ring,
      Real.exp_add, Real.exp_log ha0]
    ring
  have he4 : Real.exp (4 * Real.log a) = a ^ 4 := by
    rw [show 4 * Real.log a = 2 * Real.log a + 2 * Real.log a by ring,
      Real.exp_add, he2]
    ring
  change fzzCigarParityDelay (Real.log a) *
        fzzCigarParityDelay (4 * Real.log a) /
        fzzCigarParityDelay (2 * Real.log a) ^ 2 = _
  rw [fzzCigarParityDelay_eq_fermi hlog,
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hlog),
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hlog),
    Real.exp_log ha0, he2, he4]
  rw [fzzCigarParityKreinEigenlineAlgebraicRadialSq]
  field_simp

/-- The algebraic radial-square profile is continuous on every physical closed scale interval. -/
theorem continuousOn_fzzCigarParityKreinEigenlineAlgebraicRadialSq
    {A : ℝ} :
    ContinuousOn fzzCigarParityKreinEigenlineAlgebraicRadialSq (Icc 1 A) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  unfold fzzCigarParityKreinEigenlineAlgebraicRadialSq
  have hden : (a + 1) * (a ^ 4 + 1) ≠ 0 := by
    have ha1 : 1 ≤ a := ha.1
    positivity
  fun_prop

/-- Neutral-scale endpoint of the algebraic radial-square profile. -/
theorem fzzCigarParityKreinEigenlineAlgebraicRadialSq_one :
    fzzCigarParityKreinEigenlineAlgebraicRadialSq 1 = 1 := by
  norm_num [fzzCigarParityKreinEigenlineAlgebraicRadialSq]

/-- Elementary cofinal decay bound, avoiding an asymptotic or numerical argument. -/
theorem fzzCigarParityKreinEigenlineAlgebraicRadialSq_le_four_div
    {a : ℝ} (ha : 1 ≤ a) :
    fzzCigarParityKreinEigenlineAlgebraicRadialSq a ≤ 4 / a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hnum : (a ^ 2 + 1) ^ 2 ≤ 4 * a ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2 - 1)]
  have hden : a ^ 5 ≤ (a + 1) * (a ^ 4 + 1) := by
    have h1 : a ≤ a + 1 := by linarith
    have h2 : a ^ 4 ≤ a ^ 4 + 1 := by linarith
    have hm := mul_le_mul h1 h2 ha4 (by positivity : 0 ≤ a + 1)
    nlinarith
  rw [fzzCigarParityKreinEigenlineAlgebraicRadialSq,
    div_le_div_iff₀ (mul_pos (by positivity) (by positivity)) ha0]
  have hnuma := mul_le_mul_of_nonneg_right hnum ha0.le
  nlinarith

/-- Every strict negative real unit-circle coordinate occurs at some positive physical scale. -/
theorem exists_pos_fzzCigarParityKreinEigenline_neg_re_eq
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ beta : ℝ, 0 < beta ∧
      -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re = c := by
  let A : ℝ := 8 / c ^ 2
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hc_sq_lt_one : c ^ 2 < 1 := by
    nlinarith [mul_pos hc0 (sub_pos.mpr hc1)]
  have hA : 1 < A := by
    dsimp only [A]
    rw [lt_div_iff₀ hc2]
    nlinarith
  have hAle : 1 ≤ A := hA.le
  have hgA_le : fzzCigarParityKreinEigenlineAlgebraicRadialSq A ≤ 4 / A :=
    fzzCigarParityKreinEigenlineAlgebraicRadialSq_le_four_div hAle
  have hfourA : 4 / A = c ^ 2 / 2 := by
    dsimp only [A]
    field_simp
    ring
  have hgA : fzzCigarParityKreinEigenlineAlgebraicRadialSq A < c ^ 2 := by
    rw [hfourA] at hgA_le
    nlinarith
  have hmem : c ^ 2 ∈ Icc
      (fzzCigarParityKreinEigenlineAlgebraicRadialSq A)
      (fzzCigarParityKreinEigenlineAlgebraicRadialSq 1) := by
    rw [fzzCigarParityKreinEigenlineAlgebraicRadialSq_one]
    exact ⟨hgA.le, hc_sq_lt_one.le⟩
  obtain ⟨a, haIcc, haeq⟩ := intermediate_value_Icc' hAle
    continuousOn_fzzCigarParityKreinEigenlineAlgebraicRadialSq hmem
  have ha : 1 < a := by
    rcases haIcc.1.lt_or_eq with h | h
    · exact h
    · rw [← h, fzzCigarParityKreinEigenlineAlgebraicRadialSq_one] at haeq
      nlinarith
  refine ⟨Real.log a, Real.log_pos ha, ?_⟩
  have hsquare := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_neg_re_sq
    (Real.log_pos ha)
  rw [fzzCigarParityKreinFermiRatio_log_eq_algebraic ha, haeq] at hsquare
  have hypos : 0 <
      -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate (Real.log a)).re := by
    linarith [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg
      (Real.log_pos ha)]
  nlinarith

/-- Every unit complex phase in the strict upper-left quadrant is the balanced literal source
eigenline at an exact positive physical scale. -/
theorem exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
    {z : ℂ} (hnorm : ‖z‖ = 1) (hre : z.re < 0) (him : 0 < z.im) :
    ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta = z := by
  have hnormsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have hc0 : 0 < -z.re := by linarith
  have hc1 : -z.re < 1 := by
    nlinarith [sq_pos_of_pos him]
  obtain ⟨beta, hbeta, hreEq⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_neg_re_eq hc0 hc1
  refine ⟨beta, hbeta, Complex.ext ?_ ?_⟩
  · linarith
  · have hynorm := norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta
    have hynormsq := congrArg (fun x : ℝ => x ^ 2) hynorm
    rw [Complex.sq_norm, Complex.normSq_apply] at hynormsq
    have hyim := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta
    nlinarith

/-- Exact image classification: positive scale fills the strict upper-left unit quadrant. -/
theorem exists_pos_fzzCigarParityKreinEigenline_eq_iff_unit_upperLeft
    (z : ℂ) :
    (∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta = z) ↔
      ‖z‖ = 1 ∧ z.re < 0 ∧ 0 < z.im := by
  constructor
  · rintro ⟨beta, hbeta, rfl⟩
    exact ⟨norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta,
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta,
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta⟩
  · rintro ⟨hnorm, hre, him⟩
    exact exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft hnorm hre him

end

end RHTower
