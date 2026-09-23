import GaloisForLFunctions.RHTower.FZZCigarParityFixedMonomialDeterminismNoGo

/-!
# Joint quintic-radial scale encoding of the FZZ parity source

HC26 proves that no phase-only fixed monomial can combine unit-circle completeness with unique
physical scale. This module realizes its strongest survivor using a second coordinate already
present in the literal FZZ source.

The exact algebraic Fermi profile

`g(a) = (a^(2 : ℕ)+1)^(2 : ℕ) / ((a+1)(a^(4 : ℕ)+1))`

has strictly negative derivative for `a>1`. Consequently the squared and unsquared negative-real
coordinates of the balanced source eigenline are strictly decreasing for positive scale. Every
radial value in `(0,1)` identifies one unique positive scale.

Pairing this monotone radial clock with HC25's fixed quintic phase produces a source-native joint
encoding whose phase projection covers the unit circle and whose full report is injective in scale.
This closes the lost-scale obstruction without a target-fitted branch label. Remaining FZZ-P burden
is to derive the joint report on actual parity-delay Mellin divisor modes from literal dynamics.

`[NEW] [STRICT FERMI MONOTONICITY] [JOINT SOURCE ENCODING] [POSITIVE SURVIVOR]
[LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

def fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator
    (a : ℝ) : ℝ :=
  -a ^ (6 : ℕ) - 5 * a ^ (4 : ℕ) - 4 * a ^ (3 : ℕ) + 3 * a ^ (2 : ℕ) + 4 * a - 1

theorem fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator_neg
    {a : ℝ} (ha : 1 ≤ a) :
    fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator a < 0 := by
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 1 ≤ a ^ (2 : ℕ) := by nlinarith
  have h2le4 : a ^ (2 : ℕ) ≤ a ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha2)]
  have h4le6 : a ^ (4 : ℕ) ≤ a ^ (6 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg (a ^ (2 : ℕ))) (sub_nonneg.mpr ha2)]
  have h1le3 : a ≤ a ^ (3 : ℕ) := by
    nlinarith [mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha)) (by linarith : 0 ≤ a + 1)]
  simp only [fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator]
  nlinarith

theorem hasDerivAt_fzzCigarParityKreinEigenlineAlgebraicRadialSq
    {a : ℝ} (ha : 1 ≤ a) :
    HasDerivAt fzzCigarParityKreinEigenlineAlgebraicRadialSq
      (((a ^ (2 : ℕ) + 1) *
          fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator a) /
        (((a + 1) * (a ^ (4 : ℕ) + 1)) ^ (2 : ℕ))) a := by
  have hden : (a + 1) * (a ^ (4 : ℕ) + 1) ≠ 0 := by positivity
  unfold fzzCigarParityKreinEigenlineAlgebraicRadialSq
  convert
    ((((hasDerivAt_id a).pow 2).add_const 1).pow 2).div
      (((hasDerivAt_id a).add_const 1).mul
        (((hasDerivAt_id a).pow 4).add_const 1)) hden using 1
  all_goals try rfl
  norm_num [Function.id_def,
    fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator]
  ring

theorem deriv_fzzCigarParityKreinEigenlineAlgebraicRadialSq_neg
    {a : ℝ} (ha : 1 < a) :
    deriv fzzCigarParityKreinEigenlineAlgebraicRadialSq a < 0 := by
  rw [(hasDerivAt_fzzCigarParityKreinEigenlineAlgebraicRadialSq ha.le).deriv]
  have hnum :=
    fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator_neg ha.le
  have hleft : 0 < a ^ (2 : ℕ) + 1 := by positivity
  have hden : 0 < ((a + 1) * (a ^ (4 : ℕ) + 1)) ^ (2 : ℕ) := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hleft hnum) hden

theorem strictAntiOn_fzzCigarParityKreinEigenlineAlgebraicRadialSq :
    StrictAntiOn fzzCigarParityKreinEigenlineAlgebraicRadialSq (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro x hx
    exact (hasDerivAt_fzzCigarParityKreinEigenlineAlgebraicRadialSq hx.le).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact deriv_fzzCigarParityKreinEigenlineAlgebraicRadialSq_neg hx

theorem fzzCigarParityDilatedKreinEigenline_neg_re_sq_eq_algebraic
    {beta : ℝ} (hbeta : 0 < beta) :
    (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re) ^ (2 : ℕ) =
      fzzCigarParityKreinEigenlineAlgebraicRadialSq (Real.exp beta) := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_neg_re_sq hbeta]
  have hratio := fzzCigarParityKreinFermiRatio_log_eq_algebraic
    (a := Real.exp beta) (Real.one_lt_exp_iff.mpr hbeta)
  rwa [Real.log_exp] at hratio

theorem strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re_sq :
    StrictAntiOn
      (fun beta : ℝ =>
        (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re) ^ (2 : ℕ))
      (Set.Ioi 0) := by
  intro beta hbeta gamma hgamma hbg
  change
    (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate gamma).re) ^ (2 : ℕ) <
      (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re) ^ (2 : ℕ)
  rw [fzzCigarParityDilatedKreinEigenline_neg_re_sq_eq_algebraic hbeta,
    fzzCigarParityDilatedKreinEigenline_neg_re_sq_eq_algebraic hgamma]
  exact strictAntiOn_fzzCigarParityKreinEigenlineAlgebraicRadialSq
    (Real.one_lt_exp_iff.mpr hbeta) (Real.one_lt_exp_iff.mpr hgamma)
    (Real.exp_lt_exp.mpr hbg)

/-- The literal negative-real source coordinate is a strictly decreasing physical scale clock. -/
theorem strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re :
    StrictAntiOn
      (fun beta : ℝ =>
        -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re)
      (Set.Ioi 0) := by
  intro beta hbeta gamma hgamma hbg
  have hsq := strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re_sq
    hbeta hgamma hbg
  have hbetaPos :
      0 < -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re :=
    neg_pos.mpr (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta)
  have hgammaPos :
      0 < -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate gamma).re :=
    neg_pos.mpr (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hgamma)
  nlinarith

theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_injOn_pos :
    Set.InjOn fzzCigarParityDilatedKreinEigenlineBalancedCoordinate (Set.Ioi 0) := by
  intro beta hbeta gamma hgamma heq
  apply strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re.injOn hbeta hgamma
  exact congrArg (fun z : ℂ => -z.re) heq

/-- Every strict radial coordinate identifies one unique positive physical scale. -/
theorem existsUnique_pos_fzzCigarParityKreinEigenline_neg_re_eq
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃! beta : ℝ,
      0 < beta ∧
        -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re = c := by
  obtain ⟨beta, hbeta, heq⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_neg_re_eq hc0 hc1
  refine ⟨beta, ⟨hbeta, heq⟩, ?_⟩
  intro gamma hgamma
  exact strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re.injOn
    hgamma.1 hbeta (hgamma.2.trans heq.symm)

/-- Fixed-quintic phase paired with the literal monotone Fermi radial coordinate. -/
def fzzCigarParityJointQuinticRadialEncoding (beta : ℝ) : ℝ × ℂ :=
  (-(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re,
    fzzCigarParityFixedQuinticEigenphase beta)

theorem fzzCigarParityJointQuinticRadialEncoding_phaseComplete
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    ∃ beta : ℝ, 0 < beta ∧
      (fzzCigarParityJointQuinticRadialEncoding beta).2 = z := by
  simpa [fzzCigarParityJointQuinticRadialEncoding] using
    exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one hnorm

/-- The added literal Fermi coordinate resolves every fixed-quintic phase collision. -/
theorem fzzCigarParityJointQuinticRadialEncoding_injOn_pos :
    Set.InjOn fzzCigarParityJointQuinticRadialEncoding (Set.Ioi 0) := by
  intro beta hbeta gamma hgamma heq
  apply strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re.injOn hbeta hgamma
  exact congrArg Prod.fst heq

/-- Joint encoding is simultaneously phase-complete and scale-deterministic. -/
theorem fzzCigarParityJointQuinticRadialEncoding_complete_and_injective :
    (∀ z : ℂ, ‖z‖ = 1 →
      ∃ beta : ℝ, 0 < beta ∧
        (fzzCigarParityJointQuinticRadialEncoding beta).2 = z) ∧
      Set.InjOn fzzCigarParityJointQuinticRadialEncoding (Set.Ioi 0) := by
  exact ⟨fun _ => fzzCigarParityJointQuinticRadialEncoding_phaseComplete,
    fzzCigarParityJointQuinticRadialEncoding_injOn_pos⟩

end

end RHTower
