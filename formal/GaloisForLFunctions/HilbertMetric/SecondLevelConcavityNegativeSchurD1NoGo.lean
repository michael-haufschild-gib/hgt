import GaloisForLFunctions.HilbertMetric.SecondLevelConcavityFifthRootNoGo
import GaloisForLFunctions.RHTower.ThetaCuspReflectedEighthPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Second-level concavity plus the physical Schur signs does not force rank-three D1

The TCD route needs positivity of the native reflected rank-three polynomial `D1`.  Existing
theta-specific work proves both Schur diagonal factors positive and selects the negative coupling
sheet.  A possible generic landing from Planat--Solé second-level concavity would combine those
facts to force `D1 > 0`.

This module closes that landing as false.  For

`F(x) = exp (-x^2 - x^4/8)` and `s(t) = exp (-t - t^2/8)`, the first Laguerre expression is
`exp (-2t - t^2/4)/4`, hence its logarithmic second derivative is globally `-1/2`.  The signed even
log jets are `(A,B,C,D) = (2,3,0,0)`.  Both Schur diagonals are strict and the coupling lies on the
negative sheet, but the exact native polynomial is `D1 = -6252`.

Consequently no RH proof may replace the theta-specific singular-crossing/flux burden by this
combined static package.
-/

open Real

namespace HilbertMetric

noncomputable section

/-- Positive even kernel giving the combined second-level/Schur counterexample. -/
def tiltedQuarticGaussianKernel (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 - x ^ 4 / 8)

/-- Square-radial profile of `tiltedQuarticGaussianKernel`. -/
def tiltedQuadraticGaussianRadialProfile (x : ℝ) : ℝ :=
  Real.exp (-x - x ^ 2 / 8)

theorem hasDerivAt_tiltedQuadraticGaussianRadialProfile (x : ℝ) :
    HasDerivAt tiltedQuadraticGaussianRadialProfile
      ((-1 - x / 4) * Real.exp (-x - x ^ 2 / 8)) x := by
  have hinner : HasDerivAt (fun y : ℝ => -y - y ^ 2 / 8) (-1 - x / 4) x := by
    have h := (hasDerivAt_id x).neg.sub
      (((hasDerivAt_id x).pow 2).const_mul (1 / 8 : ℝ))
    rw [show (fun y : ℝ => -y - y ^ 2 / 8) =
        -id - fun y => (1 / 8 : ℝ) * (id ^ 2) y by
      funext y
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, id_eq]
      ring]
    refine h.congr_deriv ?_
    norm_num
    ring
  have h := (Real.hasDerivAt_exp (-x - x ^ 2 / 8)).comp x hinner
  have hfun : tiltedQuadraticGaussianRadialProfile =
      Real.exp ∘ fun y : ℝ => -y - y ^ 2 / 8 := by
    rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem iteratedDeriv_one_tiltedQuadraticGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 1 tiltedQuadraticGaussianRadialProfile x =
      (-1 - x / 4) * Real.exp (-x - x ^ 2 / 8) := by
  rw [iteratedDeriv_one,
    (hasDerivAt_tiltedQuadraticGaussianRadialProfile x).deriv]

theorem iteratedDeriv_two_tiltedQuadraticGaussianRadialProfile (x : ℝ) :
    iteratedDeriv 2 tiltedQuadraticGaussianRadialProfile x =
      ((-1 - x / 4) ^ 2 - 1 / 4) * Real.exp (-x - x ^ 2 / 8) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv tiltedQuadraticGaussianRadialProfile =
      fun y : ℝ => (-1 - y / 4) * Real.exp (-y - y ^ 2 / 8) := by
    funext y
    exact (hasDerivAt_tiltedQuadraticGaussianRadialProfile y).deriv
  rw [hfun]
  have hlinear : HasDerivAt (fun y : ℝ => -1 - y / 4) (-1 / 4) x := by
    have h := (hasDerivAt_const x (-1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul (1 / 4 : ℝ))
    rw [show (fun y : ℝ => -1 - y / 4) =
        (fun _ : ℝ => -1) - fun y => (1 / 4 : ℝ) * id y by
      funext y
      simp only [Pi.sub_apply, id_eq]
      ring]
    refine h.congr_deriv ?_
    norm_num
  have hprod := hlinear.mul (hasDerivAt_tiltedQuadraticGaussianRadialProfile x)
  change deriv ((fun y : ℝ => -1 - y / 4) *
    tiltedQuadraticGaussianRadialProfile) x = _
  rw [hprod.deriv]
  unfold tiltedQuadraticGaussianRadialProfile
  ring

theorem firstLaguerreExpression_tiltedQuadraticGaussianRadialProfile (x : ℝ) :
    firstLaguerreExpression tiltedQuadraticGaussianRadialProfile x =
      (1 / 4 : ℝ) * Real.exp (-2 * x - x ^ 2 / 4) := by
  unfold firstLaguerreExpression
  rw [iteratedDeriv_one_tiltedQuadraticGaussianRadialProfile,
    iteratedDeriv_two_tiltedQuadraticGaussianRadialProfile]
  have hexp : Real.exp (-2 * x - x ^ 2 / 4) =
      Real.exp (-x - x ^ 2 / 8) ^ 2 := by
    calc
      Real.exp (-2 * x - x ^ 2 / 4) =
          Real.exp ((-x - x ^ 2 / 8) + (-x - x ^ 2 / 8)) := by
            congr 1
            ring
      _ = Real.exp (-x - x ^ 2 / 8) * Real.exp (-x - x ^ 2 / 8) :=
        Real.exp_add _ _
      _ = Real.exp (-x - x ^ 2 / 8) ^ 2 := by ring
  rw [hexp]
  unfold tiltedQuadraticGaussianRadialProfile
  ring

theorem tiltedQuadraticGaussianRadialProfile_secondLevelLogCurvature (x : ℝ) :
    iteratedDeriv 2
      (fun y => Real.log
        (firstLaguerreExpression tiltedQuadraticGaussianRadialProfile y)) x =
      -(1 / 2 : ℝ) := by
  have hlog (y : ℝ) :
      Real.log (firstLaguerreExpression tiltedQuadraticGaussianRadialProfile y) =
        Real.log (1 / 4 : ℝ) - 2 * y - y ^ 2 / 4 := by
    rw [firstLaguerreExpression_tiltedQuadraticGaussianRadialProfile,
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hfun :
      (fun y => Real.log
        (firstLaguerreExpression tiltedQuadraticGaussianRadialProfile y)) =
      fun y => Real.log (1 / 4 : ℝ) - 2 * y - y ^ 2 / 4 := by
    funext y
    exact hlog y
  rw [hfun, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirstAt (y : ℝ) :
      HasDerivAt (fun z : ℝ => Real.log (1 / 4 : ℝ) - 2 * z - z ^ 2 / 4)
        (-2 - y / 2) y := by
    have h := (((hasDerivAt_const y (Real.log (1 / 4 : ℝ))).sub
      ((hasDerivAt_id y).const_mul 2)).sub
        (((hasDerivAt_id y).pow 2).const_mul (1 / 4 : ℝ)))
    rw [show (fun z : ℝ => Real.log (1 / 4 : ℝ) - 2 * z - z ^ 2 / 4) =
        ((fun _ : ℝ => Real.log (1 / 4 : ℝ)) - fun z => 2 * id z) -
          fun z => (1 / 4 : ℝ) * (id ^ 2) z by
      funext z
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      ring]
    refine h.congr_deriv ?_
    norm_num
    ring
  have hfirst : deriv (fun y : ℝ => Real.log (1 / 4 : ℝ) - 2 * y - y ^ 2 / 4) =
      fun y => -2 - y / 2 := by
    funext y
    exact (hfirstAt y).deriv
  rw [hfirst]
  have hsecond : HasDerivAt (fun y : ℝ => -2 - y / 2) (-(1 / 2 : ℝ)) x := by
    have h := (hasDerivAt_const x (-2 : ℝ)).sub
      ((hasDerivAt_id x).const_mul (1 / 2 : ℝ))
    rw [show (fun y : ℝ => -2 - y / 2) =
        (fun _ : ℝ => -2) - fun y => (1 / 2 : ℝ) * id y by
      funext y
      simp only [Pi.sub_apply, id_eq]
      ring]
    refine h.congr_deriv ?_
    norm_num
  exact hsecond.deriv

theorem tiltedQuadraticGaussianRadialProfile_secondLevel_strict (x : ℝ) :
    iteratedDeriv 2
      (fun y => Real.log
        (firstLaguerreExpression tiltedQuadraticGaussianRadialProfile y)) x < 0 := by
  rw [tiltedQuadraticGaussianRadialProfile_secondLevelLogCurvature]
  norm_num

theorem tiltedQuarticGaussianKernel_pos (x : ℝ) :
    0 < tiltedQuarticGaussianKernel x := by
  unfold tiltedQuarticGaussianKernel
  positivity

theorem tiltedQuarticGaussianKernel_even : Function.Even tiltedQuarticGaussianKernel := by
  intro x
  unfold tiltedQuarticGaussianKernel
  congr 1
  ring

theorem tiltedQuadraticGaussianRadialProfile_eq_kernel_sqrt
    {x : ℝ} (hx : 0 ≤ x) :
    tiltedQuadraticGaussianRadialProfile x =
      tiltedQuarticGaussianKernel (Real.sqrt x) := by
  unfold tiltedQuadraticGaussianRadialProfile tiltedQuarticGaussianKernel
  congr 1
  rw [show Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 by ring,
    Real.sq_sqrt hx]

theorem firstLaguerreExpression_tiltedQuadraticGaussianRadialProfile_pos (x : ℝ) :
    0 < firstLaguerreExpression tiltedQuadraticGaussianRadialProfile x := by
  rw [firstLaguerreExpression_tiltedQuadraticGaussianRadialProfile]
  positivity

def tiltedQuarticGaussianLogPolynomial : Polynomial ℝ :=
  -Polynomial.X ^ 2 - Polynomial.C (1 / 8 : ℝ) * Polynomial.X ^ 4

theorem log_tiltedQuarticGaussianKernel (x : ℝ) :
    Real.log (tiltedQuarticGaussianKernel x) =
      tiltedQuarticGaussianLogPolynomial.eval x := by
  rw [tiltedQuarticGaussianKernel, Real.log_exp]
  simp [tiltedQuarticGaussianLogPolynomial]
  ring

theorem iteratedDeriv_polynomial_eval_real_local
    (p : Polynomial ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => p.eval y) x =
      ((Polynomial.derivative^[n]) p).eval x := by
  induction n generalizing p x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun y => p.eval y) =
          fun y => p.derivative.eval y := by
        funext y
        exact (p.hasDerivAt y).deriv
      rw [hderiv]
      simpa [Function.iterate_succ_apply] using
        (ih (x := x) (p := p.derivative))

theorem tiltedQuarticGaussianKernel_logJet_two :
    iteratedDeriv 2 (fun x => Real.log (tiltedQuarticGaussianKernel x)) 0 = -2 := by
  rw [show (fun x => Real.log (tiltedQuarticGaussianKernel x)) =
      fun x => tiltedQuarticGaussianLogPolynomial.eval x by
    funext x; exact log_tiltedQuarticGaussianKernel x]
  rw [iteratedDeriv_polynomial_eval_real_local]
  norm_num [tiltedQuarticGaussianLogPolynomial, Function.iterate_succ_apply]

theorem tiltedQuarticGaussianKernel_logJet_four :
    iteratedDeriv 4 (fun x => Real.log (tiltedQuarticGaussianKernel x)) 0 = -3 := by
  rw [show (fun x => Real.log (tiltedQuarticGaussianKernel x)) =
      fun x => tiltedQuarticGaussianLogPolynomial.eval x by
    funext x; exact log_tiltedQuarticGaussianKernel x]
  rw [iteratedDeriv_polynomial_eval_real_local]
  norm_num [tiltedQuarticGaussianLogPolynomial, Function.iterate_succ_apply]

theorem tiltedQuarticGaussianKernel_logJet_six :
    iteratedDeriv 6 (fun x => Real.log (tiltedQuarticGaussianKernel x)) 0 = 0 := by
  rw [show (fun x => Real.log (tiltedQuarticGaussianKernel x)) =
      fun x => tiltedQuarticGaussianLogPolynomial.eval x by
    funext x; exact log_tiltedQuarticGaussianKernel x]
  rw [iteratedDeriv_polynomial_eval_real_local]
  norm_num [tiltedQuarticGaussianLogPolynomial, Function.iterate_succ_apply]

theorem tiltedQuarticGaussianKernel_logJet_eight :
    iteratedDeriv 8 (fun x => Real.log (tiltedQuarticGaussianKernel x)) 0 = 0 := by
  rw [show (fun x => Real.log (tiltedQuarticGaussianKernel x)) =
      fun x => tiltedQuarticGaussianLogPolynomial.eval x by
    funext x; exact log_tiltedQuarticGaussianKernel x]
  rw [iteratedDeriv_polynomial_eval_real_local]
  norm_num [tiltedQuarticGaussianLogPolynomial, Function.iterate_succ_apply]

/-- Exact Schur data and native reflected rank-three failure of the witness. -/
theorem tiltedQuarticGaussian_exactSchurCertificate :
    4 * (2 : ℝ) ^ 2 - 3 = 13 ∧
      1216 * (2 : ℝ) ^ 4 - 32 * 2 ^ 2 * 3 + 68 * 3 ^ 2 - 0 = 19684 ∧
      (0 : ℝ) - 64 * 2 ^ 3 = -512 ∧
      RHTower.thetaCuspReflectedEighthPolynomial 2 3 0 0 = -6252 := by
  norm_num [RHTower.thetaCuspReflectedEighthPolynomial]

/--
Generic Planat--Solé second-level strictness, even after adjoining both strict Schur diagonals and
the physical negative-sheet sign, does not imply native reflected rank-three positivity.
-/
theorem exists_secondLevelStrict_kernel_with_strictSchur_negativeSheet_D1Failure :
    ∃ (F s : ℝ → ℝ),
      (∀ x, 0 < F x) ∧
      Function.Even F ∧
      (∀ x, 0 ≤ x → s x = F (Real.sqrt x)) ∧
      (∀ x, 0 < firstLaguerreExpression s x) ∧
      (∀ x, iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression s y)) x < 0) ∧
      let A := -iteratedDeriv 2 (fun y => Real.log (F y)) 0
      let B := -iteratedDeriv 4 (fun y => Real.log (F y)) 0
      let C := -iteratedDeriv 6 (fun y => Real.log (F y)) 0
      let D := -iteratedDeriv 8 (fun y => Real.log (F y)) 0
      0 < A ∧
        0 < 4 * A ^ 2 - B ∧
        0 < 1216 * A ^ 4 - 32 * A ^ 2 * B + 68 * B ^ 2 - D ∧
        C - 64 * A ^ 3 < 0 ∧
        RHTower.thetaCuspReflectedEighthPolynomial A B C D < 0 := by
  refine ⟨tiltedQuarticGaussianKernel, tiltedQuadraticGaussianRadialProfile,
    tiltedQuarticGaussianKernel_pos, tiltedQuarticGaussianKernel_even,
    ?_, firstLaguerreExpression_tiltedQuadraticGaussianRadialProfile_pos,
    tiltedQuadraticGaussianRadialProfile_secondLevel_strict, ?_⟩
  · intro x hx
    exact tiltedQuadraticGaussianRadialProfile_eq_kernel_sqrt hx
  · dsimp only
    rw [tiltedQuarticGaussianKernel_logJet_two,
      tiltedQuarticGaussianKernel_logJet_four,
      tiltedQuarticGaussianKernel_logJet_six,
      tiltedQuarticGaussianKernel_logJet_eight]
    norm_num [RHTower.thetaCuspReflectedEighthPolynomial]

end

end HilbertMetric

