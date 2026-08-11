import GaloisForLFunctions.RHTower.DeningerExponentLineReflectionBlowupTransport
import GaloisForLFunctions.RHTower.DeningerGammaSixShellPrincipalIdeal

/-!
# Deninger exceptional transport versus Gamma-six shell reflection

This module tests a natural cross-corpus weld.  The completed-exponent blow-up
supplies a unique anti-linear scalar on each Xi exceptional direction, while
the Gamma-six principal ideal supplies forward and reflected shell powers.

The result is rigid.  The unique coefficient-faithful diagonal multiplier
carrying exponent `1 - delta` to exponent `1 + delta` is

`n ↦ lambda_n ^ (2 * delta)`.

It acquires the nontrivial Wold factor `(1/6) ^ (2 * delta)` under one source
clock step.  Consequently no coordinate-independent scalar can intertwine the
two shell orientations unless `delta = 0`; then the scalar is one.  Applied to
the literal exceptional blow-up coefficient, this gives a new exact RH
criterion.

Thus exceptional covariance and shell selection meet at a precise wall: a
source proof that the degree-one exceptional coefficient transports all
Gamma-six shell grades would prove RH.  Away from the critical line such a
transport is necessarily grade-dependent, so scalar tensor amplification
cannot supply it.

All statements are unconditional.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Literal exceptional coefficient and its metric defect -/

/-- Coefficient of the forced anti-linear exceptional-direction transport. -/
def deningerExponentExceptionalLineReflectionCoefficient
    (rho : XiDivisorSupport) : ℂ :=
  ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) /
    (starRingEnd ℂ) (rho : ℂ)

/-- The completed-exponent exceptional transport is conjugation followed by
multiplication by its source-forced coefficient. -/
theorem deningerExponentExceptionalLineReflectionDirection_eq_coefficient
    (rho : XiDivisorSupport) (w : ℂ) :
    deningerExponentExceptionalLineReflectionDirection rho w =
      (starRingEnd ℂ) w *
        deningerExponentExceptionalLineReflectionCoefficient rho := rfl

/-- Norm of the exceptional coefficient is the ratio of reflected and source
divisor radii. -/
theorem norm_deningerExponentExceptionalLineReflectionCoefficient
    (rho : XiDivisorSupport) :
    ‖deningerExponentExceptionalLineReflectionCoefficient rho‖ =
      ‖((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ)‖ /
        ‖(rho : ℂ)‖ := by
  rw [deningerExponentExceptionalLineReflectionCoefficient,
    norm_div, Complex.norm_conj]

/-- The forced exceptional transport is isometric exactly on the critical
line.  This uses the literal source coefficient, not an abstract reflection
operator. -/
theorem norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff
    (rho : XiDivisorSupport) :
    ‖deningerExponentExceptionalLineReflectionCoefficient rho‖ = 1 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [norm_deningerExponentExceptionalLineReflectionCoefficient]
  have hrho : (rho : ℂ) ≠ 0 := xiDivisorSupport_ne_zero rho
  rw [div_eq_one_iff_eq ((norm_pos_iff.mpr hrho).ne')]
  constructor
  · intro hnorm
    have hsquared := congrArg (fun x : ℝ => x ^ 2) hnorm
    rw [Complex.sq_norm, Complex.sq_norm] at hsquared
    rw [xiZeroLineConjEquiv_apply] at hsquared
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im] at hsquared
    nlinarith
  · intro hre
    apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
    rw [Complex.sq_norm, Complex.sq_norm, xiZeroLineConjEquiv_apply]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im]
    rw [hre]
    ring

/-! ## Exact diagonal shell carrier -/

/-- Forward Gamma-six shell power at horizontal displacement `delta`. -/
def deningerGammaSixForwardShellWeight (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 - delta)

/-- Reflected Gamma-six shell power at horizontal displacement `delta`. -/
def deningerGammaSixReflectedShellWeight (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 + delta)

/-- Candidate diagonal carrier between the two reflected shell powers. -/
def deningerGammaSixShellReflectionMultiplier (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (2 * delta)

theorem deningerGammaSixShellEigenvalue_pos (n : ℕ) :
    0 < deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixShellEigenvalue]
  positivity

/-- The explicit multiplier transports every forward shell coefficient to its
reflected coefficient. -/
theorem deningerGammaSixShellReflectionMultiplier_transports
    (delta : ℝ) (n : ℕ) :
    deningerGammaSixShellReflectionMultiplier delta n *
        deningerGammaSixForwardShellWeight delta n =
      deningerGammaSixReflectedShellWeight delta n := by
  rw [deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixForwardShellWeight, deningerGammaSixReflectedShellWeight,
    ← Real.rpow_add (deningerGammaSixShellEigenvalue_pos n)]
  congr 1
  ring

/-- Coefficient faithfulness: any pointwise diagonal shell transport equals
the explicit reflection multiplier. -/
theorem deningerGammaSixShellReflectionMultiplier_unique
    {delta : ℝ} {d : ℕ → ℝ}
    (htransport : ∀ n : ℕ,
      d n * deningerGammaSixForwardShellWeight delta n =
        deningerGammaSixReflectedShellWeight delta n) :
    d = deningerGammaSixShellReflectionMultiplier delta := by
  funext n
  have hforward : 0 < deningerGammaSixForwardShellWeight delta n :=
    Real.rpow_pos_of_pos (deningerGammaSixShellEigenvalue_pos n) _
  apply mul_right_cancel₀ hforward.ne'
  rw [htransport n,
    deningerGammaSixShellReflectionMultiplier_transports]

/-- One Wold source-clock step multiplies the unique carrier by
`(1/6)^(2*delta)`. -/
theorem deningerGammaSixShellReflectionMultiplier_wold
    (delta : ℝ) (n : ℕ) :
    deningerGammaSixShellReflectionMultiplier delta
        (deningerGammaSixWoldCoordinate n) =
      (1 / 6 : ℝ) ^ (2 * delta) *
        deningerGammaSixShellReflectionMultiplier delta n := by
  rw [deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixShellEigenvalue_wold,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (deningerGammaSixShellEigenvalue_nonneg n)]

/-! ## Constant-transport no-go and RH endpoints -/

/-- Two coordinates separated by one Wold step already show that a constant
scalar shell transport forces neutral horizontal displacement. -/
theorem deningerGammaSix_constantScalarShellTransport_forces_neutral
    {c delta : ℝ}
    (htransport : ∀ n : ℕ,
      c * deningerGammaSixForwardShellWeight delta n =
        deningerGammaSixReflectedShellWeight delta n) :
    delta = 0 := by
  let lam := deningerGammaSixShellEigenvalue 0
  have hlam : 0 < lam := by
    dsimp [lam, deningerGammaSixShellEigenvalue]
    positivity
  have hzero := htransport 0
  have hwold := htransport (deningerGammaSixWoldCoordinate 0)
  change c * lam ^ (1 - delta) = lam ^ (1 + delta) at hzero
  change c * deningerGammaSixShellEigenvalue (deningerGammaSixWoldCoordinate 0) ^
      (1 - delta) =
    deningerGammaSixShellEigenvalue (deningerGammaSixWoldCoordinate 0) ^
      (1 + delta) at hwold
  rw [deningerGammaSixShellEigenvalue_wold] at hwold
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6) hlam.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6) hlam.le] at hwold
  have hpow : (1 / 6 : ℝ) ^ (1 - delta) = (1 / 6 : ℝ) ^ (1 + delta) := by
    have hlamPlus : 0 < lam ^ (1 + delta) := Real.rpow_pos_of_pos hlam _
    apply (mul_right_cancel₀ hlamPlus.ne')
    calc
      (1 / 6 : ℝ) ^ (1 - delta) * lam ^ (1 + delta) =
          (1 / 6 : ℝ) ^ (1 - delta) * (c * lam ^ (1 - delta)) := by rw [hzero]
      _ = c * ((1 / 6 : ℝ) ^ (1 - delta) * lam ^ (1 - delta)) := by ring
      _ = (1 / 6 : ℝ) ^ (1 + delta) * lam ^ (1 + delta) := hwold
      _ = (1 / 6 : ℝ) ^ (1 + delta) * lam ^ (1 + delta) := rfl
  have hexp : 1 - delta = 1 + delta :=
    (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 1 / 6)
      (by norm_num : (1 / 6 : ℝ) ≠ 1)).mp hpow
  linarith

/-- Complete classification of coordinate-independent shell transports. -/
theorem deningerGammaSix_constantScalarShellTransport_iff
    (c delta : ℝ) :
    (∀ n : ℕ,
      c * deningerGammaSixForwardShellWeight delta n =
        deningerGammaSixReflectedShellWeight delta n) ↔
      c = 1 ∧ delta = 0 := by
  constructor
  · intro htransport
    have hdelta := deningerGammaSix_constantScalarShellTransport_forces_neutral htransport
    subst delta
    have hzero := htransport 0
    simp only [deningerGammaSixForwardShellWeight,
      deningerGammaSixReflectedShellWeight, sub_zero, add_zero,
      Real.rpow_one] at hzero
    have hlam := deningerGammaSixShellEigenvalue_pos 0
    constructor
    · nlinarith
    · rfl
  · rintro ⟨rfl, rfl⟩ n
    simp [deningerGammaSixForwardShellWeight,
      deningerGammaSixReflectedShellWeight]

/-- Global isometry of the literal completed-exponent blow-up transport is
equivalent to RH. -/
theorem riemannHypothesis_iff_deningerExceptionalCoefficient_isometric :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        ‖deningerExponentExceptionalLineReflectionCoefficient rho‖ = 1 := by
  constructor
  · intro hRH rho
    exact
      (norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro hisometry
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hrho
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hrho⟩
    exact
      (norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff support).1
        (hisometry support)

/-- **Exceptional/Gamma-six Frankenstein criterion.**  RH is exactly the
statement that the one source-forced exceptional coefficient transports both
Gamma-six shell orientations at every retained divisor and every shell grade.
The reverse implication uses only one coordinate and its Wold successor. -/
theorem riemannHypothesis_iff_deningerExceptionalCoefficient_transportsGammaSixShells :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∀ n : ℕ,
        ‖deningerExponentExceptionalLineReflectionCoefficient rho‖ *
            deningerGammaSixForwardShellWeight
              (2 * (rho : ℂ).re - 1) n =
          deningerGammaSixReflectedShellWeight
              (2 * (rho : ℂ).re - 1) n := by
  constructor
  · intro hRH rho n
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    have hnorm :=
      (norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff rho).2 hre
    rw [hnorm, hre]
    norm_num [deningerGammaSixForwardShellWeight,
      deningerGammaSixReflectedShellWeight]
  · intro htransport
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hrho
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hrho⟩
    have hdelta := deningerGammaSix_constantScalarShellTransport_forces_neutral
      (htransport support)
    change 2 * rho.re - 1 = 0 at hdelta
    linarith

end

end RHTower
