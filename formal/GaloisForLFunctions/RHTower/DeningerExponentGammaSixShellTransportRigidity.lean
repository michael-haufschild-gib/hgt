import GaloisForLFunctions.RHTower.DeningerExponentLineReflectionBlowupTransport
import GaloisForLFunctions.RHTower.DeningerGammaSixShellPrincipalIdeal
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixTameReaderTransgression

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

Both the exceptional coefficient and shell reflection carrier are explicit
two-sheet coboundaries.  Their reflection holonomy is therefore gauge-trivial;
the surviving invariant is mixed reflection--Wold curvature
`(1/6)^(2*delta)`, exactly `exp(-2*a)` in the physical cyclic-character
coordinate `a`.

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

/-- A canonical nonzero gauge on the exceptional divisor support. -/
def deningerExponentExceptionalReflectionGauge
    (rho : XiDivisorSupport) : ℂ := ((rho : ℂ))⁻¹

/-- The exceptional reflection coefficient is a literal two-sheet
coboundary.  Reflection covariance by itself therefore has no gauge-invariant
horizontal holonomy. -/
theorem deningerExponentExceptionalLineReflectionCoefficient_eq_gaugeCoboundary
    (rho : XiDivisorSupport) :
    deningerExponentExceptionalLineReflectionCoefficient rho =
      (starRingEnd ℂ) (deningerExponentExceptionalReflectionGauge rho) /
        deningerExponentExceptionalReflectionGauge (xiZeroLineConjEquiv rho) := by
  have hrho : (rho : ℂ) ≠ 0 := xiDivisorSupport_ne_zero rho
  have hsigma :
      ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) ≠ 0 :=
    xiDivisorSupport_lineReflection_ne_zero rho
  rw [deningerExponentExceptionalLineReflectionCoefficient,
    deningerExponentExceptionalReflectionGauge,
    deningerExponentExceptionalReflectionGauge, map_inv₀]
  field_simp [hrho, hsigma]

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

/-- Half-gauge whose reflection coboundary is the shell carrier. -/
def deningerGammaSixShellReflectionHalfGauge (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ delta

/-- Mixed reflection--Wold curvature.  This is the gauge-invariant obstruction
left after trivializing the two-sheet reflection cocycle. -/
def deningerGammaSixReflectionWoldCurvature (delta : ℝ) : ℝ :=
  (1 / 6 : ℝ) ^ (2 * delta)

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

/-- The shell reflection multiplier is itself a two-sheet coboundary: after
multiplying the reflected half-gauge it becomes the forward half-gauge. -/
theorem deningerGammaSixShellReflectionMultiplier_mul_reflectedHalfGauge
    (delta : ℝ) (n : ℕ) :
    deningerGammaSixShellReflectionMultiplier delta n *
        deningerGammaSixShellReflectionHalfGauge (-delta) n =
      deningerGammaSixShellReflectionHalfGauge delta n := by
  rw [deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixShellReflectionHalfGauge,
    deningerGammaSixShellReflectionHalfGauge,
    ← Real.rpow_add (deningerGammaSixShellEigenvalue_pos n)]
  congr 1
  ring

/-- Wold scaling of the half-gauge. -/
theorem deningerGammaSixShellReflectionHalfGauge_wold
    (delta : ℝ) (n : ℕ) :
    deningerGammaSixShellReflectionHalfGauge delta
        (deningerGammaSixWoldCoordinate n) =
      (1 / 6 : ℝ) ^ delta *
        deningerGammaSixShellReflectionHalfGauge delta n := by
  rw [deningerGammaSixShellReflectionHalfGauge,
    deningerGammaSixShellReflectionHalfGauge,
    deningerGammaSixShellEigenvalue_wold,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (deningerGammaSixShellEigenvalue_nonneg n)]

/-- Mixed curvature is trivial exactly at neutral horizontal grade. -/
theorem deningerGammaSixReflectionWoldCurvature_eq_one_iff
    (delta : ℝ) :
    deningerGammaSixReflectionWoldCurvature delta = 1 ↔ delta = 0 := by
  constructor
  · intro hcurvature
    have hexp : 2 * delta = 0 := by
      apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 1 / 6)
        (by norm_num : (1 / 6 : ℝ) ≠ 1)).mp
      simpa [deningerGammaSixReflectionWoldCurvature] using hcurvature
    linarith
  · rintro rfl
    simp [deningerGammaSixReflectionWoldCurvature]

/-- The mixed shell curvature is the inverse-square exponential of the
existing physical cyclic-character parameter.  This is the exact coordinate
change between Wold drift and the Beck--Chevalley anomaly. -/
theorem deningerGammaSixReflectionWoldCurvature_eq_exp_neg_two_physicalParameter
    (s : ℂ) :
    deningerGammaSixReflectionWoldCurvature (2 * s.re - 1) =
      Real.exp (-2 * sourceHorizontalGammaSixPhysicalCharacterParameter s) := by
  rw [deningerGammaSixReflectionWoldCurvature,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 6),
    sourceHorizontalGammaSixPhysicalCharacterParameter]
  have hlog : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
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
      deningerGammaSixReflectionWoldCurvature delta *
        deningerGammaSixShellReflectionMultiplier delta n := by
  rw [deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixShellReflectionMultiplier,
    deningerGammaSixReflectionWoldCurvature,
    deningerGammaSixShellEigenvalue_wold,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (deningerGammaSixShellEigenvalue_nonneg n)]

/-- The unique coefficient-faithful shell carrier is stationary under the
source Wold clock exactly at neutral horizontal grade. -/
theorem deningerGammaSixShellReflectionMultiplier_wold_stationary_iff
    (delta : ℝ) :
    (∀ n : ℕ,
      deningerGammaSixShellReflectionMultiplier delta
          (deningerGammaSixWoldCoordinate n) =
        deningerGammaSixShellReflectionMultiplier delta n) ↔
      delta = 0 := by
  constructor
  · intro hstationary
    have hstep := hstationary 0
    rw [deningerGammaSixShellReflectionMultiplier_wold] at hstep
    have hmultiplier :
        0 < deningerGammaSixShellReflectionMultiplier delta 0 :=
      Real.rpow_pos_of_pos (deningerGammaSixShellEigenvalue_pos 0) _
    have hfactor : (1 / 6 : ℝ) ^ (2 * delta) = 1 := by
      apply (mul_right_cancel₀ hmultiplier.ne')
      simpa [deningerGammaSixReflectionWoldCurvature] using hstep
    have hexp : 2 * delta = 0 := by
      apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 1 / 6)
        (by norm_num : (1 / 6 : ℝ) ≠ 1)).mp
      simpa using hfactor
    linarith
  · rintro rfl n
    simp [deningerGammaSixShellReflectionMultiplier]

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

/-- **Wold-stationary Frankenstein endpoint.**  RH is equivalent to the
unique shell-orientation carrier being invariant under the literal Gamma-six
source clock at every Xi divisor.  This removes the arbitrary scalar from the
preceding endpoint and isolates the missing producer as a stationarity law. -/
theorem riemannHypothesis_iff_deningerGammaSixShellReflectionMultiplier_wold_stationary :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∀ n : ℕ,
        deningerGammaSixShellReflectionMultiplier
            (2 * (rho : ℂ).re - 1)
            (deningerGammaSixWoldCoordinate n) =
          deningerGammaSixShellReflectionMultiplier
            (2 * (rho : ℂ).re - 1) n := by
  constructor
  · intro hRH rho
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    apply (deningerGammaSixShellReflectionMultiplier_wold_stationary_iff
      (2 * (rho : ℂ).re - 1)).2
    rw [hre]
    norm_num
  · intro hstationary
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hrho
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hrho⟩
    have hdelta :=
      (deningerGammaSixShellReflectionMultiplier_wold_stationary_iff
        (2 * (support : ℂ).re - 1)).1 (hstationary support)
    change 2 * rho.re - 1 = 0 at hdelta
    linarith

/-! ## Cross-presentation obstruction dictionary -/

/-- Shell Wold stationarity is exactly fixed-character cyclic descent for the
same multiplicity-labelled Xi copy.  Hence the two source presentations do not
provide independent equations. -/
theorem deningerGammaSixShellReflectionMultiplier_wold_stationary_iff_cyclicPhysicalCharacterDescends
    (q : XiZeroCopy) :
    (∀ n : ℕ,
      deningerGammaSixShellReflectionMultiplier
          (primeDepthBVWoldXiCenteredRate q.1)
          (deningerGammaSixWoldCoordinate n) =
        deningerGammaSixShellReflectionMultiplier
          (primeDepthBVWoldXiCenteredRate q.1) n) ↔
      SourceZeroGammaSixCyclicPhysicalCharacterDescends q := by
  rw [deningerGammaSixShellReflectionMultiplier_wold_stationary_iff,
    sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Isometry of the literal exceptional blow-up coefficient is also exactly
the same cyclic descent condition. -/
theorem deningerExceptionalCoefficient_isometric_iff_cyclicPhysicalCharacterDescends
    (q : XiZeroCopy) :
    ‖deningerExponentExceptionalLineReflectionCoefficient q.1‖ = 1 ↔
      SourceZeroGammaSixCyclicPhysicalCharacterDescends q := by
  rw [norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff,
    sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff]

/-- **Three-presentation no-duplication law.**  Literal blow-up isometry,
coefficient-faithful shell transport, and fixed-reader cyclic descent coincide
pointwise.  Combining them without a target-side defect absorption theorem
cannot create a second constraint. -/
theorem deningerExceptional_shellTransport_cyclicDescent_tfae
    (q : XiZeroCopy) :
    List.TFAE
      [‖deningerExponentExceptionalLineReflectionCoefficient q.1‖ = 1,
       ∀ n : ℕ,
        ‖deningerExponentExceptionalLineReflectionCoefficient q.1‖ *
            deningerGammaSixForwardShellWeight
              (primeDepthBVWoldXiCenteredRate q.1) n =
          deningerGammaSixReflectedShellWeight
              (primeDepthBVWoldXiCenteredRate q.1) n,
       SourceZeroGammaSixCyclicPhysicalCharacterDescends q] := by
  tfae_have 1 → 2 := by
    intro hisometry n
    have hline :=
      (norm_deningerExponentExceptionalLineReflectionCoefficient_eq_one_iff q.1).1
        hisometry
    rw [hisometry]
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    rw [hrate]
    simp [deningerGammaSixForwardShellWeight,
      deningerGammaSixReflectedShellWeight]
  tfae_have 2 → 3 := by
    intro htransport
    have hrate := deningerGammaSix_constantScalarShellTransport_forces_neutral
      htransport
    apply (sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff q).2
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
  tfae_have 3 → 1 := by
    exact deningerExceptionalCoefficient_isometric_iff_cyclicPhysicalCharacterDescends q |>.2
  tfae_finish

end

end RHTower
