import GaloisForLFunctions.HTGeometry.PolynomialODEJetC5FixedActionSeamClosure

/-!
# Exact completed C5 slope: optimized cumulants, chamber and flow no-go

This module replaces recursive Lie-derivative expansion by explicit division-free cumulant
numerators through order eight.  It constructs the odd-corrected derivative of the exact completed
C5 orientation, proves its seam factorization, and transports it through the Lyapunov and
source-positive charts. Integer cumulant coefficients are additive scalar multiples, and the
source Lie operator is packaged as a derivation, so high-order proofs use exact Leibniz laws rather
than recursive polynomial expansion.

The intended RH chain was: strict source-positive chamber inequalities force corrected-slope
positivity; corrected-slope positivity forces global growth of exact completed C5 orientation;
that supplies local direct fixed-action Jacobian orientation at every centre; compact/tail assembly
crosses the seam/rank-four Ptolemy wall; cofinal no-escape yields CLG/TTF or Weil positivity and RH.

The first no-go kills the chamber implication: even with every source-positive coordinate and the
reconstructed gap strictly positive, corrected completed C5 slope can be negative. The stronger
no-go proves the exact covariant boundary law and exhibits an orientation seam with positive mass
and gap, inward `U,B` velocities, zero `Q` velocity, but strictly negative orientation derivative.
The third no-go perturbs that seam into the strict adapted physical thin-clock cone
`5B < U+3B < 6B`. Thus neither chamber signs, static clock localization, nor the autonomous field
alone supply a uniform first-contact barrier. Positive survivor: centre-anchored physical-orbit
incidence, or a stronger dynamical invariant, is indispensable.
-/

open Complex Real

namespace HTGeometry

noncomputable section

private theorem continuousAt_mvPolynomial_eval_curve
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) (g : ι → ℝ → ℂ) (x : ℝ)
    (hg : ∀ j, ContinuousAt (g j) x) :
    ContinuousAt (fun s => MvPolynomial.eval (fun j => g j s) P) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => a) x)
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          fun s => MvPolynomial.eval (fun j => g j s) p +
            MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hf]
      convert hp.add hq using 1
      ext s
      rfl
  | mul_X p i hp =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s)
          (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval (fun j => g j s) p * g i s := by
        funext s
        simp
      rw [hf]
      convert hp.mul (hg i) using 1
      ext s
      rfl

/-- Division-free numerator `f₀² (log f)''`. -/
def clearedLogJetTwo {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 * f 2 - f 1 ^ 2

/-- Division-free numerator `f₀³ (log f)'''`. -/
def clearedLogJetThree {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 2 * f 3 - 3 • (f 0 * f 1 * f 2) + 2 • f 1 ^ 3

/-- Division-free numerator `f₀⁴ (log f)⁽⁴⁾`. -/
def clearedLogJetFour {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 3 * f 4 - 4 • (f 0 ^ 2 * f 1 * f 3) -
    3 • (f 0 ^ 2 * f 2 ^ 2) + 12 • (f 0 * f 1 ^ 2 * f 2) - 6 • f 1 ^ 4

/-- Division-free numerator `f₀⁵ (log f)⁽⁵⁾`. -/
def clearedLogJetFive {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 4 * f 5 - 5 • (f 0 ^ 3 * f 1 * f 4) -
    10 • (f 0 ^ 3 * f 2 * f 3) + 20 • (f 0 ^ 2 * f 1 ^ 2 * f 3) +
    30 • (f 0 ^ 2 * f 1 * f 2 ^ 2) - 60 • (f 0 * f 1 ^ 3 * f 2) +
    24 • f 1 ^ 5

/-- Division-free numerator `f₀⁶ (log f)⁽⁶⁾`. -/
def clearedLogJetSix {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 5 * f 6 - 6 • (f 0 ^ 4 * f 1 * f 5) -
    15 • (f 0 ^ 4 * f 2 * f 4) - 10 • (f 0 ^ 4 * f 3 ^ 2) +
    30 • (f 0 ^ 3 * f 1 ^ 2 * f 4) + 120 • (f 0 ^ 3 * f 1 * f 2 * f 3) +
    30 • (f 0 ^ 3 * f 2 ^ 3) - 120 • (f 0 ^ 2 * f 1 ^ 3 * f 3) -
    270 • (f 0 ^ 2 * f 1 ^ 2 * f 2 ^ 2) + 360 • (f 0 * f 1 ^ 4 * f 2) -
    120 • f 1 ^ 6

/-- Division-free numerator `f₀⁷ (log f)⁽⁷⁾`. -/
def clearedLogJetSeven {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 6 * f 7 - 7 • (f 0 ^ 5 * f 1 * f 6) -
    21 • (f 0 ^ 5 * f 2 * f 5) + 42 • (f 0 ^ 4 * f 1 ^ 2 * f 5) -
    35 • (f 0 ^ 5 * f 3 * f 4) + 210 • (f 0 ^ 4 * f 1 * f 2 * f 4) -
    210 • (f 0 ^ 3 * f 1 ^ 3 * f 4) + 140 • (f 0 ^ 4 * f 1 * f 3 ^ 2) +
    210 • (f 0 ^ 4 * f 2 ^ 2 * f 3) - 1260 • (f 0 ^ 3 * f 1 ^ 2 * f 2 * f 3) +
    840 • (f 0 ^ 2 * f 1 ^ 4 * f 3) - 630 • (f 0 ^ 3 * f 1 * f 2 ^ 3) +
    2520 • (f 0 ^ 2 * f 1 ^ 3 * f 2 ^ 2) - 2520 • (f 0 * f 1 ^ 5 * f 2) +
    720 • f 1 ^ 7

/-- Division-free numerator `f₀⁸ (log f)⁽⁸⁾`. -/
def clearedLogJetEight {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  f 0 ^ 7 * f 8 - 8 • (f 0 ^ 6 * f 1 * f 7) -
    28 • (f 0 ^ 6 * f 2 * f 6) + 56 • (f 0 ^ 5 * f 1 ^ 2 * f 6) -
    56 • (f 0 ^ 6 * f 3 * f 5) + 336 • (f 0 ^ 5 * f 1 * f 2 * f 5) -
    336 • (f 0 ^ 4 * f 1 ^ 3 * f 5) - 35 • (f 0 ^ 6 * f 4 ^ 2) +
    560 • (f 0 ^ 5 * f 1 * f 3 * f 4) + 420 • (f 0 ^ 5 * f 2 ^ 2 * f 4) -
    2520 • (f 0 ^ 4 * f 1 ^ 2 * f 2 * f 4) + 1680 • (f 0 ^ 3 * f 1 ^ 4 * f 4) +
    560 • (f 0 ^ 5 * f 2 * f 3 ^ 2) - 1680 • (f 0 ^ 4 * f 1 ^ 2 * f 3 ^ 2) -
    5040 • (f 0 ^ 4 * f 1 * f 2 ^ 2 * f 3) +
    13440 • (f 0 ^ 3 * f 1 ^ 3 * f 2 * f 3) -
    6720 • (f 0 ^ 2 * f 1 ^ 5 * f 3) - 630 • (f 0 ^ 4 * f 2 ^ 4) +
    10080 • (f 0 ^ 3 * f 1 ^ 2 * f 2 ^ 3) -
    25200 • (f 0 ^ 2 * f 1 ^ 4 * f 2 ^ 2) +
    20160 • (f 0 * f 1 ^ 6 * f 2) - 5040 • f 1 ^ 8

/-- Cleared exact derivative of the ninth-order completed C5 seam orientation. -/
def c5ExactCompletedSeamSlopeCleared {R : Type*} [CommRing R]
    (p2 p3 p4 p5 p6 p7 p8 : R) : R :=
  -p2 ^ 2 * p8 + 5 * p2 * p4 * p6 - 4 * p4 ^ 3 - 18 * p2 ^ 3 * p6 +
    36 * p2 ^ 2 * p4 ^ 2 + p2 * p3 * p7 - 6 * p4 * p3 * p5 +
    2 * p2 * p5 ^ 2 + 3 * p6 * p3 ^ 2 - 18 * p2 ^ 2 * p3 * p5 +
    72 * p2 * p4 * p3 ^ 2

/-- Four-state modular polynomial for exact odd-corrected C5 orientation slope. -/
def modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial :
    ModularThetaODEPolynomial :=
  let f := modularThetaODENormalizedSourceJet
  c5ExactCompletedSeamSlopeCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)
    (clearedLogJetEight f)

/-- On every algebraic seam, exact odd-corrected slope is source-sixth-power times the existing
direct fixed-action C5 seam polynomial. -/
theorem eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_seam
    (R : ℂ) :
    MvPolynomial.eval (modularThetaODESeamState R)
        modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial =
      MvPolynomial.eval (modularThetaODESeamState R)
          (modularThetaODENormalizedSourceJet 0) ^ 6 *
        MvPolynomial.eval (modularThetaODESeamState R)
          modularThetaODENormalizedC5FixedActionSeamPolynomial := by
  have h1 := eval_modularThetaODESourceJet_seam_odd_zero R 0
  have h3 := eval_modularThetaODESourceJet_seam_odd_zero R 1
  have h5 := eval_modularThetaODESourceJet_seam_odd_zero R 2
  have h7 := eval_modularThetaODESourceJet_seam_odd_zero R 3
  have hnorm (n : ℕ) :
      MvPolynomial.eval (modularThetaODESeamState R)
          (modularThetaODENormalizedSourceJet n) =
        MvPolynomial.eval (modularThetaODESeamState R)
          (modularThetaODESourceJet n) := by
    have hfac := congrArg (MvPolynomial.eval (modularThetaODESeamState R))
      (modularThetaODESourceJet_eq_X_H_mul_normalized n)
    simpa [modularThetaODESeamState] using hfac.symm
  unfold modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial
    modularThetaODENormalizedC5FixedActionSeamPolynomial
    c5ExactCompletedSeamSlopeCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
    clearedLogJetEight
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_ofNat, map_nsmul]
  rw [hnorm 0, hnorm 1, hnorm 2, hnorm 3, hnorm 4, hnorm 5, hnorm 6,
    hnorm 7, hnorm 8]
  rw [h1, h3, h5, h7]
  norm_num only [mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
    zero_pow, pow_succ]
  ring

/-- The exact corrected C5 slope polynomial is negative on a source-positive universal seam. -/
theorem eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_ten_re_neg :
    (MvPolynomial.eval (modularThetaODESeamState 10)
      modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  rw [eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_seam,
    eval_modularThetaODENormalizedC5FixedActionSeamPolynomial_seam]
  rw [eval_modularThetaODENormalizedSourceJet_zero]
  norm_num [modularThetaODESeamState, modularThetaC5FixedActionSeamPolynomial]

/-- Lyapunov-chart exact corrected C5 slope polynomial. -/
def modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial :
    ModularThetaLyapunovPolynomial :=
  let f := modularThetaLyapunovNormalizedSourceJet
  c5ExactCompletedSeamSlopeCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)
    (clearedLogJetEight f)

/-- Source-positive-chart exact corrected C5 slope polynomial. -/
def modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial :
    ModularThetaSourcePositivePolynomial :=
  let f := modularThetaSourcePositiveNormalizedSourceJet
  c5ExactCompletedSeamSlopeCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)
    (clearedLogJetEight f)

/-- Four-state quotient transports exact corrected C5 slope without expansion. -/
theorem modularThetaGeneralLyapunov_c5ExactCompletedSeamSlopePolynomial :
    modularThetaGeneralLyapunovPullback
        modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial =
      modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial := by
  unfold modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial
    modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial
    c5ExactCompletedSeamSlopeCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
    clearedLogJetEight
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_ofNat, map_nsmul]
  rw [modularThetaGeneralLyapunov_normalizedSourceJet 0,
    modularThetaGeneralLyapunov_normalizedSourceJet 1,
    modularThetaGeneralLyapunov_normalizedSourceJet 2,
    modularThetaGeneralLyapunov_normalizedSourceJet 3,
    modularThetaGeneralLyapunov_normalizedSourceJet 4,
    modularThetaGeneralLyapunov_normalizedSourceJet 5,
    modularThetaGeneralLyapunov_normalizedSourceJet 6,
    modularThetaGeneralLyapunov_normalizedSourceJet 7,
    modularThetaGeneralLyapunov_normalizedSourceJet 8]

/-- Source-positive chart transports exact corrected C5 slope without expansion. -/
theorem modularThetaSourcePositiveChart_c5ExactCompletedSeamSlopePolynomial :
    modularThetaSourcePositiveChartPullback
        modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial =
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial := by
  unfold modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial
    modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial
    c5ExactCompletedSeamSlopeCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
    clearedLogJetEight
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_ofNat, map_nsmul]
  rw [modularThetaSourcePositiveChart_sourceJet 0,
    modularThetaSourcePositiveChart_sourceJet 1,
    modularThetaSourcePositiveChart_sourceJet 2,
    modularThetaSourcePositiveChart_sourceJet 3,
    modularThetaSourcePositiveChart_sourceJet 4,
    modularThetaSourcePositiveChart_sourceJet 5,
    modularThetaSourcePositiveChart_sourceJet 6,
    modularThetaSourcePositiveChart_sourceJet 7,
    modularThetaSourcePositiveChart_sourceJet 8]

/-- Corrected C5 slope is negative at source-positive seam scale `X=100`. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_hundred_re_neg :
    (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  rw [← modularThetaSourcePositiveChart_c5ExactCompletedSeamSlopePolynomial]
  have hstate : modularThetaSourcePositiveSeamState 100 =
      modularThetaSourcePositiveSeamState ((10 : ℝ) ^ 2) := by norm_num
  rw [hstate]
  rw [eval_modularThetaSourcePositiveChartPullback_seam]
  rw [← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_c5ExactCompletedSeamSlopePolynomial]
  exact eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_ten_re_neg

private theorem eventually_eval_c5ExactCompletedSeamSlope_neg_of_tendsto_hundred
    (g : ModularThetaSourcePositiveState → ℝ → ℂ)
    (hg : ∀ i, ContinuousAt (g i) 0)
    (hgzero : (fun i => g i 0) = modularThetaSourcePositiveSeamState 100) :
    ∀ᶠ ε in nhds (0 : ℝ),
      (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  have hcomplex : ContinuousAt
      (fun ε => MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial) 0 :=
    continuousAt_mvPolynomial_eval_curve
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial g 0 hg
  have hreal : ContinuousAt
      (fun ε => (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re) 0 := by
    change ContinuousAt
      (Complex.re ∘ fun ε => MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial) 0
    exact Complex.continuous_re.continuousAt.comp hcomplex
  have hzero :
      (MvPolynomial.eval (fun i => g i 0)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
    rw [hgzero]
    exact eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_hundred_re_neg
  exact hreal.eventually (Iio_mem_nhds hzero)

/-- A strict source-positive chamber perturbation of the negative `X=100` seam. -/
def modularThetaSourcePositiveC5SlopeChamberPerturbation (ε : ℝ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => ε
  | .B => ε
  | .Q => 47 / 8

/-- Strict positivity of all source-positive coordinates and reconstructed gap does not force
positivity of the exact odd-corrected completed C5 seam slope. -/
theorem exists_strictSourcePositiveChamber_eval_c5ExactCompletedSeamSlope_neg :
    ∃ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) ∧
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re ∧
      (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  let g : ModularThetaSourcePositiveState → ℝ → ℂ :=
    fun i ε => modularThetaSourcePositiveC5SlopeChamberPerturbation ε i
  have hg : ∀ i, ContinuousAt (g i) 0 := by
    intro i
    cases i
    · simpa [g, modularThetaSourcePositiveC5SlopeChamberPerturbation] using
        Complex.continuous_ofReal.continuousAt
    · simpa [g, modularThetaSourcePositiveC5SlopeChamberPerturbation] using
        Complex.continuous_ofReal.continuousAt
    · simpa [g, modularThetaSourcePositiveC5SlopeChamberPerturbation] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (47 / 8 : ℂ)) 0)
  have hgzero : (fun i => g i 0) = modularThetaSourcePositiveSeamState 100 := by
    funext i
    cases i <;>
      norm_num [g, modularThetaSourcePositiveC5SlopeChamberPerturbation,
        modularThetaSourcePositiveSeamState]
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_eval_c5ExactCompletedSeamSlope_neg_of_tendsto_hundred g hg hgzero)
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := by
    exact lt_min (by linarith) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := by
    exact min_le_right _ _
  have hεδ : ε < δ := by
    have hle : ε ≤ δ / 2 := min_le_left _ _
    linarith
  have hfε :
      (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
    apply hnear
    simpa [Real.dist_eq, abs_of_pos hε] using hεδ
  refine ⟨fun i => g i ε, ?_, ?_, ?_⟩
  · intro i
    cases i <;>
      simp [g, modularThetaSourcePositiveC5SlopeChamberPerturbation, hε]
  · simp only [modularThetaSourcePositiveGap, map_sub, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp [g, modularThetaSourcePositiveC5SlopeChamberPerturbation]
    have hεsq : ((ε : ℂ) ^ 2).re = ε ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [hεsq]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεhalf)]
  · exact hfε

/-- Exact route kill: no universal implication from strict source-positive chamber signs and gap
positivity to positivity of the odd-corrected exact completed C5 slope can hold. -/
theorem not_forall_strictSourcePositiveChamber_c5ExactCompletedSeamSlope_pos :
    ¬ ∀ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) →
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re →
      0 < (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re := by
  intro h
  obtain ⟨v, hv, hgap, hslope⟩ :=
    exists_strictSourcePositiveChamber_eval_c5ExactCompletedSeamSlope_neg
  linarith [h v hv hgap]

/-- Perturb the negative `X=100` seam into the adapted thin-clock cone
`5B < U+3B < 6B`. -/
def modularThetaSourcePositiveC5SlopeThinClockPerturbation (ε : ℝ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => (5 / 2 : ℝ) * ε
  | .B => ε
  | .Q => 47 / 8

/-- The strict adapted thin-clock cone still meets the negative corrected-C5-slope chamber.

On the physical orbit the corpus identities `r=Rz`, `B=R(z-v)/3` turn
`(2/5)z<v<(1/2)z` into `5B<r<6B`, where `r=U+3B`.  This theorem proves that those
static inequalities, even together with positivity of every source coordinate and reconstructed
gap, do not force the first-contact slope sign. -/
theorem exists_strictSourcePositiveThinClockCone_eval_c5ExactCompletedSeamSlope_neg :
    ∃ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) ∧
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re ∧
      5 * (v .B).re < (v .U).re + 3 * (v .B).re ∧
      (v .U).re + 3 * (v .B).re < 6 * (v .B).re ∧
      (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
  let g : ModularThetaSourcePositiveState → ℝ → ℂ :=
    fun i ε => modularThetaSourcePositiveC5SlopeThinClockPerturbation ε i
  have hg : ∀ i, ContinuousAt (g i) 0 := by
    intro i
    cases i
    · simpa [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation] using
        Complex.continuous_ofReal.continuousAt.const_mul (5 / 2 : ℂ)
    · simpa [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation] using
        Complex.continuous_ofReal.continuousAt
    · simpa [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (47 / 8 : ℂ)) 0)
  have hgzero : (fun i => g i 0) = modularThetaSourcePositiveSeamState 100 := by
    funext i
    cases i <;>
      norm_num [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation,
        modularThetaSourcePositiveSeamState]
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_eval_c5ExactCompletedSeamSlope_neg_of_tendsto_hundred g hg hgzero)
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε < δ := by
    have hle : ε ≤ δ / 2 := min_le_left _ _
    linarith
  have hslope :
      (MvPolynomial.eval (fun i => g i ε)
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re < 0 := by
    apply hnear
    simpa [Real.dist_eq, abs_of_pos hε] using hεδ
  refine ⟨fun i => g i ε, ?_, ?_, ?_, ?_, hslope⟩
  · intro i
    cases i <;>
      simp [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation, hε]
  · simp only [modularThetaSourcePositiveGap, map_sub, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation]
    have hεsq : ((ε : ℂ) ^ 2).re = ε ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [hεsq]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεhalf)]
  · simp [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation]
    linarith
  · simp [g, modularThetaSourcePositiveC5SlopeThinClockPerturbation]
    linarith

/-- Exact route kill: physical thin-clock inequalities alone cannot supply the corrected C5
first-contact barrier, so any surviving proof must use a genuinely dynamical orbit invariant. -/
theorem not_forall_strictSourcePositiveThinClockCone_c5ExactCompletedSeamSlope_pos :
    ¬ ∀ v : ModularThetaSourcePositiveState → ℂ,
      (∀ i, 0 < (v i).re) →
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re →
      5 * (v .B).re < (v .U).re + 3 * (v .B).re →
      (v .U).re + 3 * (v .B).re < 6 * (v .B).re →
      0 < (MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial).re := by
  intro h
  obtain ⟨v, hv, hgap, hlower, hupper, hslope⟩ :=
    exists_strictSourcePositiveThinClockCone_eval_c5ExactCompletedSeamSlope_neg
  linarith [h v hv hgap hlower hupper]

private theorem modularThetaSourcePositiveLie_normalizedSourceJet (n : ℕ) :
    modularThetaSourcePositiveLie
        (modularThetaSourcePositiveNormalizedSourceJet n) =
      modularThetaSourcePositiveNormalizedSourceJet (n + 1) -
        MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B *
          modularThetaSourcePositiveNormalizedSourceJet n := by
  rw [modularThetaSourcePositiveNormalizedSourceJet]
  unfold modularThetaSourcePositiveNormalizedLie
  ring

private def modularThetaSourcePositiveLieLinearMap :
    ModularThetaSourcePositivePolynomial →ₗ[ℂ]
      ModularThetaSourcePositivePolynomial :=
  ∑ i, (MvPolynomial.pderiv i).toLinearMap.smulRight
    (modularThetaSourcePositiveVectorField i)

private theorem modularThetaSourcePositiveLieLinearMap_apply
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveLieLinearMap P = modularThetaSourcePositiveLie P := by
  unfold modularThetaSourcePositiveLieLinearMap modularThetaSourcePositiveLie
  rfl

/-- The source-positive polynomial Lie operator, packaged as a genuine derivation. -/
def modularThetaSourcePositiveLieDerivation : Derivation ℂ
    ModularThetaSourcePositivePolynomial ModularThetaSourcePositivePolynomial :=
  Derivation.mk' modularThetaSourcePositiveLieLinearMap (by
    intro P Q
    rw [modularThetaSourcePositiveLieLinearMap_apply,
      modularThetaSourcePositiveLieLinearMap_apply,
      modularThetaSourcePositiveLieLinearMap_apply,
      modularThetaSourcePositiveLie_mul]
    simp only [smul_eq_mul]
    ring)

@[simp] theorem modularThetaSourcePositiveLieDerivation_apply
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveLieDerivation P = modularThetaSourcePositiveLie P := by
  unfold modularThetaSourcePositiveLieDerivation
  exact modularThetaSourcePositiveLieLinearMap_apply P

private theorem modularThetaSourcePositiveLie_clearedLogJetTwo :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetTwo f) =
      clearedLogJetThree f +
        2 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetTwo f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetTwo clearedLogJetThree
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2]
  ring

private theorem modularThetaSourcePositiveLie_clearedLogJetThree :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetThree f) =
      clearedLogJetFour f +
        3 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetThree f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetThree clearedLogJetFour
  simp only [map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2,
    modularThetaSourcePositiveLie_normalizedSourceJet 3]
  ring

private theorem modularThetaSourcePositiveLie_clearedLogJetFour :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetFour f) =
      clearedLogJetFive f +
        4 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetFour f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetFour clearedLogJetFive
  simp only [map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2,
    modularThetaSourcePositiveLie_normalizedSourceJet 3,
    modularThetaSourcePositiveLie_normalizedSourceJet 4]
  ring

private theorem modularThetaSourcePositiveLie_clearedLogJetFive :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetFive f) =
      clearedLogJetSix f +
        5 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetFive f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetFive clearedLogJetSix
  simp only [map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2,
    modularThetaSourcePositiveLie_normalizedSourceJet 3,
    modularThetaSourcePositiveLie_normalizedSourceJet 4,
    modularThetaSourcePositiveLie_normalizedSourceJet 5]
  ring

private theorem modularThetaSourcePositiveLie_clearedLogJetSix :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetSix f) =
      clearedLogJetSeven f +
        6 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetSix f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetSix clearedLogJetSeven
  simp only [map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2,
    modularThetaSourcePositiveLie_normalizedSourceJet 3,
    modularThetaSourcePositiveLie_normalizedSourceJet 4,
    modularThetaSourcePositiveLie_normalizedSourceJet 5,
    modularThetaSourcePositiveLie_normalizedSourceJet 6]
  ring

private theorem modularThetaSourcePositiveLie_clearedLogJetSeven :
    let f := modularThetaSourcePositiveNormalizedSourceJet
    f 0 * modularThetaSourcePositiveLie (clearedLogJetSeven f) =
      clearedLogJetEight f +
        7 *
          (f 1 - MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * f 0) *
          clearedLogJetSeven f := by
  dsimp only
  rw [← modularThetaSourcePositiveLieDerivation_apply]
  unfold clearedLogJetSeven clearedLogJetEight
  simp only [map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_normalizedSourceJet 0,
    modularThetaSourcePositiveLie_normalizedSourceJet 1,
    modularThetaSourcePositiveLie_normalizedSourceJet 2,
    modularThetaSourcePositiveLie_normalizedSourceJet 3,
    modularThetaSourcePositiveLie_normalizedSourceJet 4,
    modularThetaSourcePositiveLie_normalizedSourceJet 5,
    modularThetaSourcePositiveLie_normalizedSourceJet 6,
    modularThetaSourcePositiveLie_normalizedSourceJet 7]
  ring

/-- Division-free exact completed C5 orientation in cleared log-cumulant coordinates. -/
def c5ExactCompletedSeamOrientationCleared {R : Type*} [CommRing R]
    (p2 p3 p4 p5 p6 p7 : R) : R :=
  -p2 ^ 2 * p7 + 3 • (p2 * p6 * p3) + 2 • (p2 * p4 * p5) -
    4 • (p4 ^ 2 * p3) - 18 • (p2 ^ 3 * p5) + 36 • (p2 ^ 2 * p4 * p3)

/-- Four-state normalized-source polynomial for exact completed C5 orientation. -/
def modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial :
    ModularThetaODEPolynomial :=
  let f := modularThetaODENormalizedSourceJet
  c5ExactCompletedSeamOrientationCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)

/-- Lyapunov-chart polynomial for exact completed C5 orientation. -/
def modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial :
    ModularThetaLyapunovPolynomial :=
  let f := modularThetaLyapunovNormalizedSourceJet
  c5ExactCompletedSeamOrientationCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)

/-- Source-positive polynomial for exact completed C5 orientation. -/
def modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial :
    ModularThetaSourcePositivePolynomial :=
  let f := modularThetaSourcePositiveNormalizedSourceJet
  c5ExactCompletedSeamOrientationCleared
    (clearedLogJetTwo f) (clearedLogJetThree f) (clearedLogJetFour f)
    (clearedLogJetFive f) (clearedLogJetSix f) (clearedLogJetSeven f)

/-- Four-state quotient transports exact completed C5 orientation without expansion. -/
theorem modularThetaGeneralLyapunov_c5ExactCompletedSeamOrientationPolynomial :
    modularThetaGeneralLyapunovPullback
        modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial =
      modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial := by
  unfold modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial
    modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial
    c5ExactCompletedSeamOrientationCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_nsmul]
  rw [modularThetaGeneralLyapunov_normalizedSourceJet 0,
    modularThetaGeneralLyapunov_normalizedSourceJet 1,
    modularThetaGeneralLyapunov_normalizedSourceJet 2,
    modularThetaGeneralLyapunov_normalizedSourceJet 3,
    modularThetaGeneralLyapunov_normalizedSourceJet 4,
    modularThetaGeneralLyapunov_normalizedSourceJet 5,
    modularThetaGeneralLyapunov_normalizedSourceJet 6,
    modularThetaGeneralLyapunov_normalizedSourceJet 7]

/-- Source-positive chart transports exact completed C5 orientation without expansion. -/
theorem modularThetaSourcePositiveChart_c5ExactCompletedSeamOrientationPolynomial :
    modularThetaSourcePositiveChartPullback
        modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial =
      modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial := by
  unfold modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial
    modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial
    c5ExactCompletedSeamOrientationCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_nsmul]
  rw [modularThetaSourcePositiveChart_sourceJet 0,
    modularThetaSourcePositiveChart_sourceJet 1,
    modularThetaSourcePositiveChart_sourceJet 2,
    modularThetaSourcePositiveChart_sourceJet 3,
    modularThetaSourcePositiveChart_sourceJet 4,
    modularThetaSourcePositiveChart_sourceJet 5,
    modularThetaSourcePositiveChart_sourceJet 6,
    modularThetaSourcePositiveChart_sourceJet 7]

/-- Exact completed C5 orientation vanishes on every four-state algebraic seam. -/
theorem eval_modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial_seam
    (R : ℂ) :
    MvPolynomial.eval (modularThetaODESeamState R)
      modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial = 0 := by
  have h1 := eval_modularThetaODESourceJet_seam_odd_zero R 0
  have h3 := eval_modularThetaODESourceJet_seam_odd_zero R 1
  have h5 := eval_modularThetaODESourceJet_seam_odd_zero R 2
  have h7 := eval_modularThetaODESourceJet_seam_odd_zero R 3
  have hnorm (n : ℕ) :
      MvPolynomial.eval (modularThetaODESeamState R)
          (modularThetaODENormalizedSourceJet n) =
        MvPolynomial.eval (modularThetaODESeamState R)
          (modularThetaODESourceJet n) := by
    have hfac := congrArg (MvPolynomial.eval (modularThetaODESeamState R))
      (modularThetaODESourceJet_eq_X_H_mul_normalized n)
    simpa [modularThetaODESeamState] using hfac.symm
  unfold modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial
    c5ExactCompletedSeamOrientationCleared clearedLogJetTwo clearedLogJetThree
    clearedLogJetFour clearedLogJetFive clearedLogJetSix clearedLogJetSeven
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, map_nsmul]
  rw [hnorm 0, hnorm 1, hnorm 2, hnorm 3, hnorm 4, hnorm 5, hnorm 6,
    hnorm 7]
  rw [h1, h3, h5, h7]
  simp only [nsmul_eq_mul]
  ring

/-- The source-positive `X=100` algebraic seam lies exactly on the completed C5 orientation
boundary. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_hundred_eq_zero :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial = 0 := by
  rw [← modularThetaSourcePositiveChart_c5ExactCompletedSeamOrientationPolynomial]
  have hstate : modularThetaSourcePositiveSeamState 100 =
      modularThetaSourcePositiveSeamState ((10 : ℝ) ^ 2) := by norm_num
  rw [hstate, eval_modularThetaSourcePositiveChartPullback_seam]
  rw [← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_c5ExactCompletedSeamOrientationPolynomial,
    eval_modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial_seam]

private def modularThetaSourcePositiveScaledLieLinearMap :
    ModularThetaSourcePositivePolynomial →ₗ[ℂ]
      ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveLieDerivation.toLinearMap.smulRight
    (modularThetaSourcePositiveNormalizedSourceJet 0)

private theorem modularThetaSourcePositiveScaledLieLinearMap_apply
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveScaledLieLinearMap P =
      modularThetaSourcePositiveNormalizedSourceJet 0 *
        modularThetaSourcePositiveLie P := by
  unfold modularThetaSourcePositiveScaledLieLinearMap
  simp only [LinearMap.smulRight_apply, smul_eq_mul]
  change modularThetaSourcePositiveLieLinearMap P *
      modularThetaSourcePositiveNormalizedSourceJet 0 = _
  rw [modularThetaSourcePositiveLieLinearMap_apply]
  ring

/-- Lie derivative scaled by source mass; still a derivation because the coefficient ring is
commutative. This packaging prevents recursive expansion of high cumulants. -/
private def modularThetaSourcePositiveScaledLieDerivation : Derivation ℂ
    ModularThetaSourcePositivePolynomial ModularThetaSourcePositivePolynomial :=
  Derivation.mk' modularThetaSourcePositiveScaledLieLinearMap (by
    intro P Q
    rw [modularThetaSourcePositiveScaledLieLinearMap_apply,
      modularThetaSourcePositiveScaledLieLinearMap_apply,
      modularThetaSourcePositiveScaledLieLinearMap_apply,
      modularThetaSourcePositiveLie_mul]
    simp only [smul_eq_mul]
    ring)

@[simp] private theorem modularThetaSourcePositiveScaledLieDerivation_apply
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveScaledLieDerivation P =
      modularThetaSourcePositiveNormalizedSourceJet 0 *
        modularThetaSourcePositiveLie P := by
  unfold modularThetaSourcePositiveScaledLieDerivation
  exact modularThetaSourcePositiveScaledLieLinearMap_apply P

/-- Exact weight-eleven covariant Lie law. On the orientation boundary the correction term
vanishes, so the physical vector-field derivative has exactly the sign of the corrected C5
slope whenever source mass is positive. -/
theorem modularThetaSourcePositive_c5ExactCompletedSeamOrientation_covariantLie :
    modularThetaSourcePositiveNormalizedSourceJet 0 *
        modularThetaSourcePositiveLie
          modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial =
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial +
        11 *
          (modularThetaSourcePositiveNormalizedSourceJet 1 -
            MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B *
              modularThetaSourcePositiveNormalizedSourceJet 0) *
          modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial := by
  rw [← modularThetaSourcePositiveScaledLieDerivation_apply]
  unfold modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial
    modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial
    c5ExactCompletedSeamOrientationCleared c5ExactCompletedSeamSlopeCleared
  dsimp only
  simp only [map_neg, map_sub, map_add, map_nsmul, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [modularThetaSourcePositiveScaledLieDerivation_apply,
    nsmul_eq_mul, smul_eq_mul]
  rw [modularThetaSourcePositiveLie_clearedLogJetTwo,
    modularThetaSourcePositiveLie_clearedLogJetThree,
    modularThetaSourcePositiveLie_clearedLogJetFour,
    modularThetaSourcePositiveLie_clearedLogJetFive,
    modularThetaSourcePositiveLie_clearedLogJetSix,
    modularThetaSourcePositiveLie_clearedLogJetSeven]
  ring

/-- At the `X=100` orientation boundary, the exact source-positive vector-field derivative of
completed C5 orientation is strictly negative. -/
theorem eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_hundred_re_neg :
    (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      (modularThetaSourcePositiveLie
        modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial)).re < 0 := by
  have horientation :=
    eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_hundred_eq_zero
  have hslope :=
    eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_hundred_re_neg
  have hid := congrArg (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100))
    modularThetaSourcePositive_c5ExactCompletedSeamOrientation_covariantLie
  simp only [map_mul, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X] at hid
  rw [horientation] at hid
  norm_num only [mul_zero, add_zero] at hid
  have hmass :
      MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
          (modularThetaSourcePositiveNormalizedSourceJet 0) = 47 / 8 := by
    norm_num [modularThetaSourcePositiveNormalizedSourceJet,
      modularThetaSourcePositiveSeamState]
  rw [hmass] at hid
  have hre := congrArg Complex.re hid
  norm_num [Complex.mul_re] at hre
  linarith

/-- At the same boundary witness, source mass and reconstructed gap are positive, the vector field
points strictly into positive `U` and `B`, and its `Q` velocity vanishes. -/
theorem modularThetaSourcePositiveVectorField_hundred_seam_geometry :
    0 < (modularThetaSourcePositiveSeamState 100 .Q).re ∧
    0 < (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      modularThetaSourcePositiveGap).re ∧
    0 < (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      (modularThetaSourcePositiveVectorField .U)).re ∧
    0 < (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      (modularThetaSourcePositiveVectorField .B)).re ∧
    MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      (modularThetaSourcePositiveVectorField .Q) = 0 := by
  norm_num [modularThetaSourcePositiveSeamState, modularThetaSourcePositiveGap,
    modularThetaSourcePositiveVectorField]

/-- Exact uniform-flow route kill: even on a positive-mass, positive-gap orientation boundary where
the source-positive vector field enters both positive chamber coordinates and preserves `Q` to
first order, completed C5 orientation can point strictly outward. Thus source-positive dynamics
alone do not furnish a universal invariant-region or first-contact barrier. -/
theorem not_forall_sourcePositiveC5OrientationBoundary_flow_inward :
    ¬ ∀ v : ModularThetaSourcePositiveState → ℂ,
      0 < (v .Q).re →
      0 < (MvPolynomial.eval v modularThetaSourcePositiveGap).re →
      0 < (MvPolynomial.eval v
        (modularThetaSourcePositiveVectorField .U)).re →
      0 < (MvPolynomial.eval v
        (modularThetaSourcePositiveVectorField .B)).re →
      MvPolynomial.eval v (modularThetaSourcePositiveVectorField .Q) = 0 →
      MvPolynomial.eval v
        modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial = 0 →
      0 ≤ (MvPolynomial.eval v
        (modularThetaSourcePositiveLie
          modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial)).re := by
  intro h
  obtain ⟨hQ, hgap, hU, hB, hQvel⟩ :=
    modularThetaSourcePositiveVectorField_hundred_seam_geometry
  have hinward := h (modularThetaSourcePositiveSeamState 100)
    hQ hgap hU hB hQvel
    eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_hundred_eq_zero
  linarith [
    eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_hundred_re_neg]

end

end HTGeometry
