import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveSeamNoGo

/-!
# Fixed-action C5 seam closure for the modular theta ODE

The source-positive modular closure exposes a new local obstruction test for transporting the
normalized C5 balance along fixed reflected-action levels.  Reflection kills the Jacobian on the
center seam.  Its first center coefficient has a further cancellation at displacement zero: the
known sixth-jet action-velocity obstruction disappears, and the first surviving coefficient is
the eighth-log-jet polynomial

`A^2 D - 5 A B C + 4 B^3 - 18 A^3 C + 36 A^2 B^2`.

This file performs the exact modular ODE elimination of that polynomial.  It also proves that the
resulting degree-twelve seam polynomial is positive throughout the already established physical
self-dual chamber `191/10 ≤ X < 20`.  No numerical evaluation enters either theorem.
-/

open Complex Real
open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

set_option maxHeartbeats 4000000

/-- Degree-twelve modular polynomial selected by the first nonzero direct fixed-action C5 seam
coefficient. -/
def modularThetaC5FixedActionSeamPolynomial (X : ℂ) : ℂ :=
  -5740875 / 262144 + 220066875 / 1048576 * X + 2460375 / 65536 * X ^ 2 -
    739953225 / 8388608 * X ^ 3 - 4809734235 / 67108864 * X ^ 4 +
    16101161775 / 268435456 * X ^ 5 - 3626353395 / 536870912 * X ^ 6 +
    1026844047 / 1073741824 * X ^ 7 - 345880233 / 4294967296 * X ^ 8 -
    89154405 / 17179869184 * X ^ 9 + 3449799 / 8589934592 * X ^ 10 +
    216621 / 68719476736 * X ^ 11 - 9975 / 68719476736 * X ^ 12

/-- Real form of the direct fixed-action C5 seam polynomial. -/
def modularThetaC5FixedActionSeamPolynomialReal (X : ℝ) : ℝ :=
  -5740875 / 262144 + 220066875 / 1048576 * X + 2460375 / 65536 * X ^ 2 -
    739953225 / 8388608 * X ^ 3 - 4809734235 / 67108864 * X ^ 4 +
    16101161775 / 268435456 * X ^ 5 - 3626353395 / 536870912 * X ^ 6 +
    1026844047 / 1073741824 * X ^ 7 - 345880233 / 4294967296 * X ^ 8 -
    89154405 / 17179869184 * X ^ 9 + 3449799 / 8589934592 * X ^ 10 +
    216621 / 68719476736 * X ^ 11 - 9975 / 68719476736 * X ^ 12

/-- Exact tenth-mass-jet elimination for the direct fixed-action C5 seam polynomial. -/
theorem modularThetaC5FixedActionSeamJetElimination
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
    let f : ℕ → ℂ :=
      fun n => (h (n + 2) - (1 / 4 : ℂ) * h n) / 2
    let a := -f 2
    let b := 3 * f 2 ^ 2 - f 0 * f 4
    let c := -f 0 ^ 2 * f 6 + 15 * f 0 * f 2 * f 4 - 30 * f 2 ^ 3
    let d := -f 0 ^ 3 * f 8 + 28 * f 0 ^ 2 * f 2 * f 6 +
      35 * f 0 ^ 2 * f 4 ^ 2 - 420 * f 0 * f 2 ^ 2 * f 4 + 630 * f 2 ^ 4
    a ^ 2 * d - 5 * a * b * c + 4 * b ^ 3 - 18 * a ^ 3 * c +
      36 * a ^ 2 * b ^ 2 = M ^ 6 * modularThetaC5FixedActionSeamPolynomial (R ^ 2) := by
  have hh1 := hh 0
  have hz1 := hz 0
  have hr1 := hr 0
  have hp1 := hp 0
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0]
      at hh1 hz1 hr1 hp1
  ring_nf at hh1 hz1 hr1 hp1
  have hh2 := hh 1
  have hz2 := hz 1
  have hr2 := hr 1
  have hp2 := hp 1
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1] at hh2 hz2 hr2 hp2
  ring_nf at hh2 hz2 hr2 hp2
  have hh3 := hh 2
  have hz3 := hz 2
  have hr3 := hr 2
  have hp3 := hp 2
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2]
      at hh3 hz3 hr3 hp3
  ring_nf at hh3 hz3 hr3 hp3
  have hh4 := hh 3
  have hz4 := hz 3
  have hr4 := hr 3
  have hp4 := hp 3
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3] at hh4 hz4 hr4 hp4
  ring_nf at hh4 hz4 hr4 hp4
  have hh5 := hh 4
  have hz5 := hz 4
  have hr5 := hr 4
  have hp5 := hp 4
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4]
      at hh5 hz5 hr5 hp5
  ring_nf at hh5 hz5 hr5 hp5
  have hh6 := hh 5
  have hz6 := hz 5
  have hr6 := hr 5
  have hp6 := hp 5
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5] at hh6 hz6 hr6 hp6
  ring_nf at hh6 hz6 hr6 hp6
  have hh7 := hh 6
  have hz7 := hz 6
  have hr7 := hr 6
  have hp7 := hp 6
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6]
      at hh7 hz7 hr7 hp7
  ring_nf at hh7 hz7 hr7 hp7
  have hh8 := hh 7
  have hz8 := hz 7
  have hr8 := hr 7
  have hp8 := hp 7
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6,
    hh7, hz7, hr7, hp7] at hh8 hz8 hr8 hp8
  ring_nf at hh8 hz8 hr8 hp8
  have hh9 := hh 8
  have hz9 := hz 8
  have hr9 := hr 8
  have hp9 := hp 8
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6,
    hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8]
      at hh9 hz9 hr9 hp9
  ring_nf at hh9 hz9 hr9 hp9
  have hh10 := hh 9
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6,
    hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8,
    hh9, hz9, hr9, hp9] at hh10
  ring_nf at hh10
  dsimp
  rw [hh0, hh2, hh4, hh6, hh8, hh10]
  unfold modularThetaC5FixedActionSeamPolynomial
  ring

/-- Mass-normalized direct fixed-action C5 seam polynomial in the universal four-state chart. -/
def modularThetaODENormalizedC5FixedActionSeamPolynomial : ModularThetaODEPolynomial :=
  let f := modularThetaODENormalizedSourceJet
  let a := -f 2
  let b := MvPolynomial.C 3 * f 2 ^ 2 - f 0 * f 4
  let c := -f 0 ^ 2 * f 6 + MvPolynomial.C 15 * f 0 * f 2 * f 4 -
    MvPolynomial.C 30 * f 2 ^ 3
  let d := -f 0 ^ 3 * f 8 + MvPolynomial.C 28 * f 0 ^ 2 * f 2 * f 6 +
    MvPolynomial.C 35 * f 0 ^ 2 * f 4 ^ 2 -
    MvPolynomial.C 420 * f 0 * f 2 ^ 2 * f 4 + MvPolynomial.C 630 * f 2 ^ 4
  a ^ 2 * d - MvPolynomial.C 5 * a * b * c + MvPolynomial.C 4 * b ^ 3 -
    MvPolynomial.C 18 * a ^ 3 * c + MvPolynomial.C 36 * a ^ 2 * b ^ 2

/-- Direct fixed-action C5 seam polynomial in Lyapunov coordinates. -/
def modularThetaLyapunovC5FixedActionSeamPolynomial : ModularThetaLyapunovPolynomial :=
  let f := modularThetaLyapunovNormalizedSourceJet
  let a := -f 2
  let b := MvPolynomial.C 3 * f 2 ^ 2 - f 0 * f 4
  let c := -f 0 ^ 2 * f 6 + MvPolynomial.C 15 * f 0 * f 2 * f 4 -
    MvPolynomial.C 30 * f 2 ^ 3
  let d := -f 0 ^ 3 * f 8 + MvPolynomial.C 28 * f 0 ^ 2 * f 2 * f 6 +
    MvPolynomial.C 35 * f 0 ^ 2 * f 4 ^ 2 -
    MvPolynomial.C 420 * f 0 * f 2 ^ 2 * f 4 + MvPolynomial.C 630 * f 2 ^ 4
  a ^ 2 * d - MvPolynomial.C 5 * a * b * c + MvPolynomial.C 4 * b ^ 3 -
    MvPolynomial.C 18 * a ^ 3 * c + MvPolynomial.C 36 * a ^ 2 * b ^ 2

/-- Direct fixed-action C5 seam polynomial in source-positive coordinates. -/
def modularThetaSourcePositiveC5FixedActionSeamPolynomial :
    ModularThetaSourcePositivePolynomial :=
  let f := modularThetaSourcePositiveNormalizedSourceJet
  let a := -f 2
  let b := MvPolynomial.C 3 * f 2 ^ 2 - f 0 * f 4
  let c := -f 0 ^ 2 * f 6 + MvPolynomial.C 15 * f 0 * f 2 * f 4 -
    MvPolynomial.C 30 * f 2 ^ 3
  let d := -f 0 ^ 3 * f 8 + MvPolynomial.C 28 * f 0 ^ 2 * f 2 * f 6 +
    MvPolynomial.C 35 * f 0 ^ 2 * f 4 ^ 2 -
    MvPolynomial.C 420 * f 0 * f 2 ^ 2 * f 4 + MvPolynomial.C 630 * f 2 ^ 4
  a ^ 2 * d - MvPolynomial.C 5 * a * b * c + MvPolynomial.C 4 * b ^ 3 -
    MvPolynomial.C 18 * a ^ 3 * c + MvPolynomial.C 36 * a ^ 2 * b ^ 2

/-- Four-state-to-Lyapunov transport preserves the direct fixed-action seam polynomial. -/
theorem modularThetaGeneralLyapunov_c5FixedActionSeamPolynomial :
    modularThetaGeneralLyapunovPullback
        modularThetaLyapunovC5FixedActionSeamPolynomial =
      modularThetaODENormalizedC5FixedActionSeamPolynomial := by
  unfold modularThetaLyapunovC5FixedActionSeamPolynomial
    modularThetaODENormalizedC5FixedActionSeamPolynomial
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg,
    modularThetaGeneralLyapunovPullback_C]
  rw [modularThetaGeneralLyapunov_normalizedSourceJet 0,
    modularThetaGeneralLyapunov_normalizedSourceJet 2,
    modularThetaGeneralLyapunov_normalizedSourceJet 4,
    modularThetaGeneralLyapunov_normalizedSourceJet 6,
    modularThetaGeneralLyapunov_normalizedSourceJet 8]

/-- Source-positive chart transport preserves the direct fixed-action seam polynomial. -/
theorem modularThetaSourcePositiveChart_c5FixedActionSeamPolynomial :
    modularThetaSourcePositiveChartPullback
        modularThetaLyapunovC5FixedActionSeamPolynomial =
      modularThetaSourcePositiveC5FixedActionSeamPolynomial := by
  unfold modularThetaLyapunovC5FixedActionSeamPolynomial
    modularThetaSourcePositiveC5FixedActionSeamPolynomial
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg,
    modularThetaSourcePositiveChartPullback_C]
  rw [modularThetaSourcePositiveChart_sourceJet 0,
    modularThetaSourcePositiveChart_sourceJet 2,
    modularThetaSourcePositiveChart_sourceJet 4,
    modularThetaSourcePositiveChart_sourceJet 6,
    modularThetaSourcePositiveChart_sourceJet 8]

/-- Source-positive and Lyapunov chart evaluation agree on every real algebraic seam. -/
theorem eval_modularThetaSourcePositiveChartPullback_seam
    (R : ℝ) (P : ModularThetaLyapunovPolynomial) :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState (R ^ 2))
        (modularThetaSourcePositiveChartPullback P) =
      MvPolynomial.eval (modularThetaLyapunovSeamState (R : ℂ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, hP,
        modularThetaSourcePositiveChartPullback_X]
      rw [map_mul]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval (modularThetaLyapunovSeamState (R : ℂ)) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveChartCoordinate,
          modularThetaSourcePositiveGap,
          modularThetaSourcePositiveSeamState,
          modularThetaLyapunovSeamState]
      all_goals ring

/-- The normalized four-state C5 polynomial has the exact degree-twelve seam restriction. -/
theorem eval_modularThetaODENormalizedC5FixedActionSeamPolynomial_seam
    (R : ℂ) :
    MvPolynomial.eval (modularThetaODESeamState R)
        modularThetaODENormalizedC5FixedActionSeamPolynomial =
      modularThetaC5FixedActionSeamPolynomial (R ^ 2) := by
  let v := modularThetaODESeamState R
  let h := evalModularThetaODEFormalJet v .H
  let z := evalModularThetaODEFormalJet v .Z
  let r := evalModularThetaODEFormalJet v .R
  let p := evalModularThetaODEFormalJet v .P
  have helim := modularThetaC5FixedActionSeamJetElimination
    (1 : ℂ) R h z r p
    (by simp [h, v, modularThetaODESeamState])
    (by simp [z, v, modularThetaODESeamState])
    (by simp [r, v, modularThetaODESeamState])
    (by simp [p, v, modularThetaODESeamState])
    (fun n => evalModularThetaODEFormalJet_H_succ v n)
    (fun n => evalModularThetaODEFormalJet_Z_succ v n)
    (fun n => evalModularThetaODEFormalJet_R_succ v n)
    (fun n => evalModularThetaODEFormalJet_P_succ v n)
  have hnorm (n : ℕ) :
      MvPolynomial.eval v (modularThetaODENormalizedSourceJet n) =
        MvPolynomial.eval v (modularThetaODESourceJet n) := by
    have hfac := congrArg (MvPolynomial.eval v)
      (modularThetaODESourceJet_eq_X_H_mul_normalized n)
    simpa [v, modularThetaODESeamState] using hfac.symm
  dsimp only at helim ⊢
  rw [one_pow, one_mul] at helim
  unfold modularThetaODENormalizedC5FixedActionSeamPolynomial
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_add, map_neg,
    MvPolynomial.eval_C]
  rw [hnorm 0, hnorm 2, hnorm 4, hnorm 6, hnorm 8]
  simpa only [eval_modularThetaODESourceJet_eq_formalJet] using helim

/-- The Lyapunov C5 polynomial has the same exact real seam restriction. -/
theorem eval_modularThetaLyapunovC5FixedActionSeamPolynomial_seam
    (R : ℝ) :
    MvPolynomial.eval (modularThetaLyapunovSeamState (R : ℂ))
        modularThetaLyapunovC5FixedActionSeamPolynomial =
      modularThetaC5FixedActionSeamPolynomial ((R : ℂ) ^ 2) := by
  rw [← eval_modularThetaGeneralLyapunovPullback_seam]
  rw [modularThetaGeneralLyapunov_c5FixedActionSeamPolynomial,
    eval_modularThetaODENormalizedC5FixedActionSeamPolynomial_seam]

/-- The source-positive C5 polynomial has the exact physical seam restriction. -/
theorem eval_modularThetaSourcePositiveC5FixedActionSeamPolynomial_seam
    (R : ℝ) :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState (R ^ 2))
        modularThetaSourcePositiveC5FixedActionSeamPolynomial =
      modularThetaC5FixedActionSeamPolynomial ((R : ℂ) ^ 2) := by
  rw [← modularThetaSourcePositiveChart_c5FixedActionSeamPolynomial,
    eval_modularThetaSourcePositiveChartPullback_seam,
    eval_modularThetaLyapunovC5FixedActionSeamPolynomial_seam]

/-- Raw source seam invariant is positive mass to the sixth times the source-positive polynomial. -/
theorem modularThetaSourcePositiveC5FixedActionClosure_of_ode
    (v : ModularThetaSourcePositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x)
        (modularThetaSourcePositiveVectorField i)) x)
    (H F : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (hF : ∀ x, F x = H x * v .Q x)
    (x : ℝ) :
    let f : ℕ → ℂ := fun n => iteratedDeriv n F x
    let a := -f 2
    let b := 3 * f 2 ^ 2 - f 0 * f 4
    let c := -f 0 ^ 2 * f 6 + 15 * f 0 * f 2 * f 4 - 30 * f 2 ^ 3
    let d := -f 0 ^ 3 * f 8 + 28 * f 0 ^ 2 * f 2 * f 6 +
      35 * f 0 ^ 2 * f 4 ^ 2 - 420 * f 0 * f 2 ^ 2 * f 4 + 630 * f 2 ^ 4
    a ^ 2 * d - 5 * a * b * c + 4 * b ^ 3 - 18 * a ^ 3 * c +
      36 * a ^ 2 * b ^ 2 =
        H x ^ 6 * MvPolynomial.eval (fun j => v j x)
          modularThetaSourcePositiveC5FixedActionSeamPolynomial := by
  have hfun : F = fun y => H y * v .Q y := by
    funext y
    exact hF y
  rw [hfun]
  dsimp only
  unfold modularThetaSourcePositiveC5FixedActionSeamPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, map_neg, MvPolynomial.eval_C]
  rw [iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 0,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 2,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 4,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 6,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 8]
  ring

/-- The new seam polynomial is positive on the full coarse chamber already known to contain the
literal self-dual theta scale. -/
theorem modularThetaC5FixedActionSeamPolynomialReal_pos_of_mem_physicalChamber
    {X : ℝ} (hlo : (191 / 10 : ℝ) ≤ X) (hhi : X < 20) :
    0 < modularThetaC5FixedActionSeamPolynomialReal X := by
  let y := X - (191 / 10 : ℝ)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hp0 (n : ℕ) : 0 ≤ y ^ n := pow_nonneg hy0 n
  have hp1 (n : ℕ) : y ^ n ≤ 1 := pow_le_one₀ hy0 hy1
  have hX : X = (191 / 10 : ℝ) + y := by dsimp [y]; ring
  rw [hX]
  rw [show modularThetaC5FixedActionSeamPolynomialReal ((191 / 10 : ℝ) + y) =
      2214487347729023423585466546267 / 13743895347200000000000 +
        y * (139404590908346178051518476161 / 687194767360000000000) +
        y ^ 2 * (520266231757268288453249577 / 6871947673600000000) +
        y ^ 3 * (19514476745470064741023743 / 1374389534720000000) +
        y ^ 4 * (433287597527691694530507 / 274877906944000000) +
        y ^ 5 * (3763259996955415498701 / 34359738368000000) +
        y ^ 6 * (2008074101656444857 / 429496729600000) +
        y ^ 7 * (7044599770834311 / 68719476736000) -
        y ^ 8 * (8740226080539 / 27487790694400) -
        y ^ 9 * (120598295439 / 1374389534720) -
        y ^ 10 * (835310997 / 343597383680) -
        y ^ 11 * (2069649 / 68719476736) -
        y ^ 12 * (9975 / 68719476736) by
      unfold modularThetaC5FixedActionSeamPolynomialReal
      ring]
  nlinarith [hp0 1, hp0 2, hp0 3, hp0 4, hp0 5, hp0 6, hp0 7,
    hp1 8, hp1 9, hp1 10, hp1 11, hp1 12]

end

end HTGeometry
