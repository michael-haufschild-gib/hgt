import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeLyapunovClosure

/-!
# Positive-chamber modular theta jet closure

The physical Lyapunov system admits polynomial coordinates
`U = S/3 + W`, `B = -S/3`, and `C = R(1+Z)`.  On the positive theta half-orbit all
three coordinates are strictly positive, while
`S = -3B`, `A = C(2U+6B+C)`, and `W = U+B`.  This module constructs the exact rank-three
reflected D1 polynomial in that positive chamber.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Coordinates of the positive theta chamber. -/
inductive ModularThetaPositiveState
  | U
  | B
  | C
  deriving DecidableEq, Fintype

abbrev ModularThetaPositivePolynomial := MvPolynomial ModularThetaPositiveState ℂ

/-- Discriminant-gap polynomial in positive-chamber coordinates. -/
def modularThetaPositiveGap : ModularThetaPositivePolynomial :=
  MvPolynomial.X .C *
    (MvPolynomial.C 2 * MvPolynomial.X .U +
      MvPolynomial.C 6 * MvPolynomial.X .B + MvPolynomial.X .C)

/-- Autonomous polynomial vector field in `(U,B,C)`. -/
def modularThetaPositiveVectorField :
    ModularThetaPositiveState → ModularThetaPositivePolynomial
  | .U => MvPolynomial.C 3 +
      MvPolynomial.C (1 / 4 : ℂ) * modularThetaPositiveGap +
      MvPolynomial.C 3 * MvPolynomial.X .B ^ 2 +
      MvPolynomial.C 2 * MvPolynomial.X .B * MvPolynomial.X .U
  | .B => MvPolynomial.C (-1 : ℂ) + MvPolynomial.X .B ^ 2 +
      MvPolynomial.C (1 / 4 : ℂ) * modularThetaPositiveGap
  | .C => -MvPolynomial.X .C *
      (MvPolynomial.C 2 * MvPolynomial.X .U +
        MvPolynomial.C 4 * MvPolynomial.X .B + MvPolynomial.X .C)

/-- Lie derivative along the positive-chamber vector field. -/
def modularThetaPositiveLie (Q : ModularThetaPositivePolynomial) :
    ModularThetaPositivePolynomial :=
  ∑ i, MvPolynomial.pderiv i Q * modularThetaPositiveVectorField i

/-- Covariant Lie derivative for one mass-normalized jet. -/
def modularThetaPositiveNormalizedLie (Q : ModularThetaPositivePolynomial) :
    ModularThetaPositivePolynomial :=
  modularThetaPositiveLie Q +
    MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * Q

/-- Completed-theta jets after division by common theta mass. -/
def modularThetaPositiveNormalizedHJet : ℕ → ModularThetaPositivePolynomial
  | 0 => 1
  | n + 1 =>
      modularThetaPositiveNormalizedLie (modularThetaPositiveNormalizedHJet n)

/-- Theta-cusp source jets after division by common theta mass. -/
def modularThetaPositiveNormalizedSourceJet (n : ℕ) :
    ModularThetaPositivePolynomial :=
  (modularThetaPositiveNormalizedHJet (n + 2) -
    MvPolynomial.C (1 / 4 : ℂ) * modularThetaPositiveNormalizedHJet n) *
      MvPolynomial.C (1 / 2 : ℂ)

/-- Rank-three reflected eighth polynomial in positive-chamber coordinates. -/
def modularThetaPositiveReflectedEighthPolynomial : ModularThetaPositivePolynomial :=
  let f := modularThetaPositiveNormalizedSourceJet
  let p0 := f 0 ^ 2
  let p2 := MvPolynomial.C 2 * (f 0 * f 2 - f 1 ^ 2)
  let p4 := MvPolynomial.C 2 * f 0 * f 4 - MvPolynomial.C 8 * f 1 * f 3 +
    MvPolynomial.C 6 * f 2 ^ 2
  let p6 := MvPolynomial.C 2 * f 0 * f 6 - MvPolynomial.C 12 * f 1 * f 5 +
    MvPolynomial.C 30 * f 2 * f 4 - MvPolynomial.C 20 * f 3 ^ 2
  let p8 := MvPolynomial.C 2 * f 0 * f 8 - MvPolynomial.C 16 * f 1 * f 7 +
    MvPolynomial.C 56 * f 2 * f 6 - MvPolynomial.C 112 * f 3 * f 5 +
    MvPolynomial.C 70 * f 4 ^ 2
  p0 * p4 * p8 - p0 * p6 ^ 2 - p2 ^ 2 * p8 +
    MvPolynomial.C 2 * p2 * p4 * p6 - p4 ^ 3

/-- Polynomial observables differentiate by the positive-chamber Lie derivative. -/
theorem hasDerivAt_eval_modularThetaPositivePolynomial
    (Q : ModularThetaPositivePolynomial)
    (v : ModularThetaPositiveState → ℝ → ℂ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaPositiveVectorField i)) x) :
    HasDerivAt (fun y => MvPolynomial.eval (fun j => v j y) Q)
      (MvPolynomial.eval (fun j => v j x) (modularThetaPositiveLie Q)) x := by
  have h := hasDerivAt_mvPolynomial_eval_curve_real Q v
    (fun i => MvPolynomial.eval (fun j => v j x)
      (modularThetaPositiveVectorField i)) x hv
  convert h using 1
  simp only [modularThetaPositiveLie, map_sum, map_mul]

/-- Every mass derivative is mass times its normalized positive-chamber jet. -/
theorem iteratedDeriv_eq_mass_mul_eval_modularThetaPositiveNormalizedHJet
    (v : ModularThetaPositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaPositiveVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (n : ℕ) :
    iteratedDeriv n H = fun x =>
      H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaPositiveNormalizedHJet n) := by
  induction n with
  | zero =>
      funext x
      simp [modularThetaPositiveNormalizedHJet]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hQ := hasDerivAt_eval_modularThetaPositivePolynomial
        (modularThetaPositiveNormalizedHJet n) v x (hv x)
      have hprod := (hH x).mul hQ
      have hfun :
          (fun y => H y * MvPolynomial.eval (fun j => v j y)
            (modularThetaPositiveNormalizedHJet n)) =
          H * (fun y => MvPolynomial.eval (fun j => v j y)
            (modularThetaPositiveNormalizedHJet n)) := by
        funext y
        rfl
      rw [hfun, hprod.deriv]
      rw [modularThetaPositiveNormalizedHJet]
      unfold modularThetaPositiveNormalizedLie
      simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- Each source jet is mass times its positive-chamber polynomial. -/
theorem mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq
    (v : ModularThetaPositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaPositiveVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (n : ℕ) (x : ℝ) :
    H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaPositiveNormalizedSourceJet n) =
      (iteratedDeriv (n + 2) H x -
        (1 / 4 : ℂ) * iteratedDeriv n H x) / 2 := by
  rw [iteratedDeriv_eq_mass_mul_eval_modularThetaPositiveNormalizedHJet v hv H hH,
    iteratedDeriv_eq_mass_mul_eval_modularThetaPositiveNormalizedHJet v hv H hH]
  simp only [modularThetaPositiveNormalizedSourceJet, map_mul, map_sub,
    MvPolynomial.eval_C]
  ring

/-- Exact rank-three reflected closure in positive-chamber variables. -/
theorem modularThetaPositiveReflectedEighthClosure_of_ode
    (v : ModularThetaPositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaPositiveVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (x : ℝ) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) H x -
        (1 / 4 : ℂ) * iteratedDeriv n H x) / 2
    signedEvenHankelThreeDetC
      (f 0 ^ 2)
      (2 * (f 0 * f 2 - f 1 ^ 2))
      (2 * f 0 * f 4 - 8 * f 1 * f 3 + 6 * f 2 ^ 2)
      (2 * f 0 * f 6 - 12 * f 1 * f 5 + 30 * f 2 * f 4 - 20 * f 3 ^ 2)
      (2 * f 0 * f 8 - 16 * f 1 * f 7 + 56 * f 2 * f 6 -
        112 * f 3 * f 5 + 70 * f 4 ^ 2) =
      H x ^ 6 * MvPolynomial.eval (fun j => v j x)
        modularThetaPositiveReflectedEighthPolynomial := by
  dsimp only
  unfold modularThetaPositiveReflectedEighthPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 0 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 1 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 2 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 3 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 4 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 5 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 6 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 7 x,
    ← mass_mul_eval_modularThetaPositiveNormalizedSourceJet_eq v hv H hH 8 x]
  unfold signedEvenHankelThreeDetC
  ring

end

end HTGeometry
