import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeGeneralClosure

/-!
# Three-state reduced modular theta jet closure

The mass-normalized theta ODE descends from `(H,Z,R,P)` to `(Z,R,S)` after the Riccati
change `S = P + RZ`.  This file constructs the resulting three-variable polynomial Lie
closure and proves that its rank-three reflected determinant is the exact sixth-mass factor
of every compatible trajectory.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Coordinates of the reduced mass-normalized modular theta ODE. -/
inductive ModularThetaReducedState
  | Z
  | R
  | S
  deriving DecidableEq, Fintype

abbrev ModularThetaReducedPolynomial := MvPolynomial ModularThetaReducedState ℂ

/-- Autonomous reduced vector field in `(Z,R,S)`. -/
def modularThetaReducedVectorField :
    ModularThetaReducedState → ModularThetaReducedPolynomial
  | .Z => -MvPolynomial.X .R *
      (MvPolynomial.C 1 - MvPolynomial.X .Z ^ (2 : ℕ))
  | .R => MvPolynomial.C (-(2 / 3 : ℂ)) *
      MvPolynomial.X .R * MvPolynomial.X .S
  | .S => MvPolynomial.C 3 -
      MvPolynomial.C (1 / 3 : ℂ) * MvPolynomial.X .S ^ (2 : ℕ) -
      MvPolynomial.C (3 / 4 : ℂ) * MvPolynomial.X .R ^ (2 : ℕ) *
        (MvPolynomial.C 1 - MvPolynomial.X .Z ^ (2 : ℕ))

/-- Lie derivative along the reduced modular vector field. -/
def modularThetaReducedLie (Q : ModularThetaReducedPolynomial) :
    ModularThetaReducedPolynomial :=
  ∑ i, MvPolynomial.pderiv i Q * modularThetaReducedVectorField i

/-- Covariant reduced Lie derivative for one theta-mass-normalized jet. -/
def modularThetaReducedNormalizedLie (Q : ModularThetaReducedPolynomial) :
    ModularThetaReducedPolynomial :=
  modularThetaReducedLie Q +
    MvPolynomial.C (-(1 / 6 : ℂ)) * MvPolynomial.X .S * Q

/-- Completed-theta jets after division by their common mass factor. -/
def modularThetaReducedNormalizedHJet : ℕ → ModularThetaReducedPolynomial
  | 0 => 1
  | n + 1 =>
      modularThetaReducedNormalizedLie (modularThetaReducedNormalizedHJet n)

/-- Theta-cusp source jets after division by their common mass factor. -/
def modularThetaReducedNormalizedSourceJet (n : ℕ) :
    ModularThetaReducedPolynomial :=
  (modularThetaReducedNormalizedHJet (n + 2) -
    MvPolynomial.C (1 / 4 : ℂ) * modularThetaReducedNormalizedHJet n) *
      MvPolynomial.C (1 / 2 : ℂ)

/-- Rank-three reflected eighth polynomial in the genuine three-state closure. -/
def modularThetaReducedReflectedEighthPolynomial : ModularThetaReducedPolynomial :=
  let f := modularThetaReducedNormalizedSourceJet
  let p0 := f 0 ^ (2 : ℕ)
  let p2 := MvPolynomial.C 2 * (f 0 * f 2 - f 1 ^ (2 : ℕ))
  let p4 := MvPolynomial.C 2 * f 0 * f 4 - MvPolynomial.C 8 * f 1 * f 3 +
    MvPolynomial.C 6 * f 2 ^ (2 : ℕ)
  let p6 := MvPolynomial.C 2 * f 0 * f 6 - MvPolynomial.C 12 * f 1 * f 5 +
    MvPolynomial.C 30 * f 2 * f 4 - MvPolynomial.C 20 * f 3 ^ (2 : ℕ)
  let p8 := MvPolynomial.C 2 * f 0 * f 8 - MvPolynomial.C 16 * f 1 * f 7 +
    MvPolynomial.C 56 * f 2 * f 6 - MvPolynomial.C 112 * f 3 * f 5 +
    MvPolynomial.C 70 * f 4 ^ (2 : ℕ)
  p0 * p4 * p8 - p0 * p6 ^ (2 : ℕ) - p2 ^ (2 : ℕ) * p8 +
    MvPolynomial.C 2 * p2 * p4 * p6 - p4 ^ (3 : ℕ)

/-- Differentiating a reduced polynomial observable is its reduced Lie derivative. -/
theorem hasDerivAt_eval_modularThetaReducedPolynomial
    (Q : ModularThetaReducedPolynomial)
    (v : ModularThetaReducedState → ℝ → ℂ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaReducedVectorField i)) x) :
    HasDerivAt (fun y => MvPolynomial.eval (fun j => v j y) Q)
      (MvPolynomial.eval (fun j => v j x) (modularThetaReducedLie Q)) x := by
  have h := hasDerivAt_mvPolynomial_eval_curve_real Q v
    (fun i => MvPolynomial.eval (fun j => v j x)
      (modularThetaReducedVectorField i)) x hv
  convert h using 1
  simp only [modularThetaReducedLie, map_sum, map_mul]

/-- Every completed-theta derivative is mass times the matching reduced normalized jet. -/
theorem iteratedDeriv_eq_mass_mul_eval_modularThetaReducedNormalizedHJet
    (v : ModularThetaReducedState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaReducedVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
    (n : ℕ) :
    iteratedDeriv n H = fun x =>
      H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaReducedNormalizedHJet n) := by
  induction n with
  | zero =>
      funext x
      simp [modularThetaReducedNormalizedHJet]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hQ := hasDerivAt_eval_modularThetaReducedPolynomial
        (modularThetaReducedNormalizedHJet n) v x (hv x)
      have hprod := (hH x).mul hQ
      have hfun :
          (fun y => H y * MvPolynomial.eval (fun j => v j y)
            (modularThetaReducedNormalizedHJet n)) =
          H * (fun y => MvPolynomial.eval (fun j => v j y)
            (modularThetaReducedNormalizedHJet n)) := by
        funext y
        rfl
      rw [hfun, hprod.deriv]
      rw [modularThetaReducedNormalizedHJet]
      unfold modularThetaReducedNormalizedLie
      simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- Each literal source jet is theta mass times its reduced three-state polynomial. -/
theorem mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq
    (v : ModularThetaReducedState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaReducedVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
    (n : ℕ) (x : ℝ) :
    H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaReducedNormalizedSourceJet n) =
      (iteratedDeriv (n + 2) H x -
        (1 / 4 : ℂ) * iteratedDeriv n H x) / 2 := by
  rw [iteratedDeriv_eq_mass_mul_eval_modularThetaReducedNormalizedHJet v hv H hH,
    iteratedDeriv_eq_mass_mul_eval_modularThetaReducedNormalizedHJet v hv H hH]
  simp only [modularThetaReducedNormalizedSourceJet, map_mul, map_sub,
    MvPolynomial.eval_C]
  ring

/-- Exact rank-three reflected closure in three variables, including its sixth mass factor. -/
theorem modularThetaReducedReflectedEighthClosure_of_ode
    (v : ModularThetaReducedState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaReducedVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
    (x : ℝ) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) H x -
        (1 / 4 : ℂ) * iteratedDeriv n H x) / 2
    signedEvenHankelThreeDetC
      (f 0 ^ (2 : ℕ))
      (2 * (f 0 * f 2 - f 1 ^ (2 : ℕ)))
      (2 * f 0 * f 4 - 8 * f 1 * f 3 + 6 * f 2 ^ (2 : ℕ))
      (2 * f 0 * f 6 - 12 * f 1 * f 5 + 30 * f 2 * f 4 - 20 * f 3 ^ (2 : ℕ))
      (2 * f 0 * f 8 - 16 * f 1 * f 7 + 56 * f 2 * f 6 -
        112 * f 3 * f 5 + 70 * f 4 ^ (2 : ℕ)) =
      H x ^ (6 : ℕ) * MvPolynomial.eval (fun j => v j x)
        modularThetaReducedReflectedEighthPolynomial := by
  dsimp only
  unfold modularThetaReducedReflectedEighthPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 0 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 1 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 2 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 3 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 4 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 5 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 6 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 7 x,
    ← mass_mul_eval_modularThetaReducedNormalizedSourceJet_eq v hv H hH 8 x]
  unfold signedEvenHankelThreeDetC
  ring

end

end HTGeometry
