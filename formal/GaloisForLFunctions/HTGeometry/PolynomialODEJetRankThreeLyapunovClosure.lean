import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeReducedClosure

/-!
# Lyapunov-coordinate modular theta jet closure

The reduced `(Z,R,S)` system closes once more under
`A = R²(1-Z²)` and `W = (2/3)S-RZ`.  The resulting `(S,A,W)` chart exposes the physical
Lyapunov signs while retaining an exact polynomial rank-three reflected closure.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Coordinates of the theta Lyapunov closure. -/
inductive ModularThetaLyapunovState
  | S
  | A
  | W
  deriving DecidableEq, Fintype

abbrev ModularThetaLyapunovPolynomial := MvPolynomial ModularThetaLyapunovState ℂ

/-- Autonomous vector field in `(S,A,W)`. -/
def modularThetaLyapunovVectorField :
    ModularThetaLyapunovState → ModularThetaLyapunovPolynomial
  | .S => MvPolynomial.C 3 -
      MvPolynomial.C (1 / 3 : ℂ) * MvPolynomial.X .S ^ 2 -
      MvPolynomial.C (3 / 4 : ℂ) * MvPolynomial.X .A
  | .A => MvPolynomial.C (-2 : ℂ) * MvPolynomial.X .A * MvPolynomial.X .W
  | .W => MvPolynomial.C 2 +
      MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .A +
      MvPolynomial.C (2 / 9 : ℂ) * MvPolynomial.X .S ^ 2 -
      MvPolynomial.C (2 / 3 : ℂ) * MvPolynomial.X .S * MvPolynomial.X .W

/-- Lie derivative along the Lyapunov vector field. -/
def modularThetaLyapunovLie (Q : ModularThetaLyapunovPolynomial) :
    ModularThetaLyapunovPolynomial :=
  ∑ i, MvPolynomial.pderiv i Q * modularThetaLyapunovVectorField i

/-- Covariant Lie derivative for one mass-normalized jet. -/
def modularThetaLyapunovNormalizedLie (Q : ModularThetaLyapunovPolynomial) :
    ModularThetaLyapunovPolynomial :=
  modularThetaLyapunovLie Q +
    MvPolynomial.C (-(1 / 6 : ℂ)) * MvPolynomial.X .S * Q

/-- Completed-theta jets after division by common theta mass. -/
def modularThetaLyapunovNormalizedHJet : ℕ → ModularThetaLyapunovPolynomial
  | 0 => 1
  | n + 1 =>
      modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedHJet n)

/-- Theta-cusp source jets after division by common theta mass. -/
def modularThetaLyapunovNormalizedSourceJet (n : ℕ) :
    ModularThetaLyapunovPolynomial :=
  (modularThetaLyapunovNormalizedHJet (n + 2) -
    MvPolynomial.C (1 / 4 : ℂ) * modularThetaLyapunovNormalizedHJet n) *
      MvPolynomial.C (1 / 2 : ℂ)

/-- Rank-three reflected eighth polynomial in Lyapunov coordinates. -/
def modularThetaLyapunovReflectedEighthPolynomial : ModularThetaLyapunovPolynomial :=
  let f := modularThetaLyapunovNormalizedSourceJet
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

/-- Polynomial observables differentiate by the Lyapunov Lie derivative. -/
theorem hasDerivAt_eval_modularThetaLyapunovPolynomial
    (Q : ModularThetaLyapunovPolynomial)
    (v : ModularThetaLyapunovState → ℝ → ℂ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovVectorField i)) x) :
    HasDerivAt (fun y => MvPolynomial.eval (fun j => v j y) Q)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovLie Q)) x := by
  have h := hasDerivAt_mvPolynomial_eval_curve_real Q v
    (fun i => MvPolynomial.eval (fun j => v j x)
      (modularThetaLyapunovVectorField i)) x hv
  convert h using 1
  simp only [modularThetaLyapunovLie, map_sum, map_mul]

/-- Every mass derivative is mass times its normalized Lyapunov jet. -/
theorem iteratedDeriv_eq_mass_mul_eval_modularThetaLyapunovNormalizedHJet
    (v : ModularThetaLyapunovState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
    (n : ℕ) :
    iteratedDeriv n H = fun x =>
      H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaLyapunovNormalizedHJet n) := by
  induction n with
  | zero =>
      funext x
      simp [modularThetaLyapunovNormalizedHJet]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hQ := hasDerivAt_eval_modularThetaLyapunovPolynomial
        (modularThetaLyapunovNormalizedHJet n) v x (hv x)
      have hprod := (hH x).mul hQ
      have hfun :
          (fun y => H y * MvPolynomial.eval (fun j => v j y)
            (modularThetaLyapunovNormalizedHJet n)) =
          H * (fun y => MvPolynomial.eval (fun j => v j y)
            (modularThetaLyapunovNormalizedHJet n)) := by
        funext y
        rfl
      rw [hfun, hprod.deriv]
      rw [modularThetaLyapunovNormalizedHJet]
      unfold modularThetaLyapunovNormalizedLie
      simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- Each source jet is mass times its Lyapunov-coordinate polynomial. -/
theorem mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq
    (v : ModularThetaLyapunovState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
    (n : ℕ) (x : ℝ) :
    H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaLyapunovNormalizedSourceJet n) =
      (iteratedDeriv (n + 2) H x -
        (1 / 4 : ℂ) * iteratedDeriv n H x) / 2 := by
  rw [iteratedDeriv_eq_mass_mul_eval_modularThetaLyapunovNormalizedHJet v hv H hH,
    iteratedDeriv_eq_mass_mul_eval_modularThetaLyapunovNormalizedHJet v hv H hH]
  simp only [modularThetaLyapunovNormalizedSourceJet, map_mul, map_sub,
    MvPolynomial.eval_C]
  ring

/-- Exact rank-three reflected closure in the physical Lyapunov variables. -/
theorem modularThetaLyapunovReflectedEighthClosure_of_ode
    (v : ModularThetaLyapunovState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaLyapunovVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (-(1 / 6 : ℂ) * H x * v .S x) x)
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
        modularThetaLyapunovReflectedEighthPolynomial := by
  dsimp only
  unfold modularThetaLyapunovReflectedEighthPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 0 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 1 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 2 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 3 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 4 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 5 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 6 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 7 x,
    ← mass_mul_eval_modularThetaLyapunovNormalizedSourceJet_eq v hv H hH 8 x]
  unfold signedEvenHankelThreeDetC
  ring

end

end HTGeometry
