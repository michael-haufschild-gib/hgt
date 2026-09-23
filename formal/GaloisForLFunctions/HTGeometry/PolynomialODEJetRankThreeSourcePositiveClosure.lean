import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreePositiveChamberClosure

/-!
# Source-positive modular theta jet closure

Replace the positive-chamber gap coordinate by the mass-normalized source
`Q = F/H = (6B²+A-6)/16`.  The resulting `(U,B,Q)` vector field is polynomial, and all three
coordinates are strictly positive on the physical positive half-orbit.  Source jets now start at
the literal variable `Q`, rather than being reconstructed from two theta-mass derivatives.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Coordinates of the source-positive theta chamber. -/
inductive ModularThetaSourcePositiveState
  | U
  | B
  | Q
  deriving DecidableEq, Fintype

abbrev ModularThetaSourcePositivePolynomial :=
  MvPolynomial ModularThetaSourcePositiveState ℂ

/-- Reconstructed discriminant gap `A = 16Q+6-6B²`. -/
def modularThetaSourcePositiveGap : ModularThetaSourcePositivePolynomial :=
  MvPolynomial.C 16 * MvPolynomial.X .Q + MvPolynomial.C 6 -
    MvPolynomial.C 6 * MvPolynomial.X .B ^ (2 : ℕ)

/-- Autonomous polynomial vector field in `(U,B,Q)`. -/
def modularThetaSourcePositiveVectorField :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => MvPolynomial.C (9 / 2 : ℂ) +
      MvPolynomial.C 4 * MvPolynomial.X .Q +
      MvPolynomial.C (3 / 2 : ℂ) * MvPolynomial.X .B ^ (2 : ℕ) +
      MvPolynomial.C 2 * MvPolynomial.X .B * MvPolynomial.X .U
  | .B => MvPolynomial.C (1 / 2 : ℂ) +
      MvPolynomial.C 4 * MvPolynomial.X .Q -
      MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B ^ (2 : ℕ)
  | .Q => MvPolynomial.C (3 / 4 : ℂ) * MvPolynomial.X .B *
        (MvPolynomial.C (1 / 2 : ℂ) +
          MvPolynomial.C 4 * MvPolynomial.X .Q -
          MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B ^ (2 : ℕ)) -
      MvPolynomial.C (1 / 8 : ℂ) * modularThetaSourcePositiveGap *
        (MvPolynomial.X .U + MvPolynomial.X .B)

/-- Lie derivative along the source-positive vector field. -/
def modularThetaSourcePositiveLie (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  ∑ i, MvPolynomial.pderiv i P * modularThetaSourcePositiveVectorField i

/-- Covariant Lie derivative for one mass-normalized source jet. -/
def modularThetaSourcePositiveNormalizedLie
    (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveLie P +
    MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B * P

/-- Source jets after division by common theta mass. -/
def modularThetaSourcePositiveNormalizedSourceJet :
    ℕ → ModularThetaSourcePositivePolynomial
  | 0 => MvPolynomial.X .Q
  | n + 1 => modularThetaSourcePositiveNormalizedLie
      (modularThetaSourcePositiveNormalizedSourceJet n)

/-- Rank-three reflected eighth polynomial in source-positive coordinates. -/
def modularThetaSourcePositiveReflectedEighthPolynomial :
    ModularThetaSourcePositivePolynomial :=
  let f := modularThetaSourcePositiveNormalizedSourceJet
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

/-- Polynomial observables differentiate by the source-positive Lie derivative. -/
theorem hasDerivAt_eval_modularThetaSourcePositivePolynomial
    (P : ModularThetaSourcePositivePolynomial)
    (v : ModularThetaSourcePositiveState → ℝ → ℂ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x)
        (modularThetaSourcePositiveVectorField i)) x) :
    HasDerivAt (fun y => MvPolynomial.eval (fun j => v j y) P)
      (MvPolynomial.eval (fun j => v j x) (modularThetaSourcePositiveLie P)) x := by
  have h := hasDerivAt_mvPolynomial_eval_curve_real P v
    (fun i => MvPolynomial.eval (fun j => v j x)
      (modularThetaSourcePositiveVectorField i)) x hv
  convert h using 1
  simp only [modularThetaSourcePositiveLie, map_sum, map_mul]

/-- Every source derivative is mass times its normalized source-positive jet. -/
theorem iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet
    (v : ModularThetaSourcePositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x)
        (modularThetaSourcePositiveVectorField i)) x)
    (H : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (n : ℕ) :
    iteratedDeriv n (fun x => H x * v .Q x) = fun x =>
      H x * MvPolynomial.eval (fun j => v j x)
        (modularThetaSourcePositiveNormalizedSourceJet n) := by
  induction n with
  | zero =>
      funext x
      simp [modularThetaSourcePositiveNormalizedSourceJet]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hP := hasDerivAt_eval_modularThetaSourcePositivePolynomial
        (modularThetaSourcePositiveNormalizedSourceJet n) v x (hv x)
      have hprod := (hH x).mul hP
      have hfun :
          (fun y => H y * MvPolynomial.eval (fun j => v j y)
            (modularThetaSourcePositiveNormalizedSourceJet n)) =
          H * (fun y => MvPolynomial.eval (fun j => v j y)
            (modularThetaSourcePositiveNormalizedSourceJet n)) := by
        funext y
        rfl
      rw [hfun, hprod.deriv]
      rw [modularThetaSourcePositiveNormalizedSourceJet]
      unfold modularThetaSourcePositiveNormalizedLie
      simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- Exact rank-three reflected closure in source-positive variables. -/
theorem modularThetaSourcePositiveReflectedEighthClosure_of_ode
    (v : ModularThetaSourcePositiveState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x)
        (modularThetaSourcePositiveVectorField i)) x)
    (H F : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H ((1 / 2 : ℂ) * H x * v .B x) x)
    (hF : ∀ x, F x = H x * v .Q x)
    (x : ℝ) :
    let f : ℕ → ℂ := fun n => iteratedDeriv n F x
    signedEvenHankelThreeDetC
      (f 0 ^ (2 : ℕ))
      (2 * (f 0 * f 2 - f 1 ^ (2 : ℕ)))
      (2 * f 0 * f 4 - 8 * f 1 * f 3 + 6 * f 2 ^ (2 : ℕ))
      (2 * f 0 * f 6 - 12 * f 1 * f 5 + 30 * f 2 * f 4 - 20 * f 3 ^ (2 : ℕ))
      (2 * f 0 * f 8 - 16 * f 1 * f 7 + 56 * f 2 * f 6 -
        112 * f 3 * f 5 + 70 * f 4 ^ (2 : ℕ)) =
      H x ^ (6 : ℕ) * MvPolynomial.eval (fun j => v j x)
        modularThetaSourcePositiveReflectedEighthPolynomial := by
  have hfun : F = fun y => H y * v .Q y := by
    funext y
    exact hF y
  rw [hfun]
  dsimp only
  unfold modularThetaSourcePositiveReflectedEighthPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 0,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 1,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 2,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 3,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 4,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 5,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 6,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 7,
    iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet v hv H hH 8]
  unfold signedEvenHankelThreeDetC
  ring

end

end HTGeometry
