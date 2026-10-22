import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeClosure
import GaloisForLFunctions.HTGeometry.MvPolynomialSmoothEvaluation

/-!
# Arbitrary-basepoint rank-three closure for the modular theta ODE

The four-state modular theta ODE defines a polynomial Lie derivative on its coordinate ring.
Iterating that derivation produces every completed-theta jet at an arbitrary basepoint, without
the seam restrictions `Z = P = 0`.  Evaluating the resulting universal polynomial on any real
ODE trajectory gives the exact rank-three reflected eighth-jet determinant.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

/-- Chain rule for a complex multivariate polynomial along a real-parameter complex curve. -/
theorem hasDerivAt_mvPolynomial_eval_curve_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ)
    (g : ι → ℝ → ℂ) (g' : ι → ℂ) (x : ℝ)
    (hg : ∀ j, HasDerivAt (g j) (g' j) x) :
    HasDerivAt (fun s => MvPolynomial.eval (fun j => g j s) P)
      (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j P) * g' j) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hcf : (fun s => MvPolynomial.eval (fun j => g j s)
          (MvPolynomial.C a)) = fun _ => a := by
        funext s
        simp
      rw [hcf]
      simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      exact hasDerivAt_const x a
  | add p q hp hq =>
      have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          fun s => MvPolynomial.eval (fun j => g j s) p +
            MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hf]
      convert! hp.add hq using 1
      all_goals simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      have hfun : (fun s => MvPolynomial.eval (fun j => g j s)
          (p * MvPolynomial.X i)) =
          fun s => MvPolynomial.eval (fun j => g j s) p * g i s := by
        funext s
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hfun]
      convert! hp.mul (hg i) using 1
      all_goals simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, MvPolynomial.pderiv_X, Pi.single_apply, mul_ite,
          mul_one, mul_zero, add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · intro hi
          simp at hi

/-- Coordinates of the autonomous modular theta ODE. -/
inductive ModularThetaODEState
  | H
  | Z
  | R
  | P
  deriving DecidableEq, Fintype

abbrev ModularThetaODEPolynomial := MvPolynomial ModularThetaODEState ℂ

/-- Polynomial vector field of the modular theta ODE. -/
def modularThetaODEVectorField :
    ModularThetaODEState → ModularThetaODEPolynomial
  | .H => MvPolynomial.C (-(1 / 6 : ℂ)) * MvPolynomial.X .H *
      (MvPolynomial.X .P + MvPolynomial.X .R * MvPolynomial.X .Z)
  | .Z => -MvPolynomial.X .R *
      (MvPolynomial.C 1 - MvPolynomial.X .Z ^ (2 : ℕ))
  | .R => MvPolynomial.C (-(2 / 3 : ℂ)) * MvPolynomial.X .R *
      (MvPolynomial.X .P + MvPolynomial.X .R * MvPolynomial.X .Z)
  | .P => MvPolynomial.C 3 - MvPolynomial.C (1 / 3 : ℂ) *
      MvPolynomial.X .P ^ (2 : ℕ) +
      MvPolynomial.C (1 / 12 : ℂ) * MvPolynomial.X .R ^ (2 : ℕ) *
        (MvPolynomial.C 3 + MvPolynomial.X .Z ^ (2 : ℕ))

/-- Lie derivative of a polynomial observable along the modular theta vector field. -/
def modularThetaODELie (Q : ModularThetaODEPolynomial) :
    ModularThetaODEPolynomial :=
  ∑ i, MvPolynomial.pderiv i Q * modularThetaODEVectorField i

/-- Universal polynomial for the `n`-th derivative of the completed theta profile. -/
def modularThetaODEHJet : ℕ → ModularThetaODEPolynomial
  | 0 => MvPolynomial.X .H
  | n + 1 => modularThetaODELie (modularThetaODEHJet n)

/-- Universal polynomial for the `n`-th derivative of the theta-cusp source. -/
def modularThetaODESourceJet (n : ℕ) : ModularThetaODEPolynomial :=
  (modularThetaODEHJet (n + 2) - MvPolynomial.C (1 / 4 : ℂ) *
    modularThetaODEHJet n) * MvPolynomial.C (1 / 2 : ℂ)

/-- Lie derivative after dividing a completed-theta jet by the theta-mass coordinate `H`. -/
def modularThetaODENormalizedLie (Q : ModularThetaODEPolynomial) :
    ModularThetaODEPolynomial :=
  modularThetaODELie Q +
    MvPolynomial.C (-(1 / 6 : ℂ)) *
      (MvPolynomial.X ModularThetaODEState.P +
        MvPolynomial.X ModularThetaODEState.R *
          MvPolynomial.X ModularThetaODEState.Z) * Q

/-- Universal completed-theta jet with its common theta-mass factor removed. -/
def modularThetaODENormalizedHJet : ℕ → ModularThetaODEPolynomial
  | 0 => 1
  | n + 1 => modularThetaODENormalizedLie (modularThetaODENormalizedHJet n)

/-- Universal theta-cusp source jet with its common theta-mass factor removed. -/
def modularThetaODENormalizedSourceJet (n : ℕ) : ModularThetaODEPolynomial :=
  (modularThetaODENormalizedHJet (n + 2) -
    MvPolynomial.C (1 / 4 : ℂ) * modularThetaODENormalizedHJet n) *
      MvPolynomial.C (1 / 2 : ℂ)

/-- Universal arbitrary-basepoint polynomial for raw rank-three reflected eighth curvature. -/
def modularThetaReflectedEighthGeneralPolynomial : ModularThetaODEPolynomial :=
  let f := modularThetaODESourceJet
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

/-- Universal arbitrary-basepoint rank-three polynomial after removing `H ^ (6 : ℕ)`. -/
def modularThetaReflectedEighthNormalizedPolynomial : ModularThetaODEPolynomial :=
  let f := modularThetaODENormalizedSourceJet
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

/-- The modular Lie operator satisfies the Leibniz rule. -/
theorem modularThetaODELie_mul (Q S : ModularThetaODEPolynomial) :
    modularThetaODELie (Q * S) =
      modularThetaODELie Q * S + Q * modularThetaODELie S := by
  unfold modularThetaODELie
  simp_rw [MvPolynomial.pderiv_mul, add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The modular Lie operator is additive. -/
theorem modularThetaODELie_add (Q S : ModularThetaODEPolynomial) :
    modularThetaODELie (Q + S) = modularThetaODELie Q + modularThetaODELie S := by
  simp [modularThetaODELie, add_mul, Finset.sum_add_distrib]

/-- Constant observables have zero modular Lie derivative. -/
theorem modularThetaODELie_C (c : ℂ) :
    modularThetaODELie (MvPolynomial.C c) = 0 := by
  simp [modularThetaODELie]

/-- Coordinate observables differentiate to the corresponding vector-field coordinate. -/
theorem modularThetaODELie_X (i : ModularThetaODEState) :
    modularThetaODELie (MvPolynomial.X i) = modularThetaODEVectorField i := by
  unfold modularThetaODELie
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [MvPolynomial.pderiv_X, hji]
  · simp

/-- Exact zeroth source factor after division by theta mass. -/
theorem eval_modularThetaODENormalizedSourceJet_zero
    (v : ModularThetaODEState → ℂ) :
    MvPolynomial.eval v (modularThetaODENormalizedSourceJet 0) =
      (1 / 24 : ℂ) * v ModularThetaODEState.P ^ (2 : ℕ) +
      (1 / 12 : ℂ) * v ModularThetaODEState.R * v ModularThetaODEState.P *
        v ModularThetaODEState.Z +
      (1 / 48 : ℂ) * v ModularThetaODEState.R ^ (2 : ℕ) *
        (3 - v ModularThetaODEState.Z ^ (2 : ℕ)) - 3 / 8 := by
  have h1 : modularThetaODENormalizedHJet 1 =
      MvPolynomial.C (-(1 / 6 : ℂ)) *
        (MvPolynomial.X ModularThetaODEState.P +
          MvPolynomial.X ModularThetaODEState.R *
            MvPolynomial.X ModularThetaODEState.Z) := by
    simp [modularThetaODENormalizedHJet, modularThetaODENormalizedLie,
      modularThetaODELie]
  unfold modularThetaODENormalizedSourceJet
  change MvPolynomial.eval v
    ((modularThetaODENormalizedLie (modularThetaODENormalizedHJet 1) -
      MvPolynomial.C (1 / 4 : ℂ) * 1) * MvPolynomial.C (1 / 2 : ℂ)) = _
  rw [h1]
  unfold modularThetaODENormalizedLie
  rw [modularThetaODELie_mul, modularThetaODELie_C, zero_mul, zero_add,
    modularThetaODELie_add, modularThetaODELie_X, modularThetaODELie_mul,
    modularThetaODELie_X, modularThetaODELie_X]
  unfold modularThetaODEVectorField
  simp only [map_sub, map_mul, map_add, map_neg, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_one]
  ring

/-- The Lie derivative of the theta-mass coordinate has `H` as an exact factor. -/
theorem modularThetaODELie_X_H :
    modularThetaODELie (MvPolynomial.X ModularThetaODEState.H) =
      MvPolynomial.C (-(1 / 6 : ℂ)) *
        MvPolynomial.X ModularThetaODEState.H *
          (MvPolynomial.X ModularThetaODEState.P +
            MvPolynomial.X ModularThetaODEState.R *
              MvPolynomial.X ModularThetaODEState.Z) := by
  unfold modularThetaODELie
  rw [Finset.sum_eq_single ModularThetaODEState.H]
  · simp [modularThetaODEVectorField]
  · intro i hi hne
    simp [MvPolynomial.pderiv_X, hne]
  · simp

/-- Product rule specialized to a single theta-mass factor. -/
theorem modularThetaODELie_X_H_mul (Q : ModularThetaODEPolynomial) :
    modularThetaODELie (MvPolynomial.X ModularThetaODEState.H * Q) =
      MvPolynomial.X ModularThetaODEState.H * modularThetaODENormalizedLie Q := by
  rw [modularThetaODELie_mul, modularThetaODELie_X_H]
  unfold modularThetaODENormalizedLie
  ring

/-- Every completed-theta Lie jet is divisible by the theta-mass coordinate. -/
theorem modularThetaODEHJet_eq_X_H_mul_normalized (n : ℕ) :
    modularThetaODEHJet n =
      MvPolynomial.X ModularThetaODEState.H * modularThetaODENormalizedHJet n := by
  induction n with
  | zero => simp [modularThetaODEHJet, modularThetaODENormalizedHJet]
  | succ n ih =>
      rw [modularThetaODEHJet, ih, modularThetaODELie_X_H_mul]
      rfl

/-- Every theta-cusp source jet is divisible by the theta-mass coordinate. -/
theorem modularThetaODESourceJet_eq_X_H_mul_normalized (n : ℕ) :
    modularThetaODESourceJet n =
      MvPolynomial.X ModularThetaODEState.H * modularThetaODENormalizedSourceJet n := by
  unfold modularThetaODESourceJet modularThetaODENormalizedSourceJet
  rw [modularThetaODEHJet_eq_X_H_mul_normalized,
    modularThetaODEHJet_eq_X_H_mul_normalized]
  ring

/-- The universal rank-three determinant is homogeneous of degree six in theta mass. -/
theorem modularThetaReflectedEighthGeneralPolynomial_eq_H_pow_six_mul_normalized :
    modularThetaReflectedEighthGeneralPolynomial =
      MvPolynomial.X ModularThetaODEState.H ^ (6 : ℕ) *
        modularThetaReflectedEighthNormalizedPolynomial := by
  unfold modularThetaReflectedEighthGeneralPolynomial
    modularThetaReflectedEighthNormalizedPolynomial
  dsimp only
  rw [modularThetaODESourceJet_eq_X_H_mul_normalized 0,
    modularThetaODESourceJet_eq_X_H_mul_normalized 1,
    modularThetaODESourceJet_eq_X_H_mul_normalized 2,
    modularThetaODESourceJet_eq_X_H_mul_normalized 3,
    modularThetaODESourceJet_eq_X_H_mul_normalized 4,
    modularThetaODESourceJet_eq_X_H_mul_normalized 5,
    modularThetaODESourceJet_eq_X_H_mul_normalized 6,
    modularThetaODESourceJet_eq_X_H_mul_normalized 7,
    modularThetaODESourceJet_eq_X_H_mul_normalized 8]
  ring

/-- Evaluation exposes the exact positive-mass sixth-power factor pointwise. -/
theorem eval_modularThetaReflectedEighthGeneralPolynomial_eq_H_pow_six_mul_normalized
    (v : ModularThetaODEState → ℂ) :
    MvPolynomial.eval v modularThetaReflectedEighthGeneralPolynomial =
      v ModularThetaODEState.H ^ (6 : ℕ) *
        MvPolynomial.eval v modularThetaReflectedEighthNormalizedPolynomial := by
  rw [modularThetaReflectedEighthGeneralPolynomial_eq_H_pow_six_mul_normalized]
  simp

/-- Differentiating any polynomial observable is evaluation of its modular Lie derivative. -/
theorem hasDerivAt_eval_modularThetaODEPolynomial
    (Q : ModularThetaODEPolynomial)
    (v : ModularThetaODEState → ℝ → ℂ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaODEVectorField i)) x) :
    HasDerivAt (fun y => MvPolynomial.eval (fun j => v j y) Q)
      (MvPolynomial.eval (fun j => v j x) (modularThetaODELie Q)) x := by
  have h := hasDerivAt_mvPolynomial_eval_curve_real Q v
    (fun i => MvPolynomial.eval (fun j => v j x) (modularThetaODEVectorField i)) x hv
  convert h using 1
  simp only [modularThetaODELie, map_sum, map_mul]

/-- Iterated derivatives of the `H` coordinate equal universal Lie-jet evaluation. -/
theorem iteratedDeriv_modularThetaODE_H_eq_eval
    (v : ModularThetaODEState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaODEVectorField i)) x)
    (n : ℕ) :
    iteratedDeriv n (v .H) =
      fun x => MvPolynomial.eval (fun j => v j x) (modularThetaODEHJet n) := by
  induction n with
  | zero =>
      funext x
      simp [modularThetaODEHJet]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_eval_modularThetaODEPolynomial
        (modularThetaODEHJet n) v x (hv x)).deriv

/-- Source-jet polynomial evaluates to the exact differentiated source combination. -/
theorem eval_modularThetaODESourceJet_eq
    (v : ModularThetaODEState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaODEVectorField i)) x)
    (n : ℕ) (x : ℝ) :
    MvPolynomial.eval (fun j => v j x) (modularThetaODESourceJet n) =
      (iteratedDeriv (n + 2) (v .H) x -
        (1 / 4 : ℂ) * iteratedDeriv n (v .H) x) / 2 := by
  rw [iteratedDeriv_modularThetaODE_H_eq_eval v hv,
    iteratedDeriv_modularThetaODE_H_eq_eval v hv]
  simp [modularThetaODESourceJet]
  ring

/-- Exact rank-three reflected eighth closure at every basepoint of any modular ODE trajectory. -/
theorem modularThetaReflectedEighthGeneralClosure_of_ode
    (v : ModularThetaODEState → ℝ → ℂ)
    (hv : ∀ x i, HasDerivAt (v i)
      (MvPolynomial.eval (fun j => v j x) (modularThetaODEVectorField i)) x)
    (x : ℝ) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) (v .H) x -
        (1 / 4 : ℂ) * iteratedDeriv n (v .H) x) / 2
    signedEvenHankelThreeDetC
      (f 0 ^ (2 : ℕ))
      (2 * (f 0 * f 2 - f 1 ^ (2 : ℕ)))
      (2 * f 0 * f 4 - 8 * f 1 * f 3 + 6 * f 2 ^ (2 : ℕ))
      (2 * f 0 * f 6 - 12 * f 1 * f 5 + 30 * f 2 * f 4 - 20 * f 3 ^ (2 : ℕ))
      (2 * f 0 * f 8 - 16 * f 1 * f 7 + 56 * f 2 * f 6 -
        112 * f 3 * f 5 + 70 * f 4 ^ (2 : ℕ)) =
      MvPolynomial.eval (fun j => v j x)
        modularThetaReflectedEighthGeneralPolynomial := by
  dsimp only
  unfold modularThetaReflectedEighthGeneralPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [eval_modularThetaODESourceJet_eq v hv 0 x,
    eval_modularThetaODESourceJet_eq v hv 1 x,
    eval_modularThetaODESourceJet_eq v hv 2 x,
    eval_modularThetaODESourceJet_eq v hv 3 x,
    eval_modularThetaODESourceJet_eq v hv 4 x,
    eval_modularThetaODESourceJet_eq v hv 5 x,
    eval_modularThetaODESourceJet_eq v hv 6 x,
    eval_modularThetaODESourceJet_eq v hv 7 x,
    eval_modularThetaODESourceJet_eq v hv 8 x]
  unfold signedEvenHankelThreeDetC
  ring

end


end HTGeometry
