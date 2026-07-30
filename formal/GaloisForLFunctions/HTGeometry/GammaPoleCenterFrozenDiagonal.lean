import GaloisForLFunctions.HTGeometry.GammaPoleSymbolicTriGrading

/-!
# Center-frozen maximal derivative-weight diagonal for Gamma

This file closes the noncancellation interface at Taylor order zero.  It
extends homogeneous dehomogenization from a distinguished finite jet
coordinate to the rational pole-position field, proves that polynomial
coefficient evaluation at the moving Gamma pole remains faithful, and then
identifies the exact joint coefficient at particle pole grade `D` and signed
scale grade `-W`.

For a nonzero source sector homogeneous both in particle degree `D` and
derivative weight `W`, that coefficient is

```text
(-1)^(D+W) * dehomogenized center boundary polynomial,
```

and is unconditionally nonzero.  The remaining global diagonal step is to
show that positive Taylor orders from lower derivative-weight sectors cannot
cancel this center-frozen maximal sector.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

def finiteHeadDehomogenize
    (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  optionHeadDehomogenize.comp
    (MvPolynomial.renameEquiv R (_root_.finSuccEquiv n)).toRingHom

@[simp] theorem finiteHeadDehomogenize_X_zero
    (R : Type*) [CommSemiring R] (n : ℕ) :
    finiteHeadDehomogenize R n (MvPolynomial.X 0) = 1 := by
  simp [finiteHeadDehomogenize, optionHeadDehomogenize]

@[simp] theorem finiteHeadDehomogenize_X_succ
    (R : Type*) [CommSemiring R] (n : ℕ) (j : Fin n) :
    finiteHeadDehomogenize R n (MvPolynomial.X j.succ) =
      MvPolynomial.X j := by
  simp [finiteHeadDehomogenize, optionHeadDehomogenize]

theorem finiteHeadDehomogenize_ne_zero_of_isHomogeneous
    {R : Type*} [CommSemiring R] [Nontrivial R] {n D : ℕ}
    {P : MvPolynomial (Fin (n + 1)) R}
    (hD : P.IsHomogeneous D) (hP : P ≠ 0) :
    finiteHeadDehomogenize R n P ≠ 0 := by
  let E := MvPolynomial.renameEquiv R (_root_.finSuccEquiv n)
  have hEP : (E P).IsHomogeneous D := by
    simpa [E] using hD.rename_isHomogeneous
  have hEP0 : E P ≠ 0 := E.injective.ne hP
  exact optionHeadDehomogenize_ne_zero_of_isHomogeneous hEP hEP0

def gammaPoleFiniteBoundaryDehomogenize (n : ℕ) :
    MvPolynomial (Fin (n + 1)) GammaPoleRationalBase →+*
      MvPolynomial ℕ GammaPoleRationalBase :=
  (MvPolynomial.rename fun j : Fin n => (j : ℕ)).toRingHom.comp
    (finiteHeadDehomogenize GammaPoleRationalBase n)

theorem gammaPoleFiniteBoundaryDehomogenize_ne_zero_of_isHomogeneous
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) GammaPoleRationalBase}
    (hD : P.IsHomogeneous D) (hP : P ≠ 0) :
    gammaPoleFiniteBoundaryDehomogenize n P ≠ 0 := by
  exact (MvPolynomial.rename_injective _ Fin.val_injective).ne
    (finiteHeadDehomogenize_ne_zero_of_isHomogeneous hD hP)

def gammaPoleCenterBoundaryPolynomialEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      MvPolynomial ℕ GammaPoleRationalBase :=
  (gammaPoleFiniteBoundaryDehomogenize n).comp
    (MvPolynomial.map gammaPoleCenterRationalEval)

/-- Center evaluation followed by `U₀ = 1` is faithful on every homogeneous
source sector. -/
theorem gammaPoleCenterBoundaryPolynomialEval_ne_zero_of_isHomogeneous
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D) (hP : P ≠ 0) :
    gammaPoleCenterBoundaryPolynomialEval n P ≠ 0 := by
  have hmapD : (P.map gammaPoleCenterRationalEval).IsHomogeneous D :=
    hD.map gammaPoleCenterRationalEval
  have hmap0 : P.map gammaPoleCenterRationalEval ≠ 0 := by
    simpa using (MvPolynomial.map_injective gammaPoleCenterRationalEval
      gammaPoleCenterRationalEval_injective).ne hP
  exact gammaPoleFiniteBoundaryDehomogenize_ne_zero_of_isHomogeneous
    hmapD hmap0

@[simp] theorem gammaPoleCenterBoundaryPolynomialEval_C
    (n : ℕ) (p : Polynomial ℂ) :
    gammaPoleCenterBoundaryPolynomialEval n (MvPolynomial.C p) =
      MvPolynomial.C (gammaPoleCenterRationalEval p) := by
  simp [gammaPoleCenterBoundaryPolynomialEval,
    gammaPoleFiniteBoundaryDehomogenize,
    finiteHeadDehomogenize, optionHeadDehomogenize]

@[simp] theorem gammaPoleCenterBoundaryPolynomialEval_X_zero (n : ℕ) :
    gammaPoleCenterBoundaryPolynomialEval n (MvPolynomial.X 0) = 1 := by
  simp [gammaPoleCenterBoundaryPolynomialEval,
    gammaPoleFiniteBoundaryDehomogenize]

@[simp] theorem gammaPoleCenterBoundaryPolynomialEval_X_succ
    (n : ℕ) (j : Fin n) :
    gammaPoleCenterBoundaryPolynomialEval n (MvPolynomial.X j.succ) =
      MvPolynomial.X (j : ℕ) := by
  simp [gammaPoleCenterBoundaryPolynomialEval,
    gammaPoleFiniteBoundaryDehomogenize]

def gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile
    (j : ℕ) : GammaPoleMovingJetSymbolic :=
  Polynomial.toLaurent
    ((HTGeometry.universalSimplePoleRegularProfile j).map
      gammaPoleSymbolicUnitDerivativeBoundaryEval)

theorem gammaPoleSymbolicUniversalDerivativeLaurentProfile_factor
    (j : ℕ) :
    gammaPoleSymbolicUniversalDerivativeLaurentProfile j =
      LaurentPolynomial.T 1 *
        gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile j := by
  simp [gammaPoleSymbolicUniversalDerivativeLaurentProfile,
    gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile,
    HTGeometry.universalSimplePoleJetProfile]

def gammaPoleSymbolicCenterUniversalRegularJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicCenterCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile (j : ℕ))

theorem gammaPoleSymbolicCenterUniversalJetLaurentEval_factor
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D) :
    gammaPoleSymbolicCenterUniversalJetLaurentEval n P =
      LaurentPolynomial.T 1 ^ D *
        gammaPoleSymbolicCenterUniversalRegularJetLaurentEval n P := by
  change MvPolynomial.eval₂ gammaPoleSymbolicCenterCoefficientInclude
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicUniversalDerivativeLaurentProfile (j : ℕ)) P = _
  simp_rw [gammaPoleSymbolicUniversalDerivativeLaurentProfile_factor]
  simpa only [gammaPoleSymbolicCenterUniversalRegularJetLaurentEval,
    MvPolynomial.coe_eval₂Hom] using
    isHomogeneous_eval₂_scale_general (P := P) hD
      gammaPoleSymbolicCenterCoefficientInclude
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile (j : ℕ))
      (LaurentPolynomial.T 1)

def gammaPoleSymbolicCenterUniversalRegularPolynomialEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      Polynomial GammaPoleScaleDerivativeSymbolic :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp
      (gammaPoleRationalScaleDerivativeInclude.comp
        gammaPoleCenterRationalEval))
    (fun j : Fin (n + 1) =>
      (HTGeometry.universalSimplePoleRegularProfile (j : ℕ)).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval)

theorem gammaPoleSymbolicCenterUniversalRegularJetLaurentEval_eq
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    gammaPoleSymbolicCenterUniversalRegularJetLaurentEval n P =
      Polynomial.toLaurent
        (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n P) := by
  let rhs : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleMovingJetSymbolic :=
    Polynomial.toLaurent.comp
      (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n)
  have h : gammaPoleSymbolicCenterUniversalRegularJetLaurentEval n = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [gammaPoleSymbolicCenterUniversalRegularJetLaurentEval,
        gammaPoleSymbolicCenterUniversalRegularPolynomialEval, rhs,
        gammaPoleSymbolicCenterCoefficientInclude]
    · intro j
      simp [gammaPoleSymbolicCenterUniversalRegularJetLaurentEval,
        gammaPoleSymbolicCenterUniversalRegularPolynomialEval, rhs,
        gammaPoleSymbolicUniversalRegularDerivativeLaurentProfile]
  exact RingHom.congr_fun h P

theorem gammaPoleSymbolicCenterUniversalRegularPolynomialEval_eval_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n P).eval 0 =
      LaurentPolynomial.C (gammaPoleCenterBoundaryPolynomialEval n P) := by
  let lhs : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleScaleDerivativeSymbolic :=
    (Polynomial.evalRingHom 0).comp
      (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n)
  let rhs : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleScaleDerivativeSymbolic :=
    LaurentPolynomial.C.comp (gammaPoleCenterBoundaryPolynomialEval n)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [lhs, rhs,
        gammaPoleSymbolicCenterUniversalRegularPolynomialEval,
        gammaPoleCenterBoundaryPolynomialEval,
        gammaPoleFiniteBoundaryDehomogenize,
        finiteHeadDehomogenize, optionHeadDehomogenize,
        gammaPoleRationalScaleDerivativeInclude]
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [lhs, rhs,
          gammaPoleSymbolicCenterUniversalRegularPolynomialEval,
          HTGeometry.universalSimplePoleRegularProfile_eval_zero,
          gammaPoleSymbolicUnitDerivativeBoundaryEval,
          gammaPoleSymbolicUnitDerivativeBoundaryFamily]
      · simp [lhs, rhs,
          gammaPoleSymbolicCenterUniversalRegularPolynomialEval,
          HTGeometry.universalSimplePoleRegularProfile_eval_zero,
          gammaPoleSymbolicUnitDerivativeBoundaryEval,
          gammaPoleSymbolicUnitDerivativeBoundaryFamily]
  exact RingHom.congr_fun h P

theorem gammaPoleSymbolicCenterUniversalRegularJetLaurentEval_coeff_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (gammaPoleSymbolicCenterUniversalRegularJetLaurentEval n P).coeff 0 =
      LaurentPolynomial.C (gammaPoleCenterBoundaryPolynomialEval n P) := by
  rw [gammaPoleSymbolicCenterUniversalRegularJetLaurentEval_eq,
    Polynomial.toLaurent_apply]
  change Finsupp.mapDomain (fun q : ℕ => (q : ℤ))
      (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n P).toFinsupp.coeff
        ((0 : ℕ) : ℤ) = _
  have hinj : Function.Injective (fun q : ℕ => (q : ℤ)) :=
    Int.ofNat_injective
  rw [Finsupp.mapDomain_apply hinj]
  change (gammaPoleSymbolicCenterUniversalRegularPolynomialEval n P).coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero,
    gammaPoleSymbolicCenterUniversalRegularPolynomialEval_eval_zero]

/-- The universal center-frozen factor has the exact particle-grade boundary
trace over the rational pole-position field. -/
theorem gammaPoleSymbolicCenterUniversalJetLaurentEval_coeff_particleNumber
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D) :
    (gammaPoleSymbolicCenterUniversalJetLaurentEval n P).coeff (D : ℤ) =
      LaurentPolynomial.C (gammaPoleCenterBoundaryPolynomialEval n P) := by
  rw [gammaPoleSymbolicCenterUniversalJetLaurentEval_factor hD,
    LaurentPolynomial.T_pow]
  simp only [Int.mul_one]
  have hsingle :
      (LaurentPolynomial.T (D : ℤ) : GammaPoleMovingJetSymbolic) =
        AddMonoidAlgebra.single (D : ℤ) 1 := rfl
  rw [hsingle, AddMonoidAlgebra.coeff_single_mul_apply]
  simp only [one_mul, neg_add_cancel]
  exact gammaPoleSymbolicCenterUniversalRegularJetLaurentEval_coeff_zero n P

/-- Center-frozen outer trace after restoring the exact particle and
derivative scales. -/
theorem gammaPoleSymbolicCenterJetLaurentEval_coeff_particleNumber
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    (gammaPoleSymbolicCenterJetLaurentEval n P).coeff (D : ℤ) =
      gammaPoleSymbolicBiscaleFactor D W *
        LaurentPolynomial.C (gammaPoleCenterBoundaryPolynomialEval n P) := by
  rw [gammaPoleSymbolicCenterJetLaurentEval_biscale_factor hD hW,
    gammaPoleSymbolicBiscaleFactor_outer_eq,
    ← LaurentPolynomial.smul_eq_C_mul]
  change gammaPoleSymbolicBiscaleFactor D W *
      (gammaPoleSymbolicCenterUniversalJetLaurentEval n P).coeff (D : ℤ) = _
  rw [gammaPoleSymbolicCenterUniversalJetLaurentEval_coeff_particleNumber hD]

theorem gammaPoleSymbolicBiscaleFactor_eq (D W : ℕ) :
    gammaPoleSymbolicBiscaleFactor D W =
      (-1 : GammaPoleScaleDerivativeSymbolic) ^ (D + W) *
        LaurentPolynomial.T (-(W : ℤ)) := by
  have hpow :
      (-LaurentPolynomial.T (-1) : GammaPoleScaleDerivativeSymbolic) ^ W =
        (-1 : GammaPoleScaleDerivativeSymbolic) ^ W *
          LaurentPolynomial.T (-(W : ℤ)) := by
    calc
      (-LaurentPolynomial.T (-1) : GammaPoleScaleDerivativeSymbolic) ^ W =
          ((-1 : GammaPoleScaleDerivativeSymbolic) *
            LaurentPolynomial.T (-1)) ^ W := by
              congr 1
              ring
      _ = (-1 : GammaPoleScaleDerivativeSymbolic) ^ W *
          LaurentPolynomial.T (-1) ^ W := by
            exact mul_pow _ _ _
      _ = _ := by
        congr 1
        simp [LaurentPolynomial.T_pow]
  rw [gammaPoleSymbolicBiscaleFactor, hpow, pow_add]
  ring

theorem gammaPoleSymbolicBiscaleSign_eq (D W : ℕ) :
    (-1 : GammaPoleScaleDerivativeSymbolic) ^ (D + W) =
      LaurentPolynomial.C
        (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W)))) := by
  calc
    (-1 : GammaPoleScaleDerivativeSymbolic) ^ (D + W) =
        (gammaPoleRationalScaleDerivativeInclude
          (RatFunc.C (-1 : ℂ))) ^ (D + W) := by
      simp [gammaPoleRationalScaleDerivativeInclude]
    _ = gammaPoleRationalScaleDerivativeInclude
        ((RatFunc.C (-1 : ℂ)) ^ (D + W)) := by rw [map_pow]
    _ = gammaPoleRationalScaleDerivativeInclude
        (RatFunc.C ((-1 : ℂ) ^ (D + W))) := by rw [← map_pow]
    _ = _ := rfl

/-- **Center-frozen nonlinear diagonal.** The joint coefficient at particle
pole grade `D` and derivative scale grade `-W` is exactly the signed
dehomogenized boundary polynomial. -/
theorem gammaPoleSymbolicCenterJetLaurentEval_particle_derivative_coeff
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    ((gammaPoleSymbolicCenterJetLaurentEval n P).coeff (D : ℤ)).coeff (-(W : ℤ)) =
      MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W))) *
        gammaPoleCenterBoundaryPolynomialEval n P := by
  rw [gammaPoleSymbolicCenterJetLaurentEval_coeff_particleNumber hD hW,
    gammaPoleSymbolicBiscaleFactor_eq,
    gammaPoleSymbolicBiscaleSign_eq]
  have heq :
      (LaurentPolynomial.C
          (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W)))) *
        LaurentPolynomial.T (-(W : ℤ))) *
          LaurentPolynomial.C (gammaPoleCenterBoundaryPolynomialEval n P) =
        LaurentPolynomial.C
            (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W))) *
              gammaPoleCenterBoundaryPolynomialEval n P) *
          LaurentPolynomial.T (-(W : ℤ)) := by
    rw [mul_right_comm, ← map_mul]
  rw [heq, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- The center-frozen maximal-weight diagonal of a nonzero homogeneous source
sector cannot vanish. -/
theorem gammaPoleSymbolicCenterJetLaurentEval_particle_derivative_coeff_ne_zero
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W)
    (hP : P ≠ 0) :
    ((gammaPoleSymbolicCenterJetLaurentEval n P).coeff (D : ℤ)).coeff (-(W : ℤ)) ≠ 0 := by
  rw [gammaPoleSymbolicCenterJetLaurentEval_particle_derivative_coeff hD hW]
  have hscalar :
      (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ (D + W))) :
        MvPolynomial ℕ GammaPoleRationalBase) ≠ 0 := by
    simpa only [map_zero] using
      ((MvPolynomial.C_injective ℕ GammaPoleRationalBase).ne
        (RatFunc.C_injective.ne
          (pow_ne_zero (D + W) (neg_ne_zero.mpr one_ne_zero))))
  exact mul_ne_zero hscalar
    (gammaPoleCenterBoundaryPolynomialEval_ne_zero_of_isHomogeneous hD hP)

end

end GaloisForLFunctions
