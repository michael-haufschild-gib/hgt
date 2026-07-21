import GaloisForLFunctions.HTGeometry.GammaPoleSymbolicMovingJetLaurent
import GaloisForLFunctions.HTGeometry.SimplePoleJetLatticeAffineHorizon
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Conserved tri-grading of the symbolic Gamma pole profile

The faithful symbolic Gamma target has three independent coordinates: outer
pole order, signed factorial-scale order, and the multidegree in positive
regular-unit derivatives.  This file flattens those coordinates and proves the
exact conservation law

```text
pole order + scale order + boundary derivative weight = source degree.
```

Polynomial coefficients have grade zero, every normalized Gamma derivative
profile has grade one, and substitution therefore carries every homogeneous
degree-`d` differential source to the grade-`d` hyperplane.  The final support
theorem exposes the law coefficientwise; it is the grading interface for the
maximal derivative-weight diagonal descent.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

abbrev GammaPoleTriIndex :=
  (ℤ × ℤ) × (ℕ →₀ ℕ)

abbrev GammaPoleTriMonoidAlgebra :=
  AddMonoidAlgebra GammaPoleRationalBase GammaPoleTriIndex

def gammaPoleTriFlatten :
    GammaPoleMovingJetSymbolic ≃+* GammaPoleTriMonoidAlgebra :=
  (AddMonoidAlgebra.curryRingEquiv
      (R := MvPolynomial ℕ GammaPoleRationalBase)
      (M := ℤ) (N := ℤ)).symm.trans
    (AddMonoidAlgebra.curryRingEquiv
      (R := GammaPoleRationalBase)
      (M := ℤ × ℤ) (N := ℕ →₀ ℕ)).symm

def gammaPoleBoundaryDerivativeWeight : (ℕ →₀ ℕ) →+ ℤ :=
  Finsupp.weight fun k : ℕ => (k + 1 : ℤ)

def gammaPoleTriWeight : GammaPoleTriIndex →+ ℤ where
  toFun a := a.1.1 + a.1.2 + gammaPoleBoundaryDerivativeWeight a.2
  map_zero' := by simp [gammaPoleBoundaryDerivativeWeight]
  map_add' a b := by
    simp [gammaPoleBoundaryDerivativeWeight]
    omega

def GammaPoleTrihomogeneous (d : ℤ)
    (F : GammaPoleMovingJetSymbolic) : Prop :=
  gammaPoleTriFlatten F ∈
    AddMonoidAlgebra.gradeBy GammaPoleRationalBase gammaPoleTriWeight d

theorem GammaPoleTrihomogeneous.zero (d : ℤ) :
    GammaPoleTrihomogeneous d 0 := by
  exact Submodule.zero_mem _

theorem GammaPoleTrihomogeneous.add {d : ℤ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleTrihomogeneous d F)
    (hG : GammaPoleTrihomogeneous d G) :
    GammaPoleTrihomogeneous d (F + G) := by
  change gammaPoleTriFlatten (F + G) ∈ _
  rw [map_add]
  exact Submodule.add_mem _ hF hG

theorem GammaPoleTrihomogeneous.sum {ι : Type*} {d : ℤ}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic)
    (hF : ∀ i ∈ s, GammaPoleTrihomogeneous d (F i)) :
    GammaPoleTrihomogeneous d (∑ i ∈ s, F i) := by
  change gammaPoleTriFlatten (∑ i ∈ s, F i) ∈ _
  simp only [map_sum]
  exact Submodule.sum_mem _ fun i hi => hF i hi

theorem GammaPoleTrihomogeneous.prod {ι : Type*}
    (s : Finset ι) (F : ι → GammaPoleMovingJetSymbolic) (e : ι → ℤ)
    (hF : ∀ i ∈ s, GammaPoleTrihomogeneous (e i) (F i)) :
    GammaPoleTrihomogeneous (∑ i ∈ s, e i) (∏ i ∈ s, F i) := by
  change gammaPoleTriFlatten (∏ i ∈ s, F i) ∈ _
  simp only [map_prod]
  exact SetLike.prod_mem_graded _ _ _ hF

theorem GammaPoleTrihomogeneous.mul {d e : ℤ}
    {F G : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleTrihomogeneous d F)
    (hG : GammaPoleTrihomogeneous e G) :
    GammaPoleTrihomogeneous (d + e) (F * G) := by
  change gammaPoleTriFlatten (F * G) ∈ _
  rw [map_mul]
  exact SetLike.GradedMonoid.toGradedMul.mul_mem hF hG

theorem GammaPoleTrihomogeneous.pow {d : ℤ}
    {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleTrihomogeneous d F) (n : ℕ) :
    GammaPoleTrihomogeneous (n * d) (F ^ n) := by
  change gammaPoleTriFlatten (F ^ n) ∈ _
  rw [map_pow]
  simpa [nsmul_eq_mul] using SetLike.pow_mem_graded n hF

theorem gammaPoleTriFlatten_monomial
    (q l : ℤ) (m : ℕ →₀ ℕ) (c : GammaPoleRationalBase) :
    gammaPoleTriFlatten
        (LaurentPolynomial.C
            (LaurentPolynomial.C (MvPolynomial.monomial m c) *
              LaurentPolynomial.T l) *
          LaurentPolynomial.T q) =
      Finsupp.single ((q, l), m) c := by
  have hinner :
      LaurentPolynomial.C (MvPolynomial.monomial m c) *
          LaurentPolynomial.T l =
        (Finsupp.single l (Finsupp.single m c) :
          GammaPoleScaleDerivativeSymbolic) :=
    (LaurentPolynomial.single_eq_C_mul_T (MvPolynomial.monomial m c) l).symm
  have hreplace :
      ((LaurentPolynomial.C : GammaPoleScaleDerivativeSymbolic →+*
          GammaPoleMovingJetSymbolic)
          (LaurentPolynomial.C (MvPolynomial.monomial m c) *
            LaurentPolynomial.T l) *
          LaurentPolynomial.T q : GammaPoleMovingJetSymbolic) =
        ((LaurentPolynomial.C : GammaPoleScaleDerivativeSymbolic →+*
          GammaPoleMovingJetSymbolic)
          (Finsupp.single l (Finsupp.single m c) :
            GammaPoleScaleDerivativeSymbolic) *
          LaurentPolynomial.T q : GammaPoleMovingJetSymbolic) :=
    congrArg (fun a : GammaPoleScaleDerivativeSymbolic =>
      LaurentPolynomial.C a * LaurentPolynomial.T q) hinner
  rw [hreplace]
  have houter :
      (LaurentPolynomial.C : GammaPoleScaleDerivativeSymbolic →+*
          GammaPoleMovingJetSymbolic)
          (Finsupp.single l (Finsupp.single m c) :
            GammaPoleScaleDerivativeSymbolic) *
          LaurentPolynomial.T q =
        (Finsupp.single q (Finsupp.single l (Finsupp.single m c)) :
          GammaPoleMovingJetSymbolic) :=
    (LaurentPolynomial.single_eq_C_mul_T
      (R := GammaPoleScaleDerivativeSymbolic)
      (Finsupp.single l (Finsupp.single m c) :
        GammaPoleScaleDerivativeSymbolic) q).symm
  calc
    gammaPoleTriFlatten
        ((LaurentPolynomial.C : GammaPoleScaleDerivativeSymbolic →+*
            GammaPoleMovingJetSymbolic)
          (Finsupp.single l (Finsupp.single m c) :
            GammaPoleScaleDerivativeSymbolic) * LaurentPolynomial.T q) =
      gammaPoleTriFlatten
        (Finsupp.single q (Finsupp.single l (Finsupp.single m c))) :=
      congrArg gammaPoleTriFlatten houter
    _ = _ := by
      simp only [gammaPoleTriFlatten, RingEquiv.trans_apply,
        AddMonoidAlgebra.curryRingEquiv_symm_single]

theorem gammaPoleTrihomogeneous_monomial
    (q l : ℤ) (m : ℕ →₀ ℕ) (c : GammaPoleRationalBase) :
    GammaPoleTrihomogeneous
      (q + l + gammaPoleBoundaryDerivativeWeight m)
      (LaurentPolynomial.C
          (LaurentPolynomial.C (MvPolynomial.monomial m c) *
            LaurentPolynomial.T l) *
        LaurentPolynomial.T q) := by
  change gammaPoleTriFlatten _ ∈ _
  rw [gammaPoleTriFlatten_monomial]
  exact AddMonoidAlgebra.single_mem_gradeBy _ _ _

theorem gammaPoleSymbolicMovingCoefficientLaurent_X_eq :
    gammaPoleSymbolicMovingCoefficientLaurent Polynomial.X =
      LaurentPolynomial.C
          (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational) +
        LaurentPolynomial.C gammaPoleSymbolicPhysicalScale *
          LaurentPolynomial.T (-1) := by
  simp [gammaPoleSymbolicMovingCoefficientLaurent,
    movingPoleTaylorLaurent, scaledTaylorAlgHom,
    polynomialDiagonalScaleAlgHom, gammaPoleSymbolicPhysicalScale,
    gammaPoleSymbolicScale]
  ring

theorem gammaPoleSymbolicMovingCoefficientLaurent_C_trihomogeneous
    (c : ℂ) :
    GammaPoleTrihomogeneous 0
      (gammaPoleSymbolicMovingCoefficientLaurent (Polynomial.C c)) := by
  simp [gammaPoleSymbolicMovingCoefficientLaurent,
    movingPoleTaylorLaurent, scaledTaylorAlgHom,
    polynomialDiagonalScaleAlgHom]
  simpa [gammaPoleRationalScaleDerivativeInclude,
    gammaPoleComplexScaleDerivativeInclude] using
    gammaPoleTrihomogeneous_monomial 0 0 0 (RatFunc.C c)

theorem gammaPoleSymbolicMovingCoefficientLaurent_X_trihomogeneous :
    GammaPoleTrihomogeneous 0
      (gammaPoleSymbolicMovingCoefficientLaurent Polynomial.X) := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent_X_eq]
  apply GammaPoleTrihomogeneous.add
  · simpa [gammaPoleRationalScaleDerivativeInclude] using
      gammaPoleTrihomogeneous_monomial 0 0 0 gammaPoleCenterRational
  · rw [gammaPoleSymbolicPhysicalScale, gammaPoleSymbolicScale]
    change GammaPoleTrihomogeneous 0
      (LaurentPolynomial.C (-LaurentPolynomial.T 1) *
        LaurentPolynomial.T (-1))
    have h := gammaPoleTrihomogeneous_monomial (-1) 1 0 (-1)
    have heq :
        (-LaurentPolynomial.T 1 : GammaPoleScaleDerivativeSymbolic) =
          LaurentPolynomial.C (MvPolynomial.monomial 0 (-1)) *
            LaurentPolynomial.T 1 := by
      simp
      exact (neg_one_mul
        (LaurentPolynomial.T 1 : GammaPoleScaleDerivativeSymbolic)).symm
    rw [heq]
    simpa using h

theorem gammaPoleSymbolicMovingCoefficientLaurent_trihomogeneous
    (p : Polynomial ℂ) :
    GammaPoleTrihomogeneous 0
      (gammaPoleSymbolicMovingCoefficientLaurent p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        map_mul, map_pow]
      exact (gammaPoleSymbolicMovingCoefficientLaurent_C_trihomogeneous c).mul
        (gammaPoleSymbolicMovingCoefficientLaurent_X_trihomogeneous.pow n)

theorem gammaPoleSymbolicDerivativeScale_trihomogeneous (j : ℕ) :
    GammaPoleTrihomogeneous (-(j : ℤ))
      (LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j)) := by
  have h := gammaPoleTrihomogeneous_monomial 0 (-(j : ℤ)) 0
    (RatFunc.C (-((-1 : ℂ) ^ j)))
  have heq :
      LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j) =
        LaurentPolynomial.C
            (LaurentPolynomial.C (MvPolynomial.monomial 0
              (RatFunc.C (-((-1 : ℂ) ^ j)))) *
              LaurentPolynomial.T (-(j : ℤ))) *
          LaurentPolynomial.T 0 := by
    rw [LaurentPolynomial.T_zero, mul_one]
    congr 1
    rw [gammaPoleSymbolicDerivativeScale]
    have hpowK :
        (-1 : GammaPoleRationalBase) ^ j = RatFunc.C ((-1 : ℂ) ^ j) := by
      calc
        (-1 : GammaPoleRationalBase) ^ j =
            (RatFunc.C (-1 : ℂ)) ^ j := by simp
        _ = RatFunc.C ((-1 : ℂ) ^ j) := by rw [map_pow]
    have hpow :
        (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
          LaurentPolynomial.C
            (MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j)) := by
      calc
        (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
            (gammaPoleRationalScaleDerivativeInclude
              (-1 : GammaPoleRationalBase)) ^ j := by
          simp [gammaPoleRationalScaleDerivativeInclude]
        _ = gammaPoleRationalScaleDerivativeInclude
            ((-1 : GammaPoleRationalBase) ^ j) := by rw [map_pow]
        _ = _ := rfl
    rw [hpow, hpowK]
    simp
    exact (neg_mul ((-1 : GammaPoleScaleDerivativeSymbolic) ^ j)
      (LaurentPolynomial.T (-(j : ℤ)))).symm
  rw [heq]
  simpa [gammaPoleBoundaryDerivativeWeight] using h

/-- Boundary exponent of the actual regular-unit derivative `U⁽ᵏ⁾`: the
zeroth derivative is the normalized unit, while derivative `k + 1` is the
independent symbolic coordinate indexed by `k`. -/
def gammaPoleBoundaryExponent : ℕ → (ℕ →₀ ℕ)
  | 0 => 0
  | k + 1 => Finsupp.single k 1

@[simp] theorem gammaPoleBoundaryDerivativeWeight_boundaryExponent (k : ℕ) :
    gammaPoleBoundaryDerivativeWeight (gammaPoleBoundaryExponent k) = k := by
  rcases k with (_ | k)
  · simp [gammaPoleBoundaryExponent, gammaPoleBoundaryDerivativeWeight]
  · simp [gammaPoleBoundaryExponent, gammaPoleBoundaryDerivativeWeight,
      Finsupp.weight_single]

theorem gammaPoleSymbolicUnitDerivativeBoundaryFamily_eq_monomial (k : ℕ) :
    gammaPoleSymbolicUnitDerivativeBoundaryFamily k =
      LaurentPolynomial.C
          (MvPolynomial.monomial (gammaPoleBoundaryExponent k) 1) *
        LaurentPolynomial.T 0 := by
  rcases k with (_ | k)
  · simp [gammaPoleSymbolicUnitDerivativeBoundaryFamily,
      gammaPoleBoundaryExponent]
  · simp only [gammaPoleSymbolicUnitDerivativeBoundaryFamily,
      gammaPoleBoundaryExponent, LaurentPolynomial.T_zero, mul_one]
    congr 1

def gammaPoleUniversalRegularScalar (j k : ℕ) : ℂ :=
  (j.choose k : ℂ) * (-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)

theorem gammaPoleSymbolicRegularSummand_eq (j k : ℕ) :
    Polynomial.toLaurent
        ((Polynomial.monomial (j - k)
          (MvPolynomial.C (gammaPoleUniversalRegularScalar j k) *
            MvPolynomial.X k)).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval) =
      LaurentPolynomial.C
          (LaurentPolynomial.C
              (MvPolynomial.monomial (gammaPoleBoundaryExponent k)
                (RatFunc.C (gammaPoleUniversalRegularScalar j k))) *
            LaurentPolynomial.T 0) *
        LaurentPolynomial.T ((j - k : ℕ) : ℤ) := by
  rw [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T]
  congr 1
  rw [map_mul]
  simp only [gammaPoleSymbolicUnitDerivativeBoundaryEval,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  congr 1
  change gammaPoleComplexScaleDerivativeInclude
      (gammaPoleUniversalRegularScalar j k) *
      gammaPoleSymbolicUnitDerivativeBoundaryFamily k = _
  rw [gammaPoleSymbolicUnitDerivativeBoundaryFamily_eq_monomial]
  simp [gammaPoleComplexScaleDerivativeInclude,
    gammaPoleRationalScaleDerivativeInclude,
    ← map_mul, MvPolynomial.C_mul_monomial]

theorem gammaPoleSymbolicRegularSummand_trihomogeneous
    (j k : ℕ) (hk : k ≤ j) :
    GammaPoleTrihomogeneous (j : ℤ)
      (Polynomial.toLaurent
        ((Polynomial.monomial (j - k)
          (MvPolynomial.C (gammaPoleUniversalRegularScalar j k) *
            MvPolynomial.X k)).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [gammaPoleSymbolicRegularSummand_eq]
  have h := gammaPoleTrihomogeneous_monomial
    ((j - k : ℕ) : ℤ) 0 (gammaPoleBoundaryExponent k)
    (RatFunc.C (gammaPoleUniversalRegularScalar j k))
  convert h using 1
  simp only [gammaPoleBoundaryDerivativeWeight_boundaryExponent, add_zero]
  norm_cast
  omega

theorem gammaPoleSymbolicUniversalRegularLaurentProfile_trihomogeneous
    (j : ℕ) :
    GammaPoleTrihomogeneous (j : ℤ)
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleRegularProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  change GammaPoleTrihomogeneous (j : ℤ)
    (Polynomial.toLaurent
      ((Polynomial.mapRingHom gammaPoleSymbolicUnitDerivativeBoundaryEval)
        (HTGeometry.universalSimplePoleRegularProfile j)))
  rw [HTGeometry.universalSimplePoleRegularProfile, map_sum, map_sum]
  apply GammaPoleTrihomogeneous.sum
  intro k hk
  simpa [gammaPoleUniversalRegularScalar] using
    gammaPoleSymbolicRegularSummand_trihomogeneous j k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem gammaPoleSymbolicUniversalJetLaurentProfile_trihomogeneous
    (j : ℕ) :
    GammaPoleTrihomogeneous ((j + 1 : ℕ) : ℤ)
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleJetProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)) := by
  rw [HTGeometry.universalSimplePoleJetProfile,
    Polynomial.map_mul, map_mul, Polynomial.map_X,
    Polynomial.toLaurent_X]
  have hT : GammaPoleTrihomogeneous 1
      (LaurentPolynomial.T 1 : GammaPoleMovingJetSymbolic) := by
    simpa [gammaPoleBoundaryDerivativeWeight] using
      gammaPoleTrihomogeneous_monomial 1 0 0 1
  have hR :=
    gammaPoleSymbolicUniversalRegularLaurentProfile_trihomogeneous j
  convert hT.mul hR using 1
  all_goals simp [Nat.cast_add, add_comm]

theorem gammaPoleSymbolicDerivativeLaurentProfile_trihomogeneous
    (j : ℕ) :
    GammaPoleTrihomogeneous 1
      (gammaPoleSymbolicDerivativeLaurentProfile j) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile]
  have hS := gammaPoleSymbolicDerivativeScale_trihomogeneous j
  have hJ := gammaPoleSymbolicUniversalJetLaurentProfile_trihomogeneous j
  convert hS.mul hJ using 1
  all_goals omega

/-- A homogeneous source evaluated on targets of a common tri-grade remains
homogeneous.  Coefficients may range through an arbitrary grade-zero algebra
map; this is the interface needed for moving polynomial coefficients. -/
theorem gammaPoleTrihomogeneous_eval₂_of_isHomogeneous
    {σ : Type*} {d : ℕ} {P : MvPolynomial σ (Polynomial ℂ)}
    (hP : P.IsHomogeneous d)
    (f : Polynomial ℂ →+* GammaPoleMovingJetSymbolic)
    (g : σ → GammaPoleMovingJetSymbolic)
    (hf : ∀ p, GammaPoleTrihomogeneous 0 (f p))
    (hg : ∀ i, GammaPoleTrihomogeneous 1 (g i)) :
    GammaPoleTrihomogeneous (d : ℤ) (MvPolynomial.eval₂ f g P) := by
  rw [MvPolynomial.eval₂_eq]
  apply GammaPoleTrihomogeneous.sum
  intro m hm
  have hprod : GammaPoleTrihomogeneous
      (∑ i ∈ m.support, (m i : ℤ))
      (∏ i ∈ m.support, g i ^ m i) := by
    apply GammaPoleTrihomogeneous.prod
    intro i hi
    simpa using (hg i).pow (m i)
  have hterm := (hf (P.coeff m)).mul hprod
  have hdegNat : ∑ i ∈ m.support, m i = d := by
    simpa [Finsupp.weight_apply, smul_eq_mul] using
      hP (MvPolynomial.mem_support_iff.mp hm)
  have hdegInt : ∑ i ∈ m.support, (m i : ℤ) = (d : ℤ) := by
    exact_mod_cast hdegNat
  simpa [hdegInt] using hterm

/-- **Gamma conserved tri-grading.** Every total-degree-`d` source sector has
exact symbolic weight `d`, simultaneously counting outer pole order, signed
factorial-scale order, and regular-unit derivative weight. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_trihomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : P.IsHomogeneous d) :
    GammaPoleTrihomogeneous (d : ℤ)
      (gammaPoleSymbolicPolynomialJetLaurentEval n P) := by
  simpa only [gammaPoleSymbolicPolynomialJetLaurentEval] using
    gammaPoleTrihomogeneous_eval₂_of_isHomogeneous hP
      gammaPoleSymbolicMovingCoefficientLaurent
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))
      gammaPoleSymbolicMovingCoefficientLaurent_trihomogeneous
      (fun j => gammaPoleSymbolicDerivativeLaurentProfile_trihomogeneous (j : ℕ))

@[simp] theorem gammaPoleTriFlatten_apply
    (F : GammaPoleMovingJetSymbolic) (q l : ℤ) (m : ℕ →₀ ℕ) :
    gammaPoleTriFlatten F ((q, l), m) =
      MvPolynomial.coeff m ((F q) l) := by
  rfl

/-- Coefficient form of tri-homogeneity: every nonzero symbolic monomial lies
on the same affine weight hyperplane. -/
theorem GammaPoleTrihomogeneous.support_weight
    {d : ℤ} {F : GammaPoleMovingJetSymbolic}
    (hF : GammaPoleTrihomogeneous d F)
    {q l : ℤ} {m : ℕ →₀ ℕ}
    (hcoeff : MvPolynomial.coeff m ((F q) l) ≠ 0) :
    q + l + gammaPoleBoundaryDerivativeWeight m = d := by
  have hsupp : ((q, l), m) ∈ (gammaPoleTriFlatten F).support := by
    rw [Finsupp.mem_support_iff]
    simpa using hcoeff
  simpa [gammaPoleTriWeight] using hF ((q, l), m) hsupp

/-- Exact support-selection law for the faithful symbolic Gamma profile. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_support_weight
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hP : P.IsHomogeneous d)
    {q l : ℤ} {m : ℕ →₀ ℕ}
    (hcoeff : MvPolynomial.coeff m
      ((gammaPoleSymbolicPolynomialJetLaurentEval n P q) l) ≠ 0) :
    q + l + gammaPoleBoundaryDerivativeWeight m = (d : ℤ) :=
  (gammaPoleSymbolicPolynomialJetLaurentEval_trihomogeneous hP).support_weight
    hcoeff

/-- The opposite edge to the highest-pole term: pole grade one of the
universal `j`-th jet is exactly the `j`-th regular boundary derivative. -/
theorem universalSimplePoleJetProfile_coeff_one (j : ℕ) :
    (HTGeometry.universalSimplePoleJetProfile j).coeff 1 =
      MvPolynomial.X j := by
  rw [HTGeometry.universalSimplePoleJetProfile,
    Polynomial.coeff_X_mul]
  simpa [Polynomial.coeff_zero_eq_eval_zero] using
    HTGeometry.universalSimplePoleRegularProfile_eval_zero j

theorem gammaPoleSymbolicDerivativeLaurentProfile_coeff_one (j : ℕ) :
    gammaPoleSymbolicDerivativeLaurentProfile j 1 =
      gammaPoleSymbolicDerivativeScale j *
        gammaPoleSymbolicUnitDerivativeBoundaryFamily j := by
  have hboundary :
      (((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval).coeff 1) =
        gammaPoleSymbolicUnitDerivativeBoundaryFamily j := by
    rw [Polynomial.coeff_map, universalSimplePoleJetProfile_coeff_one]
    simp [gammaPoleSymbolicUnitDerivativeBoundaryEval]
  rw [gammaPoleSymbolicDerivativeLaurentProfile,
    ← LaurentPolynomial.smul_eq_C_mul]
  change gammaPoleSymbolicDerivativeScale j *
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleJetProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval) 1) = _
  congr 1
  rw [Polynomial.toLaurent_apply]
  change Finsupp.mapDomain (fun n : ℕ => (n : ℤ))
      ((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval).toFinsupp
        ((1 : ℕ) : ℤ) = _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) :=
    Int.ofNat_injective
  rw [Finsupp.mapDomain_apply hinj]
  exact hboundary

theorem gammaPoleSymbolicDerivativeScale_mul_boundaryFamily_eq (j : ℕ) :
    gammaPoleSymbolicDerivativeScale j *
        gammaPoleSymbolicUnitDerivativeBoundaryFamily j =
      LaurentPolynomial.C
          (MvPolynomial.monomial (gammaPoleBoundaryExponent j)
            (RatFunc.C (-((-1 : ℂ) ^ j)))) *
        LaurentPolynomial.T (-(j : ℤ)) := by
  have hpow :
      (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
        LaurentPolynomial.C
          (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ j))) := by
    calc
      (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
          (gammaPoleRationalScaleDerivativeInclude
            (RatFunc.C (-1 : ℂ))) ^ j := by
        simp [gammaPoleRationalScaleDerivativeInclude]
      _ = gammaPoleRationalScaleDerivativeInclude
          ((RatFunc.C (-1 : ℂ)) ^ j) := by rw [map_pow]
      _ = gammaPoleRationalScaleDerivativeInclude
          (RatFunc.C ((-1 : ℂ) ^ j)) := by rw [← map_pow]
      _ = _ := rfl
  rw [gammaPoleSymbolicDerivativeScale, hpow,
    gammaPoleSymbolicUnitDerivativeBoundaryFamily_eq_monomial]
  simp only [LaurentPolynomial.T_zero, mul_one]
  have hcoeff :
      LaurentPolynomial.C
          (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ j))) *
        LaurentPolynomial.C
          (MvPolynomial.monomial (gammaPoleBoundaryExponent j) 1) =
      LaurentPolynomial.C
        (MvPolynomial.monomial (gammaPoleBoundaryExponent j)
          (RatFunc.C ((-1 : ℂ) ^ j))) := by
    rw [← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  calc
    -(LaurentPolynomial.C
          (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ j))) *
        LaurentPolynomial.T (-(j : ℤ))) *
          LaurentPolynomial.C
            (MvPolynomial.monomial (gammaPoleBoundaryExponent j) 1) =
        -(LaurentPolynomial.C
            (MvPolynomial.C (RatFunc.C ((-1 : ℂ) ^ j))) *
          LaurentPolynomial.C
            (MvPolynomial.monomial (gammaPoleBoundaryExponent j) 1)) *
          LaurentPolynomial.T (-(j : ℤ)) := by ring
    _ = _ := by
      rw [hcoeff, map_neg]
      have hmon :
          MvPolynomial.monomial (gammaPoleBoundaryExponent j)
              (-RatFunc.C ((-1 : ℂ) ^ j)) =
            -MvPolynomial.monomial (gammaPoleBoundaryExponent j)
              (RatFunc.C ((-1 : ℂ) ^ j)) :=
        map_neg (MvPolynomial.monomial (gammaPoleBoundaryExponent j)) _
      rw [hmon, map_neg]

/-- **Nonlinear lower-edge generator.** At outer pole grade one, scale grade
`-j`, and the maximal derivative-boundary monomial, the `j`-th symbolic Gamma
derivative has the exact unit coefficient `-(-1)^j`. -/
theorem gammaPoleSymbolicDerivativeLaurentProfile_bottom_scale_boundary
    (j : ℕ) :
    MvPolynomial.coeff (gammaPoleBoundaryExponent j)
        ((gammaPoleSymbolicDerivativeLaurentProfile j 1) (-(j : ℤ))) =
      RatFunc.C (-((-1 : ℂ) ^ j)) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile_coeff_one,
    gammaPoleSymbolicDerivativeScale_mul_boundaryFamily_eq]
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [Finsupp.single_eq_same, MvPolynomial.coeff_monomial]
  simp

/-- Symbolic counterpart of the actual monomial substitution formula. -/
theorem gammaPoleSymbolicPolynomialJetLaurentEval_monomial
    (n : ℕ) (α : Fin (n + 1) →₀ ℕ) (p : Polynomial ℂ) :
    gammaPoleSymbolicPolynomialJetLaurentEval n
        (MvPolynomial.monomial α p) =
      gammaPoleSymbolicMovingCoefficientLaurent p *
        α.prod fun j e =>
          gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) ^ e := by
  simp [gammaPoleSymbolicPolynomialJetLaurentEval,
    MvPolynomial.eval₂_monomial]

/-- The zero Taylor shift is the exact rational pole-position value and has
no scale or positive-boundary content. -/
theorem gammaPoleSymbolicMovingCoefficientLaurent_zero_scale_boundary
    (p : Polynomial ℂ) :
    MvPolynomial.coeff 0
        ((gammaPoleSymbolicMovingCoefficientLaurent p 0) 0) =
      gammaPoleCenterHasseRational p 0 := by
  have hzero :
      gammaPoleSymbolicMovingCoefficientLaurent p 0 =
        gammaPoleRationalScaleDerivativeInclude
          (gammaPoleCenterHasseRational p 0) := by
    simpa using gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg p 0
  rw [hzero]
  simp [gammaPoleRationalScaleDerivativeInclude]

/-- Weighted analogue of homogeneous scalar extraction. -/
theorem isWeightedHomogeneous_eval₂_scale
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {w : σ → ℕ} {W : ℕ} {P : MvPolynomial σ R}
    (hP : MvPolynomial.IsWeightedHomogeneous w P W)
    (f : R →+* S) (g : σ → S) (s : S) :
    MvPolynomial.eval₂ f (fun i => s ^ w i * g i) P =
      s ^ W * MvPolynomial.eval₂ f g P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hweight : ∑ i ∈ m.support, w i * m i = W := by
    have hw := hP (MvPolynomial.mem_support_iff.mp hm)
    change (∑ i ∈ m.support, m i * w i) = W at hw
    simpa [mul_comm] using hw
  have hpow : ∏ i ∈ m.support, (s ^ w i * g i) ^ m i =
      s ^ W * ∏ i ∈ m.support, g i ^ m i := by
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hweight]
  rw [hpow]
  ac_rfl

/-- Simultaneous extraction of particle degree and derivative weight. -/
theorem isHomogeneous_eval₂_scale_general
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {D : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous D)
    (f : R →+* S) (g : σ → S) (c : S) :
    MvPolynomial.eval₂ f (fun i => c * g i) P =
      c ^ D * MvPolynomial.eval₂ f g P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = D := by
    simpa [Finsupp.weight_apply, smul_eq_mul] using
      hP (MvPolynomial.mem_support_iff.mp hm)
  have hpow : ∏ i ∈ m.support, (c * g i) ^ m i =
      c ^ D * ∏ i ∈ m.support, g i ^ m i := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hpow]
  ac_rfl

theorem isHomogeneous_isWeightedHomogeneous_eval₂_biscale
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {w : σ → ℕ} {D W : ℕ} {P : MvPolynomial σ R}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous w P W)
    (f : R →+* S) (g : σ → S) (c s : S) :
    MvPolynomial.eval₂ f (fun i => c * s ^ w i * g i) P =
      c ^ D * s ^ W * MvPolynomial.eval₂ f g P := by
  calc
    MvPolynomial.eval₂ f (fun i => c * s ^ w i * g i) P =
        c ^ D * MvPolynomial.eval₂ f (fun i => s ^ w i * g i) P := by
      simpa only [mul_assoc] using
        isHomogeneous_eval₂_scale_general hD f
          (fun i => s ^ w i * g i) c
    _ = _ := by
      rw [isWeightedHomogeneous_eval₂_scale hW]
      rw [mul_assoc]

def gammaPoleSourceDerivativeWeight {n : ℕ} : Fin (n + 1) → ℕ :=
  fun j => (j : ℕ)

def gammaPoleSymbolicParticleScale : GammaPoleMovingJetSymbolic :=
  LaurentPolynomial.C (-1 : GammaPoleScaleDerivativeSymbolic)

def gammaPoleSymbolicDerivativeWeightScale : GammaPoleMovingJetSymbolic :=
  LaurentPolynomial.C (-LaurentPolynomial.T (-1) :
    GammaPoleScaleDerivativeSymbolic)

def gammaPoleSymbolicUniversalDerivativeLaurentProfile
    (j : ℕ) : GammaPoleMovingJetSymbolic :=
  Polynomial.toLaurent
    ((HTGeometry.universalSimplePoleJetProfile j).map
      gammaPoleSymbolicUnitDerivativeBoundaryEval)

theorem gammaPoleSymbolicDerivativeLaurentProfile_biscale_factor
    (j : ℕ) :
    gammaPoleSymbolicDerivativeLaurentProfile j =
      gammaPoleSymbolicParticleScale *
        gammaPoleSymbolicDerivativeWeightScale ^ j *
          gammaPoleSymbolicUniversalDerivativeLaurentProfile j := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile,
    gammaPoleSymbolicUniversalDerivativeLaurentProfile]
  congr 1
  simp only [gammaPoleSymbolicDerivativeScale,
    gammaPoleSymbolicParticleScale,
    gammaPoleSymbolicDerivativeWeightScale, map_neg, map_mul, map_pow,
    map_one]
  have hpow :
      (-LaurentPolynomial.C
          (LaurentPolynomial.T (-1) : GammaPoleScaleDerivativeSymbolic) :
          GammaPoleMovingJetSymbolic) ^ j =
        (-1 : GammaPoleMovingJetSymbolic) ^ j *
          LaurentPolynomial.C
            (LaurentPolynomial.T (-(j : ℤ)) :
              GammaPoleScaleDerivativeSymbolic) := by
    calc
      (-LaurentPolynomial.C
          (LaurentPolynomial.T (-1) : GammaPoleScaleDerivativeSymbolic) :
          GammaPoleMovingJetSymbolic) ^ j =
          ((-1 : GammaPoleMovingJetSymbolic) *
            LaurentPolynomial.C
              (LaurentPolynomial.T (-1) :
                GammaPoleScaleDerivativeSymbolic)) ^ j := by
            congr 1
            ring
      _ = (-1 : GammaPoleMovingJetSymbolic) ^ j *
          (LaurentPolynomial.C
            (LaurentPolynomial.T (-1) :
              GammaPoleScaleDerivativeSymbolic)) ^ j := by
            exact mul_pow (-1 : GammaPoleMovingJetSymbolic)
              (LaurentPolynomial.C
                (LaurentPolynomial.T (-1) :
                  GammaPoleScaleDerivativeSymbolic)) j
      _ = _ := by
        rw [← map_pow]
        congr 1
        simp [LaurentPolynomial.T_pow]
  rw [hpow]
  ring

def gammaPoleSymbolicConstantCoefficientInclude :
    ℂ →+* GammaPoleMovingJetSymbolic :=
  gammaPoleSymbolicMovingCoefficientLaurent.comp Polynomial.C

def gammaPoleSymbolicConstantJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicConstantCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))

def gammaPoleSymbolicUniversalJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicConstantCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicUniversalDerivativeLaurentProfile (j : ℕ))

@[simp] theorem gammaPoleSymbolicConstantCoefficientInclude_apply (c : ℂ) :
    gammaPoleSymbolicConstantCoefficientInclude c =
      LaurentPolynomial.C (gammaPoleComplexScaleDerivativeInclude c) := by
  simp [gammaPoleSymbolicConstantCoefficientInclude,
    gammaPoleSymbolicMovingCoefficientLaurent,
    movingPoleTaylorLaurent, scaledTaylorAlgHom,
    polynomialDiagonalScaleAlgHom,
    gammaPoleComplexScaleDerivativeInclude]

/-- The universal factor in the bigraded Gamma decomposition is exactly the
existing finite universal simple-pole evaluation, followed by the symbolic
boundary embedding and polynomial-to-Laurent inclusion. -/
theorem gammaPoleSymbolicUniversalJetLaurentEval_eq
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaPoleSymbolicUniversalJetLaurentEval n P =
      Polynomial.toLaurent
        ((HTGeometry.finiteUniversalSimplePoleProfileEval n P).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval) := by
  let rhs : MvPolynomial (Fin (n + 1)) ℂ →+*
      GammaPoleMovingJetSymbolic :=
    Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom
        gammaPoleSymbolicUnitDerivativeBoundaryEval).comp
          (HTGeometry.finiteUniversalSimplePoleProfileEval n))
  have h : gammaPoleSymbolicUniversalJetLaurentEval n = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [gammaPoleSymbolicUniversalJetLaurentEval, rhs,
        HTGeometry.finiteUniversalSimplePoleProfileEval,
        gammaPoleSymbolicUniversalDerivativeLaurentProfile,
        gammaPoleSymbolicUnitDerivativeBoundaryEval]
    · intro j
      simp [gammaPoleSymbolicUniversalJetLaurentEval, rhs,
        HTGeometry.finiteUniversalSimplePoleProfileEval,
        gammaPoleSymbolicUniversalDerivativeLaurentProfile]
  exact RingHom.congr_fun h P


/-- **Bigraded Gamma factorization.** On a source sector of particle degree
`D` and derivative weight `W`, all signed inverse factorial scales factor as
one common monomial before the universal simple-pole profile. -/
theorem gammaPoleSymbolicConstantJetLaurentEval_biscale_factor
    {n D W : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    gammaPoleSymbolicConstantJetLaurentEval n P =
      gammaPoleSymbolicParticleScale ^ D *
        gammaPoleSymbolicDerivativeWeightScale ^ W *
          gammaPoleSymbolicUniversalJetLaurentEval n P := by
  change MvPolynomial.eval₂ gammaPoleSymbolicConstantCoefficientInclude
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)) P = _
  simp_rw [gammaPoleSymbolicDerivativeLaurentProfile_biscale_factor]
  exact isHomogeneous_isWeightedHomogeneous_eval₂_biscale hD hW
    gammaPoleSymbolicConstantCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicUniversalDerivativeLaurentProfile (j : ℕ))
    gammaPoleSymbolicParticleScale gammaPoleSymbolicDerivativeWeightScale

theorem finiteUniversalSimplePoleProfileEval_coeff_particleNumber
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hD : P.IsHomogeneous D) :
    (HTGeometry.finiteUniversalSimplePoleProfileEval n P).coeff D =
      HTGeometry.simplePoleFinToNat n P := by
  rw [HTGeometry.finiteUniversalSimplePoleProfileEval_eq]
  exact HTGeometry.universalSimplePoleProfileEval_coeff_particleNumber
    hD.rename_isHomogeneous

/-- The outer particle-grade trace of the universal symbolic factor is the
finite source polynomial evaluated on the normalized boundary family. -/
theorem gammaPoleSymbolicUniversalJetLaurentEval_coeff_particleNumber
    {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hD : P.IsHomogeneous D) :
    gammaPoleSymbolicUniversalJetLaurentEval n P (D : ℤ) =
      gammaPoleSymbolicUnitDerivativeBoundaryEval
        (HTGeometry.simplePoleFinToNat n P) := by
  rw [gammaPoleSymbolicUniversalJetLaurentEval_eq]
  rw [Polynomial.toLaurent_apply]
  change Finsupp.mapDomain (fun q : ℕ => (q : ℤ))
      (((HTGeometry.finiteUniversalSimplePoleProfileEval n P).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval).toFinsupp) (D : ℤ) = _
  have hinj : Function.Injective (fun q : ℕ => (q : ℤ)) :=
    Int.ofNat_injective
  rw [Finsupp.mapDomain_apply hinj]
  change (((HTGeometry.finiteUniversalSimplePoleProfileEval n P).map
    gammaPoleSymbolicUnitDerivativeBoundaryEval).coeff D) = _
  rw [Polynomial.coeff_map,
    finiteUniversalSimplePoleProfileEval_coeff_particleNumber hD]

def gammaPoleSymbolicBiscaleFactor
    (D W : ℕ) : GammaPoleScaleDerivativeSymbolic :=
  (-1 : GammaPoleScaleDerivativeSymbolic) ^ D *
    (-LaurentPolynomial.T (-1) : GammaPoleScaleDerivativeSymbolic) ^ W

theorem gammaPoleSymbolicBiscaleFactor_outer_eq (D W : ℕ) :
    gammaPoleSymbolicParticleScale ^ D *
        gammaPoleSymbolicDerivativeWeightScale ^ W =
      LaurentPolynomial.C (gammaPoleSymbolicBiscaleFactor D W) := by
  simp [gammaPoleSymbolicParticleScale,
    gammaPoleSymbolicDerivativeWeightScale,
    gammaPoleSymbolicBiscaleFactor, map_pow, map_mul]

/-- **Sector-level lower-edge reflection, outer form.** For a constant
coefficient source sector of particle degree `D` and derivative weight `W`,
its pole-grade-`D` coefficient is the universal boundary trace multiplied by
one explicit signed scale monomial. -/
theorem gammaPoleSymbolicConstantJetLaurentEval_coeff_particleNumber
    {n D W : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    gammaPoleSymbolicConstantJetLaurentEval n P (D : ℤ) =
      gammaPoleSymbolicBiscaleFactor D W *
        gammaPoleSymbolicUnitDerivativeBoundaryEval
          (HTGeometry.simplePoleFinToNat n P) := by
  rw [gammaPoleSymbolicConstantJetLaurentEval_biscale_factor hD hW,
    gammaPoleSymbolicBiscaleFactor_outer_eq,
    ← LaurentPolynomial.smul_eq_C_mul]
  change gammaPoleSymbolicBiscaleFactor D W *
      (gammaPoleSymbolicUniversalJetLaurentEval n P (D : ℤ)) = _
  rw [gammaPoleSymbolicUniversalJetLaurentEval_coeff_particleNumber hD]

def gammaPoleSymbolicCenterCoefficientInclude :
    Polynomial ℂ →+* GammaPoleMovingJetSymbolic :=
  ((LaurentPolynomial.C : GammaPoleScaleDerivativeSymbolic →+*
      GammaPoleMovingJetSymbolic).comp
    gammaPoleRationalScaleDerivativeInclude).comp
      gammaPoleCenterRationalEval

def gammaPoleSymbolicCenterJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicCenterCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))

def gammaPoleSymbolicCenterUniversalJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicCenterCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicUniversalDerivativeLaurentProfile (j : ℕ))

theorem gammaPoleSymbolicMovingCoefficientLaurent_coeff_zero
    (p : Polynomial ℂ) :
    gammaPoleSymbolicMovingCoefficientLaurent p 0 =
      gammaPoleRationalScaleDerivativeInclude
        (gammaPoleCenterRationalEval p) := by
  have h := gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg p 0
  simpa [gammaPoleCenterHasseRational,
    gammaPoleCenterRationalEval,
    Polynomial.eval₂_eq_eval_map] using h

/-- The frozen center-value sector obeys the same exact particle/derivative
bigrading even when every source coefficient is a polynomial in the moving
coordinate. -/
theorem gammaPoleSymbolicCenterJetLaurentEval_biscale_factor
    {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      gammaPoleSourceDerivativeWeight P W) :
    gammaPoleSymbolicCenterJetLaurentEval n P =
      gammaPoleSymbolicParticleScale ^ D *
        gammaPoleSymbolicDerivativeWeightScale ^ W *
          gammaPoleSymbolicCenterUniversalJetLaurentEval n P := by
  change MvPolynomial.eval₂ gammaPoleSymbolicCenterCoefficientInclude
      (fun j : Fin (n + 1) =>
        gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)) P = _
  simp_rw [gammaPoleSymbolicDerivativeLaurentProfile_biscale_factor]
  exact isHomogeneous_isWeightedHomogeneous_eval₂_biscale hD hW
    gammaPoleSymbolicCenterCoefficientInclude
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicUniversalDerivativeLaurentProfile (j : ℕ))
    gammaPoleSymbolicParticleScale gammaPoleSymbolicDerivativeWeightScale

end

end GaloisForLFunctions
