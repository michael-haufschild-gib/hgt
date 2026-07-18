import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness after scalar extension in characteristic zero

An irreducible multivariable polynomial over a characteristic-zero field can split after a field
extension, but it cannot acquire repeated irreducible factors.  The proof singles out one variable,
passes to the fraction field in all the other variables, and applies univariate separability.

There is one genuine localization issue: a repeated factor could disappear by becoming a unit after
the other variables are inverted.  The equation-(78) support theorem rules this out.  Every
irreducible factor after scalar extension still contains every variable of the original
irreducible polynomial, hence has positive degree in the distinguished variable.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial

/-- Scalar extension of an irreducible multivariable polynomial over a characteristic-zero field
is squarefree.  Irreducibility need not survive the extension; equation (78) guarantees instead
that every irreducible factor remains nonconstant in the distinguished variable used in the
separability argument. -/
theorem irreducible_map_squarefree_of_charZero
    {F K σ : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
    {P : MvPolynomial σ F} (hP : Irreducible P) :
    Squarefree (MvPolynomial.map (algebraMap F K) P) := by
  classical
  have hmapP0 : MvPolynomial.map (algebraMap F K) P ≠ 0 := by
    simpa using ((MvPolynomial.map_injective (algebraMap F K)
      (FaithfulSMul.algebraMap_injective F K)).ne hP.ne_zero)
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hmapP0]
  intro A hA hAsq

  obtain ⟨x, hxP⟩ :=
    mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit hP.ne_zero hP.not_isUnit
  have hAdiv : A ∣ MvPolynomial.map (algebraMap F K) P :=
    (dvd_mul_right A A).trans hAsq
  have hxA : x ∈ A.vars :=
    irreducible_map_factor_vars_subset hP hA hAdiv hxP

  let eF : MvPolynomial σ F ≃ₐ[F]
      Polynomial (MvPolynomial {j : σ // j ≠ x} F) :=
    mvPolynomialPolynomialEquivAt x
  let eK : MvPolynomial σ K ≃ₐ[K]
      Polynomial (MvPolynomial {j : σ // j ≠ x} K) :=
    mvPolynomialPolynomialEquivAt x
  let PF : Polynomial (MvPolynomial {j : σ // j ≠ x} F) := eF P
  let AK : Polynomial (MvPolynomial {j : σ // j ≠ x} K) := eK A
  let ι : MvPolynomial {j : σ // j ≠ x} F →+*
      MvPolynomial {j : σ // j ≠ x} K :=
    MvPolynomial.map (algebraMap F K)

  have hPFirreducible : Irreducible PF := hP.map eF
  have hxPdegree : MvPolynomial.degreeOf x P ≠ 0 :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hxP
  have hPFdegreeEq : MvPolynomial.degreeOf x P = PF.natDegree := by
    calc
      MvPolynomial.degreeOf x P =
          (mvPolynomialAsPolynomialAt x P).natDegree :=
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt x P
      _ = (eF P).natDegree := by
        exact congrArg Polynomial.natDegree
          (mvPolynomialPolynomialEquivAt_apply x P).symm
      _ = PF.natDegree := rfl
  have hPFdegree : PF.natDegree ≠ 0 := by
    intro hzero
    exact hxPdegree (hPFdegreeEq.trans hzero)
  have hPFprimitive : PF.IsPrimitive :=
    hPFirreducible.isPrimitive hPFdegree

  let g : MvPolynomial {j : σ // j ≠ x} F →+*
      FractionRing (MvPolynomial {j : σ // j ≠ x} K) :=
    (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
      (FractionRing (MvPolynomial {j : σ // j ≠ x} K))).comp ι
  have hιinj : Function.Injective ι := by
    exact MvPolynomial.map_injective (algebraMap F K)
      (FaithfulSMul.algebraMap_injective F K)
  have hginj : Function.Injective g := by
    exact (FaithfulSMul.algebraMap_injective
      (MvPolynomial {j : σ // j ≠ x} K)
      (FractionRing (MvPolynomial {j : σ // j ≠ x} K))).comp hιinj
  let φ : FractionRing (MvPolynomial {j : σ // j ≠ x} F) →+*
      FractionRing (MvPolynomial {j : σ // j ≠ x} K) :=
    IsFractionRing.lift hginj

  have hPFfractionIrreducible : Irreducible
      (Polynomial.map
        (algebraMap (MvPolynomial {j : σ // j ≠ x} F)
          (FractionRing (MvPolynomial {j : σ // j ≠ x} F))) PF) :=
    hPFprimitive.irreducible_iff_irreducible_map_fraction_map.mp hPFirreducible
  have hPFfractionSeparable :
      (Polynomial.map
        (algebraMap (MvPolynomial {j : σ // j ≠ x} F)
          (FractionRing (MvPolynomial {j : σ // j ≠ x} F))) PF).Separable :=
    hPFfractionIrreducible.separable
  have hlocalizedMap :
      Polynomial.map
          (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
            (FractionRing (MvPolynomial {j : σ // j ≠ x} K)))
          (Polynomial.map ι PF) =
        Polynomial.map φ
          (Polynomial.map
            (algebraMap (MvPolynomial {j : σ // j ≠ x} F)
              (FractionRing (MvPolynomial {j : σ // j ≠ x} F))) PF) := by
    ext n
    simp only [Polynomial.coeff_map]
    change g (PF.coeff n) =
      IsFractionRing.lift hginj
        (algebraMap (MvPolynomial {j : σ // j ≠ x} F)
          (FractionRing (MvPolynomial {j : σ // j ≠ x} F)) (PF.coeff n))
    exact (IsFractionRing.lift_algebraMap hginj (PF.coeff n)).symm
  have htargetSeparable :
      (Polynomial.map
        (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
          (FractionRing (MvPolynomial {j : σ // j ≠ x} K)))
        (Polynomial.map ι PF)).Separable := by
    rw [hlocalizedMap]
    exact hPFfractionSeparable.map

  have hdivAtX : AK * AK ∣ Polynomial.map ι PF := by
    have hmapped := map_dvd eK hAsq
    have hleft : eK (A * A) = AK * AK := by
      simp only [map_mul]
      rfl
    have hright :
        eK (MvPolynomial.map (algebraMap F K) P) =
          Polynomial.map ι PF := by
      dsimp [PF, eF, eK, ι]
      exact mvPolynomialPolynomialEquivAt_map (algebraMap F K) x P
    rw [hleft, hright] at hmapped
    exact hmapped
  have hdivLocalized :
      Polynomial.map
          (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
            (FractionRing (MvPolynomial {j : σ // j ≠ x} K))) AK *
        Polynomial.map
          (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
            (FractionRing (MvPolynomial {j : σ // j ≠ x} K))) AK ∣
        Polynomial.map
          (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
            (FractionRing (MvPolynomial {j : σ // j ≠ x} K)))
          (Polynomial.map ι PF) := by
    obtain ⟨T, hT⟩ := hdivAtX
    refine ⟨Polynomial.map
      (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
        (FractionRing (MvPolynomial {j : σ // j ≠ x} K))) T, ?_⟩
    rw [hT, Polynomial.map_mul, Polynomial.map_mul]
  have hAKunit : IsUnit
      (Polynomial.map
        (algebraMap (MvPolynomial {j : σ // j ≠ x} K)
          (FractionRing (MvPolynomial {j : σ // j ≠ x} K))) AK) :=
    htargetSeparable.squarefree _ hdivLocalized

  have hxAdegree : MvPolynomial.degreeOf x A ≠ 0 :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hxA
  have hAKdegreeEq : MvPolynomial.degreeOf x A = AK.natDegree := by
    calc
      MvPolynomial.degreeOf x A =
          (mvPolynomialAsPolynomialAt x A).natDegree :=
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt x A
      _ = (eK A).natDegree := by
        exact congrArg Polynomial.natDegree
          (mvPolynomialPolynomialEquivAt_apply x A).symm
      _ = AK.natDegree := rfl
  have hAKdegree : AK.natDegree ≠ 0 := by
    intro hzero
    exact hxAdegree (hAKdegreeEq.trans hzero)
  apply hAKdegree
  have hdegreeMap := Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective
      (MvPolynomial {j : σ // j ≠ x} K)
      (FractionRing (MvPolynomial {j : σ // j ≠ x} K))) AK
  exact hdegreeMap.symm.trans (Polynomial.natDegree_eq_zero_of_isUnit hAKunit)

end

end GaloisForLFunctions
