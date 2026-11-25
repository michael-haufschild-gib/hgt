import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingProjectiveLaurentCohomology

/-! Multiplication by a constant polynomial acts on the Čech datum by scaling
each Laurent coefficient. -/

noncomputable section

open HTGeometry

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type*} [CommRing K] {ι ν : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ν] [DecidableEq ν]

private theorem constant_mem_twPart (r : K) {I : Finset ι} {e : ℕ}
    {z : LocAt (projCoord K ι ν) I} (hz : z ∈ twPart (projGrading K ι ν) (projCoord K ι ν) I e) :
    algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt (projCoord K ι ν) I) (MvPolynomial.C r) * z ∈
      twPart (projGrading K ι ν) (projCoord K ι ν) I e := by
  let w := projCoord K ι ν
  let c := algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt w I) (MvPolynomial.C r)
  refine (AddSubgroup.closure_le ((twPart (projGrading K ι ν) w I e).comap
    (AddMonoidHom.mulLeft c))).mpr ?_ hz
  rintro _ ⟨m, d, x, hx, hd, rfl⟩
  change algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt w I) (MvPolynomial.C r) * frac w I m x ∈
    twPart (projGrading K ι ν) w I e
  rw [algebraMap_mul_frac]
  have hc : MvPolynomial.C r ∈ projGrading K ι ν 0 := MvPolynomial.isWeightedHomogeneous_C _ _
  have hmul := SetLike.mul_mem_graded hc hx
  rw [zero_add] at hmul
  exact frac_mem_twPart hmul hd

private def constantApp (e : ℕ) (r : K) (I : Finset ι) :
    (polyTwCech K ι ν e).obj I →+ (polyTwCech K ι ν e).obj I :=
  ((AddMonoidHom.mulLeft (algebraMap (MvPolynomial (ι ⊕ ν) K)
      (LocAt (projCoord K ι ν) I) (MvPolynomial.C r))).comp
    (twPart (projGrading K ι ν) (projCoord K ι ν) I e).subtype).codRestrict _
    (fun z => constant_mem_twPart r z.2)

/-- Multiplication by a constant on the local homogeneous fractions. -/
def polynomialTwistScale (e : ℕ) (r : K) : (polyTwCech K ι ν e).Hom (polyTwCech K ι ν e) where
  app := constantApp e r
  comm {s t} h z := by
    apply twVal_injective projCoord_mem
    change resLoc (projCoord K ι ν) h
      (algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt (projCoord K ι ν) s) (MvPolynomial.C r) * z.1) =
      algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt (projCoord K ι ν) t) (MvPolynomial.C r) *
        resLoc (projCoord K ι ν) h z.1
    rw [map_mul, resLoc_algebraMap]

theorem polynomialTwistScale_val (e : ℕ) (r : K) (I : Finset ι) (z : (polyTwCech K ι ν e).obj I) :
    twVal projCoord_mem ((polynomialTwistScale e r).app I z) =
      algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt (projCoord K ι ν) I) (MvPolynomial.C r) *
        twVal projCoord_mem z := rfl

theorem polynomialTwistScale_coe (e : ℕ) (r : K) (I : Finset ι) (z : (polyTwCech K ι ν e).obj I) :
    ((polynomialTwistScale e r).app I z).1 =
      algebraMap (MvPolynomial (ι ⊕ ν) K) (LocAt (projCoord K ι ν) I) (MvPolynomial.C r) * z.1 := rfl

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν] in
private theorem laurentEmb_constant (r : K) :
    laurentEmb K ι ν (MvPolynomial.C r) = algebraMap K (LaurentRing K ι ν) r := by
  change laurentEmb K ι ν (MvPolynomial.monomial 0 r) = _
  rw [laurentEmb_monomial, map_zero]
  rfl

theorem laurentCoeffs_scale {e : ℕ} (r : K) (z : (polyTwCech K ι ν e).Cochain)
    (I : Finset ι) :
    laurentCoeffs ((polynomialTwistScale e r).onCochain z) I = r • laurentCoeffs z I := by
  change (laurentLoc K ι ν I (twVal projCoord_mem ((polynomialTwistScale e r).app I (z I)))).coeff =
    r • (laurentLoc K ι ν I (twVal projCoord_mem (z I))).coeff
  rw [polynomialTwistScale_val, map_mul, laurentLoc_algebraMap, laurentEmb_constant,
    ← Algebra.smul_def, AddMonoidAlgebra.coeff_smul]

end GlobalTheory.SchemeCohomology.RingPolynomialCech
