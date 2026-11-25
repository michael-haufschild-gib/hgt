import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialCechContraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteLaurentExponents
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! In positive degree, fully negative Laurent coefficients detect polynomial Čech cohomology. -/

noncomputable section

open CategoryTheory HTGeometry MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]

abbrev polynomialGradedCech (R : Type) [CommRing R] (n : ℤ) :=
  gradedCech (ι := ι) (polyGrading ι R) n

theorem polynomialGradedCech_d_val (n : ℤ) (p : ℕ)
    (x : (polynomialGradedCech (ι := ι) R n).X p) :
    ((polynomialGradedCech (ι := ι) R n).d p (p + 1) x).1 = (polynomialCechDatum (ι := ι) R n).d x.1 := by
  simp only [polynomialGradedCech, gradedCech, FinsetCechDatum.linearComplex, CochainComplex.of_d]
  rfl

theorem finite_polynomialGradedCech_homology_succ [IsNoetherianRing R] [Nonempty ι] (n : ℤ) (p : ℕ) :
    Module.Finite R ((polynomialGradedCech (ι := ι) R n).homology (p + 1)) := by
  classical
  let C := polynomialGradedCech (ι := ι) R n
  let S := C.sc' p (p + 1) (p + 2)
  let V := LinearMap.ker S.g.hom
  let B := LinearMap.range S.moduleCatToCycles
  let A := fullyNegativeExponents ι n
  letI : Fintype A := (finite_fullyNegativeExponents (ι := ι) n).fintype
  let φ : V →ₗ[R] (A → R) where
    toFun x a := polynomialCechCoefficients x.1.1 Finset.univ a.1
    map_add' x y := funext fun a => by
      change localizedCoefficients R _ n (x.1.1 Finset.univ + y.1.1 Finset.univ) a.1 =
        localizedCoefficients R _ n (x.1.1 Finset.univ) a.1 + localizedCoefficients R _ n (y.1.1 Finset.univ) a.1
      rw [map_add, Finsupp.add_apply]
    map_smul' r x := funext fun a => by
      change localizedCoefficients R _ n (r • x.1.1 Finset.univ) a.1 =
        r • localizedCoefficients R _ n (x.1.1 Finset.univ) a.1
      rw [map_smul, Finsupp.smul_apply]
  have hker : B = LinearMap.ker φ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine LinearMap.mem_ker.2 (funext fun a => ?_)
      change polynomialCechCoefficients (C.d p (p + 1) z).1 Finset.univ a.1 = 0
      rw [polynomialGradedCech_d_val]
      exact polynomialCech_boundary_full_negative z.1 a.1 a.2.2
    · intro hx
      have hz : (polynomialCechDatum (ι := ι) R n).d x.1.1 = 0 := by
        rw [← polynomialGradedCech_d_val n (p + 1) x.1]
        exact congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
      have hfull (a : ι → ℤ) (ha : ∀ i, a i < 0) :
          polynomialCechCoefficients x.1.1 Finset.univ a = 0 := by
        by_contra h
        have hd := (localizedCoefficients_support Finset.univ n (x.1.1 Finset.univ)
          a (Finsupp.mem_support_iff.2 h)).1
        exact h (congrFun (LinearMap.mem_ker.1 hx) ⟨a, hd, ha⟩)
      obtain ⟨z, hzdeg, hzd⟩ := polynomialCech_exists_primitive x.1.2 hz hfull
      have hz' : (polynomialCechDatum (ι := ι) R n).IsDeg z p := by
        intro s hs
        exact hzdeg s (by omega)
      refine ⟨⟨z, hz'⟩, Subtype.ext (Subtype.ext ?_)⟩
      change (C.d p (p + 1) ⟨z, hz'⟩).1 = x.1.1
      rw [polynomialGradedCech_d_val]
      exact hzd
  let L := B.liftQ φ hker.le
  haveI : Module.Finite R (V ⧸ B) := by
    apply Module.Finite.of_injective L
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := B.mkQ_surjective x
    exact (Submodule.Quotient.mk_eq_zero B).2 (hker.symm ▸ LinearMap.mem_ker.2 hx)
  let e := C.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp) ≪≫ S.moduleCatHomologyIso
  exact Module.Finite.equiv e.symm.toLinearEquiv

end GlobalTheory
