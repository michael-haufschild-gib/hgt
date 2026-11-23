import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedAffineTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedIntersectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteTraceDualLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteNormalizationProjective
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms

/-! The trace dual identifies regular top forms on the standard
intersections of a normalized projective cover. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- The trace dual of a normalized affine chart consists of the regular
top forms when the coordinate volume is used to represent them. -/
theorem IsFinCover.affine_trace_dual_iff (h : IsFinCover k E x) (i : Fin (d + 1)) (z : E) :
    (∀ b : rB k E x {i}, Algebra.trace F E (z * (b : E)) ∈ rA k x {i}) ↔
      z • (ExteriorAlgebra.ιMulti E d fun j => D k E (algebraMap F E (chartCoordinates x i j))) ∈
        omB k E (rB k E x {i}) d := by
  let A := rA k x {i}
  let e := h.pd.chartPolynomialEquiv i
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  letI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UpperTheory.Cb.isIntegrallyClosed_fin_polynomialRing k d
  letI : IsIntegrallyClosed A := .of_equiv e.toRingEquiv
  letI : IsFractionRing A F := h.pd.isFractionRing_rA i
  letI := h.fin
  letI := h.sep
  letI : Algebra.Smooth k (rB k E x {i}) := h.smooth i
  obtain ⟨b, _⟩ := h.exists_coordinateDifferentialBasis
  have he (j : Fin d) :
      algebraMap A E (e (MvPolynomial.X j)) = algebraMap F E (chartCoordinates x i j) :=
    congrArg (algebraMap F E) (h.pd.chartPolynomialEquiv_X i j)
  simpa only [he] using normalized_affine_trace_dual_iff A e b z

/-- The same trace-dual characterization on any nonempty standard
intersection, using the volume of a chart containing it. -/
theorem IsFinCover.intersection_trace_dual_iff (h : IsFinCover k E x)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (z : E) :
    (∀ b : rB k E x I, Algebra.trace F E (z * (b : E)) ∈ rA k x I) ↔
      z • (ExteriorAlgebra.ιMulti E d fun j => D k E (algebraMap F E (chartCoordinates x i j))) ∈
        omB k E (rB k E x I) d := by
  let A := rA k x {i}
  let C := rA k x I
  let B := integralClosure A E
  let T := integralClosure C E
  let s := chartDenominator k x I i
  let ω : ExteriorDifferentials k E d := exteriorPower.ιMulti E d
    (fun j => D k E (algebraMap F E (chartCoordinates x i j)))
  letI : Module.Finite A B := (h.finiteProjective_chart i).1
  letI : Algebra A C := chartIntersectionAlgebra (k := k) (x := x) hi
  letI : IsScalarTower A C F := chartIntersection_tower (k := k) (x := x) hi
  letI : IsLocalization.Away s C := chartIntersection_isLocalization h.pd hi
  letI : Algebra B T := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
  letI : IsScalarTower B T E := normalizedIntersection_tower (k := k) (x := x) (E := E) hi
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers s)) T := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (normalizedIntersection_isLocalization (E := E) h.pd hi)
  have htr := finite_trace_dual_localization (R := C) (T := T) (Submonoid.powers s) z
  simp only [mem_algebraMap_range_subalgebra] at htr
  change _ ↔ ((z • ω : ExteriorDifferentials k E d) : DR k E) ∈ _
  rw [mem_omB_chartIntersection_iff h.pd hi]
  refine htr.trans ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn⟩ := a.property
    have ht : algebraMap A E (a : A) = algebraMap F E (s : F) ^ n := by
      rw [← hn, map_pow]
      rfl
    refine ⟨n, ?_⟩
    simpa only [ht, ← smul_smul, Submodule.coe_smul_of_tower] using
      (h.affine_trace_dual_iff i _).mp ha
  · rintro ⟨n, hn⟩
    refine ⟨⟨s ^ n, ⟨n, rfl⟩⟩, (h.affine_trace_dual_iff i _).mpr ?_⟩
    simpa only [map_pow, ← smul_smul, Submodule.coe_smul_of_tower] using hn

end GlobalTheory.PD
