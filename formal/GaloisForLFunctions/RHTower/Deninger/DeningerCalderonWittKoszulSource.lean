import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittOrientedSource

/-!
# Calderón--Witt Koszul--Arakelov source differential

The distinguished Calderón unit defect is a genuine degree-one source
class.  Left cup by this class defines a linear source differential

`Q_p ⊕ P_p^alg → T_p(P_p^alg)`.

Its kernel is exactly the Calderón-defect axis and its explicit
right inverse is the normalized center-to-packet leg.  Graphing this
differential against the source Haar orientation produces a
three-term arithmetic source complex with zero middle cohomology and
one top orientation line.  This is the direct differential-level
attachment, not merely the exterior Milnor presentation.
-/

namespace RHTower

open scoped DirectSum

noncomputable section

/-! ## Local Koszul source differential -/

/-- Inclusion of the pure Calderón-defect axis. -/
def deningerCalderonWittDefectAxisInclusion
    (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeOne p :=
  LinearMap.inl ℂ
    (DeningerMeyerPrimeCalderonQuotient p)
    (DeningerPrimeFinitePacketGaugeAlgebraic p)

/-- Koszul differential given by left cup with the distinguished
Calderón unit defect. -/
def deningerCalderonWittKoszulBoundary
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo p :=
  deningerCalderonWittAlgebraicCup p
    (deningerCalderonWittUnitDefect p, 0)

/-- The Koszul differential is the nonzero half-density-scaled first
suspension of the packet coordinate. -/
theorem deningerCalderonWittKoszulBoundary_apply
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittKoszulBoundary p x =
      deningerCalderonWittHalfDensityScale p •
        deningerPrimeFinitePacketGaugeAlgebraicFirstMode p x.2 := by
  change
    deningerMeyerCalderonWittAlgebraicCrossEffect p
        (deningerCalderonWittUnitDefect p) x.2 -
      deningerMeyerCalderonWittAlgebraicCrossEffect p x.1 0 =
        deningerCalderonWittHalfDensityScale p •
          deningerPrimeFinitePacketGaugeAlgebraicFirstMode p x.2
  rw [map_zero, sub_zero,
    deningerMeyerCalderonWittAlgebraicCrossEffect_unit]

/-- The center-to-degree-one leg is an exact section of the Koszul
differential. -/
theorem deningerCalderonWittKoszulBoundary_section
    (p : Nat.Primes) :
    (deningerCalderonWittKoszulBoundary p).comp
        (deningerCalderonWittCenterToDegreeOne p) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun
    (deningerCalderonWittExteriorCup_section p) z
  simpa [deningerCalderonWittExteriorCupSection,
    deningerCalderonWittExteriorWedgeLeft_apply,
    deningerCalderonWittAlgebraicExteriorCup_ιMulti,
    deningerCalderonWittKoszulBoundary,
    LinearMap.comp_apply] using hz

theorem deningerCalderonWittKoszulBoundary_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (deningerCalderonWittKoszulBoundary p) := by
  intro z
  exact
    ⟨deningerCalderonWittCenterToDegreeOne p z,
      LinearMap.congr_fun
        (deningerCalderonWittKoszulBoundary_section p) z⟩

/-- Pure defect classes map to zero. -/
theorem deningerCalderonWittKoszulBoundary_defectAxis
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p) :
    deningerCalderonWittKoszulBoundary p
        (deningerCalderonWittDefectAxisInclusion p q) =
      0 := by
  rw [deningerCalderonWittKoszulBoundary_apply]
  change
    deningerCalderonWittHalfDensityScale p •
        deningerPrimeFinitePacketGaugeAlgebraicFirstMode p 0 =
      0
  rw [map_zero, smul_zero]

/-- The source differential kernel is exactly the pure defect axis. -/
theorem deningerCalderonWittDefectAxis_exact :
    Function.Exact
      (deningerCalderonWittDefectAxisInclusion p)
      (deningerCalderonWittKoszulBoundary p) := by
  intro x
  constructor
  · intro hx
    rw [deningerCalderonWittKoszulBoundary_apply] at hx
    have hfirst :
        deningerPrimeFinitePacketGaugeAlgebraicFirstMode p x.2 = 0 := by
      exact
        (smul_eq_zero.mp hx).resolve_left
          (deningerCalderonWittHalfDensityScale_ne_zero p)
    have hpacket : x.2 = 0 :=
      deningerPrimeFinitePacketGaugeAlgebraicFirstMode_injective p
        (by simpa using hfirst)
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact hpacket.symm
  · rintro ⟨q, rfl⟩
    exact deningerCalderonWittKoszulBoundary_defectAxis p q

/-- Retraction onto the pure defect axis. -/
def deningerCalderonWittDefectAxisRetraction
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerMeyerPrimeCalderonQuotient p :=
  LinearMap.fst ℂ
    (DeningerMeyerPrimeCalderonQuotient p)
    (DeningerPrimeFinitePacketGaugeAlgebraic p)

/-- Local Koszul--Green decomposition of every degree-one source
class into exact defect axis and center lift. -/
theorem deningerCalderonWittKoszulGreenDecomposition
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittDefectAxisInclusion p
        (deningerCalderonWittDefectAxisRetraction p x) +
      deningerCalderonWittCenterToDegreeOne p
        (deningerCalderonWittKoszulBoundary p x) =
      x := by
  apply Prod.ext
  · simp [deningerCalderonWittDefectAxisInclusion,
      deningerCalderonWittDefectAxisRetraction,
      deningerCalderonWittCenterToDegreeOne_apply]
  · rw [deningerCalderonWittKoszulBoundary_apply,
      deningerCalderonWittCenterToDegreeOne_apply]
    change
      0 +
        (deningerCalderonWittHalfDensityScale p)⁻¹ •
            (deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).symm
              (deningerCalderonWittHalfDensityScale p •
                deningerPrimeFinitePacketGaugeAlgebraicFirstMode p x.2) =
        x.2
    rw [zero_add]
    rw [map_smul]
    rw [← mul_smul, inv_mul_cancel₀
      (deningerCalderonWittHalfDensityScale_ne_zero p), one_smul]
    rw [show
      (deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).symm
          (deningerPrimeFinitePacketGaugeAlgebraicFirstMode p x.2) =
        x.2 by
      rw [←
        deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv_apply p]
      exact
        (deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p)
          |>.symm_apply_apply x.2]

/-! ## Local oriented Koszul--Arakelov complex -/

/-- Oriented Koszul differential. -/
def deningerCalderonWittOrientedKoszulBoundary
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) :=
  (deningerCalderonWittOrientedCenterGraph p).comp
    (deningerCalderonWittKoszulBoundary p)

/-- The oriented Koszul boundary has trace kernel as its exact image. -/
theorem deningerCalderonWittOrientedKoszulBoundary_exact_trace :
    Function.Exact
      (deningerCalderonWittOrientedKoszulBoundary p)
      (deningerCalderonWittOrientedTrace p) := by
  intro z
  constructor
  · intro hz
    change
      deningerCalderonWittAlgebraicCenterTrace p z.1 + z.2 =
        0 at hz
    obtain ⟨x, hx⟩ :=
      deningerCalderonWittKoszulBoundary_surjective p z.1
    refine ⟨x, ?_⟩
    apply Prod.ext
    · exact hx
    · change
        -deningerCalderonWittAlgebraicCenterTrace p
            (deningerCalderonWittKoszulBoundary p x) =
          z.2
      rw [hx]
      exact neg_eq_of_add_eq_zero_right hz
  · rintro ⟨x, rfl⟩
    exact add_neg_cancel _

/-- The pure defect axis remains exactly the middle kernel after
orientation graphing. -/
theorem deningerCalderonWittOrientedDefectAxis_exact :
    Function.Exact
      (deningerCalderonWittDefectAxisInclusion p)
      (deningerCalderonWittOrientedKoszulBoundary p) := by
  intro x
  constructor
  · intro hx
    apply (deningerCalderonWittDefectAxis_exact x).1
    exact congrArg Prod.fst hx
  · intro hx
    have hboundary :
        deningerCalderonWittKoszulBoundary p x = 0 :=
      (deningerCalderonWittDefectAxis_exact x).2 hx
    apply Prod.ext
    · exact hboundary
    · change
        -deningerCalderonWittAlgebraicCenterTrace p
            (deningerCalderonWittKoszulBoundary p x) =
          0
      rw [hboundary, map_zero, neg_zero]

/-- Direct local arithmetic source complex. -/
def deningerCalderonWittOrientedKoszulSourceComplex
    (p : Nat.Primes) :
    DeningerArithmeticThreeTermComplex ℂ
      (DeningerMeyerPrimeCalderonQuotient p)
      (DeningerCalderonWittAlgebraicDegreeOne p)
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) where
  d0 := deningerCalderonWittDefectAxisInclusion p
  d1 := deningerCalderonWittOrientedKoszulBoundary p
  d1_comp_d0 :=
    deningerCalderonWittOrientedDefectAxis_exact
      |>.linearMap_comp_eq_zero

theorem deningerCalderonWittOrientedKoszulSourceComplex_H0_eq_zero
    (p : Nat.Primes)
    (x : (deningerCalderonWittOrientedKoszulSourceComplex p).H0) :
    x = 0 :=
  deningerThreeTermH0_eq_zero_of_injective
    (deningerCalderonWittOrientedKoszulSourceComplex p)
    (by
      intro q r hqr
      exact congrArg Prod.fst hqr) x

theorem deningerCalderonWittOrientedKoszulSourceComplex_H1_eq_zero
    (p : Nat.Primes)
    (x : (deningerCalderonWittOrientedKoszulSourceComplex p).H1) :
    x = 0 :=
  deningerThreeTermH1_eq_zero_of_exact
    (deningerCalderonWittOrientedKoszulSourceComplex p)
    deningerCalderonWittOrientedDefectAxis_exact x

/-- Direct local source top cohomology is the orientation line. -/
def deningerCalderonWittOrientedKoszulSourceComplexH2Equiv
    (p : Nat.Primes) :
    (deningerCalderonWittOrientedKoszulSourceComplex p).H2 ≃ₗ[ℂ] ℂ :=
  deningerCalderonWittOrientedKoszulBoundary_exact_trace
    |>.linearEquivOfSurjective
      deningerCalderonWittOrientedTrace_surjective

/-! ## All-prime Koszul source differential -/

/-- Finite-support all-prime Calderón-defect axis. -/
abbrev DeningerCalderonWittGlobalDefectAxis : Type :=
  ⨁ p : Nat.Primes, DeningerMeyerPrimeCalderonQuotient p

/-- Insert one local defect axis into all-prime degree one. -/
def deningerCalderonWittGlobalPrimeDefectAxisInclusion
    (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  (DirectSum.lof ℂ Nat.Primes
    DeningerCalderonWittAlgebraicDegreeOne p).comp
      (deningerCalderonWittDefectAxisInclusion p)

/-- All-prime pure-defect inclusion. -/
def deningerCalderonWittGlobalDefectAxisInclusion :
    DeningerCalderonWittGlobalDefectAxis →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  DirectSum.toModule ℂ Nat.Primes
    DeningerCalderonWittAlgebraicGlobalDegreeOne
      deningerCalderonWittGlobalPrimeDefectAxisInclusion

@[simp]
theorem deningerCalderonWittGlobalDefectAxisInclusion_lof
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p) :
    deningerCalderonWittGlobalDefectAxisInclusion
        (DirectSum.lof ℂ Nat.Primes
          DeningerMeyerPrimeCalderonQuotient p q) =
      DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeOne p
          (deningerCalderonWittDefectAxisInclusion p q) := by
  rw [deningerCalderonWittGlobalDefectAxisInclusion,
    DirectSum.toModule_lof]
  rfl

/-- Insert one local Koszul boundary into the all-prime center. -/
def deningerCalderonWittGlobalPrimeKoszulBoundary
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  (DirectSum.lof ℂ Nat.Primes
    DeningerCalderonWittAlgebraicDegreeTwo p).comp
      (deningerCalderonWittKoszulBoundary p)

/-- All-prime componentwise Koszul differential.  The primewise unit
family acts diagonally without being falsely inserted as one
finite-support degree-one vector. -/
def deningerCalderonWittGlobalKoszulBoundary :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  DirectSum.toModule ℂ Nat.Primes
    DeningerCalderonWittAlgebraicGlobalDegreeTwo
      deningerCalderonWittGlobalPrimeKoszulBoundary

@[simp]
theorem deningerCalderonWittGlobalKoszulBoundary_lof
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittGlobalKoszulBoundary
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x) =
      DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeTwo p
          (deningerCalderonWittKoszulBoundary p x) := by
  rw [deningerCalderonWittGlobalKoszulBoundary,
    DirectSum.toModule_lof]
  rfl

/-- Insert one local center section into all-prime degree one. -/
def deningerCalderonWittGlobalPrimeCenterToDegreeOne
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeTwo p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  (DirectSum.lof ℂ Nat.Primes
    DeningerCalderonWittAlgebraicDegreeOne p).comp
      (deningerCalderonWittCenterToDegreeOne p)

/-- All-prime source-derived section of the Koszul differential. -/
def deningerCalderonWittGlobalCenterToDegreeOne :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  DirectSum.toModule ℂ Nat.Primes
    DeningerCalderonWittAlgebraicGlobalDegreeOne
      deningerCalderonWittGlobalPrimeCenterToDegreeOne

@[simp]
theorem deningerCalderonWittGlobalCenterToDegreeOne_lof
    (p : Nat.Primes)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p) :
    deningerCalderonWittGlobalCenterToDegreeOne
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeTwo p z) =
      DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeOne p
          (deningerCalderonWittCenterToDegreeOne p z) := by
  rw [deningerCalderonWittGlobalCenterToDegreeOne,
    DirectSum.toModule_lof]
  rfl

/-- Global Koszul differential retracts its finite-support source
section. -/
theorem deningerCalderonWittGlobalKoszulBoundary_section :
    deningerCalderonWittGlobalKoszulBoundary.comp
        deningerCalderonWittGlobalCenterToDegreeOne =
      LinearMap.id := by
  apply DirectSum.linearMap_ext ℂ
  intro p
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [deningerCalderonWittGlobalCenterToDegreeOne_lof,
    deningerCalderonWittGlobalKoszulBoundary_lof]
  have hz := LinearMap.congr_fun
    (deningerCalderonWittKoszulBoundary_section p) z
  rw [show
    deningerCalderonWittKoszulBoundary p
        (deningerCalderonWittCenterToDegreeOne p z) = z by
      simpa [LinearMap.comp_apply] using hz]

theorem deningerCalderonWittGlobalKoszulBoundary_surjective :
    Function.Surjective
      deningerCalderonWittGlobalKoszulBoundary := by
  intro z
  exact
    ⟨deningerCalderonWittGlobalCenterToDegreeOne z,
      LinearMap.congr_fun
        deningerCalderonWittGlobalKoszulBoundary_section z⟩

/-- Insert local defect retraction into the global defect sum. -/
def deningerCalderonWittGlobalPrimeDefectAxisRetraction
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittGlobalDefectAxis :=
  (DirectSum.lof ℂ Nat.Primes
    DeningerMeyerPrimeCalderonQuotient p).comp
      (deningerCalderonWittDefectAxisRetraction p)

/-- All-prime retraction onto pure Calderón defects. -/
def deningerCalderonWittGlobalDefectAxisRetraction :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittGlobalDefectAxis :=
  DirectSum.toModule ℂ Nat.Primes
    DeningerCalderonWittGlobalDefectAxis
      deningerCalderonWittGlobalPrimeDefectAxisRetraction

@[simp]
theorem deningerCalderonWittGlobalDefectAxisRetraction_lof
    (p : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittGlobalDefectAxisRetraction
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p x) =
      DirectSum.lof ℂ Nat.Primes
        DeningerMeyerPrimeCalderonQuotient p
          (deningerCalderonWittDefectAxisRetraction p x) := by
  rw [deningerCalderonWittGlobalDefectAxisRetraction,
    DirectSum.toModule_lof]
  rfl

/-- Global defect retraction splits global defect inclusion. -/
theorem deningerCalderonWittGlobalDefectAxisRetraction_section :
    deningerCalderonWittGlobalDefectAxisRetraction.comp
        deningerCalderonWittGlobalDefectAxisInclusion =
      LinearMap.id := by
  apply DirectSum.linearMap_ext ℂ
  intro p
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [deningerCalderonWittGlobalDefectAxisInclusion_lof,
    deningerCalderonWittGlobalDefectAxisRetraction_lof]
  rfl

theorem deningerCalderonWittGlobalDefectAxisInclusion_injective :
    Function.Injective
      deningerCalderonWittGlobalDefectAxisInclusion := by
  have hleft :
      Function.LeftInverse
        deningerCalderonWittGlobalDefectAxisRetraction
        deningerCalderonWittGlobalDefectAxisInclusion := by
    intro q
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun
        deningerCalderonWittGlobalDefectAxisRetraction_section q
  exact hleft.injective

/-- Global Koszul--Green decomposition. -/
theorem deningerCalderonWittGlobalKoszulGreenDecomposition
    (x : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittGlobalDefectAxisInclusion
        (deningerCalderonWittGlobalDefectAxisRetraction x) +
      deningerCalderonWittGlobalCenterToDegreeOne
        (deningerCalderonWittGlobalKoszulBoundary x) =
      x := by
  have hlinear :
      deningerCalderonWittGlobalDefectAxisInclusion.comp
          deningerCalderonWittGlobalDefectAxisRetraction +
        deningerCalderonWittGlobalCenterToDegreeOne.comp
          deningerCalderonWittGlobalKoszulBoundary =
        LinearMap.id := by
    apply DirectSum.linearMap_ext ℂ
    intro p
    apply LinearMap.ext
    intro y
    simp only [LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    rw [deningerCalderonWittGlobalDefectAxisRetraction_lof,
      deningerCalderonWittGlobalDefectAxisInclusion_lof,
      deningerCalderonWittGlobalKoszulBoundary_lof,
      deningerCalderonWittGlobalCenterToDegreeOne_lof,
      ← map_add]
    exact congrArg
      (DirectSum.lof ℂ Nat.Primes
        DeningerCalderonWittAlgebraicDegreeOne p)
      (deningerCalderonWittKoszulGreenDecomposition p y)
  exact LinearMap.congr_fun hlinear x

/-- Global Koszul differential kills the global defect axis. -/
theorem deningerCalderonWittGlobalKoszulBoundary_defectAxis :
    deningerCalderonWittGlobalKoszulBoundary.comp
        deningerCalderonWittGlobalDefectAxisInclusion =
      0 := by
  apply DirectSum.linearMap_ext ℂ
  intro p
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [deningerCalderonWittGlobalDefectAxisInclusion_lof,
    deningerCalderonWittGlobalKoszulBoundary_lof,
    deningerCalderonWittKoszulBoundary_defectAxis,
    map_zero]

/-- All-prime pure defect axis is exactly the global Koszul kernel. -/
theorem deningerCalderonWittGlobalDefectAxis_exact :
    Function.Exact
      deningerCalderonWittGlobalDefectAxisInclusion
      deningerCalderonWittGlobalKoszulBoundary := by
  intro x
  constructor
  · intro hx
    refine
      ⟨deningerCalderonWittGlobalDefectAxisRetraction x, ?_⟩
    have hdecomp :=
      deningerCalderonWittGlobalKoszulGreenDecomposition x
    rw [hx, map_zero, add_zero] at hdecomp
    exact hdecomp
  · rintro ⟨q, rfl⟩
    exact LinearMap.congr_fun
      deningerCalderonWittGlobalKoszulBoundary_defectAxis q

/-! ## All-prime oriented Koszul--Arakelov complex -/

def deningerCalderonWittGlobalOrientedKoszulBoundary :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :=
  deningerCalderonWittGlobalOrientedCenterGraph.comp
    deningerCalderonWittGlobalKoszulBoundary

theorem deningerCalderonWittGlobalOrientedKoszulBoundary_exact_trace :
    Function.Exact
      deningerCalderonWittGlobalOrientedKoszulBoundary
      deningerCalderonWittGlobalOrientedTrace := by
  intro z
  constructor
  · intro hz
    change
      deningerCalderonWittAlgebraicGlobalCenterTrace z.1 + z.2 =
        0 at hz
    obtain ⟨x, hx⟩ :=
      deningerCalderonWittGlobalKoszulBoundary_surjective z.1
    refine ⟨x, ?_⟩
    apply Prod.ext
    · exact hx
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace
            (deningerCalderonWittGlobalKoszulBoundary x) =
          z.2
      rw [hx]
      exact neg_eq_of_add_eq_zero_right hz
  · rintro ⟨x, rfl⟩
    exact add_neg_cancel _

theorem deningerCalderonWittGlobalOrientedDefectAxis_exact :
    Function.Exact
      deningerCalderonWittGlobalDefectAxisInclusion
      deningerCalderonWittGlobalOrientedKoszulBoundary := by
  intro x
  constructor
  · intro hx
    apply (deningerCalderonWittGlobalDefectAxis_exact x).1
    exact congrArg Prod.fst hx
  · intro hx
    have hboundary :
        deningerCalderonWittGlobalKoszulBoundary x = 0 :=
      (deningerCalderonWittGlobalDefectAxis_exact x).2 hx
    apply Prod.ext
    · exact hboundary
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace
            (deningerCalderonWittGlobalKoszulBoundary x) =
          0
      rw [hboundary, map_zero, neg_zero]

/-- Direct all-prime arithmetic source complex. -/
def deningerCalderonWittGlobalOrientedKoszulSourceComplex :
    DeningerArithmeticThreeTermComplex ℂ
      DeningerCalderonWittGlobalDefectAxis
      DeningerCalderonWittAlgebraicGlobalDegreeOne
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) where
  d0 := deningerCalderonWittGlobalDefectAxisInclusion
  d1 := deningerCalderonWittGlobalOrientedKoszulBoundary
  d1_comp_d0 :=
    deningerCalderonWittGlobalOrientedDefectAxis_exact
      |>.linearMap_comp_eq_zero

theorem deningerCalderonWittGlobalOrientedKoszulSourceComplex_H0_eq_zero
    (x :
      deningerCalderonWittGlobalOrientedKoszulSourceComplex.H0) :
    x = 0 :=
  deningerThreeTermH0_eq_zero_of_injective
    deningerCalderonWittGlobalOrientedKoszulSourceComplex
    deningerCalderonWittGlobalDefectAxisInclusion_injective x

theorem deningerCalderonWittGlobalOrientedKoszulSourceComplex_H1_eq_zero
    (x :
      deningerCalderonWittGlobalOrientedKoszulSourceComplex.H1) :
    x = 0 :=
  deningerThreeTermH1_eq_zero_of_exact
    deningerCalderonWittGlobalOrientedKoszulSourceComplex
    deningerCalderonWittGlobalOrientedDefectAxis_exact x

/-- Direct all-prime source top cohomology is one orientation line. -/
def deningerCalderonWittGlobalOrientedKoszulSourceComplexH2Equiv :
    deningerCalderonWittGlobalOrientedKoszulSourceComplex.H2 ≃ₗ[ℂ] ℂ :=
  deningerCalderonWittGlobalOrientedKoszulBoundary_exact_trace
    |>.linearEquivOfSurjective
      deningerCalderonWittGlobalOrientedTrace_surjective

end

end RHTower
