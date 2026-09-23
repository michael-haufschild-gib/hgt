import GaloisForLFunctions.RHTower.DeningerArithmeticAssociatedGraded
import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHilbertHodge

/-!
# Zero-indexed completed comparison target

This module assembles a completed Xi-divisor comparison target in degrees zero, one, and two:

* `H^(0 : ℕ) = C`;
* `H^(1 : ℕ) = ell^(2 : ℕ)` completion of the source jet associated graded;
* `H^(2 : ℕ) = C(-1)`.

The endpoint cup pairing is multiplication followed by the degree-two trace.  The middle cup is
the completed oriented alternating form.  Both Poincare pairings are nondegenerate, cup followed
by Hodge star is positive, endpoint Frobenius has weights zero and one, and the middle Frobenius
is the closed densely defined maximal associated-graded source generator.

The middle carrier is definitionally `XiDivisorL2`, so this is not a source-native construction of
arithmetic cohomology.  All displayed algebraic and Hilbert identities except middle
Frobenius/Hodge commutation hold unconditionally on this comparison target.  That final
compatibility is exactly RH and is not proved here.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Completed degree-zero arithmetic cohomology. -/
abbrev DeningerArithmeticCompletedH0 := ℂ

/-- Zero-indexed completed degree-one comparison carrier. -/
abbrev DeningerArithmeticCompletedH1 := XiDivisorL2

/-- Completed degree-two Tate cohomology. -/
abbrev DeningerArithmeticCompletedH2 := ℂ

/--
Source-derived Gelfand rigging of completed middle cohomology:
finite compact-support jets inside `ell^(2 : ℕ)`, inside compact-open ordinary cohomology.
-/
def deningerArithmeticCompletedGelfandTriple :
    DeningerArithmeticGelfandTriple DeningerArithmeticCompletedH1 :=
  deningerArithmeticJetGelfandTriple

/--
Canonical identification of completed middle cohomology with the Hilbert completion of the
source jet associated graded.
-/
def deningerArithmeticCompletedH1SourceEquiv :
    DeningerArithmeticCompletedH1 ≃ₗ[ℂ]
      DeningerArithmeticJetHilbert :=
  deningerArithmeticGradedHilbertEquivSourceJets

/--
Closed middle Frobenius on completed associated-graded source cohomology.

`DeningerArithmeticAssociatedGraded` proves that this diagonal operator is induced by the full
compact-open source Frobenius on every successive jet-depth quotient.
-/
def deningerArithmeticCompletedThetaH1 :
    DeningerArithmeticCompletedH1 →ₗ.[ℂ]
      DeningerArithmeticCompletedH1 :=
  deningerDivisorClosedTheta

/-- Degree-zero/degree-two Poincare cup followed by the endpoint trace. -/
def deningerArithmeticCompletedEndpointCup :
    LinearMap.BilinForm ℂ ℂ :=
  LinearMap.mk₂ ℂ
    (fun a b => a * b)
    (by intros; ring)
    (by intros; simp [smul_eq_mul]; ring)
    (by intros; ring)
    (by intros; simp [smul_eq_mul]; ring)

@[simp]
theorem deningerArithmeticCompletedEndpointCup_apply (a b : ℂ) :
    deningerArithmeticCompletedEndpointCup a b = a * b :=
  rfl

/-- Endpoint Poincare pairing is nondegenerate. -/
theorem deningerArithmeticCompletedEndpointCup_nondegenerate :
    deningerArithmeticCompletedEndpointCup.Nondegenerate := by
  constructor
  · intro a ha
    simpa using ha 1
  · intro b hb
    simpa using hb 1

/-- Even endpoint Hodge identification between `H^(0 : ℕ)` and `H^(2 : ℕ)`. -/
def deningerArithmeticCompletedEndpointHodge :
    ℂ ≃ₛₗ[starRingEnd ℂ] ℂ :=
  starLinearEquiv ℂ

@[simp]
theorem deningerArithmeticCompletedEndpointHodge_apply (a : ℂ) :
    deningerArithmeticCompletedEndpointHodge a =
      (starRingEnd ℂ) a :=
  rfl

/-- Endpoint Hodge identification is involutive. -/
theorem deningerArithmeticCompletedEndpointHodge_sq (a : ℂ) :
    deningerArithmeticCompletedEndpointHodge
        (deningerArithmeticCompletedEndpointHodge a) = a := by
  simp

/-- Endpoint cup followed by Hodge star is the scalar norm square. -/
theorem deningerArithmeticCompletedEndpointCup_hodge (a : ℂ) :
    deningerArithmeticCompletedEndpointCup a
        (deningerArithmeticCompletedEndpointHodge a) =
      (Complex.normSq a : ℂ) := by
  rw [deningerArithmeticCompletedEndpointCup_apply,
    deningerArithmeticCompletedEndpointHodge_apply,
    Complex.mul_conj]

/-- Endpoint Hodge metric is positive definite. -/
theorem deningerArithmeticCompletedEndpointHodge_positive
    {a : ℂ} (ha : a ≠ 0) :
    0 < (deningerArithmeticCompletedEndpointCup a
      (deningerArithmeticCompletedEndpointHodge a)).re := by
  rw [deningerArithmeticCompletedEndpointCup_hodge]
  simpa using Complex.normSq_pos.mpr ha

/-- Weight-zero Frobenius on completed `H^(0 : ℕ)`. -/
def deningerArithmeticCompletedThetaH0 :
    Module.End ℂ DeningerArithmeticCompletedH0 :=
  0

/-- Weight-one Frobenius on completed `H^(2 : ℕ) = C(-1)`. -/
def deningerArithmeticCompletedThetaH2 :
    Module.End ℂ DeningerArithmeticCompletedH2 :=
  LinearMap.id

@[simp]
theorem deningerArithmeticCompletedThetaH0_apply (a : ℂ) :
    deningerArithmeticCompletedThetaH0 a = 0 :=
  rfl

@[simp]
theorem deningerArithmeticCompletedThetaH2_apply (a : ℂ) :
    deningerArithmeticCompletedThetaH2 a = a :=
  rfl

/-- Endpoint Frobenius is a weight-one derivation of the `H^(0 : ℕ) x H^(2 : ℕ)` cup. -/
theorem deningerArithmeticCompletedTheta_endpointCup (a b : ℂ) :
    deningerArithmeticCompletedEndpointCup
          (deningerArithmeticCompletedThetaH0 a) b +
        deningerArithmeticCompletedEndpointCup a
          (deningerArithmeticCompletedThetaH2 b) =
      deningerArithmeticCompletedEndpointCup a b := by
  simp

/--
Exact completed Deninger package in degrees zero through two.  Final conjunct identifies the
remaining middle-purity compatibility with RH.
-/
theorem deningerArithmeticCompletedCohomology_package :
    deningerArithmeticCompletedEndpointCup.Nondegenerate ∧
    deningerArithmeticOrientedHilbertCup.IsAlt ∧
    deningerArithmeticOrientedHilbertCup.Nondegenerate ∧
    (∀ {a : DeningerArithmeticCompletedH0}, a ≠ 0 →
      0 < (deningerArithmeticCompletedEndpointCup a
        (deningerArithmeticCompletedEndpointHodge a)).re) ∧
    (∀ {a : DeningerArithmeticCompletedH1}, a ≠ 0 →
      0 < (deningerArithmeticOrientedHilbertCup a
        (deningerArithmeticOrientedHodgeLp a)).re) ∧
    deningerDivisorClosedTheta.IsClosed ∧
    Dense (deningerDivisorClosedTheta.domain :
      Set DeningerArithmeticCompletedH1) ∧
    (∀ a b : ℂ,
      deningerArithmeticCompletedEndpointCup
            (deningerArithmeticCompletedThetaH0 a) b +
          deningerArithmeticCompletedEndpointCup a
            (deningerArithmeticCompletedThetaH2 b) =
        deningerArithmeticCompletedEndpointCup a b) ∧
    (∀ x y : deningerDivisorClosedTheta.domain,
      deningerArithmeticOrientedHilbertCup
            (deningerDivisorClosedTheta x)
            (y : DeningerArithmeticCompletedH1) +
          deningerArithmeticOrientedHilbertCup
            (x : DeningerArithmeticCompletedH1)
            (deningerDivisorClosedTheta y) =
        deningerArithmeticOrientedHilbertCup
          (x : DeningerArithmeticCompletedH1)
          (y : DeningerArithmeticCompletedH1)) ∧
    ((∀ x : deningerDivisorClosedTheta.domain,
      deningerArithmeticOrientedHodgeLp (deningerDivisorClosedTheta x) =
        deningerDivisorClosedTheta
          (deningerArithmeticOrientedHodgeDomain x)) ↔
      RiemannHypothesis) := by
  exact
    ⟨deningerArithmeticCompletedEndpointCup_nondegenerate,
      deningerArithmeticOrientedHilbertCup_isAlt,
      deningerArithmeticOrientedHilbertCup_nondegenerate,
      deningerArithmeticCompletedEndpointHodge_positive,
      deningerArithmeticOrientedHilbertHodge_positive,
      deningerDivisorClosedTheta_isClosed,
      deningerDivisorClosedTheta_dense,
      deningerArithmeticCompletedTheta_endpointCup,
      deningerDivisorClosedTheta_orientedCup,
      deningerDivisorClosedTheta_orientedHodge_iff_riemannHypothesis⟩

end

end RHTower
