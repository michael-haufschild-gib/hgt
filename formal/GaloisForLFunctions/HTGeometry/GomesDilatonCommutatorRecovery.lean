import GaloisForLFunctions.HTGeometry.GomesDilatonCommutatorRecord
import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Constructive recovery and the quotient by the invisible affine sector

The reconstruction experiment from arXiv:2607.24901v1 section 4 becomes an exact inverse
problem for the corpus's polynomial connection profiles. Two existing anchored polynomial
antiderivatives construct every preimage of the commutator record. The faithful quotient
is explicitly linearly equivalent to the polynomial record space; restoring two origin jets
recovers the full generating profile.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Explicit recovery from the commutator polynomial, origin value, and origin slope. -/
def gomesDilatonRebuild (P : ℝ[X]) (v s : ℝ) : ℝ[X] :=
  anchoredRealAntiderivative (anchoredRealAntiderivative (-P) 0 s) 0 v

/-- The recovered profile realizes the requested commutator exactly. -/
theorem gomesDilatonRebuild_record (P : ℝ[X]) (v s : ℝ) :
    gomesDilatonCommutatorRecord (gomesDilatonRebuild P v s) = P := by
  rw [gomesDilatonCommutatorRecord_apply, gomesDilatonRebuild,
    derivative_anchoredRealAntiderivative, derivative_anchoredRealAntiderivative, neg_neg]

/-- The first restored boundary datum is the literal value at the origin. -/
theorem gomesDilatonRebuild_value (P : ℝ[X]) (v s : ℝ) :
    (gomesDilatonRebuild P v s).eval 0 = v :=
  eval_anchoredRealAntiderivative_anchor _ _ _

/-- The second restored boundary datum is the literal derivative at the origin. -/
theorem gomesDilatonRebuild_slope (P : ℝ[X]) (v s : ℝ) :
    (gomesDilatonRebuild P v s).derivative.eval 0 = s := by
  rw [gomesDilatonRebuild, derivative_anchoredRealAntiderivative, eval_anchoredRealAntiderivative_anchor]

/-- Every requested augmented record is realized, with no consistency premise. -/
theorem gomesDilatonRebuild_origin_record (P : ℝ[X]) (v s : ℝ) :
    gomesDilatonOriginRecord (gomesDilatonRebuild P v s) = (P, v, s) := by
  simp only [gomesDilatonOriginRecord, gomesDilatonRebuild_record,
    gomesDilatonRebuild_value, gomesDilatonRebuild_slope]

/-- Recovering from a profile's own record returns exactly that profile. -/
theorem gomesDilatonRebuild_original (H : ℝ[X]) :
    gomesDilatonRebuild (gomesDilatonCommutatorRecord H) (H.eval 0) (H.derivative.eval 0) = H := by
  apply gomesDilatonOriginRecord_injective
  rw [gomesDilatonRebuild_origin_record]
  rfl

/-- Complete solution classification for the inverse problem, including both boundary numbers. -/
theorem gomesDilatonRebuild_unique (P H : ℝ[X]) (v s : ℝ) :
    (gomesDilatonCommutatorRecord H = P ∧ H.eval 0 = v ∧ H.derivative.eval 0 = s) ↔
      H = gomesDilatonRebuild P v s := by
  have h := gomesDilatonCommutatorRecord_origin_iff H (gomesDilatonRebuild P v s)
  simpa only [gomesDilatonRebuild_record, gomesDilatonRebuild_value, gomesDilatonRebuild_slope] using h

/-- Every polynomial commutator record has an explicit profile preimage. -/
theorem gomesDilatonCommutatorRecord_surjective : Function.Surjective gomesDilatonCommutatorRecord :=
  fun P => ⟨gomesDilatonRebuild P 0 0, gomesDilatonRebuild_record P 0 0⟩

/-- The two missing boundary numbers parameterize the whole fiber of each record. -/
theorem gomesDilatonCommutatorRecord_fiber (P H : ℝ[X]) :
    gomesDilatonCommutatorRecord H = P ↔ ∃ v s : ℝ, H = gomesDilatonRebuild P v s := by
  constructor
  · intro h
    exact ⟨H.eval 0, H.derivative.eval 0,
      (gomesDilatonRebuild_unique P H _ _).mp ⟨h, rfl, rfl⟩⟩
  · rintro ⟨v, s, rfl⟩
    exact gomesDilatonRebuild_record _ _ _

/-- The augmented data and the complete polynomial profile are equivalent without restriction. -/
def gomesDilatonOriginEquiv : ℝ[X] ≃ ℝ[X] × ℝ × ℝ where
  toFun := gomesDilatonOriginRecord
  invFun r := gomesDilatonRebuild r.1 r.2.1 r.2.2
  left_inv H := gomesDilatonRebuild_original H
  right_inv r := by
    rcases r with ⟨P, v, s⟩
    exact gomesDilatonRebuild_origin_record P v s

/-- The profile quotient by the exact invisible affine kernel. -/
abbrev GomesDilatonCommutatorQuotient := ℝ[X] ⧸ LinearMap.ker gomesDilatonCommutatorRecord

/-- Quotienting by the invisible kernel gives a faithful copy of the entire record space. -/
def gomesDilatonCommutatorQuotientEquiv : GomesDilatonCommutatorQuotient ≃ₗ[ℝ] ℝ[X] :=
  gomesDilatonCommutatorRecord.quotKerEquivOfSurjective gomesDilatonCommutatorRecord_surjective

/-- The quotient equivalence sends a profile class to its actual commutator record. -/
theorem gomesDilatonCommutatorQuotientEquiv_mk (H : ℝ[X]) :
    gomesDilatonCommutatorQuotientEquiv (Submodule.Quotient.mk H) = gomesDilatonCommutatorRecord H :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- Quotient equality is exactly affine observational ambiguity. -/
theorem gomesDilatonCommutatorQuotient_eq_iff (H K : ℝ[X]) :
    (Submodule.Quotient.mk H : GomesDilatonCommutatorQuotient) = Submodule.Quotient.mk K ↔
      ∃ d e : ℝ, H = K + C d * X + C e := by
  constructor
  · intro h
    apply (gomesDilatonCommutatorRecord_eq_iff H K).mp
    have he := congrArg gomesDilatonCommutatorQuotientEquiv h
    simpa only [gomesDilatonCommutatorQuotientEquiv_mk] using he
  · intro h
    apply gomesDilatonCommutatorQuotientEquiv.injective
    rw [gomesDilatonCommutatorQuotientEquiv_mk, gomesDilatonCommutatorQuotientEquiv_mk]
    exact (gomesDilatonCommutatorRecord_eq_iff H K).mpr h

/-- The canonical representative discards exactly the two origin jets. -/
def gomesDilatonNormalize (H : ℝ[X]) : ℝ[X] :=
  gomesDilatonRebuild (gomesDilatonCommutatorRecord H) 0 0

/-- Normalization retains all commutator information. -/
theorem gomesDilatonNormalize_record (H : ℝ[X]) :
    gomesDilatonCommutatorRecord (gomesDilatonNormalize H) = gomesDilatonCommutatorRecord H :=
  gomesDilatonRebuild_record _ _ _

/-- The canonical representative has both origin jets zero. -/
theorem gomesDilatonNormalize_origin (H : ℝ[X]) :
    (gomesDilatonNormalize H).eval 0 = 0 ∧ (gomesDilatonNormalize H).derivative.eval 0 = 0 :=
  ⟨gomesDilatonRebuild_value _ _ _, gomesDilatonRebuild_slope _ _ _⟩

/-- Exact decomposition into the faithful representative and the invisible affine part. -/
theorem gomesDilatonNormalize_decomposition (H : ℝ[X]) :
    H = gomesDilatonNormalize H + C (H.derivative.eval 0) * X + C (H.eval 0) := by
  apply (gomesDilatonCommutatorRecord_origin_iff _ _).mp
  refine ⟨?_, ?_, ?_⟩
  · rw [gomesDilatonCommutatorRecord_affine, gomesDilatonNormalize_record]
  · simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero,
      (gomesDilatonNormalize_origin H).1, zero_add]
  · simp only [derivative_add, derivative_C_mul, derivative_X, mul_one, derivative_C,
      eval_add, eval_C, add_zero, (gomesDilatonNormalize_origin H).2, zero_add]

/-- Once the affine part has been removed, normalization changes nothing further. -/
theorem gomesDilatonNormalize_idempotent (H : ℝ[X]) :
    gomesDilatonNormalize (gomesDilatonNormalize H) = gomesDilatonNormalize H := by
  unfold gomesDilatonNormalize
  rw [gomesDilatonRebuild_record]

end GaloisForLFunctions.HTGeometry
