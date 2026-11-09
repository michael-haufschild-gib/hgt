import GaloisForLFunctions.HTGeometry.MonicResiduePairing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The trace cokernel of a monic order

Residue duality identifies the cokernel of the integral trace pairing
with the different quotient `R[X]/(f,f')`. This identifies the actual
modules, including the singular case, before taking cardinalities.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {R : Type*} [CommRing R]

/-- The cokernel of the trace pairing of the actual monogenic algebra. -/
abbrev MonicTraceCokernel (f : R[X]) :=
  Module.Dual R (AdjoinRoot f) ⧸ LinearMap.range (Algebra.traceForm R (AdjoinRoot f))

/-- The scheme-theoretic different quotient of a monic equation. -/
abbrev MonicDifferentQuotient (f : R[X]) :=
  R[X] ⧸ Ideal.span ({f, f.derivative} : Set R[X])

theorem range_monicDifferent_mul (f : R[X]) :
    LinearMap.range (Algebra.lmul R (AdjoinRoot f) (AdjoinRoot.mk f f.derivative)) =
      (Ideal.span ({AdjoinRoot.mk f f.derivative} : Set (AdjoinRoot f))).restrictScalars R := by
  ext x
  change (∃ y, AdjoinRoot.mk f f.derivative * y = x) ↔
    x ∈ Ideal.span ({AdjoinRoot.mk f f.derivative} : Set (AdjoinRoot f))
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

/-- Multiplication by the different element and the trace pairing have equivalent cokernels. -/
def monicDifferentMulCokernelEquivTrace {f : R[X]} (hf : f.Monic) :
    (AdjoinRoot f ⧸
      LinearMap.range (Algebra.lmul R (AdjoinRoot f) (AdjoinRoot.mk f f.derivative))) ≃ₗ[R]
      MonicTraceCokernel f :=
  Submodule.Quotient.equiv _ _ (monicResidueEquiv hf) (by
    change Submodule.map (monicResidueMap hf) _ = _
    rw [← LinearMap.range_comp, ← monic_traceForm_eq_residueMap_comp hf])

/-- Successive quotienting by `f` and its derivative gives their actual intersection ring. -/
def monicDifferentDoubleQuotientEquiv (f : R[X]) :
    (AdjoinRoot f ⧸ Ideal.span ({AdjoinRoot.mk f f.derivative} : Set (AdjoinRoot f))) ≃ₐ[R]
      MonicDifferentQuotient f := by
  let I : Ideal R[X] := Ideal.span {f}
  let J : Ideal R[X] := Ideal.span {f.derivative}
  have hm : Ideal.span ({AdjoinRoot.mk f f.derivative} : Set (AdjoinRoot f)) =
      Ideal.map (Ideal.Quotient.mk I) J := by
    simp only [J, Ideal.map_span, Set.image_singleton]
    rfl
  have hs : I ⊔ J = Ideal.span ({f, f.derivative} : Set R[X]) := by
    simp only [I, J, ← Ideal.span_union, Set.singleton_union]
  let e : ((R[X] ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J) ≃ₐ[R]
      (R[X] ⧸ (I ⊔ J)) :=
    AlgEquiv.ofRingEquiv (f := DoubleQuot.quotQuotEquivQuotSup I J) (by
      intro r
      exact DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap I J r)
  exact (Ideal.quotientEquivAlgOfEq R hm).trans
    (e.trans (Ideal.quotientEquivAlgOfEq R hs))

/-- The integral trace cokernel is the actual different quotient, with no separability condition. -/
def monicTraceCokernelEquivDifferent {f : R[X]} (hf : f.Monic) :
    MonicTraceCokernel f ≃ₗ[R] MonicDifferentQuotient f :=
  (monicDifferentMulCokernelEquivTrace hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ (range_monicDifferent_mul f)).trans
      ((Submodule.Quotient.restrictScalarsEquiv R _).trans
        (monicDifferentDoubleQuotientEquiv f).toLinearEquiv))

#print axioms monicDifferentMulCokernelEquivTrace
#print axioms monicDifferentDoubleQuotientEquiv
#print axioms monicTraceCokernelEquivDifferent
end GaloisForLFunctions.HTGeometry
