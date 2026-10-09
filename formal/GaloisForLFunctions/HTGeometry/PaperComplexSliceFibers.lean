import GaloisForLFunctions.HTGeometry.PaperComplexDerivationSlice
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.QuotientTransport
import Mathlib.RingTheory.Polynomial.Quotient

/-!
A complex slice identifies every level fibre with its constant algebra.
The quotient transport is the proven OpenAI/math construction; the polynomial
splitting is the native slice theorem. The stabilized clock supplies the slice
and termination proofs in the concrete application.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra ℚ B]
  [IsScalarTower ℚ ℂ B]

@[simp] theorem complexSliceAlgEquiv_C (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (x : complexDerivationKernel D) :
    complexSliceAlgEquiv D hs hnil (Polynomial.C x) = (x : B) :=
  Polynomial.aeval_C s x

/-- Every scalar level, including zero, has the same complex constant algebra. -/
def complexSliceFiberEquiv (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ) :
    (B ⧸ Ideal.span {s - algebraMap ℂ B c}) ≃ₐ[ℂ] complexDerivationKernel D :=
  (StableCoordinate.fiberQuotientEquiv (complexSliceAlgEquiv D hs hnil).symm
    s Polynomial.X (by
      apply (complexSliceAlgEquiv D hs hnil).injective
      rw [AlgEquiv.apply_symm_apply, complexSliceAlgEquiv_X]) c).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv
      (algebraMap ℂ (complexDerivationKernel D) c)).restrictScalars ℂ)

theorem complexSliceFiberEquiv_mk (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ) (b : B) :
    complexSliceFiberEquiv D hs hnil c (Ideal.Quotient.mk _ b) =
      ((complexSliceAlgEquiv D hs hnil).symm b).eval
        (algebraMap ℂ (complexDerivationKernel D) c) := rfl

@[simp] theorem complexSliceFiberEquiv_constant (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ)
    (x : complexDerivationKernel D) :
    complexSliceFiberEquiv D hs hnil c (Ideal.Quotient.mk _ (x : B)) = x := by
  rw [complexSliceFiberEquiv_mk]
  have hx : (complexSliceAlgEquiv D hs hnil).symm (x : B) = Polynomial.C x := by
    apply (complexSliceAlgEquiv D hs hnil).injective
    rw [AlgEquiv.apply_symm_apply, complexSliceAlgEquiv_C]
  rw [hx, Polynomial.eval_C]

@[simp] theorem complexSliceFiberEquiv_symm_constant (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ)
    (x : complexDerivationKernel D) :
    (complexSliceFiberEquiv D hs hnil c).symm x = Ideal.Quotient.mk _ (x : B) := by
  apply (complexSliceFiberEquiv D hs hnil c).injective
  rw [AlgEquiv.apply_symm_apply, complexSliceFiberEquiv_constant]

theorem complexSliceFiber_unique_constant (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ)
    (z : B ⧸ Ideal.span {s - algebraMap ℂ B c}) :
    ∃! x : complexDerivationKernel D, Ideal.Quotient.mk _ (x : B) = z := by
  refine ⟨complexSliceFiberEquiv D hs hnil c z, ?_, ?_⟩
  · apply (complexSliceFiberEquiv D hs hnil c).injective
    exact complexSliceFiberEquiv_constant D hs hnil c _
  · intro x hx
    have h := congrArg (complexSliceFiberEquiv D hs hnil c) hx
    simpa only [complexSliceFiberEquiv_constant] using h

theorem complexSliceKernel_mem_fiber_iff_zero (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c : ℂ)
    (x : complexDerivationKernel D) :
    (x : B) ∈ Ideal.span {s - algebraMap ℂ B c} ↔ x = 0 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hx
    have h := congrArg (complexSliceFiberEquiv D hs hnil c) hx
    simpa only [complexSliceFiberEquiv_constant, map_zero] using h
  · intro hx
    subst x
    exact map_zero _

/-- Canonical transport between two levels, fixing every constant of the clock. -/
def complexSliceFiberTransport (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c d : ℂ) :
    (B ⧸ Ideal.span {s - algebraMap ℂ B c}) ≃ₐ[ℂ]
      (B ⧸ Ideal.span {s - algebraMap ℂ B d}) :=
  (complexSliceFiberEquiv D hs hnil c).trans (complexSliceFiberEquiv D hs hnil d).symm

@[simp] theorem complexSliceFiberTransport_constant (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c d : ℂ)
    (x : complexDerivationKernel D) :
    complexSliceFiberTransport D hs hnil c d (Ideal.Quotient.mk _ (x : B)) =
      Ideal.Quotient.mk _ (x : B) := by
  simp only [complexSliceFiberTransport, AlgEquiv.trans_apply,
    complexSliceFiberEquiv_constant, complexSliceFiberEquiv_symm_constant]

theorem complexSliceFiberTransport_cocycle (D : Derivation ℂ B B) {s : B}
    (hs : D s = 1) (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (c d e : ℂ) :
    (complexSliceFiberTransport D hs hnil c d).trans
      (complexSliceFiberTransport D hs hnil d e) =
        complexSliceFiberTransport D hs hnil c e := by
  ext z
  simp only [complexSliceFiberTransport, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

end
end GaloisForLFunctions.HTGeometry
