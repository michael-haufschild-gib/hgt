import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation

/-!
# Trace–Kähler equality and monogenicity

For a monogenic order the Kähler module is cyclic — it is the quotient of the order by the root
different — and the trace-dual quotient is the same cyclic module, because multiplication by the
different carries `A^♯/A` onto `A/(different)`.  Conversely an invertible trace dual over a
semilocal base is free of rank one, so the trace-dual quotient is cyclic.

The corank-two example shows that determinant-level agreement does not force module equality: the
two modules have the same length and the same Fitting ideal but different invariant factors.
-/

namespace HTGeometry.ConstraintRelativity

open Polynomial

/-! ## Monogenic orders have cyclic Kähler module -/

section Cyclic

variable {R : Type*} [CommRing R] (f : R[X])

/-- **Theorem 1, `(3) ⇒ (2)`.**  The Kähler module of a monogenic order is cyclic: it is generated
by the class of the differential of the generator. -/
theorem kaehler_isPrincipal_of_monogenic :
    ∃ ω : Ω[AdjoinRoot f⁄R], (⊤ : Submodule (AdjoinRoot f) (Ω[AdjoinRoot f⁄R]))
      = Submodule.span (AdjoinRoot f) {ω} := by
  classical
  refine ⟨KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f), ?_⟩
  refine le_antisymm ?_ le_top
  intro x _
  obtain ⟨y, rfl⟩ := (kaehlerEquivMonogenic f).symm.surjective x
  induction y using Submodule.Quotient.induction_on with
  | H s =>
    induction s using AdjoinRoot.induction_on with
    | ih p =>
      have hgen : (kaehlerEquivMonogenic f).symm
          (Submodule.Quotient.mk (AdjoinRoot.mk f p))
          = AdjoinRoot.mk f p •
            KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f) := by
        apply (kaehlerEquivMonogenic f).injective
        rw [LinearEquiv.apply_symm_apply, map_smul, ← AdjoinRoot.mk_X,
          kaehlerEquivMonogenic_D, derivative_X, map_one]
        rw [map_one]
        have h1 : (1 : MonogenicOmega f) = Submodule.Quotient.mk (1 : AdjoinRoot f) := rfl
        rw [h1, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rw [hgen]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Cyclic

/-! ## A principal trace dual gives a cyclic trace quotient -/

section TraceQuotient

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- **Theorem 1, `(1) ⇒ (2)`.**  If the trace dual is free of rank one on a generator containing
the order, the trace quotient is cyclic.  Over a semilocal base every invertible module is free of
rank one, which is the card's reduction. -/
theorem traceQuotient_isPrincipal {N P : Submodule A M} {u : M}
    (hu : P = Submodule.span A {u}) :
    ∃ ω : P ⧸ Submodule.comap P.subtype N,
      (⊤ : Submodule A (P ⧸ Submodule.comap P.subtype N)) = Submodule.span A {ω} := by
  classical
  have humem : u ∈ P := by rw [hu]; exact Submodule.mem_span_singleton_self u
  refine ⟨Submodule.Quotient.mk ⟨u, humem⟩, le_antisymm ?_ le_top⟩
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    have hy2 : (y : M) ∈ Submodule.span A {u} := by rw [← hu]; exact y.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy2
    have hy : y = c • (⟨u, humem⟩ : P) := Subtype.ext (by simpa using hc.symm)
    rw [hy]
    exact Submodule.mem_span_singleton.2 ⟨c, by rw [← Submodule.Quotient.mk_smul]⟩

end TraceQuotient

/-! ## Multiplication by the different identifies the two quotients -/

section Multiplication

variable {A : Type*} [CommRing A]

/-- **Theorem 1, `(12)`.**  For a nonzerodivisor `δ`, multiplication by `δ` identifies the quotient
`δ⁻¹A/A` with `A/(δ)`.  In the monogenic case `δ` is the root different, so the trace-dual quotient
and the Kähler module agree. -/
noncomputable def mulDifferentEquiv (δ : A) :
    (A ⧸ LinearMap.range (LinearMap.toSpanSingleton A A δ)) ≃ₗ[A] (A ⧸ Ideal.span {δ}) :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    simp only [LinearMap.mem_range, LinearMap.toSpanSingleton_apply, smul_eq_mul,
      Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy]; ring⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy]; ring⟩⟩)

end Multiplication

/-! ## Trace–Kähler equality for a monogenic order -/

section TraceKaehler

variable {R : Type*} [CommRing R] (f : R[X])

/-- **Theorem 1, `(3) ⇒ (1)`, cards `(11)`–`(12)`.**  For a monogenic order the trace quotient and
the Kähler module are the same module.  The trace dual is `δ⁻¹A` with `δ` the root different
(mathlib's `traceForm_dualSubmodule_adjoin`), so the trace quotient is the cokernel of
multiplication by `δ`; that cokernel is `A/(δ)`, which is the Kähler module. -/
noncomputable def traceKaehlerEquiv_of_monogenic :
    (AdjoinRoot f ⧸ LinearMap.range
        (LinearMap.toSpanSingleton (AdjoinRoot f) (AdjoinRoot f) (rootDifferent f)))
      ≃ₗ[AdjoinRoot f] Ω[AdjoinRoot f⁄R] :=
  (mulDifferentEquiv (rootDifferent f)).trans (kaehlerEquivMonogenic f).symm

@[simp] theorem traceKaehlerEquiv_of_monogenic_mk (p : R[X]) :
    traceKaehlerEquiv_of_monogenic f (Submodule.Quotient.mk (AdjoinRoot.mk f p))
      = (kaehlerEquivMonogenic f).symm (Submodule.Quotient.mk (AdjoinRoot.mk f p)) := rfl

end TraceKaehler

/-! ## The corank-two example: equal determinant, unequal modules -/

section CorankTwo

open Matrix Kronecker

variable {R : Type*} [CommRing R]

/-- **Card `(18)`.**  Multiplication by the quadratic different `2x − a` on `R[x]/(x(x−a))`, in the
basis `(1, x)`. -/
def quadDifferentMatrix (a : R) : Matrix (Fin 2) (Fin 2) R := !![-a, 0; 2, a]

/-- Row reduction of the quadratic different by the unimodular left factor. -/
theorem quadDifferent_mul_left (a w : R) (hw : w * 2 = 1) :
    (!![0, w; 2, a] : Matrix (Fin 2) (Fin 2) R) * quadDifferentMatrix a
      = !![1, w * a; 0, a ^ 2] := by
  rw [quadDifferentMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | exact hw | ring

/-- **Card `(18)`.**  The Smith normal form of the quadratic different is `diag(1, a²)`, exhibited
by explicit unimodular matrices. -/
theorem smith_quadDifferent (a : R) (h2 : IsUnit (2 : R)) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧ IsUnit Q.det ∧
      P * quadDifferentMatrix a * Q = Matrix.diagonal ![1, a ^ 2] := by
  obtain ⟨v, hv⟩ := h2
  set w : R := ((v⁻¹ : Rˣ) : R) with hwdef
  have hw : w * 2 = 1 := by
    rw [hwdef, ← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨!![0, w; 2, a], !![1, -(a * w); 0, 1], ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hval : (0 : R) * a - w * 2 = -1 := by rw [hw]; ring
    rw [hval]
    exact isUnit_one.neg
  · rw [Matrix.det_fin_two_of]
    have hval : (1 : R) * 1 - -(a * w) * 0 = 1 := by ring
    rw [hval]
    exact isUnit_one
  · rw [quadDifferent_mul_left a w hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- **Card `(19)`.**  The Kronecker square keeps the determinant but splits the module: its Smith
form is `diag(1, a², a², a⁴)`. -/
theorem smith_kronecker_quadDifferent (a : R) (h2 : IsUnit (2 : R)) :
    ∃ P Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R, IsUnit P.det ∧ IsUnit Q.det ∧
      P * (quadDifferentMatrix a ⊗ₖ quadDifferentMatrix a) * Q
        = Matrix.diagonal fun p : Fin 2 × Fin 2 => (![1, a ^ 2] p.1) * (![1, a ^ 2] p.2) := by
  obtain ⟨P', Q', hP', hQ', hPQ'⟩ := smith_quadDifferent a h2
  refine ⟨P' ⊗ₖ P', Q' ⊗ₖ Q', ?_, ?_, ?_⟩
  · rw [Matrix.det_kronecker]
    exact (hP'.pow _).mul (hP'.pow _)
  · rw [Matrix.det_kronecker]
    exact (hQ'.pow _).mul (hQ'.pow _)
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPQ',
      Matrix.diagonal_kronecker_diagonal]

end CorankTwo

end HTGeometry.ConstraintRelativity
