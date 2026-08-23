import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import GaloisForLFunctions.HTGeometry.SplitFiniteAlgebraDiscriminant

/-!
# Trace and discriminant commute with base change

For an algebra `B` free and finite over `A`, extending scalars along `A → S` carries the trace and
the discriminant along the structure map:

```text
algebra_trace_baseChange   trace_S (S ⊗ B) (1 ⊗ x) = algebraMap A S (trace_A B x)
discr_baseChange           discr_S (b.baseChange S) = algebraMap A S (discr_A b)
discr_mem_iff_discr_quotient_eq_zero
    ** p contains the discriminant  ↔  the fibre discriminant vanishes **
discr_notMem_ker_of_split_fibre, discr_notMem_of_split_fibre
    ** a place whose fibre SPLITS does not divide the discriminant **
```

mathlib carries `LinearMap.trace_baseChange` for the linear trace but neither statement for the
algebra trace or the discriminant.  Both follow at once: multiplication by `1 ⊗ x` **is** the base
change of multiplication by `x`, and the trace matrix in the base-changed basis is the entrywise
image of the trace matrix, whose determinant the structure map carries.

The use is the Dedekind discriminant criterion: reducing the discriminant modulo a prime `p` gives
the discriminant of the fibre `B ⊗ κ(p)`, whose vanishing is degeneracy of the fibre's trace form —
that is, ramification at `p`.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct


/-- **The algebra trace commutes with base change.** -/
theorem algebra_trace_baseChange {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (S : Type*) [CommRing S] [Algebra A S] (x : B) :
    Algebra.trace S (TensorProduct A S B) (1 ⊗ₜ[A] x)
      = algebraMap A S (Algebra.trace A B x) := by
  have hlm : (Algebra.lmul S (TensorProduct A S B)) ((1 : S) ⊗ₜ[A] x)
      = LinearMap.baseChange S (Algebra.lmul A B x) := by
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, Algebra.trace_apply, hlm, LinearMap.trace_baseChange]

/-- **The discriminant commutes with base change.** -/
theorem discr_baseChange {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (S : Type*) [CommRing S] [Algebra A S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) :
    Algebra.discr S ⇑(b.baseChange S) = algebraMap A S (Algebra.discr A ⇑b) := by
  have hmat : Algebra.traceMatrix S ⇑(Module.Basis.baseChange S b)
      = (Algebra.traceMatrix A ⇑b).map (algebraMap A S) := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact algebra_trace_baseChange S _
  rw [Algebra.discr_def, Algebra.discr_def, hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **A prime contains the discriminant exactly when the fibre discriminant vanishes.**  This is the
interface the Dedekind discriminant criterion consumes: over a maximal `p` the fibre is an algebra
over the field `A ⧸ p`, and its discriminant vanishes exactly when its trace form degenerates. -/
theorem discr_mem_iff_discr_quotient_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) (p : Ideal A) :
    Algebra.discr A ⇑b ∈ p ↔
      Algebra.discr (A ⧸ p) ⇑(b.baseChange (A ⧸ p)) = 0 := by
  rw [discr_baseChange (A ⧸ p) b]
  exact (Ideal.Quotient.eq_zero_iff_mem).symm

/-- **A place whose fibre splits does not divide the discriminant.**  Stated with an abstract
residue field rather than the quotient, which keeps the instance search small. -/
theorem discr_notMem_ker_of_split_fibre {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] {n : ℕ}
    (b : Module.Basis (Fin n) A B) (κ : Type*) [Field κ] [Algebra A κ]
    (χ : Fin n → ((TensorProduct A κ B) →ₐ[κ] κ))
    (hsurj : Function.Surjective fun c : (TensorProduct A κ B) => fun i => χ i c) :
    algebraMap A κ (Algebra.discr A ⇑b) ≠ 0 := by
  rw [← discr_baseChange κ b]
  exact discr_ne_zero_of_algHom_family (b.baseChange κ) χ hsurj

/-- **The Dedekind discriminant criterion, split-fibre form.** -/
theorem discr_notMem_of_split_fibre {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] {n : ℕ}
    (b : Module.Basis (Fin n) A B) (κ : Type*) [Field κ] [Algebra A κ] {p : Ideal A}
    (hker : ∀ a : A, algebraMap A κ a = 0 ↔ a ∈ p)
    (χ : Fin n → ((TensorProduct A κ B) →ₐ[κ] κ))
    (hsurj : Function.Surjective fun c : (TensorProduct A κ B) => fun i => χ i c) :
    Algebra.discr A ⇑b ∉ p := fun hmem =>
  discr_notMem_ker_of_split_fibre b κ χ hsurj ((hker _).mpr hmem)

end GaloisForLFunctions.HTGeometry
