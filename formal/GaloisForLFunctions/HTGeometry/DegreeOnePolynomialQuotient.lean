import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Quotients by a degree-one polynomial

For `a b` in a commutative ring `A`, multiplication by a power of `a` turns any element of `A[X]`
into a constant modulo `a * X + b`.  Consequently, for every ring map `psi : A -> F` into a field
with `psi a` nonzero there is an evaluation map `A[X] -> F` sending `X` to the root, its kernel
contains `a * X + b`, and the assignment of that kernel is monotone in the kernel of `psi`.

This turns a chain of primes of `A` avoiding `a` into a chain of primes of `A[X]` containing
`a * X + b`, i.e. a chain on the hypersurface it cuts out.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {A : Type*} [CommRing A]

/-- The generic degree-one polynomial `a X + b`. -/
noncomputable def degreeOnePoly (a b : A) : A[X] := C a * X + C b

theorem degreeOnePoly_mem_span (a b : A) :
    degreeOnePoly a b ∈ Ideal.span {degreeOnePoly a b} := Ideal.subset_span rfl

theorem quotient_mk_C_mul_X (a b : A) :
    (Ideal.Quotient.mk (Ideal.span {degreeOnePoly a b})) (C a * X)
      = (Ideal.Quotient.mk (Ideal.span {degreeOnePoly a b})) (-C b) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    show (C a * X - -C b : A[X]) = degreeOnePoly a b by rw [degreeOnePoly]; ring]
  exact degreeOnePoly_mem_span a b

/-- **Clearing the leading coefficient.**  Modulo a degree-one polynomial `a X + b`, every
polynomial becomes constant after multiplication by a power of `a`. -/
theorem exists_quotient_mk_C_mul_eq (a b : A) :
    ∀ (n : ℕ) (f : A[X]), f.natDegree ≤ n →
      ∃ F : A, (Ideal.Quotient.mk (Ideal.span {degreeOnePoly a b})) (C (a ^ n) * f)
        = (Ideal.Quotient.mk (Ideal.span {degreeOnePoly a b})) (C F) := by
  intro n
  induction n with
  | zero =>
    intro f hf
    refine ⟨f.coeff 0, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hf)]
    simp
  | succ n ih =>
    intro f hf
    obtain ⟨F', hF'⟩ := ih f.divX (by
      have := Polynomial.natDegree_divX_eq_natDegree_tsub_one (p := f)
      omega)
    refine ⟨-(b * F') + a ^ (n + 1) * f.coeff 0, ?_⟩
    have hfd : f = X * f.divX + C (f.coeff 0) := (Polynomial.X_mul_divX_add f).symm
    have key : C (a ^ (n + 1)) * f
        = (C a * X) * (C (a ^ n) * f.divX) + C a * C (a ^ n) * C (f.coeff 0) := by
      rw [show (C (a ^ (n + 1)) : A[X]) = C a * C (a ^ n) by rw [← map_mul, ← pow_succ']]
      conv_lhs => rw [hfd]
      ring
    rw [key, map_add, map_mul, quotient_mk_C_mul_X, hF', ← map_mul, ← map_add]
    congr 1
    rw [pow_succ']
    simp only [map_add, map_neg, map_mul]
    ring

theorem exists_C_mul_sub_C_mem (a b : A) (f : A[X]) :
    ∃ F : A, C (a ^ f.natDegree) * f - C F ∈ Ideal.span {degreeOnePoly a b} := by
  obtain ⟨F, hF⟩ := exists_quotient_mk_C_mul_eq a b f.natDegree f le_rfl
  exact ⟨F, by rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]⟩

section Eval

variable {F : Type*} [Field F]

/-- Evaluation of a polynomial at the root of `a X + b`, pushed into a field along `ψ`. -/
noncomputable def degreeOneEval (ψ : A →+* F) (a b : A) : A[X] →+* F :=
  Polynomial.eval₂RingHom ψ (-(ψ b) / (ψ a))

@[simp] theorem degreeOneEval_C (ψ : A →+* F) (a b : A) (r : A) :
    degreeOneEval ψ a b (C r) = ψ r := by simp [degreeOneEval]

theorem degreeOneEval_degreeOnePoly (ψ : A →+* F) {a b : A} (ha : ψ a ≠ 0) :
    degreeOneEval ψ a b (degreeOnePoly a b) = 0 := by
  simp only [degreeOneEval, degreeOnePoly, coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  field_simp
  ring

theorem span_le_ker_degreeOneEval (ψ : A →+* F) {a b : A} (ha : ψ a ≠ 0) :
    Ideal.span {degreeOnePoly a b} ≤ RingHom.ker (degreeOneEval ψ a b) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact degreeOneEval_degreeOnePoly ψ ha

theorem ker_degreeOneEval_isPrime (ψ : A →+* F) (a b : A) :
    (RingHom.ker (degreeOneEval ψ a b)).IsPrime := RingHom.ker_isPrime _

theorem mem_ker_degreeOneEval_C (ψ : A →+* F) (a b : A) (r : A) :
    (C r : A[X]) ∈ RingHom.ker (degreeOneEval ψ a b) ↔ r ∈ RingHom.ker ψ := by
  simp [RingHom.mem_ker]

/-- **The kernel is monotone in the base kernel.** -/
theorem ker_degreeOneEval_mono {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    {ψ₁ : A →+* F₁} {ψ₂ : A →+* F₂} {a b : A}
    (h1 : ψ₁ a ≠ 0) (h2 : ψ₂ a ≠ 0) (hker : RingHom.ker ψ₁ ≤ RingHom.ker ψ₂) :
    RingHom.ker (degreeOneEval ψ₁ a b) ≤ RingHom.ker (degreeOneEval ψ₂ a b) := by
  intro f hf
  obtain ⟨G, hG⟩ := exists_C_mul_sub_C_mem a b f
  have hG1 : degreeOneEval ψ₁ a b (C (a ^ f.natDegree) * f - C G) = 0 :=
    span_le_ker_degreeOneEval ψ₁ h1 hG
  have hG2 : degreeOneEval ψ₂ a b (C (a ^ f.natDegree) * f - C G) = 0 :=
    span_le_ker_degreeOneEval ψ₂ h2 hG
  rw [map_sub, map_mul, degreeOneEval_C, degreeOneEval_C, map_pow, sub_eq_zero] at hG1 hG2
  have hf1 : degreeOneEval ψ₁ a b f = 0 := hf
  rw [hf1, mul_zero] at hG1
  have hGker : G ∈ RingHom.ker ψ₂ := hker (by simpa [RingHom.mem_ker] using hG1.symm)
  rw [RingHom.mem_ker] at hGker
  rw [hGker] at hG2
  have := mul_eq_zero.mp hG2
  rcases this with h | h
  · exact absurd (pow_eq_zero_iff'.mp h).1 h2
  · exact h

end Eval

end GaloisForLFunctions.HTGeometry
