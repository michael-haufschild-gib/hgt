import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The slice theorem for a locally nilpotent derivation

If `D` is a locally nilpotent derivation of a commutative `ℚ`-algebra `B` and some `s ∈ B` has
`D s = 1` (a *slice*), then

```text
B = (ker D)[s],      s transcendental over ker D,
```

so `B` is a polynomial ring in one variable over the ring of constants.  Surjectivity is the
Taylor-type induction `b ↦ b - (Dᴺ b) sᴺ / N!`, which lowers the nilpotency order; injectivity
follows from `Dᵈ (sⁱ) = 0` for `i < d` and `Dᵈ (sᵈ) = d!`.

This is the algebraic engine of the multivariable simple connectedness of affine space: for a
finite étale algebra over `R[w]`, the lift of `d/dw` is locally nilpotent, so the algebra is
constant in `w`, and the induction on the number of variables closes.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {B : Type*} [CommRing B] [Algebra ℚ B] (D : Derivation ℚ B B) {s : B}

/-- The kernel of a derivation is a subalgebra. -/
def derivationKernel : Subalgebra ℚ B where
  carrier := {b | D b = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := by simp [Set.mem_setOf_eq]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  zero_mem' := by simp [Set.mem_setOf_eq]
  algebraMap_mem' := by
    intro r
    simp [Set.mem_setOf_eq]

theorem mem_derivationKernel {b : B} : b ∈ derivationKernel D ↔ D b = 0 := Iff.rfl

variable (hs : D s = 1)

include hs in
theorem iterate_deriv_pow (i k : ℕ) :
    (⇑D)^[k] (s ^ i) = (Nat.descFactorial i k) • s ^ (i - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_nsmul, D.leibniz_pow, hs, smul_eq_mul, mul_one]
      have h1 : i - k - 1 = i - (k + 1) := by omega
      rw [Nat.descFactorial_succ, h1, Nat.mul_comm, mul_smul]


theorem iterate_deriv_kernel_mul {c : B} (hc : D c = 0) (k : ℕ) (x : B) :
    (⇑D)^[k] (c * x) = c * (⇑D)^[k] x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [← ih (D x)]
      congr 1
      rw [D.leibniz, hc, smul_zero, add_zero, smul_eq_mul]

theorem iterate_deriv_sub (k : ℕ) (x y : B) :
    (⇑D)^[k] (x - y) = (⇑D)^[k] x - (⇑D)^[k] y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_sub, ih]

variable (hs : D s = 1)

include hs in
theorem exists_polynomial_of_iterate_eq_zero :
    ∀ (N : ℕ) (b : B), (⇑D)^[N] b = 0 →
      ∃ p : Polynomial (derivationKernel D), Polynomial.aeval s p = b := by
  intro N
  induction N with
  | zero => intro b hb; exact ⟨0, by simpa using hb.symm⟩
  | succ N ih =>
      intro b hb
      set c : B := (⇑D)^[N] b with hc
      have hstep : (⇑D)^[N + 1] b = D ((⇑D)^[N] b) := Function.iterate_succ_apply' _ _ _
      have hck : D c = 0 := by rw [hc, ← hstep]; exact hb
      set r : ℚ := ((Nat.factorial N : ℚ))⁻¹ with hr
      set c' : B := r • c with hc'
      have hc'k : c' ∈ derivationKernel D := by
        rw [hc', mem_derivationKernel, Derivation.map_smul, hck, smul_zero]
      have hfac : ((Nat.factorial N : ℕ) • (1 : B)) = ((Nat.factorial N : ℚ)) • (1 : B) := by
        rw [← Nat.cast_smul_eq_nsmul ℚ]
      have hrne : ((Nat.factorial N : ℚ)) ≠ 0 := by
        exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
      have hkey : (⇑D)^[N] (c' * s ^ N) = c' * ((Nat.factorial N : ℕ) • (1 : B)) := by
        rw [iterate_deriv_kernel_mul D hc'k, iterate_deriv_pow D hs N N,
          Nat.descFactorial_self]
        simp
      have hcc : c' * ((Nat.factorial N : ℕ) • (1 : B)) = c := by
        rw [hfac, mul_smul_comm, mul_one, hc', hr, smul_smul, mul_inv_cancel₀ hrne, one_smul]
      have hb' : (⇑D)^[N] (b - c' * s ^ N) = 0 := by
        rw [iterate_deriv_sub D N, hkey, hcc, ← hc, sub_self]
      obtain ⟨p, hp⟩ := ih _ hb'
      refine ⟨p + Polynomial.C ⟨c', hc'k⟩ * Polynomial.X ^ N, ?_⟩
      rw [map_add, hp, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      show (b - c' * s ^ N) + c' * s ^ N = b
      rw [sub_add_cancel]


theorem iterate_deriv_sum {ι : Type*} (k : ℕ) (t : Finset ι) (f : ι → B) :
    (⇑D)^[k] (∑ i ∈ t, f i) = ∑ i ∈ t, (⇑D)^[k] (f i) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, map_sum]
      exact ih (fun i => D (f i))

include hs in
theorem aeval_slice_injective :
    Function.Injective (Polynomial.aeval s : Polynomial (derivationKernel D) → B) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hpne
  set d : ℕ := p.natDegree with hd
  have hexp : Polynomial.aeval s p = ∑ i ∈ Finset.range (d + 1), (p.coeff i) • s ^ i :=
    Polynomial.aeval_eq_sum_range s
  have hterm : ∀ i ∈ Finset.range (d + 1),
      (⇑D)^[d] ((p.coeff i) • s ^ i) =
        if i = d then ((Nat.factorial d : ℕ) • (1 : B)) * ((p.coeff d : B)) else 0 := by
    intro i hi
    rw [Algebra.smul_def]
    have hck : D ((algebraMap (derivationKernel D) B) (p.coeff i)) = 0 := (p.coeff i).2
    rw [iterate_deriv_kernel_mul D hck, iterate_deriv_pow D hs i d]
    rcases eq_or_ne i d with rfl | hne
    · rw [if_pos rfl, Nat.descFactorial_self]
      simp [mul_comm]
    · rw [if_neg hne]
      have hlt : i < d := by
        have := Finset.mem_range.mp hi
        omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
      simp
  have hzero : (⇑D)^[d] (Polynomial.aeval s p) = 0 := by rw [hp]; simp
  rw [hexp, iterate_deriv_sum D d, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.range (d + 1)) d] at hzero
  rw [if_pos (Finset.self_mem_range_succ d)] at hzero
  have hfacne : ((Nat.factorial d : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hcz : ((p.coeff d : B)) = 0 := by
    have hfac : ((Nat.factorial d : ℕ) • (1 : B)) = ((Nat.factorial d : ℚ)) • (1 : B) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ]
    rw [hfac, smul_mul_assoc, one_mul, smul_eq_zero] at hzero
    rcases hzero with h | h
    · exact absurd h hfacne
    · exact h
  have : p.coeff d = 0 := Subtype.ext hcz
  exact hpne (Polynomial.leadingCoeff_eq_zero.mp this)


/-- **The slice theorem for a locally nilpotent derivation.**  If `D` is a locally nilpotent
derivation of a `ℚ`-algebra and `D s = 1`, then `B` is the polynomial ring over `ker D` in `s`. -/
theorem bijective_aeval_of_locallyNilpotent (hs : D s = 1)
    (hnil : ∀ b : B, ∃ N, (⇑D)^[N] b = 0) :
    Function.Bijective (Polynomial.aeval s : Polynomial (derivationKernel D) → B) :=
  ⟨aeval_slice_injective D hs, fun b => by
    obtain ⟨N, hN⟩ := hnil b
    exact exists_polynomial_of_iterate_eq_zero D hs N b hN⟩

/-- The resulting isomorphism `(ker D)[X] ≃ₐ B`. -/
noncomputable def sliceAlgEquiv (hs : D s = 1) (hnil : ∀ b : B, ∃ N, (⇑D)^[N] b = 0) :
    Polynomial (derivationKernel D) ≃ₐ[derivationKernel D] B :=
  AlgEquiv.ofBijective (Polynomial.aeval s) (bijective_aeval_of_locallyNilpotent D hs hnil)

@[simp] theorem sliceAlgEquiv_X (hs : D s = 1) (hnil : ∀ b : B, ∃ N, (⇑D)^[N] b = 0) :
    sliceAlgEquiv D hs hnil Polynomial.X = s := by
  simp [sliceAlgEquiv]

end GaloisForLFunctions.HTGeometry
