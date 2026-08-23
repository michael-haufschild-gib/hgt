import GaloisForLFunctions.RHTower.DeningerDynSysPerfectionDense
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.NumberTheory.Basic

/-!
# The tilting comparison is injective

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.13
(`t1110`), the injectivity half of `lim_{()^p} A ≅ A♭`.

Reduction modulo `p` induces a map `lim_{()^p} A → lim_{()^p} (A / p)`.  It is injective as soon as
`A` is `p`-adically separated: if two elements have the same reduction then their `n`-th
coefficients differ by a multiple of `p`, and since the `n`-th coefficient is the `p^k`-th power of
the `(n+k)`-th one, the classical congruence `p ∣ a - b ⟹ p^{k+1} ∣ a^{p^k} - b^{p^k}` makes the
difference lie in every power of `(p)`.
-/

namespace RHTower

open Perfection

variable {A : Type*} [CommRing A] {p : ℕ}

/-- The reduction map on perfections. -/
noncomputable def deningerTiltComparison :
    Perfection A p →* Perfection (A ⧸ Ideal.span {(p : A)}) p :=
  mapMonoidHom p (Ideal.Quotient.mk (Ideal.span {(p : A)})).toMonoidHom

@[simp] theorem deningerTiltComparison_coeff (x : Perfection A p) (n : ℕ) :
    coeffMonoidHom _ p n (deningerTiltComparison x)
      = Ideal.Quotient.mk (Ideal.span {(p : A)}) (coeffMonoidHom A p n x) := rfl

/-- **Deninger, Proposition 14.13 (`t1110`), injectivity.**  For a `p`-adically separated ring the
tilting comparison `lim_{()^p} A → lim_{()^p} (A / p)` is injective. -/
theorem deningerTiltComparison_injective [IsHausdorff (Ideal.span {(p : A)}) A] :
    Function.Injective (deningerTiltComparison (A := A) (p := p)) := by
  intro x y hxy
  have hdvd : ∀ m : ℕ, (p : A) ∣ coeffMonoidHom A p m x - coeffMonoidHom A p m y := by
    intro m
    have h := congrArg (fun z => coeffMonoidHom _ p m z) hxy
    simp only [deningerTiltComparison_coeff] at h
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq.1 h
  refine Subtype.ext (funext fun n => ?_)
  show coeffMonoidHom A p n x = coeffMonoidHom A p n y
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})]
  intro k
  rw [SModEq.sub_mem]
  have hmem : coeffMonoidHom A p n x - coeffMonoidHom A p n y
      ∈ (Ideal.span {(p : A)}) ^ k := by
    rcases k with _ | j
    · simp
    · have hx := deningerPerfection_coeff_pow x n j
      have hy := deningerPerfection_coeff_pow y n j
      have hd := dvd_sub_pow_of_dvd_sub (hdvd (n + j)) j
      rw [hx, hy] at hd
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hd
  simpa using hmem

end RHTower
