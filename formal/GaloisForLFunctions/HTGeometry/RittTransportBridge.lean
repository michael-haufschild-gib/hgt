import GaloisForLFunctions.HTGeometry.RationalAffineTransport
import GaloisForLFunctions.HTGeometry.RittAffineTowerDescent

/-!
# The descent's base relation is an affine transport equation

Everything the jet-tower descent can leave on the base has the single shape

`q^I · ρ^J · ψ(a) = a + γ`,

with `q` the multiplier, `ρ` the chain-rule factor and `γ` either zero or one of the explicit
coefficients the tower supplies.  Read on rational functions — `ψ` the substitution by `R`, `ρ` the
derivative `R′` — that is exactly the corpus's affine transport equation

`a(R) · (R′)^J = b · a + c`,  `b = q^{−I}`,  `c = q^{−I}·γ`,

so the whole obstruction layer of Ritt's implication is consumed by
`RationalAffineTransport`: poles of `a` travel along `R` in both directions off the critical set
while `b` stays a unit and `c` stays regular, and a pole on an injective critical-free orbit is
impossible.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] {R : K[X]}

omit [CharZero K] in
/-- **The descent's base relation is an affine transport equation.** -/
theorem isAffineTransport_of_monomial_base_relation
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {q : K} (hq : q ≠ 0) {I J : ℤ} {a γ : RatFunc K}
    (h : (RatFunc.C q) ^ I * (algebraMap K[X] (RatFunc K) (derivative R)) ^ J
        * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
      = a + γ) :
    IsAffineTransport R hR J ((RatFunc.C q) ^ (-I)) ((RatFunc.C q) ^ (-I) * γ) a := by
  have hCq : (RatFunc.C q : RatFunc K) ≠ 0 := by
    simpa using hq
  have hinv : (RatFunc.C q : RatFunc K) ^ (-I) * (RatFunc.C q) ^ I = 1 := by
    rw [← zpow_add₀ hCq]
    simp
  rw [IsAffineTransport]
  calc ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ J
      = ((RatFunc.C q) ^ (-I) * (RatFunc.C q) ^ I)
          * ((algebraMap K[X] (RatFunc K) (derivative R)) ^ J
            * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a) := by
        rw [hinv, one_mul, mul_comm]
    _ = (RatFunc.C q) ^ (-I) * ((RatFunc.C q) ^ I
          * (algebraMap K[X] (RatFunc K) (derivative R)) ^ J
          * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a) := by ring
    _ = (RatFunc.C q) ^ (-I) * (a + γ) := by rw [h]
    _ = (RatFunc.C q) ^ (-I) * a + (RatFunc.C q) ^ (-I) * γ := by ring

omit [CharZero K] in
/-- **The homogeneous case is an invariant differential.** -/
theorem isAffineTransport_of_homogeneous_base_relation
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {q : K} (hq : q ≠ 0) {I J : ℤ} {a : RatFunc K}
    (h : (RatFunc.C q) ^ I * (algebraMap K[X] (RatFunc K) (derivative R)) ^ J
        * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a = a) :
    IsAffineTransport R hR J ((RatFunc.C q) ^ (-I)) 0 a := by
  have h' : (RatFunc.C q) ^ I * (algebraMap K[X] (RatFunc K) (derivative R)) ^ J
      * ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR a = a + 0 := by
    rw [add_zero]; exact h
  have := isAffineTransport_of_monomial_base_relation hq h'
  rwa [mul_zero] at this

end GaloisForLFunctions.HTGeometry
