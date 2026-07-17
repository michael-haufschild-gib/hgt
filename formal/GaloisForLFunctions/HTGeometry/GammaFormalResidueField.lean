import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Data.Complex.Basic

/-!
# The algebraic-logarithmic residue of the formal digamma field (§3, eq. 19)

The formal Stirling image of the digamma differential field `L` lies in `C(log s)((s⁻¹))`
(the card, §2–§3).  Model that field by `HahnSeries ℤ (RatFunc ℂ)`: the Hahn variable is `s⁻¹`
(exponents in `ℤ`) and each Laurent coefficient is a rational function of `log s` (`RatFunc ℂ`).

Eq. (19) says every nonzero element `A` has unique data `a, b ∈ ℤ` and `c ∈ ℂˣ` — a leading
monomial `c · s^a · (log s)^b`.  Here `a = A.order` (the leading `s⁻¹`-exponent), `b` is the
`log s`-degree of the leading Laurent coefficient, and `c` is that coefficient's leading complex
constant.  The load-bearing fact is `c ≠ 0`, together with the multiplicativity of the residue
(`order` additive, leading Laurent coefficient multiplicative) that makes it a genuine valuation.
-/

open scoped Classical

namespace GaloisForLFunctions

noncomputable section

/-- The leading complex constant of a rational function of `log s`: the ratio of the leading
coefficients of its numerator and denominator. -/
def ratLeadingCoeff (p : RatFunc ℂ) : ℂ :=
  (RatFunc.num p).leadingCoeff / (RatFunc.denom p).leadingCoeff

/-- A nonzero rational function has a nonzero leading constant. -/
theorem ratLeadingCoeff_ne_zero (p : RatFunc ℂ) (hp : p ≠ 0) : ratLeadingCoeff p ≠ 0 := by
  unfold ratLeadingCoeff
  refine div_ne_zero ?_ ?_
  · exact Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hp)
  · exact Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.denom_ne_zero p)

/-- The leading complex constant of rational functions of `log s` is multiplicative. -/
theorem ratLeadingCoeff_mul (p q : RatFunc ℂ) :
    ratLeadingCoeff (p * q) = ratLeadingCoeff p * ratLeadingCoeff q := by
  unfold ratLeadingCoeff
  rw [(RatFunc.monic_denom (p * q)).leadingCoeff,
    (RatFunc.monic_denom p).leadingCoeff,
    (RatFunc.monic_denom q).leadingCoeff]
  simp only [div_one]
  have h := congrArg Polynomial.leadingCoeff (RatFunc.num_denom_mul p q)
  simpa only [Polynomial.leadingCoeff_mul,
    (RatFunc.monic_denom (p * q)).leadingCoeff,
    (RatFunc.monic_denom p).leadingCoeff,
    (RatFunc.monic_denom q).leadingCoeff, mul_one] using h

/-- **eq. (19), leading constant.**  Every nonzero element of the formal digamma field
`C(log s)((s⁻¹)) = HahnSeries ℤ (RatFunc ℂ)` has a nonzero leading complex constant `c ∈ ℂˣ`. -/
theorem formalResidue_const_ne_zero (A : HahnSeries ℤ (RatFunc ℂ)) (hA : A ≠ 0) :
    ratLeadingCoeff A.leadingCoeff ≠ 0 :=
  ratLeadingCoeff_ne_zero _ (HahnSeries.leadingCoeff_ne_zero.mpr hA)

/-- The `s`-exponent `a(A) = order A` is additive: `a(A·B) = a(A) + a(B)`.  This is the `s⁻¹`-adic
valuation of the formal field. -/
theorem formalResidue_order_mul (A B : HahnSeries ℤ (RatFunc ℂ)) (hA : A ≠ 0) (hB : B ≠ 0) :
    (A * B).order = A.order + B.order := HahnSeries.order_mul hA hB

/-- The leading Laurent coefficient — the rational function of `log s` carrying the `(log s)^b`
and `c` data — is multiplicative: `lead(A·B) = lead(A)·lead(B)`. -/
theorem formalResidue_leadingCoeff_mul (A B : HahnSeries ℤ (RatFunc ℂ)) :
    (A * B).leadingCoeff = A.leadingCoeff * B.leadingCoeff := HahnSeries.leadingCoeff_mul A B

/-- The logarithmic exponent `b(A)` is additive on nonzero products. -/
theorem formalResidue_logDegree_mul
    (A B : HahnSeries ℤ (RatFunc ℂ)) (hA : A ≠ 0) (hB : B ≠ 0) :
    (A * B).leadingCoeff.intDegree =
      A.leadingCoeff.intDegree + B.leadingCoeff.intDegree := by
  rw [formalResidue_leadingCoeff_mul, RatFunc.intDegree_mul]
  · exact HahnSeries.leadingCoeff_ne_zero.mpr hA
  · exact HahnSeries.leadingCoeff_ne_zero.mpr hB

/-- The complex leading constant `c(A)` is multiplicative on the formal residue field. -/
theorem formalResidue_leadingConst_mul (A B : HahnSeries ℤ (RatFunc ℂ)) :
    ratLeadingCoeff (A * B).leadingCoeff =
      ratLeadingCoeff A.leadingCoeff * ratLeadingCoeff B.leadingCoeff := by
  rw [formalResidue_leadingCoeff_mul, ratLeadingCoeff_mul]

/-- **eq. (19) packaged.**  Every nonzero `A` in the formal digamma field carries leading data
`(a, b, c)` with `a = A.order`, `b` the `log s`-degree of the leading Laurent coefficient, and
`c ∈ ℂˣ` its leading complex constant. -/
theorem formalResidue_data (A : HahnSeries ℤ (RatFunc ℂ)) (hA : A ≠ 0) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0
      ∧ a = A.order ∧ b = A.leadingCoeff.intDegree ∧ c = ratLeadingCoeff A.leadingCoeff :=
  ⟨A.order, A.leadingCoeff.intDegree, ratLeadingCoeff A.leadingCoeff,
    formalResidue_const_ne_zero A hA, rfl, rfl, rfl⟩

end

end GaloisForLFunctions
