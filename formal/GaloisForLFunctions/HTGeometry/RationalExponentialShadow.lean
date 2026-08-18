/-
# Rational eigenfunction rigidity and constant-coefficient shadows

No nonzero rational function has a nonzero constant logarithmic derivative: cross-multiplying
`z' = μ z` gives `denom · num' - num · denom' = μ · num · denom`, and the left side has strictly
smaller degree than the right because differentiation drops the degree of a nonzero polynomial.

Consequently a product of factors `D - λ` with all `λ` nonzero has no nonzero rational function in
its kernel, so the *shadow* of a nonzero rational correction under a nonzero-exponent
constant-coefficient annihilator is again nonzero.
-/
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

noncomputable section

open Polynomial

namespace GaloisForLFunctions.RationalShadow

open GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- Cross-multiplied form of an eigenvalue equation for the coordinate derivation. -/
theorem ratFuncCoordinateDerivation_smul_cross (z : RatFunc K) {μ : K}
    (h : ratFuncCoordinateDerivation K z = algebraMap K (RatFunc K) μ * z) :
    z.denom * z.num.derivative - z.num * z.denom.derivative
      = (Polynomial.C μ) * (z.num * z.denom) := by
  have hden : algebraMap K[X] (RatFunc K) z.denom ≠ 0 := by
    intro hzero
    exact RatFunc.denom_ne_zero z
      (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hzero))
  rw [ratFuncCoordinateDerivation_apply] at h
  conv_rhs at h => rw [← RatFunc.num_div_denom z]
  have hmul : (algebraMap K[X] (RatFunc K) z.denom *
        algebraMap K[X] (RatFunc K) z.num.derivative -
      algebraMap K[X] (RatFunc K) z.num *
        algebraMap K[X] (RatFunc K) z.denom.derivative)
      = algebraMap K (RatFunc K) μ *
        (algebraMap K[X] (RatFunc K) z.num * algebraMap K[X] (RatFunc K) z.denom) := by
    field_simp at h
    linear_combination h
  have hCmu : algebraMap K (RatFunc K) μ
      = algebraMap K[X] (RatFunc K) (Polynomial.C μ) := by
    rw [RatFunc.algebraMap_C]
    rfl
  rw [hCmu] at hmul
  exact IsFractionRing.injective K[X] (RatFunc K)
    (by simpa only [map_sub, map_mul] using hmul)

/-- **Rational eigenfunction rigidity.**  No nonzero rational function has a nonzero constant
logarithmic derivative. -/
theorem ratFuncCoordinateDerivation_ne_smul {z : RatFunc K} (hz : z ≠ 0) {μ : K} (hμ : μ ≠ 0) :
    ratFuncCoordinateDerivation K z ≠ algebraMap K (RatFunc K) μ * z := by
  intro h
  have hcross := ratFuncCoordinateDerivation_smul_cross z h
  have hnum : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hdegR : (Polynomial.C μ * (z.num * z.denom)).degree = z.num.degree + z.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_C hμ, zero_add]
  have hsumne : z.num.degree + z.denom.degree ≠ ⊥ := by
    rw [← Polynomial.degree_mul]
    exact Polynomial.degree_ne_bot.mpr (mul_ne_zero hnum hden)
  have hbotlt : (⊥ : WithBot ℕ) < z.num.degree + z.denom.degree :=
    lt_of_le_of_ne bot_le (Ne.symm hsumne)
  have hdeg1 : (z.denom * z.num.derivative).degree < z.num.degree + z.denom.degree := by
    rcases eq_or_ne z.num.derivative 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact hbotlt
    · rw [Polynomial.degree_mul, add_comm]
      exact WithBot.add_lt_add_right (Polynomial.degree_ne_bot.mpr hden)
        (Polynomial.degree_derivative_lt hnum)
  have hdeg2 : (z.num * z.denom.derivative).degree < z.num.degree + z.denom.degree := by
    rcases eq_or_ne z.denom.derivative 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact hbotlt
    · rw [Polynomial.degree_mul]
      exact WithBot.add_lt_add_left (Polynomial.degree_ne_bot.mpr hnum)
        (Polynomial.degree_derivative_lt hden)
  have hlt : (z.denom * z.num.derivative - z.num * z.denom.derivative).degree
      < z.num.degree + z.denom.degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg1 hdeg2)
  rw [hcross, hdegR] at hlt
  exact lt_irrefl _ hlt

end GaloisForLFunctions.RationalShadow

namespace GaloisForLFunctions.RationalShadow

open GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- One constant-coefficient factor `D - λ` acting on rational functions. -/
def shiftedDeriv (lam : K) (z : RatFunc K) : RatFunc K :=
  ratFuncCoordinateDerivation K z - algebraMap K (RatFunc K) lam * z

@[simp]
theorem shiftedDeriv_zero (lam : K) : shiftedDeriv lam (0 : RatFunc K) = 0 := by
  simp [shiftedDeriv]

theorem shiftedDeriv_eq_zero_iff {lam : K} (hlam : lam ≠ 0) {z : RatFunc K} :
    shiftedDeriv lam z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact ratFuncCoordinateDerivation_ne_smul hz hlam (by
      rw [← sub_eq_zero]
      exact h)
  · intro h
    rw [h, shiftedDeriv_zero]

/-- The monic constant-coefficient annihilator attached to a finite list of exponents. -/
def shiftedDerivProd (l : List K) (z : RatFunc K) : RatFunc K :=
  l.foldr shiftedDeriv z

@[simp]
theorem shiftedDerivProd_nil (z : RatFunc K) : shiftedDerivProd [] z = z := rfl

@[simp]
theorem shiftedDerivProd_cons (lam : K) (l : List K) (z : RatFunc K) :
    shiftedDerivProd (lam :: l) z = shiftedDeriv lam (shiftedDerivProd l z) := rfl

/-- **Lemma 1.**  A rational function annihilated by a product of nonzero constant-coefficient
factors is zero; equivalently the rational shadow of a nonzero correction is nonzero. -/
theorem eq_zero_of_shiftedDerivProd_eq_zero {l : List K} (hl : ∀ lam ∈ l, lam ≠ 0)
    {z : RatFunc K} (h : shiftedDerivProd l z = 0) : z = 0 := by
  induction l with
  | nil => simpa using h
  | cons lam l ih =>
      rw [shiftedDerivProd_cons] at h
      have hlam : lam ≠ 0 := hl lam (List.mem_cons_self)
      have hinner : shiftedDerivProd l z = 0 :=
        (shiftedDeriv_eq_zero_iff hlam).mp h
      exact ih (fun a ha => hl a (List.mem_cons_of_mem lam ha)) hinner

/-- **Lemma 1, contrapositive.**  The rational shadow of a nonzero rational correction under a
nonzero-exponent annihilator is nonzero. -/
theorem shiftedDerivProd_ne_zero {l : List K} (hl : ∀ lam ∈ l, lam ≠ 0)
    {z : RatFunc K} (hz : z ≠ 0) : shiftedDerivProd l z ≠ 0 :=
  fun h => hz (eq_zero_of_shiftedDerivProd_eq_zero hl h)

end GaloisForLFunctions.RationalShadow
