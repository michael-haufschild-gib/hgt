import GaloisForLFunctions.HTGeometry.NonautonomousFirstOrderTailSymbolLaw
import Mathlib.FieldTheory.RatFunc.Degree

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- Substitution of `a * v` into a polynomial in the vertical first-jet coordinate `v`. -/
def verticalRescalePolynomial {K : Type*} [Field K] (a : K) (p : K[X]) : K[X] :=
  p.comp (C a * X)

@[simp]
theorem verticalRescalePolynomial_coeff {K : Type*} [Field K]
    (a : K) (p : K[X]) (n : ℕ) :
    (verticalRescalePolynomial a p).coeff n = p.coeff n * a ^ n := by
  simp [verticalRescalePolynomial]

theorem verticalRescalePolynomial_ne_zero {K : Type*} [Field K]
    {a : K} (ha : a ≠ 0) {p : K[X]} (hp : p ≠ 0) :
    verticalRescalePolynomial a p ≠ 0 := by
  rw [verticalRescalePolynomial, ne_eq, Polynomial.comp_C_mul_X_eq_zero_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)]
  exact hp

@[simp]
theorem verticalRescalePolynomial_natDegree {K : Type*} [Field K]
    {a : K} (ha : a ≠ 0) (p : K[X]) :
    (verticalRescalePolynomial a p).natDegree = p.natDegree := by
  simp [verticalRescalePolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul ha]

@[simp]
theorem verticalRescalePolynomial_leadingCoeff {K : Type*} [Field K]
    {a : K} (ha : a ≠ 0) (p : K[X]) :
    (verticalRescalePolynomial a p).leadingCoeff =
      p.leadingCoeff * a ^ p.natDegree := by
  rw [verticalRescalePolynomial, Polynomial.leadingCoeff_comp]
  · simp [Polynomial.leadingCoeff_mul]
  · simp [Polynomial.natDegree_C_mul ha]

/-- The Laurent weight at vertical infinity of a polynomial fraction. -/
def verticalLaurentWeight {K : Type*} [Field K] (numerator denominator : K[X]) : ℤ :=
  (numerator.natDegree : ℤ) - denominator.natDegree

/-- The leading Laurent coefficient at vertical infinity of a nonzero polynomial fraction. -/
def verticalLaurentCoefficient {K : Type*} [Field K]
    (numerator denominator : K[X]) : K :=
  numerator.leadingCoeff / denominator.leadingCoeff

/-- Equality after a nonzero vertical rescaling preserves the Laurent weight at infinity. -/
theorem verticalLaurentWeight_eq_of_rescaled_fraction
    {K : Type*} [Field K] {a : K} (ha : a ≠ 0)
    {p₀ q₀ p₁ q₁ : K[X]}
    (hp₀ : p₀ ≠ 0) (hq₀ : q₀ ≠ 0) (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hcross : p₀ * verticalRescalePolynomial a q₁ =
      verticalRescalePolynomial a p₁ * q₀) :
    verticalLaurentWeight p₀ q₀ = verticalLaurentWeight p₁ q₁ := by
  have hdegree := congrArg Polynomial.natDegree hcross
  have hp₁a := verticalRescalePolynomial_ne_zero ha hp₁
  have hq₁a := verticalRescalePolynomial_ne_zero ha hq₁
  rw [Polynomial.natDegree_mul hp₀ hq₁a,
    Polynomial.natDegree_mul hp₁a hq₀,
    verticalRescalePolynomial_natDegree ha,
    verticalRescalePolynomial_natDegree ha] at hdegree
  simp only [verticalLaurentWeight]
  omega

/-- Cross-multiplied leading-symbol transport.  This form is denominator-free and valid for
positive or negative Laurent weight. -/
theorem verticalLaurentCoefficient_cross_of_rescaled_fraction
    {K : Type*} [Field K] {a : K} (ha : a ≠ 0)
    {p₀ q₀ p₁ q₁ : K[X]}
    (hcross : p₀ * verticalRescalePolynomial a q₁ =
      verticalRescalePolynomial a p₁ * q₀) :
    p₀.leadingCoeff * q₁.leadingCoeff * a ^ q₁.natDegree =
      p₁.leadingCoeff * q₀.leadingCoeff * a ^ p₁.natDegree := by
  have hleading := congrArg Polynomial.leadingCoeff hcross
  rw [Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_mul,
    verticalRescalePolynomial_leadingCoeff ha,
    verticalRescalePolynomial_leadingCoeff ha] at hleading
  linear_combination hleading

/-- Exact Laurent-symbol transport under `v ↦ a*v`, in the integer-weight form used by the
first-order tail converse. -/
theorem verticalLaurentCoefficient_eq_zpow_of_rescaled_fraction
    {K : Type*} [Field K] {a : K} (ha : a ≠ 0)
    {p₀ q₀ p₁ q₁ : K[X]}
    (hp₀ : p₀ ≠ 0) (hq₀ : q₀ ≠ 0) (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hcross : p₀ * verticalRescalePolynomial a q₁ =
      verticalRescalePolynomial a p₁ * q₀) :
    verticalLaurentCoefficient p₀ q₀ =
      verticalLaurentCoefficient p₁ q₁ * a ^ verticalLaurentWeight p₁ q₁ := by
  have hlead := verticalLaurentCoefficient_cross_of_rescaled_fraction ha hcross
  have hlcp₀ : p₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp₀
  have hlcq₀ : q₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₀
  have hlcp₁ : p₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp₁
  have hlcq₁ : q₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₁
  rw [verticalLaurentCoefficient, verticalLaurentCoefficient,
    verticalLaurentWeight, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination hlead

/-- Base change in the phase coordinate followed by the vertical first-jet rescaling. -/
def verticalTransportPolynomial
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) (a : K₀) (p : K₁[X]) : K₀[X] :=
  verticalRescalePolynomial a (p.map σ)

@[simp]
theorem verticalTransportPolynomial_natDegree
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) (p : K₁[X]) :
    (verticalTransportPolynomial σ a p).natDegree = p.natDegree := by
  rw [verticalTransportPolynomial, verticalRescalePolynomial_natDegree ha,
    Polynomial.natDegree_map_eq_of_injective σ.injective]

@[simp]
theorem verticalTransportPolynomial_leadingCoeff
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) (p : K₁[X]) :
    (verticalTransportPolynomial σ a p).leadingCoeff =
      σ p.leadingCoeff * a ^ p.natDegree := by
  rw [verticalTransportPolynomial, verticalRescalePolynomial_leadingCoeff ha,
    Polynomial.leadingCoeff_map_of_injective σ.injective,
    Polynomial.natDegree_map_eq_of_injective σ.injective]

theorem verticalTransportPolynomial_ne_zero
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {p : K₁[X]} (hp : p ≠ 0) :
    verticalTransportPolynomial σ a p ≠ 0 :=
  verticalRescalePolynomial_ne_zero ha (by
    simpa using (Polynomial.map_injective σ σ.injective).ne hp)

/-- The vertical Laurent weight is phase-independent under an injective rational base change and
the first-jet rescaling `v ↦ a*v`. -/
theorem verticalLaurentWeight_eq_of_transport_fraction
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {p₀ q₀ : K₀[X]} {p₁ q₁ : K₁[X]}
    (hp₀ : p₀ ≠ 0) (hq₀ : q₀ ≠ 0) (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hcross : p₀ * verticalTransportPolynomial σ a q₁ =
      verticalTransportPolynomial σ a p₁ * q₀) :
    verticalLaurentWeight p₀ q₀ = verticalLaurentWeight p₁ q₁ := by
  have hdegree := congrArg Polynomial.natDegree hcross
  have hp₁a := verticalTransportPolynomial_ne_zero σ ha hp₁
  have hq₁a := verticalTransportPolynomial_ne_zero σ ha hq₁
  rw [Polynomial.natDegree_mul hp₀ hq₁a,
    Polynomial.natDegree_mul hp₁a hq₀,
    verticalTransportPolynomial_natDegree σ ha,
    verticalTransportPolynomial_natDegree σ ha] at hdegree
  simp only [verticalLaurentWeight]
  omega

/-- Exact phase-to-phase leading Laurent-symbol law.  This is the algebraic extraction step in
Theorem A: the source symbol equals the pulled-back terminal symbol times the Jacobian to the
common integer Laurent weight. -/
theorem verticalLaurentCoefficient_eq_zpow_of_transport_fraction
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {p₀ q₀ : K₀[X]} {p₁ q₁ : K₁[X]}
    (hp₀ : p₀ ≠ 0) (hq₀ : q₀ ≠ 0) (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hcross : p₀ * verticalTransportPolynomial σ a q₁ =
      verticalTransportPolynomial σ a p₁ * q₀) :
    verticalLaurentCoefficient p₀ q₀ =
      σ (verticalLaurentCoefficient p₁ q₁) *
        a ^ verticalLaurentWeight p₁ q₁ := by
  have hleading := congrArg Polynomial.leadingCoeff hcross
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
    verticalTransportPolynomial_leadingCoeff σ ha,
    verticalTransportPolynomial_leadingCoeff σ ha] at hleading
  have hlcp₀ : p₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp₀
  have hlcq₀ : q₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₀
  have hlcp₁ : p₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp₁
  have hlcq₁ : q₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₁
  have hσlcp₁ : σ p₁.leadingCoeff ≠ 0 := by simpa using σ.injective.ne hlcp₁
  have hσlcq₁ : σ q₁.leadingCoeff ≠ 0 := by simpa using σ.injective.ne hlcq₁
  rw [verticalLaurentCoefficient, verticalLaurentCoefficient,
    map_div₀, verticalLaurentWeight, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination hleading

/-- If a genuine vertical rational function has Laurent weight zero, subtracting its value at
vertical infinity produces a strictly negative Laurent weight.  This is the `k = 0` escape used
in the first-order tail converse. -/
theorem verticalLaurentWeight_sub_infinityValue_neg
    {K : Type*} [Field K] {p q : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hweight : verticalLaurentWeight p q = 0)
    (hdepends : p - C (verticalLaurentCoefficient p q) * q ≠ 0) :
    verticalLaurentWeight
      (p - C (verticalLaurentCoefficient p q) * q) q < 0 := by
  have hnat : p.natDegree = q.natDegree := by
    have hdegreeInt : (p.natDegree : ℤ) = (q.natDegree : ℤ) := by
      exact sub_eq_zero.mp (by simpa [verticalLaurentWeight] using hweight)
    exact_mod_cast hdegreeInt
  have hlcq : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hc : verticalLaurentCoefficient p q ≠ 0 := by
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) hlcq
  have hscaled : C (verticalLaurentCoefficient p q) * q ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc) hq
  have hdegree : p.degree = (C (verticalLaurentCoefficient p q) * q).degree := by
    rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hscaled,
      Polynomial.natDegree_mul (C_ne_zero.mpr hc) hq,
      Polynomial.natDegree_C, zero_add, hnat]
  have hleading : p.leadingCoeff =
      (C (verticalLaurentCoefficient p q) * q).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      verticalLaurentCoefficient, div_mul_cancel₀ _ hlcq]
  have hdegreeLt := Polynomial.degree_sub_lt hdegree hp hleading
  rw [Polynomial.degree_eq_natDegree hdepends,
    Polynomial.degree_eq_natDegree hp] at hdegreeLt
  have hnatLt : (p - C (verticalLaurentCoefficient p q) * q).natDegree <
      p.natDegree := by exact_mod_cast hdegreeLt
  simp only [verticalLaurentWeight]
  omega

end

end GaloisForLFunctions.HTGeometry
