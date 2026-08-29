import Mathlib.RingTheory.LaurentSeries
import GaloisForLFunctions.HTGeometry.HahnDilation
import GaloisForLFunctions.HTGeometry.MultiplicativeOrbitNonSummability

/-!
# Twisted dilations of a rational function field and their Laurent expansions

A *twisted dilation* of `K(X)` moves the coordinate by `X ↦ q X` and simultaneously moves the
coefficients by a ring endomorphism `φ` of `K`.  This is the operator produced on the second
coordinate of a two-variable difference field when the first coordinate is not fixed.

The Laurent expansion at `X = 0` intertwines the twisted dilation with the coefficientwise twist of
`HahnDilation`.  Comparing the coefficient of `X⁰` therefore turns an inhomogeneous twisted
difference equation over `K(X)` whose right-hand side is a constant into the *same* equation one
coordinate lower, over `K` itself.  This is the descent step that reduces a two-variable telescoping
hypothesis to a one-variable one.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative
open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The coefficients of a dilated polynomial. -/
theorem coeff_polyScale (q : K) (p : Polynomial K) (n : ℕ) :
    (polyScale q p).coeff n = q ^ n * p.coeff n := by
  classical
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp only [map_add, Polynomial.coeff_add, h₁, h₂, mul_add]
  | monomial m c =>
      rw [polyScale, Polynomial.aeval_monomial, mul_pow, ← Polynomial.C_pow,
        Polynomial.algebraMap_eq, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
      by_cases h : n = m
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

/-- The twisted polynomial substitution `p ↦ ∑ φ(pₙ) qⁿ Xⁿ`. -/
def polyTwist (φ : K →+* K) (q : K) : Polynomial K →+* Polynomial K :=
  ((polyScale q : Polynomial K →ₐ[K] Polynomial K) : Polynomial K →+* Polynomial K).comp
    (Polynomial.mapRingHom φ)

theorem polyTwist_apply (φ : K →+* K) (q : K) (p : Polynomial K) :
    polyTwist φ q p = polyScale q (p.map φ) := rfl

@[simp]
theorem coeff_polyTwist (φ : K →+* K) (q : K) (p : Polynomial K) (n : ℕ) :
    (polyTwist φ q p).coeff n = q ^ n * φ (p.coeff n) := by
  rw [polyTwist_apply, coeff_polyScale, Polynomial.coeff_map]

theorem polyTwist_injective {φ : K →+* K} (hφ : Function.Injective φ) {q : K} (hq : q ≠ 0) :
    Function.Injective (polyTwist φ q) :=
  (polyScale_injective hq).comp (Polynomial.map_injective φ hφ)

/-- The twisted dilation of the rational function field: `X ↦ q X` together with the coefficient
endomorphism `φ`. -/
def ratFuncTwist (φ : K →+* K) (hφ : Function.Injective φ) (q : K) (hq : q ≠ 0) :
    RatFunc K →+* RatFunc K :=
  RatFunc.mapRingHom (polyTwist φ q)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyTwist_injective hφ hq))

theorem ratFuncTwist_div (φ : K →+* K) (hφ : Function.Injective φ) (q : K) (hq : q ≠ 0)
    (p s : Polynomial K) :
    ratFuncTwist φ hφ q hq (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) s) =
      algebraMap (Polynomial K) (RatFunc K) (polyTwist φ q p) /
        algebraMap (Polynomial K) (RatFunc K) (polyTwist φ q s) :=
  RatFunc.map_apply_div (polyTwist φ q)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyTwist_injective hφ hq)) p s

/-- The dilation character of the Laurent value group. -/
def laurentChar (q : K) (hq : q ≠ 0) : Multiplicative ℤ →* Kˣ :=
  zpowersHom Kˣ (Units.mk0 q hq)

@[simp]
theorem laurentChar_apply (q : K) (hq : q ≠ 0) (n : ℤ) :
    ((laurentChar q hq (ofAdd n) : Kˣ) : K) = q ^ n := by
  simp [laurentChar]

/-- The Laurent coefficients of a polynomial. -/
theorem coeff_ofPowerSeries_polynomial (p : Polynomial K) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ K (p : PowerSeries K)).coeff n
      = if n < 0 then 0 else p.coeff n.natAbs := by
  rw [PowerSeries.coeff_coe]
  by_cases h : n < 0
  · simp [h]
  · simp [h, Polynomial.coeff_coe]

/-- The Laurent expansion intertwines the twisted dilation of `K[X]` with the coefficientwise
twist of `K⸨X⸩`. -/
theorem ofPowerSeries_polyTwist (φ : K →+* K) (q : K) (hq : q ≠ 0) (p : Polynomial K) :
    HahnSeries.ofPowerSeries ℤ K ((polyTwist φ q p : Polynomial K) : PowerSeries K)
      = hahnTwistHom φ (laurentChar q hq)
        (HahnSeries.ofPowerSeries ℤ K (p : PowerSeries K)) := by
  ext n
  rw [hahnTwistHom_apply, coeff_hahnTwist, laurentChar_apply,
    coeff_ofPowerSeries_polynomial, coeff_ofPowerSeries_polynomial]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h, coeff_polyTwist]
    congr 1
    rw [← zpow_natCast q n.natAbs, Int.natAbs_of_nonneg (not_lt.mp h)]

/-- The Laurent expansion intertwines the twisted dilation with the coefficientwise twist. -/
theorem algebraMap_ratFuncTwist (φ : K →+* K) (hφ : Function.Injective φ) (q : K) (hq : q ≠ 0)
    (f : RatFunc K) :
    algebraMap (RatFunc K) (LaurentSeries K) (ratFuncTwist φ hφ q hq f)
      = hahnTwistHom φ (laurentChar q hq) (algebraMap (RatFunc K) (LaurentSeries K) f) := by
  refine RatFunc.induction_on (P := fun f =>
    algebraMap (RatFunc K) (LaurentSeries K) (ratFuncTwist φ hφ q hq f)
      = hahnTwistHom φ (laurentChar q hq) (algebraMap (RatFunc K) (LaurentSeries K) f)) f ?_
  intro p s _
  have hpoly : ∀ t : Polynomial K,
      algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) t)
        = HahnSeries.ofPowerSeries ℤ K (t : PowerSeries K) := fun t => (RatFunc.coe_coe t).symm
  rw [ratFuncTwist_div, map_div₀, map_div₀, map_div₀, hpoly, hpoly, hpoly, hpoly,
    ofPowerSeries_polyTwist φ q hq, ofPowerSeries_polyTwist φ q hq]

/-- The Laurent expansion of a constant is the constant. -/
theorem algebraMap_const_laurentSeries (x : K) :
    algebraMap (RatFunc K) (LaurentSeries K) (algebraMap K (RatFunc K) x)
      = HahnSeries.single 0 x := by
  have hconstRat : algebraMap K (RatFunc K) x
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C x) := by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq]
  have hcoe : algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C x))
      = HahnSeries.ofPowerSeries ℤ K ((Polynomial.C x : Polynomial K) : PowerSeries K) :=
    (RatFunc.coe_coe _).symm
  rw [hconstRat, hcoe]
  ext n
  rw [coeff_ofPowerSeries_polynomial, HahnSeries.coeff_single]
  by_cases h0 : n = 0
  · subst h0; simp
  · rw [if_neg h0]
    by_cases h : n < 0
    · simp [h]
    · have hn : n.natAbs ≠ 0 := by omega
      simp [h, Polynomial.coeff_C, hn]

/-- **Descent of a twisted coboundary.**  If a constant of `K` is a twisted dilation coboundary in
`K(X)`, it is already a twisted coboundary in `K`: take the `X⁰` coefficient of the Laurent
expansion. -/
theorem exists_twistedCoboundary_of_ratFuncTwist (φ : K →+* K) (hφ : Function.Injective φ)
    (q : K) (hq : q ≠ 0) (γ P : K) (m : RatFunc K)
    (heq : algebraMap K (RatFunc K) γ * ratFuncTwist φ hφ q hq m - m
      = algebraMap K (RatFunc K) P) :
    ∃ m₀ : K, γ * φ m₀ - m₀ = P := by
  have hconst := algebraMap_const_laurentSeries (K := K)
  have h := congrArg (algebraMap (RatFunc K) (LaurentSeries K)) heq
  rw [map_sub, map_mul, hconst, hconst, algebraMap_ratFuncTwist] at h
  refine ⟨(algebraMap (RatFunc K) (LaurentSeries K) m).coeff 0, ?_⟩
  have h0 := congrArg (fun x : LaurentSeries K => x.coeff 0) h
  simp only [HahnSeries.coeff_sub, hahnTwistHom_apply, HahnSeries.coeff_single] at h0
  rw [show ((HahnSeries.single (0 : ℤ) γ) * hahnTwist φ (laurentChar q hq)
      (algebraMap (RatFunc K) (LaurentSeries K) m)).coeff 0
      = γ * (hahnTwist φ (laurentChar q hq)
        (algebraMap (RatFunc K) (LaurentSeries K) m)).coeff 0 from by
    rw [mul_comm, HahnSeries.coeff_mul_single_zero, mul_comm]] at h0
  simpa using h0

end

end GaloisForLFunctions.HTGeometry
