import GaloisForLFunctions.HTGeometry.QDifferenceLaurentOneVariable
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannHypertranscendence
import GaloisForLFunctions.HTGeometry.EulerOrdinaryDerivationBridge

/-!
# The reciprocal `q`-ladder resolvent is hypertranscendental

The bound-state counting resolvent of the reflectionless `q`-ladder satisfies
`R(x) = 1/(1+x) + β R(βx)`.  Here the multiplier of the homogeneous equation is the dilation
parameter itself, so the twisting element `x` is already rational and the one-variable Laurent
model applies: the increment `-x/(1+x)` has a simple pole at `-1` and no other pole on its
multiplicative orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Polynomial

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem qLadder_increment_eq :
    -((1 / (1 + (RatFunc.X : RatFunc k))) * (RatFunc.X : RatFunc k) ^ 1)
      = toRF (-Polynomial.X)
        / (toRF (Polynomial.X - Polynomial.C (-1 : k)) * toRF 1) := by
  have hX : (RatFunc.X : RatFunc k) = toRF Polynomial.X := RatFunc.algebraMap_X.symm
  have hden : toRF (Polynomial.X - Polynomial.C (-1 : k))
      = 1 + (RatFunc.X : RatFunc k) := by
    rw [hX, ← map_one (algebraMap (Polynomial k) (RatFunc k)),
      show (Polynomial.X - Polynomial.C (-1 : k)) = 1 + Polynomial.X from by
        rw [Polynomial.C_neg, Polynomial.C_1]
        ring]
    exact map_add _ _ _
  rw [hden, show toRF (1 : Polynomial k) = 1 from map_one _, mul_one,
    show toRF (-Polynomial.X : Polynomial k) = -(RatFunc.X : RatFunc k) from by
      rw [hX]; exact map_neg _ _, pow_one]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **The reciprocal `q`-ladder resolvent is hypertranscendental.**  Every Laurent solution of
`R(x) - β R(βx) = 1/(1+x)`, for a dilation parameter that is not a root of unity, is
differentially transcendental over `k(x)`. -/
theorem hypertranscendentalOver_qLadderResolvent [CharZero k] (β : k) (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) (β ^ 1) * innerDilation β hβ R
      = algebraMap (RatFunc k) (LaurentSeries k) (1 / (1 + (RatFunc.X : RatFunc k)))) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) R := by
  letI := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  refine hypertranscendentalOver_of_monomialTwist β hβ hβtor 1 (-1) (by norm_num)
    (-Polynomial.X) 1 (by simp) (by simp) ?_ _ R hR qLadder_increment_eq
  intro n hn
  refine regularAt_simplePoleQuotient _ _ _ _ ?_ (by simp)
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
  intro h
  refine hβtor n hn ?_
  have : (-1 : k) * β ^ n = -1 := by linear_combination h
  have hne : (-1 : k) ≠ 0 := by norm_num
  exact mul_left_cancel₀ hne (by linear_combination this)

/-! ## The general one-pole inhomogeneity -/

theorem qLadder_increment_eq_general (c₀ c₁ : k) :
    -((algebraMap k (RatFunc k) c₀ / (algebraMap k (RatFunc k) c₁ + (RatFunc.X : RatFunc k)))
        * (RatFunc.X : RatFunc k) ^ 1)
      = toRF (-(Polynomial.C c₀) * Polynomial.X)
        / (toRF (Polynomial.X - Polynomial.C (-c₁)) * toRF 1) := by
  have hX : (RatFunc.X : RatFunc k) = toRF Polynomial.X := RatFunc.algebraMap_X.symm
  have hden : toRF (Polynomial.X - Polynomial.C (-c₁))
      = algebraMap k (RatFunc k) c₁ + (RatFunc.X : RatFunc k) := by
    rw [hX, algebraMap_eq_toRF_C,
      show (Polynomial.X - Polynomial.C (-c₁)) = Polynomial.C c₁ + Polynomial.X from by
        rw [Polynomial.C_neg]
        ring]
    exact map_add _ _ _
  rw [hden, show toRF (1 : Polynomial k) = 1 from map_one _, mul_one,
    show toRF (-(Polynomial.C c₀) * Polynomial.X)
        = -(algebraMap k (RatFunc k) c₀) * (RatFunc.X : RatFunc k) from by
      rw [hX, algebraMap_eq_toRF_C,
        show toRF (-(Polynomial.C c₀) * Polynomial.X)
          = toRF (-(Polynomial.C c₀)) * toRF Polynomial.X from map_mul _ _ _,
        show toRF (-(Polynomial.C c₀)) = -toRF (Polynomial.C c₀) from map_neg _ _],
    pow_one]
  ring

set_option maxHeartbeats 1000000 in
/-- **The one-pole `q`-ladder response is hypertranscendental.**  Every Laurent solution of
`R(x) - β R(βx) = c₀/(c₁ + x)` with `c₀, c₁ ≠ 0` and `β` not a root of unity is differentially
transcendental over `k(x)`, both for the Euler derivation and for the ordinary one. -/
theorem hypertranscendentalOver_onePoleQLadder [CharZero k] (β : k) (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (c₀ c₁ : k) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) (β ^ 1) * innerDilation β hβ R
      = algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) c₀ / (algebraMap k (RatFunc k) c₁ + RatFunc.X))) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) R := by
  letI := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  refine hypertranscendentalOver_of_monomialTwist β hβ hβtor 1 (-c₁) (by simpa using hc₁)
    (-(Polynomial.C c₀) * Polynomial.X) 1 (by simp) ?_ ?_ _ R hR
    (qLadder_increment_eq_general c₀ c₁)
  · simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
    exact mul_ne_zero (neg_ne_zero.mpr hc₀) (neg_ne_zero.mpr hc₁)
  · intro n hn
    refine regularAt_simplePoleQuotient _ _ _ _ ?_ (by simp)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    intro h
    refine hβtor n hn ?_
    have h1 : c₁ * β ^ n = c₁ * 1 := by
      rw [mul_one]
      linear_combination -h
    exact mul_left_cancel₀ hc₁ h1

/-- The same conclusion for the ordinary derivation. -/
theorem hypertranscendentalOver_onePoleQLadder_ordinary [CharZero k] (β : k) (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (c₀ c₁ : k) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) (β ^ 1) * innerDilation β hβ R
      = algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) c₀ / (algebraMap k (RatFunc k) c₁ + RatFunc.X))) :
    letI := ratFuncOrdinaryDifferential (k := k)
    letI := innerOrdinaryDifferential (k := k)
    HypertranscendentalOver (RatFunc k) R :=
  hypertranscendentalOver_ordinary_of_euler
    (hypertranscendentalOver_onePoleQLadder β hβ hβtor c₀ c₁ hc₀ hc₁ R hR)

/-- **The solution selected by regularity at the origin.**  The coefficientwise solution inherits
the support of the inhomogeneity, so a one-sided inhomogeneity gives a one-sided solution. -/
theorem coeff_qDifferenceSolution_eq_zero_of_neg (a b : k) (ρ : LaurentSeries k) {n : ℤ}
    (hn : ρ.coeff n = 0) : (qDifferenceSolution a b ρ).coeff n = 0 := by
  rw [coeff_qDifferenceSolution, hn, zero_div]

end

end GaloisForLFunctions.HTGeometry
