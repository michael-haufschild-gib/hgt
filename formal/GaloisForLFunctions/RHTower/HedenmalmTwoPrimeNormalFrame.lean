import GaloisForLFunctions.RHTower.HedenmalmThetaIntervalTransform
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The two-prime normal frame of the Xi divisor

The centered prime windows transform to `ĉ_n = a_n Ξ_C`.  Because `a_2` and `a_3` have no common
zero, the pair of prime windows retains every zero of `Ξ_C` together with its exact analytic
order: at a zero `ζ` at least one multiplier is nonzero there, and multiplying by a unit does not
move the analytic order.

In the compact reciprocal coordinate `μ = -1/ζ` of the Grushin inverse the normal multiplier
becomes `A_n(μ) = 2 n^{-1/2} μ sin(L_n/(2μ))`, which has an essential singularity at the compact
spectral boundary `μ = 0` yet reproduces `a_n(ζ)` on every root block.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

/-! ### The centered multiplier in closed trigonometric form -/

theorem centeredMultiplier_eq_sin (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplier n z
      = 2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
        * Complex.sin (z * ((Real.log n / 2 : ℝ) : ℂ)) / z := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set w : ℂ := z * ((Real.log n / 2 : ℝ) : ℂ) with hw
  have e1 : Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ) = w * Complex.I := by
    rw [hw]; ring
  have hsin : Complex.exp (w * Complex.I) - Complex.exp (-(w * Complex.I))
      = 2 * Complex.I * Complex.sin w := by
    rw [Complex.sin]
    linear_combination (Complex.exp (w * Complex.I) - Complex.exp (-(w * Complex.I))) * hI2
  rw [centeredMultiplier, e1, hsin]
  field_simp
  ring

/-! ### Analyticity away from the origin -/

theorem analyticAt_centeredMultiplier (n : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    AnalyticAt ℂ (centeredMultiplier n) ζ := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ)) ζ :=
    (analyticAt_const.mul analyticAt_id).mul analyticAt_const
  have hnum : AnalyticAt ℂ (fun z : ℂ => ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
      * (Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))))) ζ :=
    analyticAt_const.mul (hlin.cexp.sub hlin.neg.cexp)
  have hden : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) ζ :=
    analyticAt_const.mul analyticAt_id
  have hne : (fun z : ℂ => Complex.I * z) ζ ≠ 0 := mul_ne_zero Complex.I_ne_zero hζ
  exact hnum.div hden hne

/-! ### The prime windows retain the exact analytic order -/

/-- The normal jet of the centered prime window: the transform side of `ĉ_n = a_n Ξ_C`. -/
def centeredWindowTransform (n : ℕ) (z : ℂ) : ℂ := centeredMultiplier n z * XiC z

/-- **A prime window with a nonvanishing multiplier retains the exact analytic order of `Ξ_C`.**
This is the multiplicity clause `(15)`--`(16)`: all jets below the order vanish, and the first
nonzero jet is `a_n(ζ) Ξ_C^{(m)}(ζ)`. -/
theorem analyticOrderAt_centeredWindowTransform {n : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hne : centeredMultiplier n ζ ≠ 0) :
    analyticOrderAt (centeredWindowTransform n) ζ = analyticOrderAt XiC ζ := by
  have ha : AnalyticAt ℂ (centeredMultiplier n) ζ := analyticAt_centeredMultiplier n hζ
  have hX : AnalyticAt ℂ XiC ζ := XiC_analytic ζ (Set.mem_univ _)
  have hmul : analyticOrderAt (centeredMultiplier n * XiC) ζ
      = analyticOrderAt (centeredMultiplier n) ζ + analyticOrderAt XiC ζ :=
    analyticOrderAt_mul ha hX
  have hzero : analyticOrderAt (centeredMultiplier n) ζ = 0 :=
    (AnalyticAt.analyticOrderAt_eq_zero ha).mpr hne
  have hfun : centeredWindowTransform n = centeredMultiplier n * XiC := rfl
  rw [hfun, hmul, hzero, zero_add]

/-- **Two literal primes frame every normal direction.**  At every point other than the origin at
least one of the two prime windows has a nonvanishing multiplier, hence retains the exact analytic
order of `Ξ_C` there. -/
theorem two_prime_retains_analyticOrder {ζ : ℂ} (hζ : ζ ≠ 0) :
    analyticOrderAt (centeredWindowTransform 2) ζ = analyticOrderAt XiC ζ
      ∨ analyticOrderAt (centeredWindowTransform 3) ζ = analyticOrderAt XiC ζ := by
  by_cases h2 : centeredMultiplier 2 ζ = 0
  · refine Or.inr (analyticOrderAt_centeredWindowTransform hζ ?_)
    intro h3
    exact hζ (no_common_zero_centered_two_three h2 h3)
  · exact Or.inl (analyticOrderAt_centeredWindowTransform hζ h2)

/-- **The normal frame is nowhere zero on the divisor.**  Every zero of `Ξ_C` is a zero of the same
exact order of at least one prime window transform. -/
theorem two_prime_retains_divisor {ζ : ℂ} (hζ : XiC ζ = 0) :
    ζ ≠ 0 ∧ (analyticOrderAt (centeredWindowTransform 2) ζ = analyticOrderAt XiC ζ
      ∨ analyticOrderAt (centeredWindowTransform 3) ζ = analyticOrderAt XiC ζ) := by
  have hz : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    exact XiC_zero_ne hζ
  exact ⟨hz, two_prime_retains_analyticOrder hz⟩

/-! ### The compact reciprocal coordinate -/

/-- The normal multiplier in the compact reciprocal coordinate `μ = -1/ζ` of the Grushin
inverse. -/
def compactNormalMultiplier (n : ℕ) (μ : ℂ) : ℂ := centeredMultiplier n (-μ⁻¹)

/-- **The compact normal multiplier in closed form**, `A_n(μ) = 2 n^{-1/2} μ sin(L_n/(2μ))`.
The sine of a reciprocal argument exhibits the essential singularity at the compact spectral
boundary `μ = 0`. -/
theorem compactNormalMultiplier_eq (n : ℕ) {μ : ℂ} (hμ : μ ≠ 0) :
    compactNormalMultiplier n μ
      = -(2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * μ
        * Complex.sin (μ⁻¹ * ((Real.log n / 2 : ℝ) : ℂ))) := by
  have hne : (-μ⁻¹ : ℂ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hμ)
  rw [compactNormalMultiplier, centeredMultiplier_eq_sin n hne,
    show (-μ⁻¹ : ℂ) * ((Real.log n / 2 : ℝ) : ℂ)
      = -(μ⁻¹ * ((Real.log n / 2 : ℝ) : ℂ)) by ring, Complex.sin_neg]
  field_simp

/-- **The compact multiplier reproduces the normal multiplier on every root block.** -/
theorem compactNormalMultiplier_root (n : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    compactNormalMultiplier n (-ζ⁻¹) = centeredMultiplier n ζ := by
  rw [compactNormalMultiplier]
  congr 1
  rw [inv_neg, inv_inv, neg_neg]

end HedenmalmThetaSource

end

end RHTower
