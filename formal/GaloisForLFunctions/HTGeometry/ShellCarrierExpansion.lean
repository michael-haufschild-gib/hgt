import GaloisForLFunctions.HTGeometry.ShellExpansionBounds

/-!
# The carrier distortion as a single truncated expansion

Every factor of the shell form of the carrier distortion -- the two fixed shell powers, the
exponential of the root defect, and each term of the Poincaré sum -- is bounded and expandable on a
disc in the reciprocal spectral parameter.  Closing the product under the calculus of bounded
expansions therefore gives the distortion a single polynomial approximant of any prescribed order,
with degree below that order.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

/-- The carrier distortion read as a function of the reciprocal spectral parameter. -/
def shellCarrierProfile (a x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)
    * (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-1 / 2 : ℝ)) : ℂ)
    * (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-1 / 4 : ℝ)) : ℂ)
    * Complex.exp (-((a : ℂ) * shellDefect x w))
    * ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k * w ^ k
        * (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ)

theorem carrierDistortion_eq_shellCarrierProfile (a : ℝ) {t : ℂ} (htre : 0 < t.re)
    (htim : 0 < t.im) (x : ℝ) (hsmall : Real.sqrt 2 * x ^ 2 < t.re * ‖t‖) (n : ℕ) :
    carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n
      = shellCarrierProfile a x n t⁻¹ :=
  carrierDistortion_eq_shellPowers htre htim x hsmall n

section Factors

/-- A shell power with a nonpositive exponent is a bounded expansion. -/
theorem bddPolyExpansion_shellPow {α : ℝ} (hα : α ≤ 0) {x r : ℝ} (hr0 : 0 ≤ r)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (m : ℕ) :
    BddPolyExpansion r m (fun w : ℂ => (1 + (x : ℂ) ^ 2 * w ^ 2) ^ ((α : ℝ) : ℂ)) := by
  have hC : (0 : ℝ) ≤ cbinomAbsCoeff α m * |x| ^ (2 * m) :=
    mul_nonneg (cbinomAbsCoeff_nonneg α m) (pow_nonneg (abs_nonneg x) _)
  exact ⟨cbinomAbsCoeff α m * |x| ^ (2 * m) * r ^ (2 * m - m), (2 : ℝ) ^ (-α),
    shellBinomPoly α m x, mul_nonneg hC (pow_nonneg hr0 _),
    fun w hw => norm_shellPow_le hα hxr hw,
    (hasPolyExpansion_shellBinom hα m x hxr).mono hC (by omega)⟩

/-- A monomial is a bounded expansion of every order. -/
theorem bddPolyExpansion_monomial (r : ℝ) (m k : ℕ) :
    BddPolyExpansion r m (fun w : ℂ => w ^ k) :=
  ⟨0, r ^ k, Polynomial.X ^ k, le_rfl, fun w hw => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg w) hw k,
    hasPolyExpansion_monomial r m k⟩

/-- The exponential of the scaled root defect is a bounded expansion once the disc is small enough
that the defect stays below one half. -/
theorem bddPolyExpansion_defectExp {a x : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr0 : 0 ≤ r)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hdef : a * shellDefectRate x * r ≤ 1 / 2) (m : ℕ) :
    BddPolyExpansion r m (fun w : ℂ => Complex.exp (-((a : ℂ) * shellDefect x w))) := by
  have hrate := shellDefectRate_nonneg x
  have hna : ‖(-(a : ℂ))‖ = a := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hCD0 : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)) :=
    mul_nonneg (cbinomAbsCoeff_nonneg _ _) (pow_nonneg (abs_nonneg x) _)
  have hE0 := ((hasPolyExpansion_shellDefect m x hxr).const_mul (-(a : ℂ))).mono
    (mul_nonneg (norm_nonneg _) hCD0) (by omega : m ≤ 2 * m + 1)
  have hCE0 : (0 : ℝ) ≤ ‖(-(a : ℂ))‖ * (cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)))
      * r ^ (2 * m + 1 - m) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hCD0) (pow_nonneg hr0 _)
  have hEr0 : (0 : ℝ) ≤ ‖(-(a : ℂ))‖ * (cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)))
      * r ^ (2 * m + 1 - m) * r ^ m := mul_nonneg hCE0 (pow_nonneg hr0 m)
  have hEb : ∀ w : ℂ, ‖w‖ ≤ r → ‖(-(a : ℂ)) * shellDefect x w‖ ≤ a * shellDefectRate x * r := by
    intro w hw
    rw [norm_mul, hna]
    have h1 := norm_shellDefect_le hxr hw
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h1),
      mul_nonneg (mul_nonneg ha hrate) (sub_nonneg.mpr hw)]
  have hdef0 : (0 : ℝ) ≤ a * shellDefectRate x * r := by
    have h := hEb 0 (by simpa using hr0)
    exact le_trans (norm_nonneg _) h
  have hsmall : ∀ w : ℂ, ‖w‖ ≤ r → ‖(-(a : ℂ)) * shellDefect x w‖
      ≤ a * shellDefectRate x * ‖w‖ := by
    intro w hw
    rw [norm_mul, hna]
    have h1 := norm_shellDefect_le hxr hw
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h1)]
  have hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖(-(a : ℂ)) * shellDefect x w‖
      ≤ 1 + a * shellDefectRate x * r
        + ‖(-(a : ℂ))‖ * (cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)))
          * r ^ (2 * m + 1 - m) * r ^ m := by
    intro w hw
    have := hEb w hw
    linarith
  have hPb : ∀ w : ℂ, ‖w‖ ≤ r →
      ‖(Polynomial.C (-(a : ℂ)) * shellDefectPoly m x).eval w‖
      ≤ 1 + a * shellDefectRate x * r
        + ‖(-(a : ℂ))‖ * (cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)))
          * r ^ (2 * m + 1 - m) * r ^ m := by
    intro w hw
    have := hE0.norm_poly_le hEb hCE0 hw
    linarith
  have htiny : ∀ w : ℂ, ‖w‖ ≤ r →
      ‖(-(a : ℂ)) * shellDefect x w‖ / ((m : ℝ) + 1) ≤ 1 / 2 := by
    intro w hw
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hEb w hw
    have h2 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith
  have hres := bddPolyExpansion_cexp hE0 hfb hPb (by linarith) hCE0
    (mul_nonneg ha hrate) hsmall htiny
  have hfun : (fun w : ℂ => Complex.exp ((-(a : ℂ)) * shellDefect x w))
      = fun w : ℂ => Complex.exp (-((a : ℂ) * shellDefect x w)) := by
    funext w
    rw [neg_mul]
  rwa [hfun] at hres

end Factors

section Assembly

/-- **The carrier profile is a bounded expansion of every order.** -/
theorem bddPolyExpansion_shellCarrierProfile {a x : ℝ} (ha : 0 ≤ a) (n m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hdef : a * shellDefectRate x * r ≤ 1 / 2) :
    BddPolyExpansion r m (shellCarrierProfile a x n) := by
  have hA : BddPolyExpansion r m
      (fun w : ℂ => (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-1 / 2 : ℝ)) : ℂ)) :=
    bddPolyExpansion_shellPow (by norm_num) hr0 hxr m
  have hB : BddPolyExpansion r m
      (fun w : ℂ => (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-1 / 4 : ℝ)) : ℂ)) :=
    bddPolyExpansion_shellPow (by norm_num) hr0 hxr m
  have hExp := bddPolyExpansion_defectExp (a := a) (x := x) ha hr0 hxr hdef m
  have hS : BddPolyExpansion r m (fun w : ℂ =>
      ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k * w ^ k
        * (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ)) := by
    refine BddPolyExpansion.finsetSum _ fun k _ => ?_
    have hk0 : (-(k : ℝ) / 2 : ℝ) ≤ 0 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hqk : BddPolyExpansion r m
        (fun w : ℂ => (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ)) :=
      bddPolyExpansion_shellPow hk0 hr0 hxr m
    exact ((bddPolyExpansion_monomial r m k).const_mul
      (((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k)).mul hr0 hqk
  exact ((((hA.const_mul ((Real.sqrt 2 : ℝ) : ℂ)).mul hr0 hB).mul hr0 hExp).mul hr0 hS)

/-- **The carrier distortion has a polynomial approximant of every order.**

The approximant has degree below the order, and the error is the corresponding power of the
reciprocal spectral parameter. -/
theorem exists_poly_approx_carrierDistortion {a x : ℝ} (ha : 0 ≤ a) (n m : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) :
    ∃ C : ℝ, ∃ P : Polynomial ℂ, 0 ≤ C ∧ (∀ j, m ≤ j → P.coeff j = 0) ∧
      ∀ t : ℂ, 0 < t.re → 0 < t.im → Real.sqrt 2 * x ^ 2 < t.re * ‖t‖ → ‖t⁻¹‖ ≤ r →
        ‖carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n - P.eval t⁻¹‖
          ≤ C * ‖t⁻¹‖ ^ m := by
  obtain ⟨C, P, hC, hcoeff, hP⟩ :=
    (bddPolyExpansion_shellCarrierProfile ha n m hr0 hxr hdef).trunc hr1
  refine ⟨C, P, hC, hcoeff, fun t htre htim hsm hw => ?_⟩
  rw [carrierDistortion_eq_shellCarrierProfile a htre htim x hsm n]
  exact hP t⁻¹ hw

end Assembly

end

end GaloisForLFunctions.HTGeometry
