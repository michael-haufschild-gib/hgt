import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayersAtAnOddPrimeHaveSmoothedMainTerms

/-!
# The cubic classes keep their main terms at large primes

For an odd primary prime `q` (`ρ = |q|`, `N = ρ²`) the smoothed main term of the unit layer on the cubic class
`χ_q(gen A) = c` is `⅓(α₁ + c̄α_χ + c̄²α_χ̄)·e^{4/9}Res S₁·X^{2/3}` (`classUnitLayer_smoothed_main_term`) with

* `α₁ = K/A`, `|A − K| = ρ^{2/3}`, `|K| = ρ^{8/3}`, so `|α₁ − 1| ≤ ρ^{2/3}/(ρ^{8/3} − ρ^{2/3}) = 1/(N − 1)`;
* `|α_χ| = 2ρ^{5/3}/(ρ² + 1) = 2N^{5/6}/(N + 1)` (a Gauss-sum phase);
* `|α_χ̄| = ρ²/|A| ≤ N^{2/3}/(N − 1)`.

With `t = ρ^{1/3}` the three deviations sum to `(1 + t⁴)/(t⁶ − 1) + 2t⁵/(t⁶ + 1) < 1` once `t ≥ 3`. Hence for
`N(q) ≥ 729` **no cubic residue class modulo `q` loses the main term** (`classMainTerm_ne_zero`): the bias
`X^{2/3}` of the squared cubic Gauss sums is present on every cubic class, with weight `⅓(1 + O(N^{−1/6}))` of the
untwisted one.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `|A(s) − K(s)| = ρ^{2 − Re s}`. -/
theorem norm_conjFactor_sub_oddK (h2 : (2 : P.Res) ≠ 0) (s : ℂ) :
    ‖P.conjFactor s - P.oddK s‖ = ‖ringComplex P.p‖ ^ (2 - s.re) := by
  have hρ0 := P.norm_pos
  have hA : P.conjFactor s - P.oddK s =
      P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹ := by
    rw [show P.conjFactor s = P.oddK s +
      P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹ from rfl]
    ring
  rw [hA, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, P.norm_normC, P.norm_fracJacobi h2,
    Complex.norm_cpow_eq_rpow_re_of_pos hρ0, Complex.neg_re, P.norm_eulerGauss, P.norm_gaussAt_one,
    Real.rpow_sub hρ0, Real.rpow_two, Real.rpow_neg hρ0.le]
  field_simp

/-- `|A(s)| ≥ ρ^{2Re s} − ρ^{2 − Re s}`. -/
theorem norm_conjFactor_ge (h2 : (2 : P.Res) ≠ 0) (s : ℂ) :
    ‖ringComplex P.p‖ ^ (2 * s.re) - ‖ringComplex P.p‖ ^ (2 - s.re) ≤ ‖P.conjFactor s‖ := by
  have h := norm_sub_norm_le (P.oddK s) (P.oddK s - P.conjFactor s)
  rw [sub_sub_cancel, P.norm_oddK h2, norm_sub_rev, P.norm_conjFactor_sub_oddK h2] at h
  exact h

theorem norm_unitWeight_four_thirds :
    ‖P.unitWeight (4 / 3)‖ = 2 * ‖ringComplex P.p‖ ^ (5 / 3 : ℝ) / (‖ringComplex P.p‖ ^ 2 + 1) := by
  have hρ0 := P.norm_pos
  have h9 : IsCoprime (9 : O) P.p := by
    have := P.isCoprime_three.pow_left (m := 2)
    norm_num at this
    exact this
  have hu : ‖star (ringComplex (symbol 9 P.p)) * normalizedCubicUnitGauss P.p‖ = 1 := by
    rw [norm_mul, norm_star, symbol_norm_one 9 P.p P.primary h9,
      normalizedCubicUnitGauss_prime_norm P.p P.prime P.primary, mul_one]
  have hd : ‖(‖ringComplex P.p‖ : ℂ) ^ 2 + 1‖ = ‖ringComplex P.p‖ ^ 2 + 1 := by
    rw [show (‖ringComplex P.p‖ : ℂ) ^ 2 + 1 = ((‖ringComplex P.p‖ ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [P.unitWeight_four_thirds, norm_mul, hu, mul_one, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hρ0, hd]
  norm_num

theorem norm_conjAlpha_four_thirds (h2 : (2 : P.Res) ≠ 0) :
    ‖P.conjAlpha (4 / 3)‖ = ‖ringComplex P.p‖ ^ 2 / ‖P.conjFactor (4 / 3)‖ := by
  have hρ0 := P.norm_pos
  rw [P.conjAlpha_four_thirds, norm_div, norm_mul, norm_mul, P.norm_normC, P.norm_fracJacobi h2,
    P.norm_gaussAt_one]
  field_simp

theorem norm_principalAlpha_sub_one (h2 : (2 : P.Res) ≠ 0) :
    ‖P.principalAlpha (4 / 3) - 1‖ = ‖ringComplex P.p‖ ^ (2 / 3 : ℝ) / ‖P.conjFactor (4 / 3)‖ := by
  have hA0 := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  have hK : P.principalAlpha (4 / 3) - 1 = -(P.conjFactor (4 / 3) - P.oddK (4 / 3)) / P.conjFactor (4 / 3) := by
    rw [P.principalAlpha_four_thirds]
    field_simp
    ring
  rw [hK, norm_div, norm_neg, P.norm_conjFactor_sub_oddK h2]
  norm_num

/-- **The class weights do not vanish at large primes.** For `N(q) ≥ 729` and every cube root of unity `c`,
`α₁ + c̄α_χ + c̄²α_χ̄ ≠ 0`. -/
theorem classWeight_ne_zero (h2 : (2 : P.Res) ≠ 0) (hρ : 27 ≤ ‖ringComplex P.p‖) (c : ℂ) (hc : c ^ 3 = 1) :
    P.principalAlpha (4 / 3) + c⁻¹ * P.unitWeight (4 / 3) + c⁻¹ ^ 2 * P.conjAlpha (4 / 3) ≠ 0 := by
  set ρ := ‖ringComplex P.p‖ with hρdef
  have hρ0 : 0 < ρ := P.norm_pos
  have hc1 : ‖c‖ = 1 := by
    have h := congrArg norm hc
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by norm_num)).mp h
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc1, inv_one]
  set t : ℝ := ρ ^ (1 / 3 : ℝ) with ht
  have ht3 : 3 ≤ t := by
    have h := Real.rpow_le_rpow (by norm_num) hρ (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hpow : ∀ n : ℕ, ρ ^ ((n : ℝ) / 3) = t ^ n := fun n => by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
    ring
  have e23 : ρ ^ (2 / 3 : ℝ) = t ^ 2 := by simpa using hpow 2
  have e53 : ρ ^ (5 / 3 : ℝ) = t ^ 5 := by simpa using hpow 5
  have e83 : ρ ^ (2 * (4 / 3 : ℂ).re) = t ^ 8 := by
    rw [show 2 * (4 / 3 : ℂ).re = ((8 : ℕ) : ℝ) / 3 by norm_num]
    exact hpow 8
  have e2' : ρ ^ (2 - (4 / 3 : ℂ).re) = t ^ 2 := by
    rw [show 2 - (4 / 3 : ℂ).re = ((2 : ℕ) : ℝ) / 3 by norm_num]
    exact hpow 2
  have e6 : ρ ^ 2 = t ^ 6 := by
    have h := hpow 6
    rw [show ((6 : ℕ) : ℝ) / 3 = (2 : ℝ) by norm_num, Real.rpow_two] at h
    exact h
  have hA := P.norm_conjFactor_ge h2 (4 / 3)
  rw [← hρdef, e83, e2'] at hA
  have h6 : 1 < t ^ 6 := one_lt_pow₀ (by linarith) (by norm_num)
  have hgap : 0 < t ^ 8 - t ^ 2 := by
    rw [show t ^ 8 - t ^ 2 = t ^ 2 * (t ^ 6 - 1) by ring]
    exact mul_pos (by positivity) (by linarith)
  have hApos : 0 < ‖P.conjFactor (4 / 3)‖ := lt_of_lt_of_le hgap hA
  have h1 := P.norm_principalAlpha_sub_one h2
  have hχ := P.norm_unitWeight_four_thirds
  have hχc := P.norm_conjAlpha_four_thirds h2
  rw [← hρdef, e23] at h1
  rw [← hρdef, e53, e6] at hχ
  rw [← hρdef, e6] at hχc
  -- the three deviations from `1`
  have b1 : ‖P.principalAlpha (4 / 3) - 1‖ ≤ 1 / (t ^ 6 - 1) := by
    rw [h1, div_le_div_iff₀ hApos (by nlinarith [pow_le_pow_left₀ (by norm_num) ht3 6])]
    nlinarith [hA]
  have b3 : ‖P.conjAlpha (4 / 3)‖ ≤ t ^ 4 / (t ^ 6 - 1) := by
    rw [hχc, div_le_div_iff₀ hApos (by nlinarith [pow_le_pow_left₀ (by norm_num) ht3 6])]
    nlinarith [hA, pow_nonneg (by linarith : (0 : ℝ) ≤ t) 4]
  have h729 : 729 ≤ t ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) ht3 6
    norm_num at this
    exact this
  have h6p : 0 < t ^ 6 - 1 := by linarith
  have ba : 1 / (t ^ 6 - 1) ≤ 1 / 728 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have bb : 2 * t ^ 5 / (t ^ 6 + 1) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : 0 ≤ t ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ht3 h5]
  have bc : t ^ 4 / (t ^ 6 - 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ h6p]
    have h4 : 0 ≤ t ^ 4 := by positivity
    have ht9 : 9 ≤ t ^ 2 := by nlinarith
    have h81 : 81 ≤ t ^ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht9 h4]
  have hsum : 1 / (t ^ 6 - 1) + 2 * t ^ 5 / (t ^ 6 + 1) + t ^ 4 / (t ^ 6 - 1) < 1 := by linarith
  intro h0
  have hrel : (1 : ℂ) = -((P.principalAlpha (4 / 3) - 1) + c⁻¹ * P.unitWeight (4 / 3) +
      c⁻¹ ^ 2 * P.conjAlpha (4 / 3)) := by linear_combination h0
  have hn := congrArg norm hrel
  rw [norm_one, norm_neg] at hn
  have hle : ‖(P.principalAlpha (4 / 3) - 1) + c⁻¹ * P.unitWeight (4 / 3) + c⁻¹ ^ 2 * P.conjAlpha (4 / 3)‖ ≤
      1 / (t ^ 6 - 1) + 2 * t ^ 5 / (t ^ 6 + 1) + t ^ 4 / (t ^ 6 - 1) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add b1 ?_)) ?_)
    · rw [norm_mul, hci, one_mul, hχ]
    · rw [norm_mul, norm_pow, hci, one_pow, one_mul]
      exact b3
  linarith

/-- **Every cubic class keeps its main term** at a primary prime of norm at least `729`. -/
theorem classMainTerm_ne_zero (h2 : (2 : P.Res) ≠ 0) (hρ : 27 ≤ ‖ringComplex P.p‖) (c : ℂ) (hc : c ^ 3 = 1) :
    Complex.exp ((2 / 3 : ℂ) ^ 2) *
      (1 / 3 * (P.principalAlpha (4 / 3) + c⁻¹ * P.unitWeight (4 / 3) + c⁻¹ ^ 2 * P.conjAlpha (4 / 3)) *
        untwistedThetaResidue) ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero (by norm_num)
    (P.classWeight_ne_zero h2 hρ c hc)) untwistedThetaResidue_ne_zero)

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
