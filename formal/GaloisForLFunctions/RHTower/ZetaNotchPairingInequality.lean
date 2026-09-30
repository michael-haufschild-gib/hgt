import GaloisForLFunctions.RHTower.ZetaNotchSmoothTest
import GaloisForLFunctions.RHTower.SmoothNumberLogSeries

/-!
# The pairing inequality for the `|ζ|²` notch

Let `P` be a finite set of primes and `v : ℕ → ℝ` supported on `P`-smooth numbers with
`|v(n)| ≤ 2 log n + A`. If the null potential `−ψ_v` is positive definite, then for every window
scale `L > 0` and every smooth weight `q ≥ 0` (`sum_mul_re_weightedMoment_nonpos`)

`Σ_n v(n) Re ∫ ω(t) q(t) |ζ(½+it)|² n^{−it} dt ≤ 0`.

This is Bochner's measure `σ` of `−ψ_v` paired with the notch test `g = ω q w^{−1}` on the frequency
line: `Ξ² g = ω q |ζ|²` and `∫ g(t/2π) dσ ≥ 0`. The logarithmic series over `P`-smooth numbers
(`summable_smoothLogSeries`) supplies the summability of `|v(n)|(1 + log n)^{−(2#P+2)}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open FourierTransform
open scoped ComplexConjugate

namespace RHTower.ZetaNotch

open RHTower.SmoothNumbers

/-- The `q`-weighted twisted moment `M_q(y) = ∫ ω(t) q(t) |ζ(½+it)|² e^{−iyt} dt`. -/
def weightedMoment (L : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t, notchWindow L t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)

theorem weightedMoment_neg (L : ℝ) (q : ℝ → ℝ) (y : ℝ) :
    weightedMoment L q (-y) = conj (weightedMoment L q y) := by
  unfold weightedMoment
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, notchWindow, blockWindowC, Complex.conj_ofReal, zetaSq_eq_normSq]
  rw [← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal]

/-- The logarithmic summability of a deviation supported on smooth numbers. -/
theorem summable_abs_mul_inv_log_pow {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ}
    (hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) :
    Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ (2 * P.card + 2))⁻¹ := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_smoothLogSeries hP).mul_left (2 + A))
  by_cases hv : v n = 0
  · rw [hv, abs_zero, zero_mul]
    positivity
  · have hs := hsupp n hv
    rw [if_pos hs]
    have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h1 : 1 ≤ 1 + Real.log n := by linarith
    have hpos : 0 < (1 + Real.log n) ^ (2 * P.card) := by positivity
    have hv' : |v n| ≤ (2 + A) * (1 + Real.log n) := by nlinarith [ha n]
    calc |v n| * ((1 + Real.log n) ^ (2 * P.card + 2))⁻¹
        ≤ (2 + A) * (1 + Real.log n) * ((1 + Real.log n) ^ (2 * P.card + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hv' (by positivity)
      _ = (2 + A) * (((1 + Real.log n) ^ (2 * P.card))⁻¹ * ((1 + Real.log n))⁻¹) := by
          rw [pow_add, mul_inv]
          field_simp
      _ ≤ (2 + A) * ((1 + Real.log n) ^ (2 * P.card))⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          calc ((1 + Real.log n) ^ (2 * P.card))⁻¹ * (1 + Real.log n)⁻¹
              ≤ ((1 + Real.log n) ^ (2 * P.card))⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ h1) (by positivity)
            _ = ((1 + Real.log n) ^ (2 * P.card))⁻¹ := mul_one _

/-- **The pairing inequality**, for any deviation with log-summable coefficients. -/
theorem sum_mul_re_weightedMoment_nonpos_of_summable {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {J : ℕ} (hJ : 2 ≤ J)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    {L : ℝ} (hL : 0 < L) {q : ℝ → ℝ} (hq0 : ∀ t, 0 ≤ q t)
    (hqs : ContDiff ℝ J fun t => (q t : ℂ)) :
    ∑' n : ℕ, v n * (weightedMoment L q (Real.log n)).re ≤ 0 := by
  have hcont := RHTower.WeilRegular.continuous_nullPotential_of_log hv0 hA ha
  obtain ⟨σ, hσf, hσ⟩ := exists_charFun_eq_of_positiveDefinite hPD
    (Complex.continuous_ofReal.comp hcont.neg)
  set Q : ℝ → ℂ := fun t => (q t : ℂ) with hQ
  set g : ℝ → ℂ := notchTestFreq L Q with hg
  have hgs : ContDiff ℝ J g := contDiff_notchTestFreq hqs
  have hgsupp : HasCompactSupport g := hasCompactSupport_notchTestFreq hL
  have hgc : Continuous g := hgs.continuous
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgsupp
  obtain ⟨Cg, hdec⟩ := exists_norm_fourier_mul_pow_le hgs hgsupp
  have hpair := RHTower.WeilRegular.nullPotential_pairing hv0 hA ha hJ hs σ hσ hgc hgi hdec
  set c : ℝ := 1 / (2 * Real.pi) with hc
  have hc0 : 0 < c := by positivity
  have hF : ∀ y, 𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) y =
      (c : ℂ) * weightedMoment L q y := by
    intro y
    rw [hg, fourier_riemannXi_sq_mul_notchTestFreq]
    rfl
  have hterm : ∀ n : ℕ, (v n : ℂ) *
      (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ((2 * c * (v n * (weightedMoment L q (Real.log n)).re) : ℝ) : ℂ) := by
    intro n
    rw [hF, hF, weightedMoment_neg, ← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum] at hpair
  have hre := congrArg Complex.re hpair
  rw [Complex.ofReal_re, Complex.neg_re] at hre
  have hGeq : (fun t => g (t / (2 * Real.pi))) = notchTest L Q := by
    funext t
    rw [hg, notchTestFreq_div_two_pi]
  have hGc : Continuous (notchTest L Q) :=
    ((contDiff_notchWindow L).continuous.mul hqs.continuous).mul
      (contDiff_gammaWeightInv 0).continuous
  have hGsupp : HasCompactSupport (notchTest L Q) :=
    HasCompactSupport.intro isCompact_Icc fun t ht => by
      unfold notchTest
      rw [notchWindow_eq_zero hL ht, zero_mul, zero_mul]
  have hGi : Integrable (notchTest L Q) σ := hGc.integrable_of_hasCompactSupport hGsupp
  have hnn : 0 ≤ (∫ t, g (t / (2 * Real.pi)) ∂σ).re := by
    have h := integral_re hGi
    simp only [RCLike.re_to_complex] at h
    rw [hGeq, ← h]
    exact integral_nonneg fun t => notchTest_re_nonneg hq0 t
  rw [tsum_mul_left] at hre
  have h2c : 0 < 2 * c := by positivity
  by_contra hpos
  push Not at hpos
  have : 0 < 2 * c * ∑' n : ℕ, v n * (weightedMoment L q (Real.log n)).re := mul_pos h2c hpos
  linarith

/-- **The pairing inequality** for a deviation supported on `P`-smooth numbers. -/
theorem sum_mul_re_weightedMoment_nonpos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ}
    (hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    {L : ℝ} (hL : 0 < L) {q : ℝ → ℝ} (hq0 : ∀ t, 0 ≤ q t)
    (hqs : ContDiff ℝ (2 * P.card + 2) fun t => (q t : ℂ)) :
    ∑' n : ℕ, v n * (weightedMoment L q (Real.log n)).re ≤ 0 := by
  have hv0 : v 0 = 0 := by
    by_contra h
    have := (hsupp 0 h).1
    omega
  exact sum_mul_re_weightedMoment_nonpos_of_summable hv0 hA ha (J := 2 * P.card + 2) (by omega)
    (summable_abs_mul_inv_log_pow hP hsupp hA ha) hPD hL hq0 (by exact_mod_cast hqs)

end RHTower.ZetaNotch
