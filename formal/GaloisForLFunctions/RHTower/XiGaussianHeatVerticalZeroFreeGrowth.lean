import GaloisForLFunctions.RHTower.XiGaussianHeatPrimeChirpReceiver
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# Unconditional vertical growth of the heat trace and of the prime chirp

On the vertical line `Re τ = a` RH is equivalent to boundedness of the Xi heat trace
`ν(a + ib) = Σ_q exp(-(a+ib) z_q²)` and to the square-root bound for the Gaussian–von Mangoldt chirp
`S(a+ib) = Σ Λ(n) n^{-1/2} exp(-(log n)²/(4(a+ib)))`
(`riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm`).  This module records the best
unconditional bound that the corpus zero-free region gives.

* Without any zero-free region, every term obeys
  `|exp(-τ z²)| ≤ exp(a/4 - a γ² + |b| |γ|) ≤ exp(a/4 + b²/(4a))`.  This is the trivial size, and it
  matches the trivial size of `S`.
* The region `|β - 1/2| ≤ 1/2 - 1/(58 log|γ|)` (`re_le_one_sub_of_zeta_zero` and its reflection)
  removes a factor `exp(-b²/(116 a log(2|b|/a)))`.  The terms that can reach the trivial size sit at
  height `|γ| ≈ |b|/(2a)`, where the region is `1/(58 log)`-wide
  (`norm_xiGaussianHeatTraceC_le_zeroFree`, `norm_gaussianPrimeChirpSum_le_zeroFree`).

The HCF producer asks for `O(1)` and `O(|τ|^{1/2})`.  The unconditional state is the saving
`exp(-c b²/(a log b))` below the trivial `exp(b²/(4a))`.  This is the de la Vallée Poussin analogue
for the chirp.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The corpus zero-free region in spectral coordinates: every copy satisfies
`|Im z| ≤ 1/2 - 1/(58 log |Re z|)`, and `|Re z| ≥ 4`. -/
theorem xiSpectralPoint_im_le_zeroFree (q : XiZeroCopy) :
    4 ≤ |(xiSpectralPoint q).re| ∧
      |(xiSpectralPoint q).im| ≤ 1 / 2 - 1 / 58 / Real.log |(xiSpectralPoint q).re| := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hxi := xi_eq_zero_of_mem_divisor_support q.1
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h] at hstrip; simp at hstrip
  have hzeta : riemannZeta (q.1 : ℂ) = 0 := (xi_eq_zero_iff hstrip.1 hne1).1 hxi
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  have h4 := four_le_abs_im_of_zeta_zero hstrip.1 hstrip.2 hzeta
  have hup := re_le_one_sub_of_zeta_zero hstrip.1 hstrip.2 hzeta
  have hlow := one_div_le_re_of_zeta_zero hstrip.1 hstrip.2 hzeta
  rw [hre, him, abs_neg]
  refine ⟨h4, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- **Termwise zero-free bound.**  For `X = 2|b|/a ≥ 4`, every term of the heat trace at `a + ib` is
at most `(exp(M)(X² + 1/4) + (2/a) e^{a/2}) / ‖z‖²`, where
`M = a/4 + (1 - 1/(29 log X)) b²/(4a)`. -/
theorem norm_xiGaussianHeatTermC_le_zeroFree {a b : ℝ} (ha : 0 < a) (hX : 4 ≤ 2 * |b| / a)
    (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC ((a : ℂ) + b * I) q‖ ≤
      (Real.exp (a / 4 + (1 - 1 / 29 / Real.log (2 * |b| / a)) * (b ^ 2 / (4 * a))) *
          ((2 * |b| / a) ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set X : ℝ := 2 * |b| / a
  obtain ⟨h4, hzf⟩ := xiSpectralPoint_im_le_zeroFree q
  set x := (xiSpectralPoint q).re
  set y := (xiSpectralPoint q).im
  have hN : ‖xiSpectralPoint q‖ ^ (2 : ℕ) = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hy : |y| ≤ 1 / 2 := by
    have : 0 < 1 / 58 / Real.log |x| := by
      have : 0 < Real.log |x| := Real.log_pos (by linarith)
      positivity
    linarith
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
    linarith
  have hx16 : 16 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hNpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  rw [norm_xiGaussianHeatTermC, hN]
  have hre : ((a : ℂ) + b * I).re = a := by simp
  have him : ((a : ℂ) + b * I).im = b := by simp
  have hw_re : (xiSpectralPoint q ^ (2 : ℕ)).re = x ^ 2 - y ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hw_im : (xiSpectralPoint q ^ (2 : ℕ)).im = 2 * x * y := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hre, him, hw_re, hw_im]
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set M : ℝ := a / 4 + (1 - 1 / 29 / Real.log X) * (b ^ 2 / (4 * a))
  have hbxy : b * (2 * x * y) ≤ |b| * |x| * (2 * |y|) := by
    calc b * (2 * x * y) ≤ |b * (2 * x * y)| := le_abs_self _
      _ = |b| * |x| * (2 * |y|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  have hfinal : ∀ E : ℝ, Real.exp E ≤ Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) ∨
      Real.exp E ≤ 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) →
      Real.exp E ≤ (Real.exp M * (X ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
        (1 / (x ^ 2 + y ^ 2)) := by
    intro E h
    have h1 : 0 ≤ Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by positivity
    have h2 : 0 ≤ 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by positivity
    have heq : (Real.exp M * (X ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) * (1 / (x ^ 2 + y ^ 2)) =
        Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) +
          2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by ring
    rw [heq]
    rcases h with h | h <;> linarith
  apply hfinal
  rcases le_or_gt |x| X with hxX | hxX
  · -- the window `|x| ≤ X`: the zero-free region saves `1/(29 log X)`
    left
    have hlogx : Real.log |x| ≤ Real.log X := Real.log_le_log (by linarith) hxX
    have hlogx0 : 0 < Real.log |x| := Real.log_pos (by linarith)
    have hη : 1 / 58 / Real.log X ≤ 1 / 58 / Real.log |x| :=
      div_le_div_of_nonneg_left (by norm_num) hlogx0 hlogx
    set c : ℝ := 1 - 1 / 29 / Real.log X
    have hc0 : 0 ≤ c := by
      have : 1 / 29 / Real.log X ≤ 1 := by
        rw [div_le_one hlogX]
        have : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
        have h4 : (1 : ℝ) / 29 ≤ Real.log 4 := by
          have := Real.add_one_le_exp (1 / 29 : ℝ)
          rw [Real.le_log_iff_exp_le (by norm_num)]
          have : Real.exp (1 / 29) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
          have := Real.exp_one_lt_d9
          linarith
        linarith
      simp only [c]; linarith
    have hc1 : c ≤ 1 := by
      have : 0 ≤ 1 / 29 / Real.log X := by positivity
      simp only [c]; linarith
    have h2y : 2 * |y| ≤ c := by
      have : 2 * |y| ≤ 1 - 2 * (1 / 58 / Real.log |x|) := by linarith
      have h' : 1 - 2 * (1 / 58 / Real.log |x|) ≤ c := by
        simp only [c]
        have : 1 / 29 / Real.log X = 2 * (1 / 58 / Real.log X) := by ring
        rw [this]; linarith
      linarith
    have hE : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) ≤ M := by
      have hbx : |b| * |x| * (2 * |y|) ≤ |b| * |x| * c :=
        mul_le_mul_of_nonneg_left h2y (by positivity)
      have hsq : -a * x ^ 2 + c * |b| * |x| ≤ c ^ 2 * b ^ 2 / (4 * a) := by
        have key : 0 ≤ 4 * a ^ 2 * x ^ 2 - 4 * a * c * |b| * |x| + c ^ 2 * b ^ 2 := by
          have h := sq_nonneg (2 * a * |x| - c * |b|)
          have e : (2 * a * |x| - c * |b|) ^ 2 =
              4 * a ^ 2 * |x| ^ 2 - 4 * a * c * |b| * |x| + c ^ 2 * |b| ^ 2 := by ring
          rw [e, sq_abs, sq_abs] at h
          exact h
        rw [le_div_iff₀ (by positivity)]
        nlinarith [key]
      have hc2 : c ^ 2 * b ^ 2 / (4 * a) ≤ c * (b ^ 2 / (4 * a)) := by
        have : c ^ 2 ≤ c := by nlinarith
        rw [mul_div_assoc, ← mul_div_assoc c]
        have hb : 0 ≤ b ^ 2 / (4 * a) := by positivity
        calc c ^ 2 * (b ^ 2 / (4 * a)) ≤ c * (b ^ 2 / (4 * a)) :=
              mul_le_mul_of_nonneg_right this hb
          _ = c * b ^ 2 / (4 * a) := by ring
      simp only [M]
      nlinarith
    have hR : 1 ≤ (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by
      rw [le_div_iff₀ hNpos, one_mul]
      have : x ^ 2 ≤ X ^ 2 := by
        have := sq_le_sq' (by linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]) hxX
        rwa [sq_abs] at this
      linarith
    calc Real.exp (-(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)))
        ≤ Real.exp M := Real.exp_le_exp.2 hE
      _ ≤ Real.exp M * ((X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2)) :=
          le_mul_of_one_le_right (Real.exp_pos _).le hR
      _ = Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by ring
  · -- the tail `|x| > X`: the Gaussian beats the linear growth
    right
    have hbx : |b| * |x| ≤ a * x ^ 2 / 2 := by
      have : 2 * |b| ≤ a * |x| := by
        have := hxX
        simp only [X] at this
        rw [div_lt_iff₀ ha] at this
        linarith
      have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [abs_nonneg x]
    have hy1 : 2 * |y| ≤ 1 := by linarith
    have hE : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) ≤ a / 2 - a / 2 * (x ^ 2 + y ^ 2) := by
      have h1 : |b| * |x| * (2 * |y|) ≤ |b| * |x| :=
        mul_le_of_le_one_right (by positivity) hy1
      nlinarith
    have hpos : 0 < a / 2 * (x ^ 2 + y ^ 2) := by positivity
    calc Real.exp (-(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)))
        ≤ Real.exp (a / 2 - a / 2 * (x ^ 2 + y ^ 2)) := Real.exp_le_exp.2 hE
      _ = Real.exp (a / 2) * Real.exp (-(a / 2 * (x ^ 2 + y ^ 2))) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (a / 2) * (1 / (a / 2 * (x ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos hpos) (Real.exp_pos _).le
      _ = 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by field_simp

/-- **Unconditional vertical growth of the heat trace.**  For `a > 0` and `|b| ≥ 2a`,
`‖ν(a+ib)‖ ≤ K ((2|b|/a)² + 1/4) exp(a/4 + (1 - 1/(29 log(2|b|/a))) b²/(4a)) + (2K/a) e^{a/2}`,
where `K = Σ_q ‖z_q‖⁻²`.  The trivial bound is the same expression with `1` in place of
`1 - 1/(29 log(2|b|/a))`. -/
theorem norm_xiGaussianHeatTraceC_le_zeroFree {a b : ℝ} (ha : 0 < a) (hb : 2 * a ≤ |b|) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
      (Real.exp (a / 4 + (1 - 1 / 29 / Real.log (2 * |b| / a)) * (b ^ 2 / (4 * a))) *
          ((2 * |b| / a) ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hX : 4 ≤ 2 * |b| / a := by rw [le_div_iff₀ ha]; linarith
  have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
    (Summable.tsum_le_tsum (norm_xiGaussianHeatTermC_le_zeroFree ha hX)
      (summable_norm_xiGaussianHeatTermC hτ) (xiSpectralPoint_inv_sq_summable.mul_left _))

/-- **Unconditional vertical growth of the prime chirp.**  For `a > 0` and `|b| ≥ 2a`,
`‖S(a+ib)‖ ≤ √(‖a+ib‖/π) (A + 2π e^{a/4} + π V(b))`, where `A` is the critical-line archimedean
constant and `V(b)` the zero-free heat-trace bound of `norm_xiGaussianHeatTraceC_le_zeroFree`. -/
theorem norm_gaussianPrimeChirpSum_le_zeroFree {a b : ℝ} (ha : 0 < a) (hb : 2 * a ≤ |b|) :
    ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ ≤
      Real.sqrt ‖(a : ℂ) + b * I‖ / Real.sqrt Real.pi *
        ((∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖) + 2 * Real.pi * Real.exp (a / 4) +
          Real.pi * ((Real.exp (a / 4 + (1 - 1 / 29 / Real.log (2 * |b| / a)) * (b ^ 2 / (4 * a))) *
            ((2 * |b| / a) ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
              ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) := by
  set τ : ℂ := (a : ℂ) + b * I
  have hτre : 0 < τ.re := by simpa [τ] using ha
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτre; simp at hτre
  have hsq : 0 < Real.sqrt ‖τ‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hτ0)
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hne : (Real.pi : ℂ) / τ ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hτ0
  have hfac : ‖gaussianPrimeChirpC τ‖ =
      Real.sqrt Real.pi * (‖gaussianPrimeChirpSum τ‖ / Real.sqrt ‖τ‖) := by
    rw [gaussianPrimeChirpC, norm_mul, Complex.norm_cpow_of_ne_zero hne]
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    have hre2 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [him, hre2, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Real.div_rpow Real.pi_pos.le (norm_nonneg _), ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
    ring
  have hprime : gaussianPrimeChirpC τ =
      gaussianArchCriticalC τ + gaussianArchPoleC τ - (Real.pi : ℂ) * xiGaussianHeatTraceC τ := by
    rw [pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime hτre]; ring
  have hbound : ‖gaussianPrimeChirpC τ‖ ≤
      (∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖) + 2 * Real.pi * Real.exp (a / 4) +
        Real.pi * ((Real.exp (a / 4 + (1 - 1 / 29 / Real.log (2 * |b| / a)) * (b ^ 2 / (4 * a))) *
          ((2 * |b| / a) ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    rw [hprime]
    calc ‖gaussianArchCriticalC τ + gaussianArchPoleC τ - (Real.pi : ℂ) * xiGaussianHeatTraceC τ‖
        ≤ ‖gaussianArchCriticalC τ + gaussianArchPoleC τ‖ +
            ‖(Real.pi : ℂ) * xiGaussianHeatTraceC τ‖ := norm_sub_le _ _
      _ ≤ ‖gaussianArchCriticalC τ‖ + ‖gaussianArchPoleC τ‖ +
            ‖(Real.pi : ℂ) * xiGaussianHeatTraceC τ‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by
          rw [norm_mul, hpi]
          gcongr
          · exact norm_gaussianArchCriticalC_le a b
          · exact (norm_gaussianArchPoleC a b).le
          · exact norm_xiGaussianHeatTraceC_le_zeroFree ha hb
  rw [hfac] at hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ hspi]
  have h := hbound
  rw [mul_comm, ← le_div_iff₀ hspi, div_le_iff₀ hsq] at h
  calc ‖gaussianPrimeChirpSum τ‖ * Real.sqrt Real.pi
      ≤ (_ / Real.sqrt Real.pi * Real.sqrt ‖τ‖) * Real.sqrt Real.pi :=
        mul_le_mul_of_nonneg_right h hspi.le
    _ = _ := by field_simp

end

end RHTower
