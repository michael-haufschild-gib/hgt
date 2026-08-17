import GaloisForLFunctions.RHTower.XiMassCausticNullJet
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound
import GaloisForLFunctions.HTGeometry.PolynomialSpectralWeight

/-!
# The jet-modified analytic test

`g_{N,τ}(z) = P_N(ω(z)) e^{-τ ω(z)}` is the source-side receiver of the caustic-null jet hierarchy.
On the real axis the jet multiplier collapses to the real polynomial `(x² + 4a⁴)^{2N}`, so the
modified test obeys the same exponential strip bound as the unmodified one with one extra polynomial
factor.  A polynomial is absorbed by half of the strip exponential, so every majorant of the base
theory survives with an explicit constant: the jet-modified strip Fourier transform is uniformly
bounded on every positive vertical line, exactly as the base profile is.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- The jet-modified analytic test `g_{N,τ}(z) = P_N(ω(z))·e^{-τω(z)}`. -/
def xiMassJetAnalyticTest (a : ℝ) (N : ℕ) (τ : ℂ) (z : ℂ) : ℂ :=
  xiMassCausticJet a N (xiMassAnalyticSqrt a z) * xiMassAnalyticTest a τ z

/-- **On the real axis the jet-modified test is a real polynomial times the base test.** -/
theorem xiMassJetAnalyticTest_ofReal {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (τ : ℂ) (x : ℝ) :
    xiMassJetAnalyticTest a N τ (x : ℂ)
      = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) ^ (2 * N) * xiMassAnalyticTest a τ (x : ℂ) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  rw [xiMassJetAnalyticTest, xiMassAnalyticSqrt_ofReal_eq ha0,
    xiMassCausticJet_dispersion ha N x]

/-- The real-axis majorant of the jet-modified test. -/
def xiMassJetMajorant (a : ℝ) (N : ℕ) (σ x : ℝ) : ℝ :=
  (x ^ 2 + 4 * a ^ 4) ^ (2 * N) * Real.exp (-(σ * |x|))

theorem xiMassJetMajorant_nonneg {a : ℝ} (N : ℕ) (σ x : ℝ) :
    0 ≤ xiMassJetMajorant a N σ x := by
  rw [xiMassJetMajorant]
  have h : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
  positivity

/-- The constant by which the polynomial jet is absorbed into half the strip exponential. -/
def xiMassJetAbsorbConstant (a : ℝ) (N : ℕ) (σ : ℝ) : ℝ :=
  (1 + 4 * a ^ 4) ^ (2 * N)
    * ((Nat.factorial (4 * N) : ℝ) / (σ / 2) ^ (4 * N) * Real.exp (σ / 2))

/-- **A polynomial jet is absorbed by half of the strip exponential.** -/
theorem xiMassJetMajorant_le {a : ℝ} (N : ℕ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    xiMassJetMajorant a N σ x
      ≤ xiMassJetAbsorbConstant a N σ * Real.exp (-((σ / 2) * |x|)) := by
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hbase : x ^ 2 + 4 * a ^ 4 ≤ (1 + 4 * a ^ 4) * (1 + |x|) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (1 + |x|) ^ 2 := by nlinarith
    have h2 : |x| ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith
    have h3 : 4 * a ^ 4 * 1 ≤ 4 * a ^ 4 * (1 + |x|) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hsq]
    nlinarith [h2, h3]
  have hnn : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
  have hpow : (x ^ 2 + 4 * a ^ 4) ^ (2 * N)
      ≤ (1 + 4 * a ^ 4) ^ (2 * N) * (1 + |x|) ^ (4 * N) := by
    refine le_trans (pow_le_pow_left₀ hnn hbase (2 * N)) (le_of_eq ?_)
    rw [mul_pow, ← pow_mul]
    congr 2
    ring
  have hgrow := HTGeometry.one_add_pow_le_const_mul_exp habs (half_pos hσ) (4 * N)
  have hexp : Real.exp ((σ / 2) * |x|) * Real.exp (-(σ * |x|))
      = Real.exp (-((σ / 2) * |x|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc1 : (0 : ℝ) ≤ (1 + 4 * a ^ 4) ^ (2 * N) := by positivity
  have hfac : (0 : ℝ) ≤ (Nat.factorial (4 * N) : ℝ) / (σ / 2) ^ (4 * N) * Real.exp (σ / 2) := by
    have hden : (0 : ℝ) < (σ / 2) ^ (4 * N) := by positivity
    have : (0 : ℝ) ≤ (Nat.factorial (4 * N) : ℝ) / (σ / 2) ^ (4 * N) :=
      div_nonneg (by positivity) hden.le
    positivity
  calc xiMassJetMajorant a N σ x
      = (x ^ 2 + 4 * a ^ 4) ^ (2 * N) * Real.exp (-(σ * |x|)) := rfl
    _ ≤ ((1 + 4 * a ^ 4) ^ (2 * N) * (1 + |x|) ^ (4 * N)) * Real.exp (-(σ * |x|)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ ≤ ((1 + 4 * a ^ 4) ^ (2 * N)
          * ((Nat.factorial (4 * N) : ℝ) / (σ / 2) ^ (4 * N) * Real.exp (σ / 2)
            * Real.exp ((σ / 2) * |x|))) * Real.exp (-(σ * |x|)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ hc1
        refine hgrow.trans (le_of_eq ?_)
        ring
    _ = xiMassJetAbsorbConstant a N σ * (Real.exp ((σ / 2) * |x|) * Real.exp (-(σ * |x|))) := by
        rw [xiMassJetAbsorbConstant]
        ring
    _ = xiMassJetAbsorbConstant a N σ * Real.exp (-((σ / 2) * |x|)) := by rw [hexp]

theorem continuous_xiMassJetMajorant (a : ℝ) (N : ℕ) (σ : ℝ) :
    Continuous (xiMassJetMajorant a N σ) := by
  unfold xiMassJetMajorant
  fun_prop

theorem integrable_xiMassJetMajorant (a : ℝ) (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (xiMassJetMajorant a N σ) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (half_pos hσ)).const_mul (xiMassJetAbsorbConstant a N σ))
    (continuous_xiMassJetMajorant a N σ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (xiMassJetMajorant_nonneg N σ x)]
  exact xiMassJetMajorant_le N hσ x

/-- The uniform vertical bound of the jet-modified mass Fourier profile. -/
def xiMassJetVerticalBound (a : ℝ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∫ x : ℝ, xiMassJetMajorant a N σ x

theorem xiMassJetVerticalBound_nonneg (a : ℝ) (N : ℕ) (σ : ℝ) :
    0 ≤ xiMassJetVerticalBound a N σ :=
  integral_nonneg fun x => xiMassJetMajorant_nonneg N σ x

/-- **The jet-modified strip Fourier transform is uniformly bounded on every positive vertical
line.**  The polynomial jet costs only the explicit constant `xiMassJetVerticalBound`. -/
theorem norm_stripFourier_xiMassJetAnalyticTest_vertical_le {a σ : ℝ} (ha : 1 / 2 < a)
    (hσ : 0 < σ) (N : ℕ) (u w : ℝ) :
    ‖stripFourier (xiMassJetAnalyticTest a N ((σ : ℂ) + u * I)) (w : ℂ)‖
      ≤ xiMassJetVerticalBound a N σ := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  unfold stripFourier xiMassJetVerticalBound
  refine norm_integral_le_of_norm_le (integrable_xiMassJetMajorant a N hσ) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha0
  have hg := norm_xiMassAnalyticTest_le (τ := ((σ : ℂ) + u * I))
    ha0 (by simpa using hσ.le) hmem
  rw [norm_mul, Complex.norm_exp]
  have hphase : (-(I * (w : ℂ) * (x : ℂ))).re = 0 := by simp
  rw [hphase, Real.exp_zero, mul_one, xiMassJetAnalyticTest_ofReal ha N _ x, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4)]
  have hgg : ‖xiMassAnalyticTest a ((σ : ℂ) + u * I) (x : ℂ)‖ ≤ Real.exp (-(σ * |x|)) := by
    refine hg.trans (le_of_eq ?_)
    congr 1
    simp
  refine le_trans (mul_le_mul_of_nonneg_left hgg (by positivity)) (le_of_eq rfl)

end

end RHTower
