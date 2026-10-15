import GaloisForLFunctions.RHTower.ThetaQuotientParityFeedback
import GaloisForLFunctions.RHTower.SawtoothFourierSeries

/-!
# The actual theta parity reference core and its Volterra limit

The sine and cosine-defect features belong to unweighted source L2. Their exact
Gram matrices are the theta CDF-action matrices S and C. Their finite rank-one
sum is the positive-reference channel before the directed feedback is subtracted.

Its literal finite kernel converges on the negative source half-line to pi/2
times the lower-triangle indicator, with diagonal value pi/4. The proof uses
the corpus's convergent sine partial sums and the actual strictly increasing
theta CDF. Every truncation defines a bounded operator on the full source line.

This module supplies the local kernel identity and source operator realization.
Spectral divergence and forced residue alternation require further lemmas;
no critical-wall or Riemann-hypothesis conclusion is asserted here.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower
open HedenmalmThetaSource
noncomputable section

def paritySinePartial (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.sin ((n : ℝ) * (2 * Real.pi * t)) / n

theorem paritySinePartial_neg (N : ℕ) (t : ℝ) :
    paritySinePartial N (-t) = -paritySinePartial N t := by
  simp [paritySinePartial, mul_neg, Real.sin_neg, neg_div, Finset.sum_neg_distrib]

theorem paritySinePartial_zero (N : ℕ) : paritySinePartial N 0 = 0 := by
  simp [paritySinePartial]

theorem tendsto_paritySinePartial {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun N => paritySinePartial N t) atTop (𝓝 (Real.pi * (1 / 2 - t))) := by
  have hθ : 2 * Real.pi * t ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨mul_pos (by positivity) ht.1, by nlinarith [Real.pi_pos, ht.2]⟩
  have h := GaloisForLFunctions.RHTower.tendsto_sum_sawtoothSine hθ
  rw [GaloisForLFunctions.RHTower.sawWave_eq_of_mem_Ioo hθ] at h
  have he : (Real.pi - 2 * Real.pi * t) / 2 = Real.pi * (1 / 2 - t) := by ring
  simpa only [paritySinePartial, he] using h

theorem tendsto_paritySinePartial_neg {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    Tendsto (fun N => paritySinePartial N t) atTop (𝓝 (Real.pi * (-1 / 2 - t))) := by
  have hp := (tendsto_paritySinePartial (t := -t) (by constructor <;> linarith [ht.1, ht.2])).neg
  have he : - (Real.pi * (1 / 2 - -t)) = Real.pi * (-1 / 2 - t) := by ring
  rw [he] at hp
  simpa only [paritySinePartial_neg, neg_neg] using hp

/-- The finite positive-reference kernel before boundary feedback is subtracted. -/
def parityReferenceKernel (N : ℕ) (t s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (1 - Real.cos ((n : ℝ) * (2 * Real.pi * t))) *
      Real.sin ((n : ℝ) * (2 * Real.pi * s)) / n

theorem parityReferenceKernel_eq_sinePartial (N : ℕ) (t s : ℝ) :
    parityReferenceKernel N t s = paritySinePartial N s -
      (paritySinePartial N (s + t) + paritySinePartial N (s - t)) / 2 := by
  unfold parityReferenceKernel paritySinePartial
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show (n : ℝ) * (2 * Real.pi * (s + t)) =
      n * (2 * Real.pi * s) + n * (2 * Real.pi * t) by ring,
    show (n : ℝ) * (2 * Real.pi * (s - t)) =
      n * (2 * Real.pi * s) - n * (2 * Real.pi * t) by ring,
    Real.sin_add, Real.sin_sub]
  ring

theorem tendsto_parityReferenceKernel_lower {t s : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) (hs : s ∈ Ioo (0 : ℝ) (1 / 2))
    (hst : s < t) :
    Tendsto (fun N => parityReferenceKernel N t s) atTop (𝓝 (Real.pi / 2)) := by
  have h1 := tendsto_paritySinePartial (t := s) ⟨hs.1, by linarith [hs.2]⟩
  have h2 := tendsto_paritySinePartial (t := s + t) (by constructor <;> linarith [ht.1, ht.2, hs.1, hs.2])
  have h3 := tendsto_paritySinePartial_neg (t := s - t) (by constructor <;> linarith [ht.2, hs.1])
  have h := h1.sub ((h2.add h3).div_const 2)
  have he : Real.pi * (1 / 2 - s) -
      (Real.pi * (1 / 2 - (s + t)) + Real.pi * (-1 / 2 - (s - t))) / 2 = Real.pi / 2 := by ring
  rw [he] at h
  simpa only [← parityReferenceKernel_eq_sinePartial] using h

theorem tendsto_parityReferenceKernel_upper {t s : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) (hs : s ∈ Ioo (0 : ℝ) (1 / 2))
    (hts : t < s) :
    Tendsto (fun N => parityReferenceKernel N t s) atTop (𝓝 0) := by
  have h1 := tendsto_paritySinePartial (t := s) ⟨hs.1, by linarith [hs.2]⟩
  have h2 := tendsto_paritySinePartial (t := s + t) (by constructor <;> linarith [ht.1, ht.2, hs.1, hs.2])
  have h3 := tendsto_paritySinePartial (t := s - t) (by constructor <;> linarith [ht.1, hs.2])
  have h := h1.sub ((h2.add h3).div_const 2)
  have he : Real.pi * (1 / 2 - s) -
      (Real.pi * (1 / 2 - (s + t)) + Real.pi * (1 / 2 - (s - t))) / 2 = 0 := by ring
  rw [he] at h
  simpa only [← parityReferenceKernel_eq_sinePartial] using h

theorem tendsto_parityReferenceKernel_diagonal {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (fun N => parityReferenceKernel N t t) atTop (𝓝 (Real.pi / 4)) := by
  have h1 := tendsto_paritySinePartial (t := t) ⟨ht.1, by linarith [ht.2]⟩
  have h2 := tendsto_paritySinePartial (t := t + t) (by constructor <;> linarith [ht.1, ht.2])
  have h := h1.sub (h2.div_const 2)
  have he : Real.pi * (1 / 2 - t) - Real.pi * (1 / 2 - (t + t)) / 2 = Real.pi / 4 := by ring
  rw [he] at h
  simpa only [parityReferenceKernel_eq_sinePartial, sub_self, paritySinePartial_zero, add_zero] using h

def thetaParityReferenceKernel (N : ℕ) (x y : ℝ) : ℝ :=
  parityReferenceKernel N (thetaSource.cdfFun x) (thetaSource.cdfFun y)

private theorem cdf_negative_mem_half {x : ℝ} (hx : x < 0) :
    thetaSource.cdfFun x ∈ Ioo (0 : ℝ) (1 / 2) := by
  have h0 : thetaSource.cdfFun 0 = 1 / 2 := by
    have h := HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even 0
    simp only [neg_zero] at h
    linarith
  exact ⟨(thetaSource.cdfFun_mem_Ioo x).1, h0 ▸ thetaSource.strictMono_cdfFun hx⟩

/-- The actual theta positive-reference core has a literal Volterra limit on the left half-line. -/
theorem tendsto_thetaParityReferenceKernel {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    Tendsto (fun N => thetaParityReferenceKernel N x y) atTop
      (𝓝 (if y < x then Real.pi / 2 else if x < y then 0 else Real.pi / 4)) := by
  rcases lt_trichotomy y x with h | rfl | h
  · rw [if_pos h]
    exact tendsto_parityReferenceKernel_lower (cdf_negative_mem_half hx)
      (cdf_negative_mem_half hy) (thetaSource.strictMono_cdfFun h)
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    exact tendsto_parityReferenceKernel_diagonal (cdf_negative_mem_half hx)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
    exact tendsto_parityReferenceKernel_upper (cdf_negative_mem_half hx)
      (cdf_negative_mem_half hy) (thetaSource.strictMono_cdfFun h)

abbrev ThetaParitySourceL2 := Lp ℂ 2 (volume : Measure ℝ)

def thetaParitySineFun (n : ℤ) (x : ℝ) : ℂ :=
  Real.sin (2 * Real.pi * n * thetaSource.cdfFun x)

def thetaParityCosineFun (n : ℤ) (x : ℝ) : ℂ :=
  ((1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x) : ℝ) : ℂ)

private theorem continuous_thetaParitySineFun (n : ℤ) : Continuous (thetaParitySineFun n) := by
  exact Complex.continuous_ofReal.comp (Real.continuous_sin.comp
    (continuous_const.mul thetaSource.continuous_cdfFun))

private theorem continuous_thetaParityCosineFun (n : ℤ) : Continuous (thetaParityCosineFun n) := by
  exact Complex.continuous_ofReal.comp (continuous_const.sub (Real.continuous_cos.comp
    (continuous_const.mul thetaSource.continuous_cdfFun)))

theorem memLp_thetaParitySineFun (n : ℤ) : MemLp (thetaParitySineFun n) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_thetaParitySineFun n).aestronglyMeasurable).mpr
  apply ((integrable_cdfAction_integrand n).const_mul 2).mono'
    ((continuous_thetaParitySineFun n).norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [thetaParitySineFun, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have he := Real.sin_sq_add_cos_sq (2 * Real.pi * n * thetaSource.cdfFun x)
  nlinarith [sq_nonneg (1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x))]

theorem memLp_thetaParityCosineFun (n : ℤ) : MemLp (thetaParityCosineFun n) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_thetaParityCosineFun n).aestronglyMeasurable).mpr
  apply ((integrable_cdfAction_integrand n).const_mul 2).mono'
    ((continuous_thetaParityCosineFun n).norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [thetaParityCosineFun, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hlo := Real.neg_one_le_cos (2 * Real.pi * n * thetaSource.cdfFun x)
  have hhi := Real.cos_le_one (2 * Real.pi * n * thetaSource.cdfFun x)
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith :
    0 ≤ 1 + Real.cos (2 * Real.pi * n * thetaSource.cdfFun x))]

def thetaParitySineVec (n : ℤ) : ThetaParitySourceL2 :=
  (memLp_thetaParitySineFun n).toLp (thetaParitySineFun n)

def thetaParityCosineVec (n : ℤ) : ThetaParitySourceL2 :=
  (memLp_thetaParityCosineFun n).toLp (thetaParityCosineFun n)

theorem thetaParitySineVec_ae (n : ℤ) :
    (thetaParitySineVec n : ℝ → ℂ) =ᵐ[volume] thetaParitySineFun n :=
  (memLp_thetaParitySineFun n).coeFn_toLp

theorem thetaParityCosineVec_ae (n : ℤ) :
    (thetaParityCosineVec n : ℝ → ℂ) =ᵐ[volume] thetaParityCosineFun n :=
  (memLp_thetaParityCosineFun n).coeFn_toLp

theorem inner_thetaParitySineVec (m n : ℤ) :
    inner ℂ (thetaParitySineVec m) (thetaParitySineVec n) = (thetaCdfSineGram m n : ℂ) := by
  rw [MeasureTheory.L2.inner_def, thetaCdfSineGram_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [thetaParitySineVec_ae m, thetaParitySineVec_ae n] with x hm hn
  rw [hm, hn, thetaParitySineFun, thetaParitySineFun, RCLike.inner_apply']
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, mul_comm]

theorem inner_thetaParityCosineVec (m n : ℤ) :
    inner ℂ (thetaParityCosineVec m) (thetaParityCosineVec n) = (thetaCdfCosineGram m n : ℂ) := by
  rw [MeasureTheory.L2.inner_def, thetaCdfCosineGram_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [thetaParityCosineVec_ae m, thetaParityCosineVec_ae n] with x hm hn
  rw [hm, hn, thetaParityCosineFun, thetaParityCosineFun, RCLike.inner_apply']
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, mul_comm]

/-- Actual finite reference operator on the unweighted source line. The zero-frequency
summand vanishes by the scalar coefficient, so `N+1` includes frequencies `1,...,N`. -/
def thetaParityReferenceOperator (N : ℕ) : ThetaParitySourceL2 →L[ℂ] ThetaParitySourceL2 :=
  ∑ n ∈ Finset.range N,
    ((n : ℂ)⁻¹) • (innerSL ℂ (thetaParitySineVec n)).smulRight (thetaParityCosineVec n)

theorem thetaParityReferenceOperator_apply (N : ℕ) (f : ThetaParitySourceL2) :
    thetaParityReferenceOperator N f =
      ∑ n ∈ Finset.range N, ((n : ℂ)⁻¹ * inner ℂ (thetaParitySineVec n) f) • thetaParityCosineVec n := by
  simp [thetaParityReferenceOperator,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

theorem inner_thetaParityReferenceOperator (N : ℕ) (f g : ThetaParitySourceL2) :
    inner ℂ f (thetaParityReferenceOperator N g) =
      ∑ n ∈ Finset.range N,
        ((n : ℂ)⁻¹ * inner ℂ (thetaParitySineVec n) g) * inner ℂ f (thetaParityCosineVec n) := by
  rw [thetaParityReferenceOperator_apply, inner_sum]
  exact Finset.sum_congr rfl fun n _ => inner_smul_right _ _ _

end
end RHTower

