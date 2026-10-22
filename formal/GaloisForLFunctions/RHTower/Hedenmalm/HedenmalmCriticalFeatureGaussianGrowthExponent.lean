import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureGaussianAmplifiedReceiver
import GaloisForLFunctions.HTGeometry.GaussianLightConeGrowthExponent

/-!
# The amplification rate of the HCF trace is the depth of the light cone

For the Gaussian-amplified critical-feature diagonal
`𝒜(t, σ) = Σ_γ F_t(γ)² exp(-σ (γ - t)²)` the exponent of the copy `γ` has real part
`(Re γ − t)² − (Im γ)²`.  Its light-cone depth over the height `t` is
`M(t) = max_γ ((Im γ)² − (Re γ − t)²)`.  If some copy lies in the open light cone (`M(t) > 0`), then:

* `‖𝒜(t, σ)‖ ≤ K e^{σ M(t)} + E(t)` for all `σ ≥ 0`, with `E(t)` the Hermitian feature energy;
* for every `δ > 0`, `‖𝒜(t, σ)‖ ≥ e^{σ (M(t) − δ)}` at arbitrarily large `σ`

(`criticalFeatureGaussianAmplifiedTrace_growthExponent`).  So `limsup σ⁻¹ log ‖𝒜(t, σ)‖ = M(t)`:
the amplification rate measures the depth of the deepest off-line zero cone over `t`.
-/

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem re_xiSpectralPoint_sub_sq (t : ℝ) (q : XiZeroCopy) :
    ((xiSpectralPoint q - t) ^ 2).re =
      ((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2 :=
  re_sub_ofReal_sq _ t

theorem criticalFeatureCauchyKernelTest_sq_xiSpectralPoint (t : ℝ) (q : XiZeroCopy) :
    criticalFeatureCauchyKernelTest t (xiSpectralPoint q) ^ 2 =
      (2 / (1 + (xiSpectralPoint q - t) ^ 2)) ^ 2 := by
  rw [criticalFeatureCauchyKernelTest_eq_div (abs_xiSpectralPoint_im_lt_half q)]

theorem one_add_xiSpectralPoint_sub_sq_ne_zero (t : ℝ) (q : XiZeroCopy) :
    1 + (xiSpectralPoint q - t) ^ 2 ≠ 0 := fun h => by
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.one_re, re_xiSpectralPoint_sub_sq, Complex.zero_re] at hre
  have him := abs_xiSpectralPoint_im_lt_half q
  have hy : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
    have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
    linarith
  nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]

/-- The open light cone over `t` holds finitely many zero copies. -/
theorem finite_xiSpectralPoint_lightCone (t : ℝ) :
    {q : XiZeroCopy | ((xiSpectralPoint q - t) ^ 2).re < 0}.Finite := by
  refine (finite_xiSpectralPoint_norm_le (|t| + 1)).subset fun q hq => ?_
  simp only [Set.mem_setOf_eq] at hq ⊢
  have him := abs_xiSpectralPoint_im_lt_half q
  rw [re_xiSpectralPoint_sub_sq] at hq
  have hy : (xiSpectralPoint q).im ^ 2 < (1 / 2) ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
    linarith
  have hre : |(xiSpectralPoint q).re - t| < 1 / 2 := by
    have h1 : ((xiSpectralPoint q).re - t) ^ 2 < (1 / 2) ^ 2 := by linarith
    rw [sq_lt_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    exact h1
  have hret : |(xiSpectralPoint q).re| ≤ |t| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re t
    linarith
  calc ‖xiSpectralPoint q‖
      ≤ |(xiSpectralPoint q).re| + |(xiSpectralPoint q).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|t| + 1 / 2) + 1 / 2 := add_le_add hret him.le
    _ = |t| + 1 := by ring

/-- **Growth exponent of the amplified HCF trace.**  If some zero copy lies in the open light cone
over `t`, its depth `M = max_γ ((Im γ)² − (Re γ − t)²)` is positive, `‖𝒜(t, σ)‖ ≤ K e^{σM} + E(t)`
for `σ ≥ 0`, and for every `δ > 0` the trace exceeds `e^{σ(M − δ)}` at arbitrarily large `σ`. -/
theorem criticalFeatureGaussianAmplifiedTrace_growthExponent {t : ℝ}
    (hoff : ∃ q₀ : XiZeroCopy, |(xiSpectralPoint q₀).re - t| < |(xiSpectralPoint q₀).im|) :
    ∃ M : ℝ, 0 < M ∧
      (∃ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - t) ^ 2 = M) ∧
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - t) ^ 2 ≤ M) ∧
      (∃ K : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤
        K * Real.exp (σ * M) + criticalFeatureHermitianEnergyTrace t) ∧
      (∀ δ : ℝ, 0 < δ → ∀ S : ℝ, ∃ σ : ℝ, S ≤ σ ∧ 0 ≤ σ ∧
        Real.exp (σ * (M - δ)) ≤ ‖criticalFeatureGaussianAmplifiedTrace t σ‖) := by
  classical
  set w : XiZeroCopy → ℂ := fun q => (xiSpectralPoint q - t) ^ 2 with hw
  set c : XiZeroCopy → ℂ := fun q => criticalFeatureCauchyKernelTest t (xiSpectralPoint q) ^ 2
    with hc
  have hfin := finite_xiSpectralPoint_lightCone t
  obtain ⟨q₀, hq₀⟩ := hoff
  have hq₀neg : (w q₀).re < 0 := by
    simp only [hw]; rw [re_xiSpectralPoint_sub_sq]; have := sq_lt_sq.2 hq₀; linarith
  obtain ⟨qs, hqsP, hqsmax⟩ := hfin.toFinset.exists_max_image (fun q => -(w q).re)
    ⟨q₀, by rw [Set.Finite.mem_toFinset]; exact hq₀neg⟩
  rw [Set.Finite.mem_toFinset] at hqsP
  have hqsneg : (w qs).re < 0 := hqsP
  set M : ℝ := -(w qs).re with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  have hMmax : ∀ q, (w q).re < 0 → -(w q).re ≤ M := fun q hq =>
    hqsmax q (by rw [Set.Finite.mem_toFinset]; exact hq)
  have hMall : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - t) ^ 2 ≤ M := fun q => by
    have hre : -(w q).re = (xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - t) ^ 2 := by
      simp only [hw]; rw [re_xiSpectralPoint_sub_sq]; ring
    by_cases hq : (w q).re < 0
    · rw [← hre]; exact hMmax q hq
    · rw [← hre]; linarith
  have hcoef : ∀ i j, w i = w j → c i = c j := fun i j h => by
    simp only [hc, criticalFeatureCauchyKernelTest_sq_xiSpectralPoint]
    simp only [hw] at h
    rw [h]
  have hcne : ∀ i, (w i).re < 0 → c i ≠ 0 := fun i _ => by
    simp only [hc]
    rw [criticalFeatureCauchyKernelTest_sq_xiSpectralPoint]
    exact pow_ne_zero _ (div_ne_zero two_ne_zero (one_add_xiSpectralPoint_sub_sq_ne_zero t i))
  have hmaj : ∀ i, 0 ≤ (w i).re → ∀ σ, (0 : ℝ) ≤ σ →
      ‖c i * Complex.exp (-(σ : ℂ) * w i)‖ ≤
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint i)) := by
    intro i hi σ hσ
    simp only [hw] at hi
    rw [re_xiSpectralPoint_sub_sq] at hi
    exact norm_criticalFeatureGaussianAmplifiedTerm_le_of_cone hσ (by linarith)
  have hsum : ∀ σ, (0 : ℝ) ≤ σ → Summable (fun i => ‖c i * Complex.exp (-(σ : ℂ) * w i)‖) :=
    fun σ hσ => summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ
  have htrace : ∀ σ, criticalFeatureGaussianAmplifiedTrace t σ =
      ∑' i, c i * Complex.exp (-(σ : ℂ) * w i) := fun σ => rfl
  have hE : criticalFeatureHermitianEnergyTrace t =
      ∑' q : XiZeroCopy, Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) :=
    rfl
  refine ⟨M, hM, ⟨qs, ?_⟩, hMall, ?_, ?_⟩
  · simp only [hMdef, hw]; rw [re_xiSpectralPoint_sub_sq]; ring
  · obtain ⟨K, hK⟩ := exists_norm_tsum_mul_exp_neg_le_exp le_rfl hfin
      (fun _ => Complex.normSq_nonneg _) (criticalFeatureHermitianEnergy_summable t) hmaj hsum
      M hMmax
    exact ⟨K, fun σ hσ => by rw [htrace, hE]; exact hK σ hσ⟩
  · intro δ hδ S
    obtain ⟨σ, hSσ, hσ, hlow⟩ := exists_exp_le_norm_tsum_mul_exp_neg le_rfl hcoef hcne hfin
      (fun _ => Complex.normSq_nonneg _) (criticalFeatureHermitianEnergy_summable t) hmaj hsum
      M ⟨qs, by rw [hMdef]; ring, hqsneg⟩ hMmax δ hδ S
    exact ⟨σ, hSσ, hσ, by rw [htrace]; exact hlow⟩

end

end RHTower
