import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureGaussianAmplifiedReceiver
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip

/-!
# The amplified HCF diagonal detects the on-line zeros at every height

The Gaussian-amplified HCF diagonal is `𝒜(t, σ) = Σ_q F_t(z_q)² exp(-σ (z_q - t)²)`, with
`F_t(z) = 2/(1 + (z - t)²)`.  As `σ → ∞` each term either

* stays equal to `F_t(t)² = 4`, if `z_q = t` (an on-line zero at height `t`);
* tends to `0`, if `z_q` lies strictly outside the closed light cone over `t`;
* or grows, if `z_q` lies inside the open cone.

**Theorem** (`tendsto_criticalFeatureGaussianAmplifiedTrace_of_outside_cones`).  If every copy is
either the on-line point `t` or strictly outside the closed cone over `t`, then
`𝒜(t, σ) → 4 · #{q : z_q = t}` as `σ → ∞`.  The amplification limit counts the on-line zero at
height `t` with multiplicity.

**Theorem** (`riemannHypothesis_iff_forall_tendsto_criticalFeatureGaussianAmplifiedTrace`).  RH holds
iff at every height `t` the amplified diagonal converges as `σ → ∞`.  Under RH the limit is
`4 m(t)`, with `m(t)` the multiplicity of `1/2 + it`; otherwise it diverges at the height of an
off-line zero.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

theorem criticalFeatureCauchyKernelTest_self (t : ℝ) :
    criticalFeatureCauchyKernelTest t (t : ℂ) = 2 := by
  rw [criticalFeatureCauchyKernelTest_eq_div (by simp)]
  simp

/-- **The HCF zero detector.** -/
theorem tendsto_criticalFeatureGaussianAmplifiedTrace_of_outside_cones {t : ℝ}
    (hout : ∀ q : XiZeroCopy, xiSpectralPoint q = (t : ℂ) ∨
      (xiSpectralPoint q).im ^ 2 < ((xiSpectralPoint q).re - t) ^ 2) :
    Tendsto (fun σ : ℝ => criticalFeatureGaussianAmplifiedTrace t σ) atTop
      (𝓝 (∑' q : XiZeroCopy, if xiSpectralPoint q = (t : ℂ) then (4 : ℂ) else 0)) := by
  classical
  have hcone : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
    intro q
    rcases hout q with h | h
    · rw [h]; simp
    · exact h.le
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun q => Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
    (criticalFeatureHermitianEnergy_summable t) (fun q => ?_) ?_
  · rcases hout q with h | h
    · rw [if_pos h]
      refine tendsto_const_nhds.congr fun σ => ?_
      rw [criticalFeatureGaussianAmplifiedTerm, h, sub_self, criticalFeatureCauchyKernelTest_self]
      simp
      norm_num
    · rw [if_neg (fun h' => by
        rw [h'] at h; simp at h)]
      apply squeeze_zero_norm (a := fun σ : ℝ =>
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) *
          Real.exp (-(σ * (((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2))))
      · intro σ
        rw [norm_criticalFeatureGaussianAmplifiedTerm]
      · have hpos : 0 < ((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2 := by linarith
        have hlim : Tendsto (fun σ : ℝ =>
            Real.exp (-(σ * (((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2))))
            atTop (𝓝 0) := by
          refine Real.tendsto_exp_atBot.comp ?_
          exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hpos)
        simpa using hlim.const_mul (Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with σ hσ q
    exact norm_criticalFeatureGaussianAmplifiedTerm_le_of_cone hσ (hcone q)

/-- **RH as convergence of the amplification.**  RH holds iff at every height the amplified HCF
diagonal converges as the amplification tends to infinity. -/
theorem riemannHypothesis_iff_forall_tendsto_criticalFeatureGaussianAmplifiedTrace :
    RiemannHypothesis ↔ ∀ t : ℝ, ∃ L : ℂ,
      Tendsto (fun σ : ℝ => criticalFeatureGaussianAmplifiedTrace t σ) atTop (𝓝 L) := by
  constructor
  · intro hRH t
    refine ⟨_, tendsto_criticalFeatureGaussianAmplifiedTrace_of_outside_cones fun q => ?_⟩
    have him : (xiSpectralPoint q).im = 0 := by
      have h := (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q
      exact h
    by_cases hx : (xiSpectralPoint q).re = t
    · left
      exact Complex.ext (by simp [hx]) (by simp [him])
    · right
      rw [him]
      have : 0 < ((xiSpectralPoint q).re - t) ^ 2 := by
        have : (xiSpectralPoint q).re - t ≠ 0 := sub_ne_zero.2 hx
        positivity
      linarith [sq_nonneg (0 : ℝ)]
  · intro h
    rw [riemannHypothesis_iff_forall_criticalFeatureGaussianAmplifiedTrace_bounded]
    intro t
    obtain ⟨L, hL⟩ := h t
    obtain ⟨σ₀, hσ₀⟩ := Metric.tendsto_atTop.1 hL 1 one_pos
    refine ⟨max (‖L‖ + 1) (Real.exp (max σ₀ 0 / 4) * criticalFeatureHermitianEnergyTrace t),
      fun σ hσ => ?_⟩
    rcases le_or_gt σ₀ σ with hbig | hsmall
    · have := hσ₀ σ hbig
      rw [dist_eq_norm] at this
      have htri := norm_sub_norm_le (criticalFeatureGaussianAmplifiedTrace t σ) L
      exact le_max_of_le_left (by linarith)
    · refine le_max_of_le_right ?_
      have hterm : ∀ q : XiZeroCopy,
          ‖criticalFeatureGaussianAmplifiedTerm t σ (xiSpectralPoint q)‖ ≤
            Real.exp (max σ₀ 0 / 4) *
              Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
        intro q
        refine (norm_criticalFeatureGaussianAmplifiedTerm_le hσ
          (abs_xiSpectralPoint_im_lt_half q)).trans ?_
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by
          have := le_max_left σ₀ 0; linarith)) (Complex.normSq_nonneg _)
      rw [criticalFeatureHermitianEnergyTrace, ← tsum_mul_left]
      exact (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ)).trans
        ((summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ).tsum_le_tsum hterm
          ((criticalFeatureHermitianEnergy_summable t).mul_left _))

end

end RHTower
