import GaloisForLFunctions.RHTower.MobiusDivisorCriticalChildAbelMellinWeld
import GaloisForLFunctions.RHTower.HarmonicResidueAbscissaReader

/-!
# Prime-zeta magnification of the critical Abel source

The actual critical Abel primitive has a finite nonzero Mellin jet at its
right boundary. Multiplication by the prime-zeta factor introduces a
logarithmic singularity: the normalized product is unbounded. This is a
source-side singularity witness, not yet the Mellin transform of a terminal
prime head.
-/

noncomputable section
open Filter Topology Set Complex
namespace RHTower

private theorem primeZeta_tendsto_atTop_right :
    Tendsto primeZeta (𝓝[>] (1 : ℝ)) atTop := by
  have h := tendsto_primeZeta_add_log_sub.add_atTop tendsto_abscissaLog_atTop
  convert h using 1
  funext s
  simp only [abscissaLog]
  ring

theorem criticalAbelMellin_finiteJet :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ w : ℂ in 𝓝 1, 1 < w.re →
        mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ)) (-(w + 1 / 2)) =
          (w - 1) ^ r * g w / (w * (2 * w + 1)) := by
  obtain ⟨r, hr, g, hga, hg0, hfac⟩ := criticalSourceCurrentGap_finiteJet
  refine ⟨r, hr, g, hga, hg0, ?_⟩
  filter_upwards [hfac] with w hwfac hwr
  have hs : (3 / 2 : ℝ) < (w + 1 / 2).re := by
    simp only [add_re]
    norm_num at hwr ⊢
    linarith
  have hm := (hasMellin_criticalContinuousAbel hs).2
  have hshift : w + 1 / 2 - 1 / 2 = w := by ring
  rw [hshift] at hm
  rw [hm, criticalStepSourceMellin_eq_centeredCurrentGap hwr, hwfac]
  have hw0 : w ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs0 : w + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by linarith)
  field_simp

theorem criticalAbelMellin_normalizedJet :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun δ : ℝ =>
        mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  obtain ⟨r, hr, g, hga, hg0, hfac⟩ := criticalAbelMellin_finiteJet
  have hc : g 1 / 3 ≠ 0 := div_ne_zero hg0 (by norm_num)
  refine ⟨r, hr, g 1 / 3, hc, ?_⟩
  have hδ : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.add hδ
  have hfacR := hshift.eventually hfac
  have heq : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r =
        g (1 + (δ : ℂ)) /
          ((1 + (δ : ℂ)) * (2 * (1 + (δ : ℂ)) + 1)) := by
    filter_upwards [hfacR, self_mem_nhdsWithin] with δ hf hpos
    have hw : 1 < ((1 : ℂ) + (δ : ℂ)).re := by
      simp only [add_re, one_re, ofReal_re]
      exact lt_add_of_pos_right 1 hpos
    rw [hf hw]
    have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    rw [show (1 : ℂ) + (δ : ℂ) - 1 = (δ : ℂ) by ring]
    field_simp
  have hgT : Tendsto (fun δ : ℝ => g (1 + (δ : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (g 1)) := hga.continuousAt.tendsto.comp hshift
  have hdenT : Tendsto
      (fun δ : ℝ => ((1 : ℂ) + (δ : ℂ)) * (2 * (1 + (δ : ℂ)) + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℂ)) := by
    have hcont : ContinuousAt (fun w : ℂ => w * (2 * w + 1)) 1 := by fun_prop
    simpa [Function.comp_def, show (2 : ℂ) + 1 = 3 by norm_num] using
      hcont.tendsto.comp hshift
  refine (hgT.div hdenT (by norm_num)).congr' ?_
  filter_upwards [heq] with δ h
  exact h.symm

theorem criticalAbelPrimeMellin_logJet :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun δ : ℝ =>
        (mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r) *
          ((primeZeta (1 + δ) / abscissaLog (1 + δ) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  obtain ⟨r, hr, c, hc, hjet⟩ := criticalAbelMellin_normalizedJet
  refine ⟨r, hr, c, hc, ?_⟩
  have hshift : Tendsto (fun δ : ℝ => 1 + δ)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun δ : ℝ => 1 + δ) (𝓝 0) (𝓝 (1 + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simpa using hδ
  have hprimeR := tendsto_primeZeta_div_abscissaLog.comp hshift
  have hprimeC : Tendsto
      (fun δ : ℝ => ((primeZeta (1 + δ) / abscissaLog (1 + δ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp hprimeR
  simpa only [mul_one] using hjet.mul hprimeC

theorem criticalAbelPrimeMellin_unboundedJet :
    ∃ r : ℕ, 1 ≤ r ∧
      Tendsto (fun δ : ℝ =>
        primeZeta (1 + δ) *
          ‖mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
            (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r‖)
        (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨r, hr, c, hc, hjet⟩ := criticalAbelMellin_normalizedJet
  refine ⟨r, hr, ?_⟩
  have hshift : Tendsto (fun δ : ℝ => 1 + δ)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun δ : ℝ => 1 + δ) (𝓝 0) (𝓝 (1 + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simpa using hδ
  have hprime := primeZeta_tendsto_atTop_right.comp hshift
  have hnorm : Tendsto (fun δ : ℝ =>
        ‖mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖c‖) := (continuous_norm.tendsto c).comp hjet
  exact hprime.atTop_mul_pos (norm_pos_iff.mpr hc) hnorm

end RHTower
