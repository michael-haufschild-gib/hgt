import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalBetaKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Critical Suzuki energy on every bounded nonnegative profile

The normalized primary density recovers its extended Lévy energy without a
finite-energy assumption. A finite limiting integral supplies its own dominating
function through the exact exponential tail correction. Fatou's lemma handles
an infinite limit, so divergent energies are never replaced by totalized real
Bochner integrals.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section

private theorem lintegral_tendsto_top_of_pointwise {F : ℝ → ℝ → ℝ≥0∞} {g : ℝ → ℝ≥0∞}
    {μ : Measure ℝ} (hF : ∀ w, AEMeasurable (F w) μ)
    (hg : ∀ᵐ t ∂μ, Tendsto (fun w => F w t) (𝓝[>] 0) (𝓝 (g t)))
    (htop : ∫⁻ t, g t ∂μ = ⊤) :
    Tendsto (fun w => ∫⁻ t, F w t ∂μ) (𝓝[>] 0) (𝓝 ⊤) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · calc
      ⊤ = ∫⁻ t, g t ∂μ := htop.symm
      _ = ∫⁻ t, liminf (fun w => F w t) (𝓝[>] 0) ∂μ := by
        apply lintegral_congr_ae
        exact hg.mono fun t ht => ht.liminf_eq.symm
      _ ≤ liminf (fun w => ∫⁻ t, F w t ∂μ) (𝓝[>] 0) :=
        lintegral_liminf_le' hF
  · exact le_top
  · exact ⟨⊤, Eventually.of_forall fun _ => le_top⟩
  · exact ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

/-- The normalized positive primary source paired with a nonnegative compensator. -/
def suzukiCriticalCompensatedEnergy (D : ℝ → ℝ) (omega : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (D t * (suzukiCriticalPrimaryDensity omega t / omega))

/-- The extended critical energy; bounded profiles may still have infinite energy at the origin. -/
def suzukiCriticalLimitingCompensatedEnergy (D : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (D t *
    (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))

private theorem tangentWeight_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ 2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) := by
  have hd : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  positivity

private theorem levyWeight_eq_tangent_add_decay {t : ℝ} (ht : 0 < t) :
    2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) =
      2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) +
        2 * Real.exp (-t / 2) := by
  have hd : 1 - Real.exp (-2 * t) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have he : Real.exp (-(5 / 2 : ℝ) * t) =
      Real.exp (-t / 2) * Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply (div_eq_iff hd).mpr
  rw [add_mul, div_mul_cancel₀ _ hd]
  ring

private theorem bounded_compensator_integrable {D : ℝ → ℝ} {R omega : ℝ}
    (hDm : Measurable D) (hDnn : ∀ t, 0 ≤ D t) (hDb : ∀ t, D t ≤ R)
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    IntegrableOn (fun t => D t * (suzukiCriticalPrimaryDensity omega t / omega))
      (Ioi 0) := by
  have hi := (integrableOn_suzukiCriticalPrimaryDensity homega homega5).div_const omega
  apply hi.bdd_mul hDm.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hDnn t)] using hDb t

private theorem bounded_compensator_nonneg {D : ℝ → ℝ} {omega : ℝ}
    (hDnn : ∀ t, 0 ≤ D t) (homega : 0 < omega) :
    ∀ᵐ t ∂volume.restrict (Ioi 0),
      0 ≤ D t * (suzukiCriticalPrimaryDensity omega t / omega) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (hDnn t)
    (div_nonneg (suzukiCriticalPrimaryDensity_pos homega ht).le homega.le)

private theorem bounded_compensator_levy_integrable {D : ℝ → ℝ} {R : ℝ}
    (hDm : Measurable D) (hDnn : ∀ t, 0 ≤ D t) (hDb : ∀ t, D t ≤ R)
    (hfin : suzukiCriticalLimitingCompensatedEnergy D ≠ ⊤) :
    IntegrableOn (fun t => D t *
      (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) (Ioi 0) := by
  have hm : Measurable (fun t : ℝ => D t *
      (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) :=
    hDm.mul (by fun_prop)
  have hK : IntegrableOn (fun t => D t *
      (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) (Ioi 0) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have he : (∫⁻ t in Ioi 0, ‖D t *
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))‖ₑ) =
        suzukiCriticalLimitingCompensatedEnergy D := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.enorm_eq_ofReal (mul_nonneg (hDnn t) (tangentWeight_nonneg ht))
    rw [he]
    exact hfin.lt_top
  have hdec : IntegrableOn (fun t : ℝ => 2 * Real.exp (-t / 2)) (Ioi 0) := by
    have hi : IntegrableOn (fun t : ℝ => 2 * Real.exp ((-1 / 2) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) (0 : ℝ)).const_mul 2
    apply hi.congr_fun _ measurableSet_Ioi
    intro t _
    dsimp only
    congr 2
    ring
  have htail : IntegrableOn (fun t : ℝ => D t * (2 * Real.exp (-t / 2))) (Ioi 0) :=
    hdec.bdd_mul hDm.aestronglyMeasurable (Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hDnn t)] using hDb t)
  apply (hK.add htail).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.add_apply]
  rw [levyWeight_eq_tangent_add_decay ht, mul_add]

/-- Every bounded nonnegative measurable profile has its exact extended critical energy limit.
The conclusion includes infinite energy; no integrability of the limiting Lévy weight is assumed. -/
theorem tendsto_suzukiCriticalCompensatedEnergy {D : ℝ → ℝ}
    (hDm : Measurable D) (hDnn : ∀ t, 0 ≤ D t) (hDb : ∃ R, ∀ t, D t ≤ R) :
    Tendsto (suzukiCriticalCompensatedEnergy D) (𝓝[>] 0)
      (𝓝 (suzukiCriticalLimitingCompensatedEnergy D)) := by
  obtain ⟨R, hR⟩ := hDb
  by_cases htop : suzukiCriticalLimitingCompensatedEnergy D = ⊤
  · rw [htop]
    apply lintegral_tendsto_top_of_pointwise
    · intro omega
      exact (hDm.mul ((measurable_suzukiCriticalPrimaryDensity omega).div
        measurable_const)).ennreal_ofReal.aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_suzukiCriticalPrimaryDensity_div ht).const_mul (D t))
    · exact htop
  · have hlev := bounded_compensator_levy_integrable hDm hDnn hR htop
    have hlim := tendsto_integral_compensated_suzukiCriticalPrimaryDensity
      hDm.aestronglyMeasurable (Eventually.of_forall hDnn) hlev
    have hreal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
    have hKnn : ∀ᵐ t ∂volume.restrict (Ioi 0),
        0 ≤ D t * (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (hDnn t) (tangentWeight_nonneg ht)
    have hKm : AEStronglyMeasurable (fun t : ℝ => D t *
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))
        (volume.restrict (Ioi 0)) := (hDm.mul (by fun_prop)).aestronglyMeasurable
    have he : ENNReal.ofReal (∫ t in Ioi 0, D t *
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) =
        suzukiCriticalLimitingCompensatedEnergy D := by
      rw [integral_eq_lintegral_of_nonneg_ae hKnn hKm]
      exact ENNReal.ofReal_toReal htop
    rw [he] at hreal
    apply hreal.congr'
    have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
    filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
    change 0 < omega at homega
    exact ofReal_integral_eq_lintegral_ofReal
      (bounded_compensator_integrable hDm hDnn hR homega (by linarith))
      (bounded_compensator_nonneg hDnn homega)

end
end RHTower
