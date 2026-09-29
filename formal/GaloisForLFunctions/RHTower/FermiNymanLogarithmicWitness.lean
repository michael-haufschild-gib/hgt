import GaloisForLFunctions.RHTower.FermiNymanWitnessMellin
import GaloisForLFunctions.RHTower.MellinIteratedDerivative

/-!
# Logarithmic witnesses of the alternating Nyman–Beurling source

Every logarithmic Mellin jet below the analytic order of a right-strip zeta zero is a continuous
square-integrable witness of the literal alternating generators. Bounded source densities with
bounded right support admit all logarithmic Mellin derivatives. The generator Mellin transform
factors as an analytic source unit times zeta, so its jets vanish to at least the zeta order.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
noncomputable section
namespace RHTower

theorem mellinRapid_of_bounded_rightSupport {f : ℝ → ℂ} (hf : Measurable f)
    {M c : ℝ} (hb : ∀ t, ‖f t‖ ≤ M) (hc : 0 < c) (hs : ∀ t, c < t → f t = 0) :
    MellinRapid f := by
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le]
    apply IntegrableOn.union
    · exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
        (Filter.Eventually.of_forall hb)
    · exact (integrableOn_zero).congr_fun (fun t ht => (hs t ht).symm) measurableSet_Ioi
  refine ⟨hi.locallyIntegrableOn, ?_, ?_⟩
  · intro a
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop c] with t ht
    rw [hs t ht, norm_zero, zero_mul]
  · intro b hb0
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    have hM : 0 ≤ M := (norm_nonneg (f t)).trans (hb t)
    have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by linarith : -b ≤ 0)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_pos_of_pos ht _).le]
    exact (hb t).trans (by nlinarith)

theorem mellinRapid_fermiNymanGen {a : ℝ} (ha : 0 < a) : MellinRapid (fermiNymanGen a) :=
  mellinRapid_of_bounded_rightSupport (measurable_fermiNymanGen a) (norm_fermiNymanGen_le a)
    (one_div_pos.mpr ha) (fun _ ht => fermiNymanGen_eq_zero_of_inv_lt ha ht)

/-- The logarithmic power function `(log t)^j t^(z-1)`. -/
def logPowerWitness (z : ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ((Real.log t : ℝ) : ℂ) ^ j * powerWitness z t

theorem continuousOn_logPowerWitness (z : ℂ) (j : ℕ) :
    ContinuousOn (logPowerWitness z j) (Ioc (0 : ℝ) 1) := by
  exact ((Complex.continuous_ofReal.comp_continuousOn
    (Real.continuousOn_log.mono (fun t ht => Set.mem_compl_singleton_iff.mpr (ne_of_gt ht.1)))).pow j).mul
      (continuousOn_powerWitness z)

theorem MellinRapid.mellinConvergent {f : ℝ → ℂ} (hf : MellinRapid f) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow hf.loc (hf.top (s.re + 1)) (by linarith)
    (hf.bot (s.re / 2) (by linarith)) (by linarith)

theorem mellinRapid_unitIndicator : MellinRapid (unitExt (fun _ => (1 : ℂ))) := by
  refine mellinRapid_of_bounded_rightSupport
    (measurable_unitExt_of_continuousOn continuousOn_const) (M := 1) ?_ zero_lt_one ?_
  · intro t
    unfold unitExt
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, norm_one]
    · rw [Set.indicator_of_notMem ht, norm_zero]; exact zero_le_one
  · intro t ht
    exact unitExt_eq_zero_of_one_lt ht

theorem integrableOn_normSq_logPowerWitness {z : ℂ} (hz : 1 / 2 < z.re) (j : ℕ) :
    IntegrableOn (fun t => ‖logPowerWitness z j t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have hi : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (((2 * z.re - 1 : ℝ) : ℂ) - 1) •
        logWeighted (unitExt (fun _ => (1 : ℂ))) (2 * j) t) (Ioi 0) :=
    (mellinRapid_unitIndicator.logWeighted (2 * j)).mellinConvergent
    (s := ((2 * z.re - 1 : ℝ) : ℂ)) (by simp; linarith)
  have hin : IntegrableOn (fun t : ℝ =>
      ‖(t : ℂ) ^ (((2 * z.re - 1 : ℝ) : ℂ) - 1) •
        logWeighted (unitExt (fun _ => (1 : ℂ))) (2 * j) t‖) (Ioi 0) := hi.norm
  refine (hin.mono_set Ioc_subset_Ioi_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
  change ‖(t : ℂ) ^ (((2 * z.re - 1 : ℝ) : ℂ) - 1) •
    logWeighted (unitExt (fun _ => (1 : ℂ))) (2 * j) t‖ = ‖logPowerWitness z j t‖ ^ 2
  rw [logWeighted, unitExt, Set.indicator_of_mem ht]
  simp only [logPowerWitness, powerWitness, norm_smul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one, Complex.ofReal_re,
    Complex.sub_re, Complex.one_re, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  rw [mul_pow, ← pow_mul]
  have hp := Real.rpow_mul ht.1.le (z.re - 1) (2 : ℝ)
  norm_num only [Real.rpow_ofNat] at hp
  rw [← hp, show 2 * z.re - 1 - 1 = (z.re - 1) * (2 : ℝ) by ring]
  simp [mul_comm]

theorem logPowerWitness_pairing {a : ℝ} (ha : 1 ≤ a) {ρ : ℂ} (hρ : 0 < ρ.re)
    (hne : ρ ≠ 1) (j : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t *
      (starRingEnd ℂ) (logPowerWitness ((starRingEnd ℂ) ρ) j t)) =
        iteratedDeriv j (fermiNymanMellinRHS a) ρ := by
  have ha0 := lt_of_lt_of_le one_pos ha
  have heq : mellin (fermiNymanGen a) =ᶠ[𝓝 ρ] fermiNymanMellinRHS a := by
    filter_upwards [isOpen_puncturedRightHalfPlane.mem_nhds ⟨hρ, hne⟩] with z hz
    exact mellin_fermiNymanGen_of_mem ha0 hz
  rw [← heq.iteratedDeriv_eq j, iteratedDeriv_mellin (mellinRapid_fermiNymanGen ha0) j hρ]
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [logPowerWitness, powerWitness, map_mul, map_pow, Complex.conj_ofReal,
      conj_ofReal_cpow ht.1, map_sub, map_one, Complex.conj_conj, logWeighted,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_pow]
    ring
  · intro t ht
    have ht1 : 1 < t := by
      rcases ht with ⟨ht0, htn⟩
      simp only [mem_Ioc, not_and, not_le] at htn
      exact htn ht0
    have hcut : 1 / a < t := lt_of_le_of_lt ((div_le_one ha0).2 ha) ht1
    simp [logWeighted, fermiNymanGen_eq_zero_of_inv_lt ha0 hcut]

def fermiNymanSourceUnit (a : ℝ) (s : ℂ) : ℂ :=
  -((a : ℂ) ^ (-s) * (1 - (2 : ℂ) ^ (1 - s)) / s)

theorem analyticAt_fermiNymanSourceUnit {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (fermiNymanSourceUnit a) s := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hA : Differentiable ℂ (fun z : ℂ => (a : ℂ) ^ (-z)) :=
    fun _ => (differentiableAt_id.neg).const_cpow (Or.inl ha0)
  have hB : Differentiable ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - z)) :=
    fun _ => ((differentiableAt_const _).sub differentiableAt_id).const_cpow
      (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  exact (((hA.analyticAt s).mul (analyticAt_const.sub (hB.analyticAt s))).div
    analyticAt_id hs).neg

theorem fermiNymanMellinRHS_eq_unit_mul_zeta (a : ℝ) :
    fermiNymanMellinRHS a = fermiNymanSourceUnit a * riemannZeta := by
  funext s
  unfold fermiNymanMellinRHS fermiNymanSourceUnit
  simp only [Pi.mul_apply]
  ring

/-- Every logarithmic jet below the zeta order is a literal Fermi witness. -/
theorem isFermiNymanWitness_logPower_of_order {ρ : ℂ}
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) (j : ℕ)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    IsFermiNymanWitness (logPowerWitness ((starRingEnd ℂ) ρ) j) := by
  have hρ0 : ρ ≠ 0 := by intro h; subst ρ; simp at h1; linarith
  have hρ1 : ρ ≠ 1 := by intro h; subst ρ; simp at h2
  have hζa : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  refine ⟨continuousOn_logPowerWitness _ _, integrableOn_normSq_logPowerWitness
    (by simpa only [Complex.conj_re] using h1) j, fun a ha => ?_⟩
  rw [logPowerWitness_pairing ha (by linarith) hρ1]
  have hua := analyticAt_fermiNymanSourceUnit (lt_of_lt_of_le one_pos ha) hρ0
  have hFA : AnalyticAt ℂ (fermiNymanMellinRHS a) ρ := by
    rw [fermiNymanMellinRHS_eq_unit_mul_zeta]
    exact hua.mul hζa
  have horder : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fermiNymanMellinRHS a) ρ := by
    rw [fermiNymanMellinRHS_eq_unit_mul_zeta, analyticOrderAt_mul hua hζa]
    exact hj.trans (le_add_of_nonneg_left (by exact zero_le))
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hFA).1 horder j (by omega)

end RHTower
