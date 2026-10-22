import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivativeBoundary
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDyadicResolvent

/-!
# A linear cusp in the literal power-damped residual

A critical zeta zero detects the residual at a distance equal to the damping.
The exact step-source Mellin identity retains the fractional-part correction.
The conclusion concerns finite horizons and assumes neither RH nor admission.
-/

open MeasureTheory Set Filter Topology Complex Finset RHTower
open GaloisForLFunctions.NymanMellin
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The original residual, with no change of weight or centering. -/
def pmPowerDampedDualResidual (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (pmPowerDampedCenteredDivisorPrefix ε n - 1) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

private def cuspStepTail (a : ℕ → ℝ) : ℝ → ℂ :=
  (Ici (1 : ℝ)).indicator (fun x => (a ⌊x⌋₊ : ℂ))

private def cuspStepHead (a : ℕ → ℝ) (u : ℝ) : ℂ := cuspStepTail a (1 / u)

private theorem cuspStepHead_zero (a : ℕ → ℝ) {u : ℝ} (hu : 1 < u) :
    cuspStepHead a u = 0 := by
  unfold cuspStepHead cuspStepTail
  apply indicator_of_notMem
  exact not_le.mpr ((div_lt_one (lt_trans zero_lt_one hu)).mpr hu)

private theorem cuspStepHead_eq (a : ℕ → ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    cuspStepHead a u = (a ⌊1 / u⌋₊ : ℂ) := by
  unfold cuspStepHead cuspStepTail
  apply indicator_of_mem
  exact (le_div_iff₀ hu).mpr (by simpa using hu1)

private theorem measurable_cuspStepHead (a : ℕ → ℝ) : Measurable (cuspStepHead a) :=
  (((Complex.measurable_ofReal.comp
    ((measurable_of_countable a).comp Nat.measurable_floor)).indicator measurableSet_Ici).comp
      (measurable_const.div measurable_id))

private theorem cuspStepTail_energy (a : ℕ → ℝ) :
    (fun x : ℝ => ‖cuspStepTail a x‖ ^ 2 / x ^ 2) =
      (Ici (1 : ℝ)).indicator
        (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2) := by
  funext x
  by_cases hx : x ∈ Ici (1 : ℝ)
  · rw [cuspStepTail, indicator_of_mem hx, indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, div_eq_mul_inv, ← inv_pow]
    rw [sq]
  · simp [cuspStepTail, indicator_of_notMem hx]

private theorem cuspStepHead_integrable {a : ℕ → ℝ}
    (ha : Summable (fun n : ℕ => a (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)))) :
    MemLp (cuspStepHead a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_cuspStepHead a).aestronglyMeasurable]
  change IntegrableOn (fun u => ‖cuspStepTail a (1 / u)‖ ^ 2) (Ioi (0 : ℝ))
  rw [pm_integrable_normSq_reciprocal_iff, cuspStepTail_energy]
  have hi := (integrableOn_stepEnergy_iff_summable a).mpr ha
  have hi' : IntegrableOn (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
  exact ((integrable_indicator_iff measurableSet_Ici).mpr hi').mono_measure
    Measure.restrict_le_self

private theorem cuspStepHead_energy {a : ℕ → ℝ}
    (ha : Summable (fun n : ℕ => a (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)))) :
    (∫ u in Ioi (0 : ℝ), ‖cuspStepHead a u‖ ^ 2) =
      ∑' n : ℕ, a (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  change (∫ u in Ioi (0 : ℝ), ‖cuspStepTail a (1 / u)‖ ^ 2) = _
  rw [pm_integral_normSq_reciprocal, cuspStepTail_energy,
    setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr (show Ici (1 : ℝ) ⊆ Ioi 0 from fun x hx =>
      show 0 < x from lt_of_lt_of_le zero_lt_one hx),
    integral_Ici_eq_integral_Ioi]
  have hi := (integrableOn_stepEnergy_iff_summable a).mpr ha
  have hu : IntegrableOn (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2)
      (⋃ n : ℕ, tailCell n) := by simpa only [iUnion_tailCell] using hi
  have hh := hasSum_integral_iUnion measurableSet_tailCell pairwise_disjoint_tailCell hu
  simp_rw [integral_tailCell_stepGramIntegrand] at hh
  rw [iUnion_tailCell] at hh
  simpa only [sq] using hh.tsum_eq.symm

/-- The literal residual on the reciprocal unit interval. -/
def pmPowerDampedResidualHead (ε : ℝ) : ℝ → ℂ :=
  cuspStepHead (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1)

private theorem dualResidual_eq_range (ε : ℝ) (T : ℕ) :
    pmPowerDampedDualResidual ε T =
      ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold pmPowerDampedDualResidual
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

private theorem residualHead_of_budget {ε C : ℝ}
    (hC : ∀ T : ℕ, pmPowerDampedDualResidual ε T ≤ C) :
    MemLp (pmPowerDampedResidualHead ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ u in Ioi (0 : ℝ), ‖pmPowerDampedResidualHead ε u‖ ^ 2) ≤ C := by
  have hn (n : ℕ) : 0 ≤ (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by positivity
  have hs : Summable (fun n : ℕ => (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    apply summable_of_sum_range_le hn
    intro T
    simpa only [dualResidual_eq_range] using hC T
  have hq : MemLp (cuspStepHead (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1))
      2 (volume.restrict (Ioi (0 : ℝ))) :=
    cuspStepHead_integrable (a := fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) hs
  refine ⟨hq, ?_⟩
  change (∫ u in Ioi (0 : ℝ),
    ‖cuspStepHead (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) u‖ ^ 2) ≤ C
  rw [cuspStepHead_energy (a := fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) hs]
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall fun T => by
    simpa only [dualResidual_eq_range] using hC T)

private theorem residualHead_eq_centered {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 0 < u) :
    pmPowerDampedResidualHead ε u = pmPowerDampedCenteredSource ε u +
      pmPowerDampedDivisorDensity ε * nymanGen 1 u -
        (if u ≤ 1 then (1 : ℂ) else 0) := by
  have hfract := pmPowerDampedDivisorRemainder_eq_centered_prefix hε
    (one_div_pos.mpr hu).le
  change pmPowerDampedResidualHead ε u = pmPowerDampedDivisorRemainder ε (1 / u) + _ - _
  rw [hfract]
  simp only [nymanGen, one_mul]
  by_cases hu1 : u ≤ 1
  · rw [if_pos hu1, pmPowerDampedResidualHead, cuspStepHead_eq _ hu hu1]
    push_cast
    ring
  · rw [if_neg hu1, pmPowerDampedResidualHead, cuspStepHead_zero _ (lt_of_not_ge hu1),
      Nat.floor_eq_zero.mpr ((div_lt_one hu).mpr (lt_of_not_ge hu1))]
    simp [pmPowerDampedCenteredDivisorPrefix]

private theorem residualHead_dyadic {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 0 < u) :
    pmPowerDampedResidualHead ε u - 2 * pmPowerDampedResidualHead ε (2 * u) =
      pmPowerDampedFermiSource ε u + pmPowerDampedDivisorDensity ε * fermiNymanGen 1 u -
        pmSupportedDyadicHaar u := by
  rw [residualHead_eq_centered hε hu, residualHead_eq_centered hε (by positivity),
    pmPowerDampedFermiSource_eq_centered_difference ε hu,
    pmSupportedDyadicHaar_eq_cutoffs hu]
  have hc : (if (2 : ℝ) * u ≤ 1 then (1 : ℂ) else 0) =
      (if u ≤ 1 / 2 then (1 : ℂ) else 0) := by
    congr 1
    apply propext
    constructor <;> intro h <;> linarith
  rw [hc]
  simp only [fermiNymanGen, nymanGen, one_mul, mul_one]
  ring

private theorem fermi_memLp_of_residual {ε : ℝ} (hε : 0 < ε)
    (hq : MemLp (pmPowerDampedResidualHead ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hd : MemLp (fun u => pmPowerDampedResidualHead ε (2 * u)) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
    pm_memLp_pos_dilate (measurable_cuspStepHead _) hq (by norm_num : (0 : ℝ) < 2)
  have hs := (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)).const_mul
    (pmPowerDampedDivisorDensity ε)
  apply (memLp_congr_ae ?_).mp (((hq.sub (hd.const_mul (2 : ℂ))).sub hs).add
    memLp_pmSupportedDyadicHaar)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have h := residualHead_dyadic hε hu
  dsimp only [Pi.add_apply, Pi.sub_apply]
  linear_combination h

/-- The step correction contributes `-r ζ(s)/s`, rather than the continuous pole term. -/
theorem mellin_pmPowerDampedResidualHead {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hq : MemLp (pmPowerDampedResidualHead ε) 2 (volume.restrict (Ioi (0 : ℝ))))
    {s : ℂ} (hs : 1 / 2 < s.re ∧ s.re < 1)
    (hshift : s + (ε : ℂ) ≠ 1) (hz : riemannZeta (s + (ε : ℂ)) ≠ 0) :
    mellin (pmPowerDampedResidualHead ε) s =
      (riemannZeta s / riemannZeta (s + (ε : ℂ)) -
        pmPowerDampedDivisorDensity ε * riemannZeta s - 1) / s := by
  have hf := fermi_memLp_of_residual hε hq
  have hqm := pm_mellinConvergent_of_memLp hq (fun _ hu => cuspStepHead_zero _ hu) hs.1
  have hd : MemLp (fun u => pmPowerDampedResidualHead ε (2 * u)) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
    pm_memLp_pos_dilate (measurable_cuspStepHead _) hq (by norm_num : (0 : ℝ) < 2)
  have hdm := pm_mellinConvergent_of_memLp hd (fun u hu =>
    cuspStepHead_zero _ (by linarith : 1 < 2 * u)) hs.1
  have hfm := mellinConvergent_pmPowerDampedFermiSource ε hf hs.1
  have hsm := pm_mellinConvergent_of_memLp
    (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1))
    (fun _ hu => fermiNymanGen_eq_zero_of_inv_lt (by norm_num) (by simpa using hu)) hs.1
  have hhm := (hasMellin_pmSupportedDyadicHaar (by linarith : 0 < s.re)).1
  have hleft := (hasMellin_sub hqm (hdm.const_smul (2 : ℂ))).2
  have hright := (hasMellin_sub
    (hasMellin_add hfm (hsm.const_smul (pmPowerDampedDivisorDensity ε))).1 hhm).2
  have heq : mellin (fun u => pmPowerDampedResidualHead ε u -
      (2 : ℂ) • pmPowerDampedResidualHead ε (2 * u)) s =
      mellin (fun u => (pmPowerDampedFermiSource ε u +
        pmPowerDampedDivisorDensity ε • fermiNymanGen 1 u) - pmSupportedDyadicHaar u) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [residualHead_dyadic hε hu]
  rw [hleft, hright,
    (hasMellin_add hfm (hsm.const_smul (pmPowerDampedDivisorDensity ε))).2,
    (hasMellin_const_smul hdm (2 : ℂ)).2,
    (hasMellin_const_smul hsm (pmPowerDampedDivisorDensity ε)).2,
    mellin_comp_mul_left _ _ (by norm_num : (0 : ℝ) < 2),
    mellin_fermiNymanGen (by linarith : 0 < s.re) hs.2 (by norm_num : (0 : ℝ) < 1),
    (hasMellin_pmSupportedDyadicHaar (by linarith : 0 < s.re)).2] at heq
  simp only [smul_eq_mul, Complex.ofReal_one, Complex.one_cpow, one_mul] at heq
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith [hs.1])
  have heta : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := one_sub_two_cpow_ne_zero hs.2
  have hp : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  have hfmval := pmPowerDamped_cleared_mellin ε hε hε1 hf hs
  rw [zetaResidueUnit, Function.update_of_ne hshift] at hfmval
  have hm : mellin (pmPowerDampedFermiSource ε) s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s /
        (s * riemannZeta (s + (ε : ℂ))) := by
    apply (eq_div_iff (mul_ne_zero hs0 hz)).mpr
    apply mul_left_cancel₀ (sub_ne_zero.mpr hshift)
    linear_combination hfmval
  rw [hm] at heq
  norm_num only [Complex.ofReal_ofNat] at heq
  rw [← mul_assoc, hp] at heq
  apply mul_left_cancel₀ heta
  field_simp [hs0, hz] at heq ⊢
  linear_combination heq

private theorem residual_mellin_sq_le {ε C : ℝ}
    (hC : ∀ T : ℕ, pmPowerDampedDualResidual ε T ≤ C)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (2 * s.re - 1) * ‖mellin (pmPowerDampedResidualHead ε) s‖ ^ 2 ≤ C := by
  obtain ⟨hq, he⟩ := residualHead_of_budget hC
  have hhead : MemLp (pmPowerDampedResidualHead ε) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hq.mono_measure (Measure.restrict_mono Set.Ioo_subset_Ioi_self le_rfl)
  have hlp := memLp_two_logChartHead (by norm_num : (0 : ℝ) < 1) hhead
  have hb := HTGeometry.norm_laplaceRay_le hlp
    (show 0 < (s - 1 / 2).re by simpa using sub_pos.mpr hs)
  rw [← pm_mellin_eq_head_laplace (f := pmPowerDampedResidualHead ε)
    (fun _ hu => cuspStepHead_zero _ hu)] at hb
  have hden : 2 * (s - 1 / 2).re = 2 * s.re - 1 := by
    have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
    rw [Complex.sub_re, hhalf]
    ring
  rw [hden] at hb
  have hint := hq.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hehead : (∫ u in Ioo (0 : ℝ) 1, ‖pmPowerDampedResidualHead ε u‖ ^ 2) ≤ C :=
    (setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hu => Set.Ioo_subset_Ioi_self hu)).trans he
  have hnorm : HTGeometry.rayL2Norm (logChartHead 1 (pmPowerDampedResidualHead ε)) ^ 2 ≤ C := by
    rw [HTGeometry.rayL2Norm, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
      integral_norm_sq_logChartHead (by norm_num : (0 : ℝ) < 1)]
    exact hehead
  have hp : 0 < 2 * s.re - 1 := by linarith
  have hm := (le_div_iff₀ (Real.sqrt_pos.mpr hp)).mp hb
  have hsq : (‖mellin (pmPowerDampedResidualHead ε) s‖ * Real.sqrt (2 * s.re - 1)) ^ 2 ≤
      HTGeometry.rayL2Norm (logChartHead 1 (pmPowerDampedResidualHead ε)) ^ 2 := by
    simpa only [sq] using
      mul_self_le_mul_self (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hm
  rw [mul_pow, Real.sq_sqrt hp.le] at hsq
  nlinarith

private theorem critical_radial_ratio {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun ε : ℝ => riemannZeta (ρ + (ε : ℂ)) /
        riemannZeta (ρ + 2 * (ε : ℂ))) (𝓝[>] 0) (𝓝 ((1 / 2 : ℂ) ^ m)) ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0, riemannZeta (ρ + 2 * (ε : ℂ)) ≠ 0 := by
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hρ
  have hana := Sieve.analyticAt_riemannZeta_of_ne_one hρ1
  have hnz : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
    intro hz
    apply not_eventually_zetaResidueUnit_eq_zero ρ
    filter_upwards [hz, isOpen_compl_singleton.mem_nhds hρ1] with z hz hz1
    simp [zetaResidueUnit, Function.update_of_ne hz1, hz]
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hfactor' : riemannZeta =ᶠ[𝓝 ρ] (fun z => (z - ρ) ^ m • g z) := hfactor
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      apply hg0
      have hv := hfactor'.eq_of_nhds
      rw [hm, hzero] at hv
      simpa using hv.symm
    · exact hm
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa using tendsto_const_nhds.add hreal
  have hp2 : Tendsto (fun ε : ℝ => ρ + 2 * (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa using tendsto_const_nhds.add (hreal.const_mul 2)
  have hg1 := hg.continuousAt.tendsto.comp hp
  have hg2 := hg.continuousAt.tendsto.comp hp2
  have hg2ne : ∀ᶠ ε : ℝ in 𝓝[>] 0, g (ρ + 2 * (ε : ℂ)) ≠ 0 :=
    hg2.eventually (isOpen_compl_singleton.mem_nhds hg0)
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      riemannZeta (ρ + (ε : ℂ)) / riemannZeta (ρ + 2 * (ε : ℂ)) =
        (1 / 2 : ℂ) ^ m * (g (ρ + (ε : ℂ)) / g (ρ + 2 * (ε : ℂ))) := by
    filter_upwards [hp.eventually hfactor, hp2.eventually hfactor, hg2ne,
      self_mem_nhdsWithin] with ε h1 h2 hgne hε
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε : ε ≠ 0)
    rw [h1, h2]
    simp only [add_sub_cancel_left, smul_eq_mul, mul_pow, div_pow, one_pow]
    field_simp
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, riemannZeta (ρ + 2 * (ε : ℂ)) ≠ 0 := by
    filter_upwards [hp2.eventually hfactor, hg2ne, self_mem_nhdsWithin] with ε h2 hgne hε
    rw [h2]
    simp only [add_sub_cancel_left, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero m (mul_ne_zero (by norm_num)
      (by exact_mod_cast (ne_of_gt hε : ε ≠ 0)))) hgne
  refine ⟨m, hm, ?_, hne⟩
  have hr := (hg1.div hg2 hg0).const_mul ((1 / 2 : ℂ) ^ m)
  simp only [div_self hg0, mul_one] at hr
  apply hr.congr'
  filter_upwards [heq] with ε h
  exact h.symm

private def cuspMellinValue (ρ : ℂ) (ε : ℝ) : ℂ :=
  (riemannZeta (ρ + (ε : ℂ)) / riemannZeta (ρ + 2 * (ε : ℂ)) -
    pmPowerDampedDivisorDensity ε * riemannZeta (ρ + (ε : ℂ)) - 1) / (ρ + (ε : ℂ))

private theorem cuspMellinValue_tendsto {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) {m : ℕ}
    (hratio : Tendsto (fun ε : ℝ => riemannZeta (ρ + (ε : ℂ)) /
      riemannZeta (ρ + 2 * (ε : ℂ))) (𝓝[>] 0) (𝓝 ((1 / 2 : ℂ) ^ m))) :
    Tendsto (cuspMellinValue ρ) (𝓝[>] 0) (𝓝 (((1 / 2 : ℂ) ^ m - 1) / ρ)) := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hρ
  have hp : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have hr : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add hr
  have hz : Tendsto (fun ε : ℝ => riemannZeta (ρ + (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using
      (Sieve.analyticAt_riemannZeta_of_ne_one hρ1).continuousAt.tendsto.comp hp
  have hd : Tendsto pmPowerDampedDivisorDensity (𝓝[>] 0) (𝓝 0) := by
    have hh := (Complex.continuous_ofReal.tendsto 0).comp
      tendsto_pmPowerDampedDivisorDensity_re_zero
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmPowerDampedDivisorDensity_eq_ofReal_re hε).symm
  have hlim := ((hratio.sub (hd.mul hz)).sub_const 1).div hp hρ0
  simp only [mul_zero, sub_zero] at hlim
  convert hlim using 1
  ext ε
  rfl

private theorem critical_cusp_constant_lt {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) :
    1 / (4 * ‖ρ‖ ^ 2) < 2 * ‖((1 / 2 : ℂ) ^ m - 1) / ρ‖ ^ 2 := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have hn : 0 < ‖ρ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hρ0)
  have hpow (k : ℕ) : (1 / 2 : ℝ) ^ k ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; nlinarith
  have hhalf : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [pow_succ]
    nlinarith [hpow k]
  have hc : (1 / 2 : ℂ) ^ m - 1 = (((1 / 2 : ℝ) ^ m - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_div, div_pow, hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hrew : 1 / (4 * ‖ρ‖ ^ 2) = (1 / 4 : ℝ) / ‖ρ‖ ^ 2 := by ring
  rw [hrew, ← mul_div_assoc]
  apply (div_lt_div_iff_of_pos_right hn).mpr
  nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ m - 1 / 2)]

/-- Every sufficiently small positive damping has a finite horizon with a linear residual
cost. A critical zero supplies the explicit positive coefficient; admission is not assumed. -/
theorem exists_criticalZero_linear_dualResidual_floor :
    ∃ ρ : ℂ, ρ.re = 1 / 2 ∧ riemannZeta ρ = 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ∃ T : ℕ, (1 / (4 * ‖ρ‖ ^ 2)) * ε < pmPowerDampedDualResidual ε T := by
  obtain ⟨ρ, hρ, hzero⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  obtain ⟨m, hm, hratio, hne⟩ := critical_radial_ratio hρ hzero
  have hv := cuspMellinValue_tendsto hρ hzero hratio
  have hlarge : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      1 / (4 * ‖ρ‖ ^ 2) < 2 * ‖cuspMellinValue ρ ε‖ ^ 2 :=
    ((hv.norm.pow 2).const_mul 2).eventually
      (lt_mem_nhds (critical_cusp_constant_lt hρ hm))
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ T : ℕ, (1 / (4 * ‖ρ‖ ^ 2)) * ε < pmPowerDampedDualResidual ε T := by
    filter_upwards [hlarge, hne, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds]
      with ε hlarge hne hε hεsmall
    change 0 < ε at hε
    by_contra hnot
    push Not at hnot
    have hs : 1 / 2 < (ρ + (ε : ℂ)).re ∧ (ρ + (ε : ℂ)).re < 1 := by
      simp only [Complex.add_re, Complex.ofReal_re, hρ]
      constructor <;> linarith
    have hshift : ρ + (ε : ℂ) + (ε : ℂ) ≠ 1 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, hρ] at hre
      linarith
    have harg : ρ + (ε : ℂ) + (ε : ℂ) = ρ + 2 * (ε : ℂ) := by ring
    have hζ : riemannZeta (ρ + (ε : ℂ) + (ε : ℂ)) ≠ 0 := by simpa only [harg] using hne
    have hq := (residualHead_of_budget hnot).1
    have hmel := mellin_pmPowerDampedResidualHead hε (by linarith) hq hs hshift hζ
    have hval : mellin (pmPowerDampedResidualHead ε) (ρ + (ε : ℂ)) =
        cuspMellinValue ρ ε := by simpa only [cuspMellinValue, harg] using hmel
    have hb := residual_mellin_sq_le hnot hs.1
    rw [hval] at hb
    simp only [Complex.add_re, Complex.ofReal_re, hρ] at hb
    have hpositive := mul_pos hε (sub_pos.mpr hlarge)
    nlinarith
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨ρ, hρ, hzero, δ, hδ, fun ε hε hεδ => hsub ⟨hε, hεδ⟩⟩

/-- An unconditional positive linear floor for the original finite-horizon residual. -/
theorem exists_positive_linear_dualResidual_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ T : ℕ, κ * ε < pmPowerDampedDualResidual ε T := by
  obtain ⟨ρ, hρ, _, δ, hδ, h⟩ := exists_criticalZero_linear_dualResidual_floor
  have hρ0 : ρ ≠ 0 := by intro he; simp [he] at hρ
  exact ⟨1 / (4 * ‖ρ‖ ^ 2), by positivity, δ, hδ, h⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
