import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivativeMellin
import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection
import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree

/-!
# Canonical Hilbert obstruction for the power-damping tangent

The actual dyadic Chebyshev source is not canonically L²: a critical zero
forces a nonzero boundary residue, while the Hilbert Mellin estimate forces
that residue to vanish. The actual damping quotients have no finite eventual
canonical L² budget, despite their certified strong L¹ convergence.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower
theorem pmDyadicChebyshevSource_cleared_mellin
    (hf : MemLp pmDyadicChebyshevSource 2 (volume.restrict (Ioi 0)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    s * (s - 1) * zetaResidueUnit s * mellin pmDyadicChebyshevSource s =
      -(1 - (2 : ℂ) ^ (1 - s)) *
        ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) := by
  let S : Set ℂ := {z | 1 / 2 < z.re}
  have hF := pm_analyticOnNhd_mellin_of_memLp hf
    (fun _ ht => pmDyadicChebyshevSource_eq_zero_of_one_lt ht)
  have hleft : AnalyticOnNhd ℂ (fun z => z * (z - 1) * zetaResidueUnit z *
      mellin pmDyadicChebyshevSource z) S := by
    intro z hz
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
      (analyticAt_zetaResidueUnit z)).mul (hF z hz)
  have hright : AnalyticOnNhd ℂ (fun z => -(1 - (2 : ℂ) ^ (1 - z)) *
      ((z - 1) * deriv zetaResidueUnit z - zetaResidueUnit z)) S := by
    intro z _
    have hp : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) z := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
    exact ((analyticAt_const.sub hp).neg).mul
      (((analyticAt_id.sub analyticAt_const).mul (analyticAt_zetaResidueUnit z).deriv).sub
        (analyticAt_zetaResidueUnit z))
  have hinit (z : ℂ) (hz : 1 < z.re) :
      z * (z - 1) * zetaResidueUnit z * mellin pmDyadicChebyshevSource z =
        -(1 - (2 : ℂ) ^ (1 - z)) *
          ((z - 1) * deriv zetaResidueUnit z - zetaResidueUnit z) := by
    have hz1 : z ≠ 1 := fun h => (ne_of_gt hz) (congrArg Complex.re h)
    have hz0 : z ≠ 0 := ne_zero_of_re_pos (lt_trans zero_lt_one hz)
    have hU : zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit, Function.update_of_ne hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re hz)
    rw [(hasMellin_pmDyadicChebyshevSource hz).2, logDeriv_zeta_eq hz1 hU, logDeriv_apply]
    field_simp
  have hevent : (fun z => z * (z - 1) * zetaResidueUnit z *
      mellin pmDyadicChebyshevSource z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => -(1 - (2 : ℂ) ^ (1 - z)) *
        ((z - 1) * deriv zetaResidueUnit z - zetaResidueUnit z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    exact hinit z hz
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (by change (1 / 2 : ℝ) < (2 : ℂ).re; norm_num : (2 : ℂ) ∈ S) hevent hs

theorem pm_mellin_L2_boundary_decay {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi 0)))
    (hsupp : ∀ t : ℝ, 1 < t → f t = 0) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    Tendsto (fun x : ℝ => (x : ℂ) * mellin f (ρ + (x : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  let C := GaloisForLFunctions.HTGeometry.rayL2Norm (logChartHead 1 f)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hhead : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hf.mono_measure (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
  have hlp := memLp_two_logChartHead (by norm_num : (0 : ℝ) < 1) hhead
  have hbound : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ),
      ‖(x : ℂ) * mellin f (ρ + (x : ℂ))‖ ≤ C * Real.sqrt x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    have hre : (ρ + (x : ℂ) - 1 / 2).re = x := by simp [hρ]
    have hb := GaloisForLFunctions.HTGeometry.norm_laplaceRay_le hlp
      (show 0 < (ρ + (x : ℂ) - 1 / 2).re by rw [hre]; exact hx)
    rw [hre, ← pm_mellin_eq_head_laplace hsupp] at hb
    change ‖mellin f (ρ + (x : ℂ))‖ ≤ C / Real.sqrt (2 * x) at hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    calc
      _ ≤ x * (C / Real.sqrt (2 * x)) := mul_le_mul_of_nonneg_left hb hx.le
      _ ≤ C * Real.sqrt x := by
        rw [← mul_div_assoc, div_le_iff₀ (Real.sqrt_pos.2 (by linarith : 0 < 2 * x))]
        have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
        have hprod : x ≤ Real.sqrt x * Real.sqrt (2 * x) := by
          calc
            x = Real.sqrt x * Real.sqrt x := hsq.symm
            _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
              (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hprod hC]
  apply squeeze_zero_norm' hbound
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simpa using h.const_mul C


theorem not_memLp_pmDyadicChebyshevSource :
    ¬ MemLp pmDyadicChebyshevSource 2 (volume.restrict (Ioi 0)) := by
  intro hf
  obtain ⟨ρ, hρ, hζ⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hρ
  have hana := analyticAt_zetaResidueUnit ρ
  have hnz := not_eventually_zetaResidueUnit_eq_zero ρ
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hfactor' : zetaResidueUnit =ᶠ[𝓝 ρ] (fun z => (z - ρ) ^ m • g z) := hfactor
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      apply hg0
      have hv := hfactor'.eq_of_nhds
      rw [hm] at hv
      simpa [zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hζ] using hv.symm
    · exact hm
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpath0 : Tendsto (fun x : ℝ => ρ + (x : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa using tendsto_const_nhds.add hreal
  have hpath : Tendsto (fun x : ℝ => ρ + (x : ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hpath0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    change ρ + (x : ℂ) ≠ ρ
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re] at hr
    linarith
  have hres : Tendsto (fun x : ℝ => (x : ℂ) * logDeriv zetaResidueUnit (ρ + (x : ℂ)))
      (𝓝[>] 0) (𝓝 (m : ℂ)) := by
    have h := (logDeriv_residue_of_factorization hg hg0 hfactor').comp hpath
    exact h.congr (fun x => by dsimp; ring)
  have hcorr : Tendsto (fun x : ℝ => (x : ℂ) * (ρ + (x : ℂ) - 1)⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hreal.mul ((hpath0.sub_const 1).inv₀ (sub_ne_zero.mpr hρ1))
  have hp : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - z)) ρ := by
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
  have hB : Tendsto (fun x : ℝ => -((1 - (2 : ℂ) ^ (1 - (ρ + (x : ℂ)))) / (ρ + (x : ℂ))))
      (𝓝[>] 0) (𝓝 (-((1 - (2 : ℂ) ^ (1 - ρ)) / ρ))) :=
    ((((analyticAt_const.sub hp).div analyticAt_id hρ0).neg).continuousAt.tendsto).comp hpath0
  have hprod := hB.mul (hres.sub hcorr)
  have heq : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ),
      -((1 - (2 : ℂ) ^ (1 - (ρ + (x : ℂ)))) / (ρ + (x : ℂ))) *
        ((x : ℂ) * logDeriv zetaResidueUnit (ρ + (x : ℂ)) -
          (x : ℂ) * (ρ + (x : ℂ) - 1)⁻¹) =
      (x : ℂ) * mellin pmDyadicChebyshevSource (ρ + (x : ℂ)) := by
    have hUne := hana.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
    have h1 : ∀ᶠ (z : ℂ) in 𝓝 ρ, z ≠ 1 :=
      isOpen_compl_singleton.mem_nhds hρ1
    filter_upwards [self_mem_nhdsWithin, hpath.eventually hUne, hpath0.eventually h1]
      with x hx hUx hx1
    change 0 < x at hx
    let s : ℂ := ρ + (x : ℂ)
    have hs : 1 / 2 < s.re := by change (1 / 2 : ℝ) < ρ.re + x; linarith
    have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hUs : zetaResidueUnit s ≠ 0 := hUx
    have hF : mellin pmDyadicChebyshevSource s =
        -((1 - (2 : ℂ) ^ (1 - s)) / s) *
          (logDeriv zetaResidueUnit s - (s - 1)⁻¹) := by
      apply mul_left_cancel₀ (show s * (s - 1) * zetaResidueUnit s ≠ 0 from
        mul_ne_zero (mul_ne_zero hs0 hs1) hUs)
      rw [pmDyadicChebyshevSource_cleared_mellin hf hs, logDeriv_apply]
      field_simp
    change -((1 - (2 : ℂ) ^ (1 - s)) / s) *
      ((x : ℂ) * logDeriv zetaResidueUnit s - (x : ℂ) * (s - 1)⁻¹) =
      (x : ℂ) * mellin pmDyadicChebyshevSource s
    rw [hF]
    ring
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) * mellin pmDyadicChebyshevSource (ρ + (x : ℂ)))
      (𝓝[>] 0) (𝓝 (-((1 - (2 : ℂ) ^ (1 - ρ)) / ρ) * (m : ℂ))) := by
    simpa only [sub_zero] using hprod.congr' heq
  have hzero := pm_mellin_L2_boundary_decay hf
    (fun _ ht => pmDyadicChebyshevSource_eq_zero_of_one_lt ht) hρ
  have hbad := tendsto_nhds_unique hzero hlim
  have hnonzero : -((1 - (2 : ℂ) ^ (1 - ρ)) / ρ) * (m : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (div_ne_zero (one_sub_two_cpow_ne_zero (by linarith)) hρ0)
    · exact_mod_cast (show m ≠ 0 by omega)
  exact hnonzero hbad.symm


theorem not_memLp_pmDyadicChebyshevSource_carrier :
    ¬ MemLp pmDyadicChebyshevSource 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  intro hf
  apply not_memLp_pmDyadicChebyshevSource
  apply (memLp_two_iff_integrable_sq_norm
    measurable_pmDyadicChebyshevSource.aestronglyMeasurable).mpr
  have hh : IntegrableOn (fun t => ‖pmDyadicChebyshevSource t‖ ^ (2 : ℕ)) (Ioc (0 : ℝ) 1) :=
    hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have ht : IntegrableOn (fun t => ‖pmDyadicChebyshevSource t‖ ^ (2 : ℕ)) (Ioi (1 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro t ht
    change (0 : ℝ) = ‖pmDyadicChebyshevSource t‖ ^ (2 : ℕ)
    rw [pmDyadicChebyshevSource_eq_zero_of_one_lt ht, norm_zero, zero_pow (by norm_num)]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)]
  exact hh.union ht

theorem pmPowerDampedDifferenceQuotient_no_eventual_L2_budget (C : ℝ) :
    ¬ ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
      eLpNorm (pmPowerDampedDifferenceQuotient ε) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ENNReal.ofReal C := by
  intro hbound
  have hnorm : eLpNorm pmDyadicChebyshevSource 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto hbound
      (fun ε => (measurable_pmPowerDampedDifferenceQuotient ε).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact tendsto_pmPowerDampedDifferenceQuotient ht
  exact not_memLp_pmDyadicChebyshevSource_carrier
    ⟨measurable_pmDyadicChebyshevSource.aestronglyMeasurable,
      hnorm.trans_lt ENNReal.ofReal_lt_top⟩

theorem pmPowerDampedDifferenceQuotient_L2_norm_exceeds (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ENNReal.ofReal C <
      eLpNorm (pmPowerDampedDifferenceQuotient ε) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  by_contra hn
  apply pmPowerDampedDifferenceQuotient_no_eventual_L2_budget C
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
  exact le_of_not_gt (fun h => hn ⟨ε, hε, hεδ, h⟩)

end RHTower
