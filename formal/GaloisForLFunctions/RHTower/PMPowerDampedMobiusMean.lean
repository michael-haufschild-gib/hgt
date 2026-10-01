import GaloisForLFunctions.RHTower.PMPowerDampedMobiusNormFloor
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Canonical mean of the power-damped Möbius Fermi source

Every positive damping admits the literal source in L¹. Its exact mean is
`log 2 / ζ(1+ε)` and its first mean slope at zero is `log 2`.
The final identity separates the admitted L² energy from the Haar error.
No small-positive L² admission or upper energy bound is assumed or proved.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem pm_integrable_fermiNymanGen {a : ℝ} (ha : 0 < a) :
    Integrable (fermiNymanGen a) (volume.restrict (Ioi (0 : ℝ))) := by
  have hsq : Integrable (fun t => ‖fermiNymanGen a t‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_pm_fermiNymanGen ha).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply (hsq.ofReal (𝕜 := ℂ)).neg.congr
  exact Eventually.of_forall (fun t => by
    change -((‖fermiNymanGen a t‖ ^ 2 : ℝ) : ℂ) = fermiNymanGen a t
    rw [pm_fermiNymanGen_norm_sq_eq_neg, neg_neg])

theorem pm_integral_fermiNymanGen {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), fermiNymanGen a t) = -((Real.log 2 / a : ℝ) : ℂ) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), -((‖fermiNymanGen a t‖ ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by dsimp only [Pi.neg_apply]; rw [pm_fermiNymanGen_norm_sq_eq_neg, neg_neg])
    _ = -((∫ t in Ioi (0 : ℝ), ‖fermiNymanGen a t‖ ^ 2 : ℝ) : ℂ) := by
      rw [integral_neg, integral_complex_ofReal]
    _ = _ := by rw [pm_integral_normSq_fermiNymanGen ha]

theorem pm_hasMellin_fermiNymanGen_one :
    HasMellin (fermiNymanGen 1) 1 (-(Real.log 2 : ℂ)) := by
  constructor
  · simpa only [MellinConvergent, IntegrableOn, sub_self, Complex.cpow_zero, one_smul] using
      pm_integrable_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  · simpa only [mellin, sub_self, Complex.cpow_zero, one_smul, div_one] using
      pm_integral_fermiNymanGen (by norm_num : (0 : ℝ) < 1)

theorem hasMellin_pmPowerDampedFermiSource_one {ε : ℝ} (hε : 0 < ε) :
    HasMellin (pmPowerDampedFermiSource ε) 1
      ((Real.log 2 : ℂ) / riemannZeta (1 + (ε : ℂ))) := by
  have hs : 1 < (1 : ℂ).re + ε := by simpa only [Complex.one_re] using (lt_add_of_pos_right 1 hε)
  have h := pmWeightedDilationSource_hasMellin (pmPowerDampedMobiusCoeff ε)
    (fermiNymanGen 1) (pmPowerDampedMobiusCoeff_zero ε)
    (pmPowerDampedMobiusCoeff_lSeriesSummable ε hs) pm_hasMellin_fermiNymanGen_one.1
  have hneg : mellin (pmPowerDampedFermiSource ε) 1 =
      -mellin (pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1)) 1 := by
    unfold mellin
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ ((1 : ℂ) - 1) • pmPowerDampedFermiSource ε t =
      -((t : ℂ) ^ ((1 : ℂ) - 1) •
        pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1) t)
    rw [pmPowerDampedFermiSource_eq_dilation ε ht, smul_neg]
  constructor
  · apply h.1.neg.congr_fun _ measurableSet_Ioi
    intro t ht
    change -((t : ℂ) ^ ((1 : ℂ) - 1) •
      pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1) t) =
        (t : ℂ) ^ ((1 : ℂ) - 1) • pmPowerDampedFermiSource ε t
    rw [pmPowerDampedFermiSource_eq_dilation ε ht, smul_neg]
  · rw [hneg, h.2, pmPowerDampedMobiusCoeff_lSeries ε hs, pm_hasMellin_fermiNymanGen_one.2]
    simp only [div_eq_mul_inv]
    ring

/-- Every positive damping admits the literal source in canonical L¹. -/
theorem integrable_pmPowerDampedFermiSource {ε : ℝ} (hε : 0 < ε) :
    Integrable (pmPowerDampedFermiSource ε) (volume.restrict (Ioi (0 : ℝ))) := by
  simpa only [MellinConvergent, IntegrableOn, sub_self, Complex.cpow_zero, one_smul] using
    (hasMellin_pmPowerDampedFermiSource_one hε).1

/-- The canonical mean is exact throughout the positive damping range. -/
theorem pmPowerDampedFermiSource_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi (0 : ℝ), pmPowerDampedFermiSource ε t) =
      (Real.log 2 : ℂ) / riemannZeta (1 + (ε : ℂ)) := by
  simpa only [mellin, sub_self, Complex.cpow_zero, one_smul] using
    (hasMellin_pmPowerDampedFermiSource_one hε).2

theorem tendsto_pmPowerDampedFermiSource_mean_div_parameter :
    Tendsto (fun ε : ℝ => (∫ t in Ioi (0 : ℝ), pmPowerDampedFermiSource ε t) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (Real.log 2 : ℂ)) := by
  have hz : Tendsto (fun ε : ℝ => 1 + (ε : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun ε : ℝ => 1 + (ε : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu := zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hz
  rw [zetaResidueUnit_one] at hu
  have h : Tendsto (fun ε : ℝ => (Real.log 2 : ℂ) / zetaResidueUnit (1 + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (Real.log 2 : ℂ)) := by
    convert (tendsto_const_nhds (x := (Real.log 2 : ℂ))).div hu
      (by norm_num : (1 : ℂ) ≠ 0) using 1
    · funext ε
      rfl
    · simp only [div_one]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpos : 0 < ε := hε
  have he : 1 + (ε : ℂ) ≠ 1 := by
    intro he
    have hzero : (ε : ℂ) = 0 := by linear_combination he
    exact (ne_of_gt hpos) (Complex.ofReal_eq_zero.mp hzero)
  have hunit : zetaResidueUnit (1 + (ε : ℂ)) =
      (ε : ℂ) * riemannZeta (1 + (ε : ℂ)) := by
    rw [zetaResidueUnit, Function.update_of_ne he]
    congr 1
    ring
  rw [pmPowerDampedFermiSource_integral hpos, hunit, div_div]
  congr 1
  ring

theorem pmPowerDampedFermiSource_first_band (ε : ℝ) {t : ℝ}
    (ht : t ∈ Ioc (1 / 2 : ℝ) 1) : pmPowerDampedFermiSource ε t = 1 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hN : ⌊1 / t⌋₊ ≤ 1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ ht0).2 (by linarith [ht.1])
  rw [pmPowerDampedFermiSource_eq_sum ε ht0 hN]
  simp only [Finset.Icc_self, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, Nat.cast_one, Real.one_rpow, one_mul, Complex.ofReal_one]
  rw [pm_fermiNymanGen_first_band (by norm_num : (0 : ℝ) < 1) ht0
    (by simpa using ht.1) (by simpa using ht.2)]
  simp

theorem memLp_pm_dyadicHaar : MemLp dyadicHaar 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  refine ⟨measurable_dyadicHaar.aestronglyMeasurable, ?_⟩
  rw [pm_eLpNorm_dyadicHaar]
  norm_num

theorem pm_integral_dyadicHaar : (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t) = 0 := by
  simpa using integral_dyadicHaar_mul_cpow (s := (1 : ℂ)) (by norm_num)

theorem pmPowerDampedFermiSource_integral_carrier {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioc (0 : ℝ) 1, pmPowerDampedFermiSource ε t) =
      (Real.log 2 : ℂ) / riemannZeta (1 + (ε : ℂ)) := by
  rw [← pmPowerDampedFermiSource_integral hε]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ ht => ht.1)
  intro t ht
  exact pmPowerDampedFermiSource_eq_zero_of_one_lt ε (by
    have hnot := ht.2
    simp only [mem_Ioc, not_and] at hnot
    exact lt_of_not_ge (hnot ht.1))

theorem pmPowerDampedFermiSource_error_energy_identity {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ t in Ioc (0 : ℝ) 1, ‖pmPowerDampedFermiSource ε t - dyadicHaar t‖ ^ 2) =
      (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedFermiSource ε t‖ ^ 2) - 1 +
        2 * ((Real.log 2 : ℂ) / riemannZeta (1 + (ε : ℂ))).re := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hsmall := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hsquare := hsmall.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hmean := (integrable_pmPowerDampedFermiSource hε).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have hH := memLp_pm_dyadicHaar.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖pmPowerDampedFermiSource ε t - dyadicHaar t‖ ^ 2 =
      ‖pmPowerDampedFermiSource ε t‖ ^ 2 + 2 * (pmPowerDampedFermiSource ε t).re -
        1 - 2 * (dyadicHaar t).re := by
    by_cases hhalf : t ≤ 1 / 2
    · rw [dyadicHaar, if_pos hhalf]
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
      ring
    · rw [pmPowerDampedFermiSource_first_band ε ⟨lt_of_not_ge hhalf, ht.2⟩,
        dyadicHaar, if_neg hhalf]
      norm_num
  have hmeanR : (∫ t in Ioc (0 : ℝ) 1, (pmPowerDampedFermiSource ε t).re) =
      ((Real.log 2 : ℂ) / riemannZeta (1 + (ε : ℂ))).re := by
    calc
      _ = (∫ t in Ioc (0 : ℝ) 1, pmPowerDampedFermiSource ε t).re := integral_re hmean
      _ = _ := by rw [pmPowerDampedFermiSource_integral_carrier hε]
  have hHR : (∫ t in Ioc (0 : ℝ) 1, (dyadicHaar t).re) = 0 := by
    calc
      _ = (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t).re := integral_re hH
      _ = _ := by rw [pm_integral_dyadicHaar, Complex.zero_re]
  have henergy : (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedFermiSource ε t‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1, ‖pmPowerDampedFermiSource ε t‖ ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    intro t ht
    have hgt : 1 < t := by
      have hnot := ht.2
      simp only [mem_Ioc, not_and] at hnot
      exact lt_of_not_ge (hnot ht.1)
    rw [pmPowerDampedFermiSource_eq_zero_of_one_lt ε hgt, norm_zero, zero_pow (by decide)]
  rw [setIntegral_congr_fun measurableSet_Ioc hpoint]
  erw [integral_sub ((hsquare.add (hmean.re.const_mul 2)).sub (integrable_const 1))
      (hH.re.const_mul 2),
    integral_sub (hsquare.add (hmean.re.const_mul 2)) (integrable_const 1),
    integral_add hsquare (hmean.re.const_mul 2), integral_const_mul,
    integral_const_mul, hmeanR, hHR, integral_const, henergy]
  simp
  ring

end RHTower
