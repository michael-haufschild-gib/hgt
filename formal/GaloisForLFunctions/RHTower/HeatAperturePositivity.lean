import GaloisForLFunctions.RHTower.HeatDoubleSum

/-!
# Strict positivity of the additive heat aperture

The Fourier multiplier of the additive heat kernel is strictly positive, and the boundary germ
carries at least the mass of its first mode.  Hence the heat aperture energy is a strictly
positive real number for every finite aperture, with no zeta value entering its definition.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- **The heat multiplier is strictly positive.**  Immediate from the Poisson form. -/
theorem heatMultiplierValue_pos {x : ℝ} (hx : 0 < x) (θ : ℝ) : 0 < heatMultiplierValue x θ := by
  rw [heatMultiplierValue]
  refine mul_pos (Real.rpow_pos_of_pos hx _) ?_
  exact lt_of_lt_of_le (heatGauss_pos x 0 θ)
    ((summable_heatGauss hx θ).le_tsum 0 fun j _ => (heatGauss_pos x j θ).le)

theorem memLp_expMode (m : ℤ) :
    MemLp (fun θ : ℝ => Complex.exp (I * (m : ℂ) * (θ : ℂ))) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1 ?_
  filter_upwards with θ
  rw [norm_exp_I_mul_real]

theorem integral_expMode_normSq (m : ℤ) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖Complex.exp (I * (m : ℂ) * (θ : ℂ))‖ ^ 2)
      = 2 * Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : ∀ θ : ℝ, ‖Complex.exp (I * (m : ℂ) * (θ : ℂ))‖ ^ 2 = (1 : ℝ) := by
    intro θ
    rw [norm_exp_I_mul_real, one_pow]
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => h θ, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, Real.volume_real_Ioc, max_eq_left (by linarith)]
  ring

theorem one_mem_modeSet {N : ℕ} (hN : 1 ≤ N) : (1 : ℤ) ∈ modeSet N := by
  rw [modeSet, Finset.mem_map]
  exact ⟨0, Finset.mem_range.mpr hN, by simp⟩

/-- The first Fourier coefficient of a truncation is `1`. -/
theorem integral_dirichletTrunc_mul_expNeg (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        dirichletTrunc s N θ * Complex.exp (I * ((-1 : ℤ) : ℂ) * (θ : ℂ)))
      = 2 * Real.pi := by
  have hterm : ∀ θ : ℝ, dirichletTrunc s N θ * Complex.exp (I * ((-1 : ℤ) : ℂ) * (θ : ℂ))
      = ∑ n ∈ modeSet N,
        (((n : ℝ)) : ℂ) ^ (-s) * Complex.exp (I * ((n - 1 : ℤ) : ℂ) * (θ : ℂ)) := by
    intro θ
    rw [dirichletTrunc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => hterm θ,
    MeasureTheory.integral_finsetSum _
      (fun n _ => ((integrableOn_exp_int_mul (n - 1)).const_mul _))]
  rw [Finset.sum_eq_single_of_mem (1 : ℤ) (one_mem_modeSet hN)]
  · rw [MeasureTheory.integral_const_mul, show ((1 : ℤ) - 1) = (0 : ℤ) by ring,
      setIntegral_exp_int_mul 0, if_pos rfl]
    norm_num
  · intro n _ hne
    rw [MeasureTheory.integral_const_mul, setIntegral_exp_int_mul (n - 1),
      if_neg (by omega), mul_zero]

/-- **The first Fourier coefficient of the boundary germ is `1`.** -/
theorem integral_phaseGerm_mul_expNeg {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        phaseGerm s θ * Complex.exp (I * ((-1 : ℤ) : ℂ) * (θ : ℂ)))
      = 2 * Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set g : ℝ → ℂ := fun θ => Complex.exp (I * ((-1 : ℤ) : ℂ) * (θ : ℂ)) with hg
  have hmemg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := memLp_expMode (-1)
  have hmemf : MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    memLp_phaseGerm h0 h1
  have hbound : ∀ N : ℕ, ‖(∫ θ in Ioc (-Real.pi) Real.pi, dirichletTrunc s N θ * g θ)
      - (∫ θ in Ioc (-Real.pi) Real.pi, phaseGerm s θ * g θ)‖
      ≤ Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
        * Real.sqrt (2 * Real.pi) := by
    intro N
    have hmemt : MemLp (dirichletTrunc s N) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_dirichletTrunc s N
    have hmemu : MemLp (fun θ => phaseGerm s θ - dirichletTrunc s N θ) 2
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := memLp_germ_sub_trunc h0 h1 N
    have hint1 : IntegrableOn (fun θ : ℝ => dirichletTrunc s N θ * g θ)
        (Ioc (-Real.pi) Real.pi) := hmemt.integrable_mul hmemg
    have hint2 : IntegrableOn (fun θ : ℝ => phaseGerm s θ * g θ) (Ioc (-Real.pi) Real.pi) :=
      hmemf.integrable_mul hmemg
    rw [← MeasureTheory.integral_sub hint1 hint2]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hptw : ∀ θ ∈ Ioc (-Real.pi) Real.pi,
        ‖dirichletTrunc s N θ * g θ - phaseGerm s θ * g θ‖
          ≤ ‖phaseGerm s θ - dirichletTrunc s N θ‖ * ‖g θ‖ := by
      intro θ _
      rw [← sub_mul, norm_mul, ← norm_neg (dirichletTrunc s N θ - phaseGerm s θ), neg_sub]
    have hmajint : IntegrableOn
        (fun θ : ℝ => ‖phaseGerm s θ - dirichletTrunc s N θ‖ * ‖g θ‖) (Ioc (-Real.pi) Real.pi) :=
      integrable_norm_mul hmemu hmemg
    refine (MeasureTheory.setIntegral_mono_on (hint1.sub hint2).norm hmajint measurableSet_Ioc
      hptw).trans ?_
    refine (integral_norm_mul_le_sqrt hmemu hmemg).trans ?_
    rw [integral_expMode_normSq (-1)]
  have hlim : Tendsto (fun N : ℕ => ∫ θ in Ioc (-Real.pi) Real.pi, dirichletTrunc s N θ * g θ)
      atTop (𝓝 (∫ θ in Ioc (-Real.pi) Real.pi, phaseGerm s θ * g θ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _)
      (Filter.Eventually.of_forall hbound) ?_
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_integral_germ_sub_trunc h0 h1)).mul_const (Real.sqrt (2 * Real.pi))
    rw [Real.sqrt_zero] at h2
    simpa using h2
  have hev : ∀ᶠ N : ℕ in atTop,
      (∫ θ in Ioc (-Real.pi) Real.pi, dirichletTrunc s N θ * g θ) = ((2 * Real.pi : ℝ) : ℂ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [integral_dirichletTrunc_mul_expNeg s hN]
    push_cast
    ring
  have hconst := Filter.Tendsto.congr' hev hlim
  have hfin := tendsto_nhds_unique hconst tendsto_const_nhds
  show (∫ θ in Ioc (-Real.pi) Real.pi, phaseGerm s θ * g θ) = 2 * (Real.pi : ℂ)
  rw [hfin]
  push_cast
  ring

/-- **The germ carries at least the mass of its first mode.** -/
theorem two_pi_le_integral_phaseGerm_normSq {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    2 * Real.pi ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set g : ℝ → ℂ := fun θ => Complex.exp (I * ((-1 : ℤ) : ℂ) * (θ : ℂ)) with hg
  have hmemg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := memLp_expMode (-1)
  have hmemf : MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    memLp_phaseGerm h0 h1
  have hCS := integral_norm_mul_le_sqrt hmemf hmemg
  rw [integral_expMode_normSq (-1)] at hCS
  have hlow : (2 * Real.pi : ℝ)
      ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ * ‖g θ‖ := by
    have hn : ‖(∫ θ in Ioc (-Real.pi) Real.pi, phaseGerm s θ * g θ)‖ = 2 * Real.pi := by
      rw [integral_phaseGerm_mul_expNeg h0 h1]
      rw [show ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (2 * Real.pi : ℝ) = ‖(∫ θ in Ioc (-Real.pi) Real.pi, phaseGerm s θ * g θ)‖ := hn.symm
      _ ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ * g θ‖ := norm_integral_le_integral_norm _
      _ = ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ * ‖g θ‖ := by
          refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
          rw [norm_mul]
  have hchain : (2 * Real.pi : ℝ)
      ≤ Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2)
        * Real.sqrt (2 * Real.pi) := le_trans hlow hCS
  set A : ℝ := ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2 with hA
  have hsq : Real.sqrt (2 * Real.pi) ≤ Real.sqrt A := by
    have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hid : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg A]
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioc fun θ _ => by positivity
  nlinarith [Real.sq_sqrt hAnn, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi),
    Real.sqrt_nonneg A, Real.sqrt_nonneg (2 * Real.pi)]

/-! ## The aperture energy as a positive real -/

/-- The additive heat-aperture energy as a real number. -/
noncomputable def realHeatEnergy (s : ℂ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi))
    * ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2 * heatMultiplierValue x θ

theorem heatEnergy_eq_ofReal {s : ℂ} {x : ℝ} (hx : 0 < x) :
    heatEnergy s x = ((realHeatEnergy s x : ℝ) : ℂ) := by
  have hc : (1 / (2 * (Real.pi : ℂ))) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [heatEnergy, realHeatEnergy, Complex.ofReal_mul, ← integral_complex_ofReal, hc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  rw [Complex.ofReal_mul, heatMultiplier_eq_value hx, Complex.mul_conj]
  congr 2
  rw [Complex.normSq_eq_norm_sq]

theorem integrableOn_germSq_mul_heatMultiplierValue {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => ‖phaseGerm s θ‖ ^ 2 * heatMultiplierValue x θ)
      (Ioc (-Real.pi) Real.pi) := by
  have hsq : IntegrableOn (fun θ : ℝ => ‖phaseGerm s θ‖ ^ 2) (Ioc (-Real.pi) Real.pi) :=
    (memLp_two_iff_integrable_sq_norm
      (memLp_phaseGerm h0 h1).aestronglyMeasurable).mp (memLp_phaseGerm h0 h1)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hcont : Continuous (fun θ : ℝ => heatMultiplierValue x θ) := by
    have := continuous_heatMultiplier (x := x) hx
    have hre : (fun θ : ℝ => heatMultiplierValue x θ)
        = fun θ : ℝ => (heatMultiplier x θ).re := by
      funext θ
      rw [heatMultiplier_eq_value hx, Complex.ofReal_re]
    rw [hre]
    exact Complex.continuous_re.comp this
  have hbd : IntegrableOn
      (fun θ : ℝ => heatMultiplierValue x θ * ‖phaseGerm s θ‖ ^ 2) (Ioc (-Real.pi) Real.pi) := by
    refine MeasureTheory.Integrable.bdd_mul (c := M) hsq
      (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, hθ.2⟩
    rw [Real.norm_of_nonneg (heatMultiplierValue_nonneg hx θ), ← norm_heatMultiplier hx]
    exact hM θ hmem
  refine hbd.congr ?_
  filter_upwards with θ
  ring

/-- **The additive heat aperture energy is strictly positive at every finite aperture.** -/
theorem realHeatEnergy_pos {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    0 < realHeatEnergy s x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcont : ContinuousOn (fun θ : ℝ => heatMultiplierValue x θ) (Icc (-Real.pi) Real.pi) := by
    have hre : (fun θ : ℝ => heatMultiplierValue x θ)
        = fun θ : ℝ => (heatMultiplier x θ).re := by
      funext θ
      rw [heatMultiplier_eq_value hx, Complex.ofReal_re]
    rw [hre]
    exact (Complex.continuous_re.comp (continuous_heatMultiplier hx)).continuousOn
  obtain ⟨θ₀, hθ₀, hmin⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_isMinOn
    ⟨0, by constructor <;> linarith⟩ hcont
  set c : ℝ := heatMultiplierValue x θ₀ with hc
  have hc0 : 0 < c := heatMultiplierValue_pos hx θ₀
  have hsq : IntegrableOn (fun θ : ℝ => ‖phaseGerm s θ‖ ^ 2) (Ioc (-Real.pi) Real.pi) :=
    (memLp_two_iff_integrable_sq_norm
      (memLp_phaseGerm h0 h1).aestronglyMeasurable).mp (memLp_phaseGerm h0 h1)
  have hmono : (∫ θ in Ioc (-Real.pi) Real.pi, c * ‖phaseGerm s θ‖ ^ 2)
      ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2 * heatMultiplierValue x θ := by
    refine MeasureTheory.setIntegral_mono_on (hsq.const_mul c)
      (integrableOn_germSq_mul_heatMultiplierValue h0 h1 hx) measurableSet_Ioc fun θ hθ => ?_
    have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, hθ.2⟩
    have hcle : c ≤ heatMultiplierValue x θ := hmin hmem
    have hnn : (0 : ℝ) ≤ ‖phaseGerm s θ‖ ^ 2 := by positivity
    nlinarith
  rw [MeasureTheory.integral_const_mul] at hmono
  have hlow := two_pi_le_integral_phaseGerm_normSq h0 h1
  rw [realHeatEnergy]
  have hkey : 0 < ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2 * heatMultiplierValue x θ := by
    nlinarith
  positivity

theorem heatEnergy_ne_zero {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    heatEnergy s x ≠ 0 := by
  rw [heatEnergy_eq_ofReal hx]
  exact Complex.ofReal_ne_zero.mpr (realHeatEnergy_pos h0 h1 hx).ne'

end RHTower
