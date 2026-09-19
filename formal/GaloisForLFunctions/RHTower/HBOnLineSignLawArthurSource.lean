import GaloisForLFunctions.RHTower.EisensteinArthurSource

/-!
# The on-line sign law for the Arthur-truncated Eisenstein source

The source `F_A = ‖Λ^{e²} E*(·, ½+it)‖²` — the square of the genuinely (Arthur-)truncated completed
Eisenstein series on the line — lies in `L²(𝒟)`, its mean is the Maass–Selberg value
`Re msLineValue(t, e²)` (and is at least `(5/2)‖Λ(1+2it)‖²`), and its mean square obeys the same
bound `vBound t` as the principal-subtraction source.  Hence the spectral assembly gives the on-line
sign law for this source too: `0 < Re⟪(Im K̂)(C) F_A, F_A⟫` for all large `t`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
open GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget (fullDomain)
open RHTower.D4BMScalarStream
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- The Arthur source on `ℍ`. -/
def arthurReal (t : ℝ) (z : ℍ) : ℝ := arthurCoord t z.re z.im

theorem arthurReal_eq (t : ℝ) (z : ℍ) :
    arthurReal t z = ‖truncatedLineModel ((t : ℂ) * Complex.I) sourceHeight z‖ ^ 2 := rfl

theorem setIntegral_fd_arthurReal (t : ℝ) :
    ∫ z in fd, arthurReal t z = ∫ p in fullDomain, arthurCoord t p.1 p.2 / p.2 ^ 2 := by
  rw [← integral_height_sq_cell (fun p => arthurCoord t p.1 p.2 / p.2 ^ 2)]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [arthurReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

theorem setIntegral_fd_arthurReal_sq (t : ℝ) :
    ∫ z in fd, arthurReal t z ^ 2 = ∫ p in fullDomain, arthurCoord t p.1 p.2 ^ 2 / p.2 ^ 2 := by
  rw [← integral_height_sq_cell (fun p => arthurCoord t p.1 p.2 ^ 2 / p.2 ^ 2)]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [arthurReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

/-- The source as a complex-valued function. -/
def arthurC (t : ℝ) (z : ℍ) : ℂ := ((arthurReal t z : ℝ) : ℂ)

theorem measurable_arthurReal (t : ℝ) : Measurable (arthurReal t) := by
  have h : arthurReal t = fun z => ‖truncatedLineModel ((t : ℂ) * Complex.I) sourceHeight z‖ ^ 2 :=
    funext (arthurReal_eq t)
  rw [h]
  exact (measurable_truncatedLineModel _ _).norm.pow_const 2

theorem norm_arthurC_le {t : ℝ} (ht : 2 ≤ t) {z : ℍ} (hz : z ∈ fd) :
    ‖arthurC t z‖ ≤ arthurBound t := by
  rw [arthurC, Complex.norm_real, Real.norm_eq_abs, arthurReal,
    abs_of_nonneg (arthurCoord_nonneg _ _ _)]
  exact arthurCoord_le_arthurBound ht (half_lt_im_of_mem_fd hz).le z.re

theorem memLp_arthurC {t : ℝ} (ht : 2 ≤ t) : MemLp (arthurC t) 2 modularCellMeasure := by
  refine MemLp.of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (measurable_arthurReal t).aestronglyMeasurable) (arthurBound t) ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => norm_arthurC_le ht hz)

/-- The Arthur source as an element of `L²(𝒟)`. -/
def arthurL2 (t : ℝ) (ht : 2 ≤ t) : ModularL2 := toModularL2 (arthurC t) (memLp_arthurC ht)

theorem coeFn_arthurL2 {t : ℝ} (ht : 2 ≤ t) :
    (modularToLp (arthurL2 t ht) : ℍ → ℂ) =ᵐ[modularCellMeasure] arthurC t :=
  MemLp.coeFn_toLp (memLp_arthurC ht)

theorem setIntegral_arthurL2 {t : ℝ} (ht : 2 ≤ t) :
    ∫ z in fd, modularToLp (arthurL2 t ht) z ∂volume =
      ((∫ z in fd, arthurReal t z : ℝ) : ℂ) := by
  rw [integral_congr_ae (coeFn_arthurL2 ht)]
  exact integral_ofReal

theorem norm_sq_arthurL2 {t : ℝ} (ht : 2 ≤ t) :
    ‖arthurL2 t ht‖ ^ 2 = ∫ z in fd, arthurReal t z ^ 2 := by
  have h : RCLike.re ⟪modularToLp (arthurL2 t ht), modularToLp (arthurL2 t ht)⟫_ℂ =
      ∫ z in fd, arthurReal t z ^ 2 := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_arthurL2 ht] with z hz
    rw [hz, RCLike.inner_apply, arthurC, Complex.conj_ofReal, RCLike.re_to_complex,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have h2 : ‖modularToLp (arthurL2 t ht)‖ ^ 2 =
      RCLike.re ⟪modularToLp (arthurL2 t ht), modularToLp (arthurL2 t ht)⟫_ℂ :=
    (inner_self_eq_norm_sq _).symm
  rw [h] at h2
  exact h2

/-- **The mean of the Arthur source is the Maass–Selberg value.** -/
theorem setIntegral_fd_arthurReal_eq_msLineValue {t : ℝ} (ht : 0 < t) :
    ∫ z in fd, arthurReal t z = (msLineValue t sourceHeight).re := by
  rw [← integral_norm_sq_truncatedLineModel_line ht one_lt_sourceHeight.le]
  rfl

/-- **The on-line sign law for the Arthur-truncated source.** -/
theorem hb_online_sign_law_arthur_source :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∃ ht : 2 ≤ t,
      0 < RCLike.re ⟪cfc (skewCovKernelIm t) modularCovariance (arthurL2 t ht),
        arthurL2 t ht⟫_ℂ := by
  obtain ⟨B, T, hB, hT3, hV⟩ := exists_vBound_le_growth
  have hH : 0 < sourceHeight := Real.exp_pos 2
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_mul_growth_lt (128 * sourceHeight + B))
  refine ⟨max (max T T₂) 50, fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₂ : T₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht50 : (50 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht3 : 3 ≤ t := le_trans hT3 htT
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  refine ⟨ht2, ?_⟩
  have hasm := hb_online_clock_spectral_assembly' t ht50 (arthurL2 t ht2)
  have hgrow := hT₂ t htT₂
  have hVb := hV t htT
  -- the mean and the Lambda value, as opaque names
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ p in fullDomain, arthurCoord t p.1 p.2 / p.2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖eisLineLambda t‖ ^ 2 := ⟨_, rfl⟩
  have hMge : (5 / 2) * L ≤ M := by
    rw [hM, hL]; exact setIntegral_fullDomain_arthur_div_ge ht2
  have hLpos : 0 < L := by rw [hL]; exact norm_sq_eisLineLambda_pos ht0.le
  have hMnn : 0 ≤ M := by linarith
  -- the constant mode is `M²`
  have hI : ‖∫ z in fd, modularToLp (arthurL2 t ht2) z ∂volume‖ ^ 2 = M ^ 2 := by
    rw [setIntegral_arthurL2 ht2, setIntegral_fd_arthurReal, ← hM, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  -- the fluctuation is at most the mean square
  have hN : ‖arthurL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurL2 t ht2)‖ ^ 2 ≤
      L ^ 2 * (128 * sourceHeight + B * growth t) := by
    calc ‖arthurL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurL2 t ht2)‖ ^ 2
        ≤ ‖arthurL2 t ht2‖ ^ 2 := norm_sub_starProjection_sq_le _
      _ = ∫ p in fullDomain, arthurCoord t p.1 p.2 ^ 2 / p.2 ^ 2 := by
          rw [norm_sq_arthurL2, setIntegral_fd_arthurReal_sq]
      _ ≤ vBound t := setIntegral_fullDomain_arthur_sq_div_le ht2
      _ ≤ ‖eisLineLambda t‖ ^ 4 * (128 * sourceHeight + B * growth t) := hVb
      _ = L ^ 2 * (128 * sourceHeight + B * growth t) := by rw [hL]; ring
  -- volume bounds
  have hvol := volume_fd_toReal_pos
  have hvol2 := volume_fd_toReal_le_two
  -- `M²/vol ≥ (25/4) L² / 2`
  have hM2 : (25 / 4) * L ^ 2 ≤ M ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hMge 2
    nlinarith [this]
  have hq : (25 / 4) * L ^ 2 / 2 ≤ M ^ 2 / ((volume : Measure ℍ) fd).toReal := by
    rw [div_le_div_iff₀ (by norm_num) hvol]
    nlinarith [hM2, hvol2, sq_nonneg L, hvol]
  -- the growth term is small
  have hgr1 := one_le_growth ht3
  have hsmall : 128 * sourceHeight + B * growth t < 25 * t ^ 2 / 17408 := by
    have : 128 * sourceHeight + B * growth t ≤ (128 * sourceHeight + B) * growth t := by
      nlinarith [hgr1, hH]
    linarith
  -- the strict lower bound
  have key : 0 < t ^ 11 / 2176 * (M ^ 2 / ((volume : Measure ℍ) fd).toReal) -
      t ^ 9 * (L ^ 2 * (128 * sourceHeight + B * growth t)) := by
    have h1 : t ^ 11 / 2176 * ((25 / 4) * L ^ 2 / 2) ≤
        t ^ 11 / 2176 * (M ^ 2 / ((volume : Measure ℍ) fd).toReal) := by gcongr
    have h2 : t ^ 9 * (L ^ 2 * (128 * sourceHeight + B * growth t)) <
        t ^ 9 * (L ^ 2 * (25 * t ^ 2 / 17408)) := by gcongr
    have h3 : t ^ 11 / 2176 * ((25 / 4) * L ^ 2 / 2) = t ^ 9 * (L ^ 2 * (25 * t ^ 2 / 17408)) := by
      ring
    linarith
  have hfinal : 0 < t ^ 11 / 2176 *
      (‖∫ z in fd, modularToLp (arthurL2 t ht2) z ∂volume‖ ^ 2 /
        ((volume : Measure ℍ) fd).toReal) -
      t ^ 9 * ‖arthurL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurL2 t ht2)‖ ^ 2 := by
    rw [hI]
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ t ^ 9)
    linarith
  exact lt_of_lt_of_le hfinal hasm


end

end RHTower
