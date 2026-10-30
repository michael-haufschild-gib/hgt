import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheNormalizedAtomicTransform
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheOverlapGramHasBoundedRows
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.LogarithmicBandMass
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialSpanTestPolarPrimeGammaBudgets
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# A Gamma reserve at every fixed overlap

Boosting the cubic spline removes its real Fourier zeros. After normalization
of its support to the unit interval, every fixed spectral band has a positive
Fourier floor. The logarithmic Montgomery–Vaughan inequality then retains
coefficient mass in a band proportional to the horizon. The Gamma symbol's
logarithmic growth on that band gives a positive reserve at every fixed
overlap; bounded Gram rows pay its globally bounded negative part.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset Zeta23 RHTower

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge
  ArithmeticElectrostatics ArithmeticPositivityTheory

/-- The boosted cubic spline, translated and dilated to support `[0,1]`. -/
def tiltedUnitSpline (u : ℝ) : ℝ := atomDilate splineProbe (1 / 8) (u - 1 / 2)

theorem contDiff_tiltedUnitSpline : ContDiff ℝ 2 tiltedUnitSpline := by
  unfold tiltedUnitSpline atomDilate
  exact contDiff_splineProbe.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem hasCompactSupport_tiltedUnitSpline : HasCompactSupport tiltedUnitSpline :=
  (hasCompactSupport_atomDilate (by norm_num : (1 / 8 : ℝ) ≠ 0)
    hasCompactSupport_splineProbe).comp_homeomorph (Homeomorph.subRight (1 / 2))

theorem tiltedUnitSpline_eq_zero (u : ℝ) (hu : u ∉ Set.Icc 0 1) : tiltedUnitSpline u = 0 := by
  apply splineProbe_eq_zero
  have hu' : u < 0 ∨ 1 < u := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hu
  rcases hu' with hu0 | hu1
  · apply lt_of_lt_of_le _ (neg_le_abs ((u - 1 / 2) / (1 / 8)))
    norm_num
    linarith only [hu0]
  · apply lt_of_lt_of_le _ (le_abs_self ((u - 1 / 2) / (1 / 8)))
    norm_num
    linarith only [hu1]

/-- Exponential boosting shifts real frequencies off the spline transform's zero line. -/
theorem paperFT_splineProbe_real_ne_zero (r : ℝ) : paperFT (cx splineProbe) (r : ℂ) ≠ 0 := by
  change paperFT (fun u => (tiltedSource cubicSpline 1 u : ℂ)) (r : ℂ) ≠ 0
  rw [paperFT_tiltedSource]
  apply paperFT_cubicSpline_ne_zero
  norm_num

/-- Translation and positive dilation preserve real Fourier nonvanishing. -/
theorem paperFT_tiltedUnitSpline_real_ne_zero (r : ℝ) :
    paperFT (cx tiltedUnitSpline) (r : ℂ) ≠ 0 := by
  have heq : cx tiltedUnitSpline =
      ArithmeticCastelnuovoSeveri.translate (1 / 2) (cx (atomDilate splineProbe (1 / 8))) := rfl
  rw [heq, paperFT_translate, paperFT_atomDilate (by norm_num : (0 : ℝ) < 1 / 8)]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by norm_num) ?_)
  have hz : ((1 / 8 : ℝ) : ℂ) * (r : ℂ) = ((r / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  exact paperFT_splineProbe_real_ne_zero (r / 8)

private theorem integral_sq_pos_of_nonzero_transform {f : ℝ → ℝ}
    (hc : Continuous f) (hcs : HasCompactSupport f) (hft : paperFT (cx f) 0 ≠ 0) :
    0 < ∫ u, f u ^ 2 := by
  have hsqc : HasCompactSupport (fun u => f u ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hi : Integrable (fun u => f u ^ 2) :=
    (hc.pow 2).integrable_of_hasCompactSupport hsqc
  by_contra hpos
  have hz : (∫ u, f u ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg fun u => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun u => sq_nonneg (f u)) hi).mp hz
  have heq := (Continuous.ae_eq_iff_eq volume (hc.pow 2) continuous_const).mp hae
  have hfzero : ∀ u, f u = 0 := by
    intro u
    have h := congrFun heq u
    change f u ^ 2 = 0 at h
    nlinarith only [h]
  apply hft
  simp only [paperFT, cx, hfzero, Complex.ofReal_zero, zero_mul, integral_zero]

theorem integral_tiltedUnitSpline_sq_pos : 0 < ∫ u, tiltedUnitSpline u ^ 2 :=
  integral_sq_pos_of_nonzero_transform contDiff_tiltedUnitSpline.continuous
    hasCompactSupport_tiltedUnitSpline (paperFT_tiltedUnitSpline_real_ne_zero 0)

theorem tiltedUnitSpline_atom_support {w : ℝ} (hw : 0 < w) :
    ∀ u, u ∉ Set.Icc 0 w → atomDilate tiltedUnitSpline w u = 0 := by
  intro u hu
  apply tiltedUnitSpline_eq_zero
  intro h
  apply hu
  exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hw).mp h.1,
    (div_le_one hw).mp h.2⟩

/-- A high band gains its logarithmic Gamma weight; all remaining mass has bounded cost. -/
theorem archForm_ge_log_band_sub_mass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {R : ℝ} (hR : 0 < R) :
    Real.log R / (2 * Real.pi) *
        (∫ t in R..101 * R, ‖paperFT (cx f) (t : ℂ)‖ ^ 2) -
      (factorialSpanGammaOffset + Real.log 2) * (∫ u, f u ^ 2) ≤ archForm f := by
  let F : ℝ → ℝ := fun t => ‖paperFT (cx f) (t : ℂ)‖ ^ 2
  have hFi : Integrable F := integrable_normSq_paperFT_ofReal hf hfc
  have hGi : Integrable (fun t => F t * EF.gammaBracket t) :=
    RHTower.integrable_normSq_paperFT_mul_gammaBracket hf hfc
  have hsplit := integral_add_compl (measurableSet_Icc (a := R) (b := 101 * R)) hGi
  have hmassSplit := integral_add_compl (measurableSet_Icc (a := R) (b := 101 * R)) hFi
  have hband : (Real.log R - factorialSpanGammaOffset) * (∫ t in Set.Icc R (101 * R), F t) ≤
      ∫ t in Set.Icc R (101 * R), F t * EF.gammaBracket t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hFi.integrableOn.const_mul _) hGi.integrableOn
      measurableSet_Icc fun t ht => ?_
    have hγ := gammaBracket_ge_log_of_le_abs hR (ht.1.trans (le_abs_self t))
    have hF : 0 ≤ F t := sq_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left hγ hF]
  have hcompl : -(factorialSpanGammaOffset + Real.log 2) *
        (∫ t in (Set.Icc R (101 * R))ᶜ, F t) ≤
      ∫ t in (Set.Icc R (101 * R))ᶜ, F t * EF.gammaBracket t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hFi.integrableOn.const_mul _) hGi.integrableOn
      measurableSet_Icc.compl fun t _ => ?_
    have hγ := gammaBracket_ge_neg_offset t
    have hF : 0 ≤ F t := sq_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left hγ hF]
  have hband0 : 0 ≤ ∫ t in Set.Icc R (101 * R), F t := integral_nonneg fun t => sq_nonneg _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hplain : Real.log R * (∫ t in Set.Icc R (101 * R), F t) -
      (factorialSpanGammaOffset + Real.log 2) *
        ((∫ t in Set.Icc R (101 * R), F t) + (∫ t in (Set.Icc R (101 * R))ᶜ, F t)) ≤
      ∫ t, F t * EF.gammaBracket t := by
    linarith only [hband, hcompl, hsplit, mul_nonneg hlog2 hband0]
  have hPl := LebesgueAtomWeil.integral_norm_sq_paperFT_eq
    (Complex.ofRealCLM.contDiff.comp hf) (hfc.comp_left Complex.ofReal_zero)
  change (1 / (2 * Real.pi)) * (∫ t, F t) = ∫ u, ‖(f u : ℂ)‖ ^ 2 at hPl
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hPl
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [intervalIntegral.integral_of_le (by linarith only [hR] : R ≤ 101 * R),
    ← integral_Icc_eq_integral_Ioc]
  calc
    _ = (1 / (2 * Real.pi)) *
        (Real.log R * (∫ t in Set.Icc R (101 * R), F t) -
          (factorialSpanGammaOffset + Real.log 2) *
            ((∫ t in Set.Icc R (101 * R), F t) + (∫ t in (Set.Icc R (101 * R))ᶜ, F t))) := by
      rw [hmassSplit]
      change Real.log R / (2 * Real.pi) * (∫ t in Set.Icc R (101 * R), F t) -
          (factorialSpanGammaOffset + Real.log 2) * (∫ u, f u ^ 2) = _
      rw [← hPl]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hplain hpi


/-- The explicit profile has a positive Fourier floor on every fixed compact band. -/
theorem exists_tiltedUnitSpline_fourier_floor {c : ℝ} (hc : 0 < c) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc c (101 * c),
      m ≤ ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2 := by
  have hd := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp contDiff_tiltedUnitSpline.continuous)
    (hasCompactSupport_tiltedUnitSpline.comp_left Complex.ofReal_zero)
  have hcont : Continuous (fun t : ℝ => ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc c (101 * c)).Nonempty from ⟨c, le_rfl, by linarith only [hc]⟩)
    hcont.continuousOn
  refine ⟨_, ?_, fun r hr => hmin hr⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr (paperFT_tiltedUnitSpline_real_ne_zero t))

private theorem tiltedUnitSpline_highBand_mass {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hfloor : ∀ t ∈ Set.Icc c (101 * c), m ≤ ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (48 * (c / N) ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ t in (N : ℝ)..101 * N,
        ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline (c / N)))) (t : ℂ)‖ ^ 2 := by
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hwN : w * (N : ℝ) = c := by dsimp only [w]; field_simp [hNR.ne']
  have hg : ContDiff ℝ 2 (atomDilate tiltedUnitSpline w) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest (tiltedUnitSpline_atom_support hw) N x
  have hhat := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp hf.continuous) (hfc.comp_left Complex.ofReal_zero)
  have hFcont : Continuous (fun t : ℝ =>
      ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline w))) (t : ℂ)‖ ^ 2) :=
    (hhat.continuous.comp Complex.continuous_ofReal).norm.pow 2
  have hDcont : Continuous (fun t : ℝ => ‖dirichletPoly N x (t : ℂ)‖ ^ 2) := by
    unfold dirichletPoly
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (N : ℝ) (101 * N),
      (w ^ 2 * m) * ‖dirichletPoly N x (t : ℂ)‖ ^ 2 ≤
        ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline w))) (t : ℂ)‖ ^ 2 := by
    intro t ht
    have hlow := mul_le_mul_of_nonneg_left ht.1 hw.le
    have hhigh := mul_le_mul_of_nonneg_left ht.2 hw.le
    have hmem : w * t ∈ Set.Icc c (101 * c) := by
      constructor <;> nlinarith only [hlow, hhigh, hwN]
    have hmval := hfloor (w * t) hmem
    rw [paperFT_atomicTest_atomDilate contDiff_tiltedUnitSpline.continuous
      hasCompactSupport_tiltedUnitSpline hw, ← Complex.ofReal_mul]
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmval (sq_nonneg ‖dirichletPoly N x (t : ℂ)‖))
      (sq_nonneg w)
    simpa only [mul_assoc] using hscaled
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (show (N : ℝ) ≤ 101 * N by linarith only [hNR])
    ((hDcont.const_mul (w ^ 2 * m)).intervalIntegrable _ _)
    (hFcont.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  have hMV := TransMetzlerWeilPositivity.BoundedOverlap.dirichletPoly_highBand_mass hN x
  calc
    _ = (w ^ 2 * m) * ((48 * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by ring
    _ ≤ (w ^ 2 * m) * (∫ t in (N : ℝ)..101 * N, ‖dirichletPoly N x (t : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hMV (mul_nonneg (sq_nonneg w) hm.le)
    _ ≤ _ := hint

/-- At every fixed overlap, the actual Gamma form of the explicit spline atoms
retains a positive logarithmic coefficient reserve, uniformly over all signed packets. -/
theorem exists_tiltedUnitSpline_archForm_reserve {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℕ → ℝ,
      (a * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
        archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  obtain ⟨m, hm, hfloor⟩ := exists_tiltedUnitSpline_fourier_floor hc
  let M := ∫ u, tiltedUnitSpline u ^ 2
  let a := 48 * c * m / (2 * Real.pi * M)
  let b := (factorialSpanGammaOffset + Real.log 2) * (1 + 2 * c * Real.exp c)
  have hM : 0 < M := integral_tiltedUnitSpline_sq_pos
  have hoffset : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg (by norm_num))
  refine ⟨a, by dsimp only [a]; positivity, b,
    mul_nonneg hoffset (by positivity), fun N hN x => ?_⟩
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hg : ContDiff ℝ 2 (atomDilate tiltedUnitSpline w) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hgsupp := tiltedUnitSpline_atom_support hw
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := tiltedUnitSpline_highBand_mass hc hm hfloor hN x
  have hphysical := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN hgsupp x
  rw [integral_atomDilate_sq hw] at hphysical
  have hbandCost := mul_le_mul_of_nonneg_left hband
    (div_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN))
      (by positivity : 0 ≤ 2 * Real.pi))
  have hmassCost := mul_le_mul_of_nonneg_left hphysical hoffset
  have hid : ((a * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2)) * (w * M) =
      Real.log N / (2 * Real.pi) *
        ((48 * w ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) -
      (factorialSpanGammaOffset + Real.log 2) *
        ((w * M) * (1 + 2 * c * Real.exp c) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by
    dsimp only [a, b, w]
    field_simp [hM.ne', hNR.ne', Real.pi_ne_zero]
  apply (le_div_iff₀ (mul_pos hw hM)).mpr
  rw [hid]
  linarith only [hgamma, hbandCost, hmassCost]

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.paperFT_tiltedUnitSpline_real_ne_zero
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_tiltedUnitSpline_archForm_reserve
