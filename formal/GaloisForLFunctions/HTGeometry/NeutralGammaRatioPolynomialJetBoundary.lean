import GaloisForLFunctions.HTGeometry.NeutralGammaRatioProjectiveBoundary
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.DigammaSecondOrderVertical
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound
import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.GammaNatShift
import GaloisForLFunctions.HTGeometry.GammaFactorialMovingHarmonicResidue
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.ArchimedeanFinitePhaseRank
import GaloisForLFunctions.HTGeometry.CarrierTranslationEquivariance
import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRankSharp

open Filter Set Topology Function intervalIntegral
open scoped UnivMeroFieldInstances BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem gamma_imag_shift_exp_integral {z : ℂ} (hz : 0 < z.re) {θ : ℝ} (hθ : 0 ≤ θ) :
    Complex.Gamma (z + Complex.I * (θ : ℂ)) = Complex.Gamma z *
      Complex.exp (∫ y in (0 : ℝ)..θ,
        Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) := by
  classical
  have hcontAll : Continuous (fun y : ℝ =>
      Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : 0 < (z + Complex.I * (y : ℂ)).re := by simpa using hz
    have hpath : ContinuousAt (fun u : ℝ => z + Complex.I * (u : ℂ)) y := by fun_prop
    have hdig : ContinuousAt (fun u : ℝ =>
        Complex.digamma (z + Complex.I * (u : ℂ))) y :=
      ContinuousAt.comp (x := y) (g := Complex.digamma)
        (continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre)) hpath
    exact continuousAt_const.mul hdig
  have hcont : ContinuousOn (fun y : ℝ =>
      Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) (Set.uIcc 0 θ) :=
    hcontAll.continuousOn
  have hint : IntervalIntegrable (fun y : ℝ =>
      Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)))
      MeasureTheory.volume 0 θ := hcont.intervalIntegrable
  set Ψ : ℝ → ℂ := fun u => ∫ y in (0 : ℝ)..u,
    Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)) with hΨ
  have hderivΨ : ∀ u ∈ Set.uIcc (0 : ℝ) θ,
      HasDerivAt Ψ (Complex.I * Complex.digamma (z + Complex.I * (u : ℂ))) u := by
    intro u hu
    have hsubu : Set.uIcc (0 : ℝ) u ⊆ Set.uIcc (0 : ℝ) θ := by
      rw [Set.uIcc_of_le hθ]
      rw [Set.uIcc_of_le (by rw [Set.uIcc_of_le hθ] at hu; exact hu.1)]
      rw [Set.uIcc_of_le hθ] at hu
      exact Set.Icc_subset_Icc le_rfl hu.2
    refine intervalIntegral.integral_hasDerivAt_right (hint.mono_set hsubu) ?_ ?_
    · exact hcontAll.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact hcontAll.continuousAt
  have hzero : ∀ u ∈ Set.uIcc (0 : ℝ) θ,
      HasDerivAt (fun y : ℝ => Complex.Gamma (z + Complex.I * (y : ℂ)) *
        Complex.exp (-Ψ y)) 0 u := by
    intro u hu
    have hre : 0 < (z + Complex.I * (u : ℂ)).re := by simpa using hz
    have hinner : HasDerivAt (fun w : ℂ => z + Complex.I * w) Complex.I (u : ℂ) := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id (𝕜 := ℂ) (u : ℂ)).const_mul Complex.I).const_add z)
    have houter : HasDerivAt Complex.Gamma
        (deriv Complex.Gamma (z + Complex.I * (u : ℂ)))
        (z + Complex.I * (u : ℂ)) := (differentiableAt_gamma_of_re_pos hre).hasDerivAt
    have hΓc := houter.comp (u : ℂ) hinner
    have hΓ : HasDerivAt (fun y : ℝ => Complex.Gamma (z + Complex.I * (y : ℂ)))
        (Complex.Gamma (z + Complex.I * (u : ℂ)) *
          Complex.digamma (z + Complex.I * (u : ℂ)) * Complex.I) u := by
      have h := hΓc.comp_ofReal
      rw [deriv_gamma_eq hre] at h
      exact h
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-Ψ y))
        (Complex.exp (-Ψ u) *
          -(Complex.I * Complex.digamma (z + Complex.I * (u : ℂ)))) u :=
      ((hderivΨ u hu).neg).cexp
    have hprod := hΓ.mul hexp
    have hval :
        (Complex.Gamma (z + Complex.I * (u : ℂ)) *
              Complex.digamma (z + Complex.I * (u : ℂ)) * Complex.I) * Complex.exp (-Ψ u) +
            Complex.Gamma (z + Complex.I * (u : ℂ)) *
              (Complex.exp (-Ψ u) *
                -(Complex.I * Complex.digamma (z + Complex.I * (u : ℂ)))) = 0 := by ring
    rw [hval] at hprod
    exact hprod
  have hΨ0 : Ψ 0 = 0 := by simp [hΨ]
  have heq : Complex.Gamma (z + Complex.I * (θ : ℂ)) * Complex.exp (-Ψ θ) =
      Complex.Gamma z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hzero
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at h
    have hstep := sub_eq_zero.mp h.symm
    have h0 : Complex.Gamma (z + Complex.I * (((0 : ℝ) : ℂ))) *
        Complex.exp (-Ψ 0) = Complex.Gamma z := by rw [hΨ0]; norm_num
    rw [h0] at hstep
    exact hstep
  rw [← heq, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- First subprincipal coefficient of `Γ(z+iθ)/Γ(z)`. -/
def neutralGammaFirstCoeff (θ : ℝ) : ℂ :=
  (Complex.I * (θ : ℂ)) * (Complex.I * (θ : ℂ) - 1) / 2

/-- Uniform quadratic error for the integrated-digamma exponent of a fixed imaginary Gamma
shift. The estimate is deliberately coarse; its constant is explicit and independent of `s`
once the height dominates `s.im`. -/
theorem norm_neutralGammaExponent_sub_le {θ T : ℝ} (hθ : 0 ≤ θ) (s : ℂ)
    (hs : 0 < s.re) (hT : 2 * |s.im| + 4 ≤ T) (hTθ : 4 * θ ≤ T) :
    let z := s + Complex.I * (T : ℂ)
    ‖(∫ y in (0 : ℝ)..θ,
          Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) -
        (Complex.I * (θ : ℂ) * Complex.log z + neutralGammaFirstCoeff θ / z)‖
      ≤ θ * (80 / 3 + 4 * θ ^ 2 + 2 * θ) / T ^ 2 := by
  dsimp only
  set z : ℂ := s + Complex.I * (T : ℂ) with hzdef
  have hTabs : 2 * |s.im| + 4 ≤ T := hT
  have hT4 : (4 : ℝ) ≤ T := by nlinarith [abs_nonneg s.im]
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT4
  have hzre : 0 < z.re := by simpa [z] using hs
  have hzim : z.im = s.im + T := by simp [z]
  have hznorm : T / 2 ≤ ‖z‖ := by
    have himnorm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hsimlow : -|s.im| ≤ s.im := neg_abs_le s.im
    have hzimlow : T / 2 ≤ z.im := by rw [hzim]; nlinarith
    have hzimpos : 0 ≤ z.im := le_trans (by positivity : 0 ≤ T / 2) hzimlow
    rw [abs_of_nonneg hzimpos] at himnorm
    exact le_trans hzimlow himnorm
  have hznormpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < T / 2) hznorm
  have hz0 : z ≠ 0 := norm_pos_iff.mp hznormpos
  have hpoint : ∀ y ∈ Set.uIoc (0 : ℝ) θ,
      ‖Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)) -
          (Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z))‖
        ≤ (80 / 3 + 4 * θ ^ 2 + 2 * θ) / T ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le hθ] at hy
    have hy0 : 0 ≤ y := le_of_lt hy.1
    have hyθ : y ≤ θ := hy.2
    set t : ℝ := T + s.im + y with htdef
    set w : ℂ := z + Complex.I * (y : ℂ) with hwdef
    have hsimlow : -|s.im| ≤ s.im := neg_abs_le s.im
    have ht2 : 2 ≤ t := by
      rw [htdef]
      nlinarith
    have htT : T / 2 ≤ t := by
      rw [htdef]
      nlinarith
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht2
    have hwre : 0 < w.re := by simpa [w, hwdef] using hzre
    have hwform : w = ((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [w, hwdef, z, t]
      ring
    have hstirling :
        ‖Complex.digamma w - Complex.log w + 1 / (2 * w)‖ ≤ (80 / 3) / T ^ 2 := by
      rw [hwform]
      refine le_trans (norm_digamma_sub_log_add_half_inv_le hs ht2) ?_
      have htTpos : 0 < t := htpos
      have hsq : T ^ 2 ≤ 4 * t ^ 2 := by nlinarith [sq_nonneg (t - T / 2)]
      have hT2pos : 0 < T ^ 2 := sq_pos_of_pos hTpos
      have ht2pos : 0 < t ^ 2 := sq_pos_of_pos htpos
      rw [div_le_div_iff₀ ht2pos hT2pos]
      nlinarith
    set u : ℂ := Complex.I * (y : ℂ) / z with hudef
    have hunorm : ‖u‖ = y / ‖z‖ := by
      rw [hudef, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hy0]
    have huhalf : ‖u‖ ≤ 1 / 2 := by
      rw [hunorm, div_le_iff₀ hznormpos]
      have : 2 * y ≤ ‖z‖ := by
        calc 2 * y ≤ 2 * θ := by linarith
          _ ≤ T / 2 := by linarith
          _ ≤ ‖z‖ := hznorm
      linarith
    have hult : ‖u‖ < 1 := lt_of_le_of_lt huhalf (by norm_num)
    have hquot : w / z = 1 + u := by
      rw [hwdef, hudef, add_div, div_self hz0]
    have hlogsplit : Complex.log w - Complex.log z = Complex.log (1 + u) := by
      rw [GaloisForLFunctions.HTGeometry.log_sub_log_of_re_pos hwre hzre, hquot]
    have hlogerr : ‖Complex.log w - Complex.log z - Complex.I * (y : ℂ) / z‖
        ≤ 4 * θ ^ 2 / T ^ 2 := by
      rw [hlogsplit, ← hudef]
      have hraw := Complex.norm_log_one_add_sub_self_le hult
      have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hraw' : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
        refine le_trans hraw ?_
        nlinarith [sq_nonneg ‖u‖]
      refine le_trans hraw' ?_
      rw [hunorm, div_pow]
      have hy2 : y ^ 2 ≤ θ ^ 2 := by nlinarith
      have hden : T ^ 2 ≤ 4 * ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - T / 2)]
      rw [div_le_div_iff₀ (sq_pos_of_pos hznormpos) (sq_pos_of_pos hTpos)]
      nlinarith
    have hwnorm : T / 2 ≤ ‖w‖ := by
      have himnorm : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      have hwim : w.im = t := by rw [hwform]; simp
      rw [hwim, abs_of_pos htpos] at himnorm
      exact le_trans htT himnorm
    have hwnormpos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity : 0 < T / 2) hwnorm
    have hw0 : w ≠ 0 := norm_pos_iff.mp hwnormpos
    have hinverr : ‖1 / w - 1 / z‖ ≤ 4 * θ / T ^ 2 := by
      have hfrac : 1 / w - 1 / z = (z - w) / (w * z) := by
        field_simp [hw0, hz0]
      have hzw : z - w = -(Complex.I * (y : ℂ)) := by rw [hwdef]; ring
      have heq : 1 / w - 1 / z = -(Complex.I * (y : ℂ)) / (w * z) := by
        rw [hfrac, hzw]
      rw [heq, norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
      have hprod : T ^ 2 / 4 ≤ ‖w‖ * ‖z‖ := by nlinarith
      rw [div_le_div_iff₀ (mul_pos hwnormpos hznormpos) (sq_pos_of_pos hTpos)]
      nlinarith
    have hdecomp :
        Complex.I * Complex.digamma w -
            (Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z)) =
          Complex.I * (Complex.digamma w - Complex.log w + 1 / (2 * w)) +
          Complex.I * (Complex.log w - Complex.log z - Complex.I * (y : ℂ) / z) -
          Complex.I / 2 * (1 / w - 1 / z) := by
      have hw0' : z + Complex.I * (y : ℂ) ≠ 0 := hwdef ▸ hw0
      rw [hwdef]
      field_simp [hz0, hw0']
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hdecomp]
    calc
      ‖Complex.I * (Complex.digamma w - Complex.log w + 1 / (2 * w)) +
          Complex.I * (Complex.log w - Complex.log z - Complex.I * (y : ℂ) / z) -
          Complex.I / 2 * (1 / w - 1 / z)‖
          ≤ ‖Complex.I * (Complex.digamma w - Complex.log w + 1 / (2 * w))‖ +
              ‖Complex.I * (Complex.log w - Complex.log z - Complex.I * (y : ℂ) / z)‖ +
              ‖Complex.I / 2 * (1 / w - 1 / z)‖ := by
            exact le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (80 / 3) / T ^ 2 + 4 * θ ^ 2 / T ^ 2 + (2 * θ) / T ^ 2 := by
            have hhalf : ‖Complex.I / 2‖ = (1 / 2 : ℝ) := by norm_num
            have hhalferr : (1 / 2 : ℝ) * ‖1 / w - 1 / z‖ ≤ 2 * θ / T ^ 2 := by
              calc
                (1 / 2 : ℝ) * ‖1 / w - 1 / z‖ ≤
                    (1 / 2 : ℝ) * (4 * θ / T ^ 2) :=
                  mul_le_mul_of_nonneg_left hinverr (by norm_num)
                _ = 2 * θ / T ^ 2 := by ring
            simp only [norm_mul, Complex.norm_I, one_mul, hhalf]
            exact add_le_add (add_le_add hstirling hlogerr) hhalferr
      _ = (80 / 3 + 4 * θ ^ 2 + 2 * θ) / T ^ 2 := by ring
  have hcontInt : ContinuousOn (fun y : ℝ =>
      Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)) -
        (Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z)))
      (Set.uIcc 0 θ) := by
    have hdig : Continuous (fun y : ℝ => Complex.digamma (z + Complex.I * (y : ℂ))) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hre : 0 < (z + Complex.I * (y : ℂ)).re := by simpa using hzre
      have hpath : ContinuousAt (fun u : ℝ => z + Complex.I * (u : ℂ)) y := by fun_prop
      exact ContinuousAt.comp (x := y) (g := Complex.digamma)
        (continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre)) hpath
    have helem : Continuous (fun y : ℝ =>
        Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z)) := by fun_prop
    exact ((continuous_const.mul hdig).sub helem).continuousOn
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hgammaInt : IntervalIntegrable (fun y : ℝ =>
      Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)))
      MeasureTheory.volume 0 θ := by
    have hdig : ContinuousOn (fun y : ℝ =>
        Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) (Set.uIcc 0 θ) := by
      intro y hy
      have hre : 0 < (z + Complex.I * (y : ℂ)).re := by simpa using hzre
      have hpath : ContinuousAt (fun u : ℝ => z + Complex.I * (u : ℂ)) y := by fun_prop
      have hc : ContinuousAt (fun u : ℝ =>
          Complex.digamma (z + Complex.I * (u : ℂ))) y :=
        ContinuousAt.comp (x := y) (g := Complex.digamma)
          (continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre)) hpath
      exact (continuousAt_const.mul hc).continuousWithinAt
    exact hdig.intervalIntegrable
  have hmodelInt : IntervalIntegrable (fun y : ℝ =>
      Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z))
      MeasureTheory.volume 0 θ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmodelEval :
      (∫ y in (0 : ℝ)..θ,
        (Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z))) =
      Complex.I * (θ : ℂ) * Complex.log z + neutralGammaFirstCoeff θ / z := by
    have hyint : IntervalIntegrable (fun y : ℝ => (y : ℂ) / z)
        MeasureTheory.volume 0 θ := by apply Continuous.intervalIntegrable; fun_prop
    have hleftInt : IntervalIntegrable (fun y : ℝ =>
        Complex.I * Complex.log z - (y : ℂ) / z) MeasureTheory.volume 0 θ :=
      (intervalIntegrable_const.sub hyint)
    rw [intervalIntegral.integral_sub
      hleftInt
      (intervalIntegrable_const),
      intervalIntegral.integral_sub (intervalIntegrable_const)
        hyint,
      intervalIntegral.integral_const, intervalIntegral.integral_const,
      show (fun y : ℝ => (y : ℂ) / z) = fun y : ℝ => (y : ℂ) * z⁻¹ by funext y; rw [div_eq_mul_inv],
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_id]
    simp [neutralGammaFirstCoeff]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  have hidentity :
      (∫ y in (0 : ℝ)..θ,
          Complex.I * Complex.digamma (z + Complex.I * (y : ℂ))) -
        (Complex.I * (θ : ℂ) * Complex.log z + neutralGammaFirstCoeff θ / z) =
      ∫ y in (0 : ℝ)..θ,
        (Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)) -
          (Complex.I * Complex.log z - (y : ℂ) / z - Complex.I / (2 * z))) := by
    rw [intervalIntegral.integral_sub hgammaInt hmodelInt, hmodelEval]
  rw [hidentity]
  refine le_trans hbound ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hθ)]
  simp only [sub_zero, div_eq_mul_inv]
  ring_nf
  exact le_rfl

/-- Coarse explicit constant for the integrated exponent error. -/
def neutralGammaExponentErrorConst (θ : ℝ) : ℝ :=
  θ * (80 / 3 + 4 * θ ^ 2 + 2 * θ)

/-- The neutral Gamma ratio has its exact first subprincipal expansion on every right-half-plane
vertical tube. -/
theorem norm_neutralGammaRatio_div_cpow_sub_le {θ T : ℝ} (hθ : 0 ≤ θ) (s : ℂ)
    (hs : 0 < s.re) (hT : 2 * |s.im| + 4 ≤ T) (hTθ : 4 * θ ≤ T)
    (hsmall : (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) / T ≤ 1) :
    let z := s + Complex.I * (T : ℂ)
    ‖neutralGammaRatio θ z / z ^ (Complex.I * (θ : ℂ)) -
        (1 + neutralGammaFirstCoeff θ / z)‖ ≤
      (neutralGammaExponentErrorConst θ +
        (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) ^ 2) / T ^ 2 := by
  dsimp only
  set z : ℂ := s + Complex.I * (T : ℂ) with hzdef
  set J : ℂ := ∫ y in (0 : ℝ)..θ,
    Complex.I * Complex.digamma (z + Complex.I * (y : ℂ)) with hJ
  set c : ℂ := neutralGammaFirstCoeff θ with hc
  set A : ℝ := neutralGammaExponentErrorConst θ with hA
  set E : ℂ := J - (Complex.I * (θ : ℂ) * Complex.log z + c / z) with hE
  have hT4 : (4 : ℝ) ≤ T := by nlinarith [abs_nonneg s.im]
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT4
  have hT1 : (1 : ℝ) ≤ T := le_trans (by norm_num) hT4
  have hzre : 0 < z.re := by simpa [z] using hs
  have hzim : z.im = s.im + T := by simp [z]
  have hznorm : T / 2 ≤ ‖z‖ := by
    have himnorm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hsimlow : -|s.im| ≤ s.im := neg_abs_le s.im
    have hzimlow : T / 2 ≤ z.im := by rw [hzim]; nlinarith
    have hzimpos : 0 ≤ z.im := le_trans (by positivity : 0 ≤ T / 2) hzimlow
    rw [abs_of_nonneg hzimpos] at himnorm
    exact le_trans hzimlow himnorm
  have hznormpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < T / 2) hznorm
  have hz0 : z ≠ 0 := norm_pos_iff.mp hznormpos
  have hEbound : ‖E‖ ≤ A / T ^ 2 := by
    rw [hE, hA, hJ, hc]
    simpa [neutralGammaExponentErrorConst] using
      norm_neutralGammaExponent_sub_le hθ s hs hT hTθ
  have hcz : ‖c / z‖ ≤ 2 * ‖c‖ / T := by
    rw [norm_div]
    rw [div_le_div_iff₀ hznormpos hTpos]
    nlinarith [norm_nonneg c]
  set q : ℂ := c / z + E with hq
  have hqbound : ‖q‖ ≤ (2 * ‖c‖ + A) / T := by
    calc
      ‖q‖ ≤ ‖c / z‖ + ‖E‖ := by rw [hq]; exact norm_add_le _ _
      _ ≤ 2 * ‖c‖ / T + A / T ^ 2 := add_le_add hcz hEbound
      _ ≤ (2 * ‖c‖ + A) / T := by
        have hA0 : 0 ≤ A := by simp [A, neutralGammaExponentErrorConst]; positivity
        have hAscale : A / T ^ 2 ≤ A / T := by
          apply div_le_div_of_nonneg_left hA0 hTpos
          nlinarith
        calc
          2 * ‖c‖ / T + A / T ^ 2 ≤ 2 * ‖c‖ / T + A / T :=
            add_le_add le_rfl hAscale
          _ = (2 * ‖c‖ + A) / T := by ring
  have hqsmall : ‖q‖ ≤ 1 := le_trans hqbound (by simpa [c, A] using hsmall)
  have hqSq : ‖q‖ ^ 2 ≤ (2 * ‖c‖ + A) ^ 2 / T ^ 2 := by
    have hnonneg : 0 ≤ (2 * ‖c‖ + A) / T := le_trans (norm_nonneg q) hqbound
    have := (sq_le_sq₀ (norm_nonneg q) hnonneg).2 hqbound
    rw [div_pow] at this
    exact this
  have hexpTaylor := Complex.norm_exp_sub_one_sub_id_le hqsmall
  have hratio : neutralGammaRatio θ z / z ^ (Complex.I * (θ : ℂ)) = Complex.exp q := by
    have hgamma := gamma_imag_shift_exp_integral hzre hθ
    have hΓ0 : Complex.Gamma z ≠ 0 := gamma_ne_zero_of_re_pos hzre
    have hcpow : z ^ (Complex.I * (θ : ℂ)) =
        Complex.exp (Complex.I * (θ : ℂ) * Complex.log z) := by
      rw [Complex.cpow_def_of_ne_zero hz0]
      congr 1
      ring
    have hJsplit : J = Complex.I * (θ : ℂ) * Complex.log z + q := by
      rw [hq, hE]
      ring
    rw [neutralGammaRatio, hgamma, hcpow, ← hJ, hJsplit, Complex.exp_add]
    field_simp [hΓ0, Complex.exp_ne_zero]
  rw [hratio]
  have hsplit : Complex.exp q - (1 + c / z) =
      (Complex.exp q - 1 - q) + E := by rw [hq]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hexpTaylor hEbound) ?_
  refine le_trans (add_le_add hqSq le_rfl) ?_
  rw [hc, hA]
  ring_nf
  exact le_rfl

/-- Principal-log splitting at large positive imaginary height. -/
theorem log_add_imaginary_height_eq {s : ℂ} {T : ℝ} (hT : 2 * ‖s‖ ≤ T)
    (hTpos : 0 < T) :
    Complex.log (s + Complex.I * (T : ℂ)) =
      Complex.log (Complex.I * (T : ℂ)) +
        Complex.log (1 + s / (Complex.I * (T : ℂ))) := by
  set b : ℂ := Complex.I * (T : ℂ) with hb
  set q : ℂ := 1 + s / b with hq
  have hb0 : b ≠ 0 := by
    rw [hb]
    apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast hTpos.ne'
  have hbnorm : ‖b‖ = T := by
    rw [hb, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hTpos]
  have hsq : ‖s / b‖ ≤ 1 / 2 := by
    rw [norm_div, hbnorm, div_le_iff₀ hTpos]
    linarith
  have hqre : 0 < q.re := by
    have hre := Complex.abs_re_le_norm (s / b)
    have hlow : -(1 / 2 : ℝ) ≤ (s / b).re := (abs_le.mp (le_trans hre hsq)).1
    rw [hq]
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hq0 : q ≠ 0 := by
    intro h
    have : q.re = 0 := by rw [h]; simp
    linarith
  have hargb : Complex.arg b = Real.pi / 2 := by
    rw [hb, mul_comm, Complex.arg_real_mul _ hTpos, Complex.arg_I]
  have hargq : |Complex.arg q| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hqre)
  have hsum : Complex.arg b + Complex.arg q ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hargb]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hbounds := abs_lt.mp hargq
    constructor <;> linarith
  have hmul : b * q = s + Complex.I * (T : ℂ) := by
    rw [hb, hq]
    field_simp
    ring
  rw [← hmul, Complex.log_mul_eq_add_log_iff hb0 hq0 |>.mpr hsum]

/-- Quantitative first jet of the complex power carrying the neutral Gamma phase. -/
theorem norm_cpow_add_imaginary_height_ratio_sub_le {θ M T : ℝ}
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hTpos : 0 < T) (hTM : 2 * M ≤ T)
    (hsmall : 3 * θ * M / (2 * T) ≤ 1) (s : ℂ) (hsM : ‖s‖ ≤ M) :
    ‖(s + Complex.I * (T : ℂ)) ^ (Complex.I * (θ : ℂ)) /
          (Complex.I * (T : ℂ)) ^ (Complex.I * (θ : ℂ)) -
        (1 + ((θ / T : ℝ) : ℂ) * s)‖ ≤
      (θ * M ^ 2 + (9 / 4) * θ ^ 2 * M ^ 2) / T ^ 2 := by
  set b : ℂ := Complex.I * (T : ℂ) with hb
  set u : ℂ := s / b with hu
  set v : ℂ := Complex.I * (θ : ℂ) * Complex.log (1 + u) with hv
  set w : ℂ := ((θ / T : ℝ) : ℂ) * s with hw
  have hb0 : b ≠ 0 := by
    rw [hb]
    apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast hTpos.ne'
  have hbnorm : ‖b‖ = T := by
    rw [hb, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hTpos]
  have huNorm : ‖u‖ ≤ M / T := by
    rw [hu, norm_div, hbnorm]
    exact div_le_div_of_nonneg_right hsM hTpos.le
  have hMdiv : M / T ≤ 1 / 2 := by
    rw [div_le_iff₀ hTpos]
    linarith
  have huHalf : ‖u‖ ≤ 1 / 2 := le_trans huNorm hMdiv
  have huLt : ‖u‖ < 1 := lt_of_le_of_lt huHalf (by norm_num)
  have hlogerr : ‖Complex.log (1 + u) - u‖ ≤ M ^ 2 / T ^ 2 := by
    have hraw := Complex.norm_log_one_add_sub_self_le huLt
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hraw' : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
      refine le_trans hraw ?_
      nlinarith [sq_nonneg ‖u‖]
    have hsq := (sq_le_sq₀ (norm_nonneg u) (by positivity : 0 ≤ M / T)).2 huNorm
    rw [div_pow] at hsq
    exact le_trans hraw' hsq
  have hIu : Complex.I * (θ : ℂ) * u = w := by
    rw [hu, hw, hb]
    field_simp
    push_cast
    ring
  have hvw : ‖v - w‖ ≤ θ * M ^ 2 / T ^ 2 := by
    have heq : v - w = Complex.I * (θ : ℂ) * (Complex.log (1 + u) - u) := by
      rw [hv, ← hIu]
      ring
    rw [heq, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hθ]
    calc
      θ * ‖Complex.log (1 + u) - u‖ ≤ θ * (M ^ 2 / T ^ 2) :=
        mul_le_mul_of_nonneg_left hlogerr hθ
      _ = θ * M ^ 2 / T ^ 2 := by ring
  have hwNorm : ‖w‖ ≤ θ * M / T := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hθ hTpos.le)]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsM hθ) hTpos.le
  have hvNorm : ‖v‖ ≤ 3 * θ * M / (2 * T) := by
    have hvtri : ‖v‖ ≤ ‖w‖ + ‖v - w‖ := by
      have := norm_add_le w (v - w)
      rw [add_sub_cancel] at this
      exact this
    have hMT : M / T ≤ 1 / 2 := hMdiv
    have hfactor : θ * M ^ 2 / T ^ 2 ≤ θ * M / (2 * T) := by
      have hθM : 0 ≤ θ * M := mul_nonneg hθ hM
      calc
        θ * M ^ 2 / T ^ 2 = (θ * M / T) * (M / T) := by ring
        _ ≤ (θ * M / T) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hMT (div_nonneg hθM hTpos.le)
        _ = θ * M / (2 * T) := by ring
    calc
      ‖v‖ ≤ ‖w‖ + ‖v - w‖ := hvtri
      _ ≤ θ * M / T + θ * M ^ 2 / T ^ 2 :=
        add_le_add hwNorm hvw
      _ ≤ θ * M / T + θ * M / (2 * T) := add_le_add le_rfl hfactor
      _ = 3 * θ * M / (2 * T) := by ring
  have hvSmall : ‖v‖ ≤ 1 := le_trans hvNorm hsmall
  have hvSq : ‖v‖ ^ 2 ≤ (9 / 4) * θ ^ 2 * M ^ 2 / T ^ 2 := by
    have hright : 0 ≤ 3 * θ * M / (2 * T) := by positivity
    have hsquare := (sq_le_sq₀ (norm_nonneg v) hright).2 hvNorm
    refine le_trans hsquare (le_of_eq ?_)
    ring
  have hexp := Complex.norm_exp_sub_one_sub_id_le hvSmall
  have hpow : (s + Complex.I * (T : ℂ)) ^ (Complex.I * (θ : ℂ)) /
      (Complex.I * (T : ℂ)) ^ (Complex.I * (θ : ℂ)) = Complex.exp v := by
    have hbpow0 : b ^ (Complex.I * (θ : ℂ)) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hb0]
      exact Complex.exp_ne_zero _
    have hlog := log_add_imaginary_height_eq (le_trans (mul_le_mul_of_nonneg_left hsM (by norm_num)) hTM)
      hTpos
    have hnum0 : s + Complex.I * (T : ℂ) ≠ 0 := by
      intro hzero
      have : ‖s‖ = T := by
        have hsEq : s = -(Complex.I * (T : ℂ)) := by linear_combination hzero
        rw [hsEq, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hTpos]
      rw [this] at hsM
      nlinarith
    rw [Complex.cpow_def_of_ne_zero hnum0, Complex.cpow_def_of_ne_zero hb0,
      hlog, ← hb, ← hu]
    have hexponent :
        (Complex.log b + Complex.log (1 + u)) * (Complex.I * (θ : ℂ)) =
          Complex.log b * (Complex.I * (θ : ℂ)) + v := by rw [hv]; ring
    rw [hexponent, Complex.exp_add]
    field_simp [Complex.exp_ne_zero]
  rw [hpow]
  have hsplit : Complex.exp v - (1 + w) = (Complex.exp v - 1 - v) + (v - w) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  exact le_trans (add_le_add hexp hvw) (by
    refine le_trans (add_le_add hvSq le_rfl) (le_of_eq ?_)
    ring)

def neutralGammaAffineConstant (θ : ℝ) : ℂ :=
  (θ : ℂ) * (Complex.I * (θ : ℂ) - 1) / 2

def neutralGammaAffineJet (θ : ℝ) (s : ℂ) : ℂ :=
  (θ : ℂ) * s + neutralGammaAffineConstant θ

def neutralGammaPhase (θ T : ℝ) : ℂ :=
  (Complex.I * (T : ℂ)) ^ (Complex.I * (θ : ℂ))

def neutralGammaPowerErrorConst (θ M : ℝ) : ℝ :=
  θ * M ^ 2 + (9 / 4) * θ ^ 2 * M ^ 2

def neutralGammaRatioErrorConst (θ : ℝ) : ℝ :=
  neutralGammaExponentErrorConst θ +
    (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) ^ 2

def neutralGammaScaledJetErrorConst (θ M : ℝ) : ℝ :=
  neutralGammaPowerErrorConst θ M + 2 * ‖neutralGammaFirstCoeff θ‖ * M +
    neutralGammaRatioErrorConst θ +
    (θ * M + neutralGammaPowerErrorConst θ M) *
      (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaRatioErrorConst θ)

/-- Uniform `O(T⁻¹)` estimate after first-jet scaling on a bounded right-half-plane tube. -/
theorem norm_neutralGamma_scaledPhaseJet_sub_le {θ M T : ℝ}
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hT : 2 * M + 4 ≤ T) (hTθ : 4 * θ ≤ T)
    (hsmallPow : 3 * θ * M / (2 * T) ≤ 1)
    (hsmallRatio :
      (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) / T ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (hsM : ‖s‖ ≤ M) :
    ‖((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (s + Complex.I * (T : ℂ)) - neutralGammaPhase θ T) -
        neutralGammaAffineJet θ s‖ ≤ neutralGammaScaledJetErrorConst θ M / T := by
  set z : ℂ := s + Complex.I * (T : ℂ) with hz
  set b : ℂ := Complex.I * (T : ℂ) with hb
  set phase : ℂ := neutralGammaPhase θ T with hphase
  set c : ℂ := neutralGammaFirstCoeff θ with hc
  set d : ℂ := neutralGammaAffineConstant θ with hd
  set P : ℂ := z ^ (Complex.I * (θ : ℂ)) / phase with hP
  set Q : ℂ := neutralGammaRatio θ z / z ^ (Complex.I * (θ : ℂ)) with hQ
  set ep : ℂ := P - (1 + ((θ / T : ℝ) : ℂ) * s) with hep
  set ec : ℂ := c / z - d / (T : ℂ) with hec
  set eq : ℂ := Q - (1 + c / z) with heq
  have hT4 : (4 : ℝ) ≤ T := by nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT4
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT4
  have hTM : 2 * M ≤ T := by linarith
  have hTim : 2 * |s.im| + 4 ≤ T := by
    have him := Complex.abs_im_le_norm s
    linarith
  have hzNorm : T / 2 ≤ ‖z‖ := by
    have hdist : ‖b‖ ≤ ‖z‖ + ‖s‖ := by
      have := norm_sub_le z s
      have hzs : z - s = b := by rw [hz, hb]; ring
      rw [hzs] at this
      exact this
    have hbNorm : ‖b‖ = T := by
      rw [hb, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hTpos]
    rw [hbNorm] at hdist
    linarith
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < T / 2) hzNorm
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzNormPos
  have hb0 : b ≠ 0 := by
    rw [hb]
    apply mul_ne_zero Complex.I_ne_zero
    exact_mod_cast hTpos.ne'
  have hphaseEq : phase = b ^ (Complex.I * (θ : ℂ)) := by rw [hphase, neutralGammaPhase, hb]
  have hphase0 : phase ≠ 0 := by
    rw [hphaseEq, Complex.cpow_def_of_ne_zero hb0]
    exact Complex.exp_ne_zero _
  have hzpow0 : z ^ (Complex.I * (θ : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hz0]
    exact Complex.exp_ne_zero _
  have hepBound : ‖ep‖ ≤ neutralGammaPowerErrorConst θ M / T ^ 2 := by
    rw [hep, hP, hphaseEq, hz, hb]
    simpa [neutralGammaPowerErrorConst] using
      norm_cpow_add_imaginary_height_ratio_sub_le hθ hM hTpos hTM hsmallPow s hsM
  have heqBound : ‖eq‖ ≤ neutralGammaRatioErrorConst θ / T ^ 2 := by
    rw [heq, hQ, hz, hc]
    simpa [neutralGammaRatioErrorConst] using
      norm_neutralGammaRatio_div_cpow_sub_le hθ s hs hTim hTθ hsmallRatio
  have hcOverZ : ‖c / z‖ ≤ 2 * ‖c‖ / T := by
    rw [norm_div, div_le_div_iff₀ hzNormPos hTpos]
    nlinarith [norm_nonneg c]
  have hcOverB : c / b = d / (T : ℂ) := by
    rw [hc, hd, hb, neutralGammaFirstCoeff, neutralGammaAffineConstant]
    field_simp
  have hecBound : ‖ec‖ ≤ 2 * ‖c‖ * M / T ^ 2 := by
    have hfrac : 1 / z - 1 / b = -s / (z * b) := by
      have hzb : b - z = -s := by rw [hb, hz]; ring
      calc
        1 / z - 1 / b = (b - z) / (z * b) := by field_simp [hz0, hb0]
        _ = -s / (z * b) := by rw [hzb]
    have hecEq : ec = c * (1 / z - 1 / b) := by
      rw [hec, ← hcOverB]
      field_simp [hz0, hb0]
    rw [hecEq, hfrac, norm_mul, norm_div, norm_neg, norm_mul]
    have hbNorm : ‖b‖ = T := by
      rw [hb, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hTpos]
    rw [hbNorm]
    have hbase : ‖s‖ / (‖z‖ * T) ≤ 2 * M / T ^ 2 := by
      have hden : T ^ 2 / 2 ≤ ‖z‖ * T := by
        nlinarith [mul_le_mul_of_nonneg_right hzNorm hTpos.le]
      calc
        ‖s‖ / (‖z‖ * T) ≤ M / (‖z‖ * T) :=
          div_le_div_of_nonneg_right hsM (mul_nonneg (norm_nonneg z) hTpos.le)
        _ ≤ M / (T ^ 2 / 2) :=
          div_le_div_of_nonneg_left hM (by positivity) hden
        _ = 2 * M / T ^ 2 := by field_simp
    calc
      ‖c‖ * (‖s‖ / (‖z‖ * T)) ≤ ‖c‖ * (2 * M / T ^ 2) :=
        mul_le_mul_of_nonneg_left hbase (norm_nonneg c)
      _ = 2 * ‖c‖ * M / T ^ 2 := by ring
  have hPminus : ‖P - 1‖ ≤
      (θ * M + neutralGammaPowerErrorConst θ M) / T := by
    have hsplit : P - 1 = ep + ((θ / T : ℝ) : ℂ) * s := by rw [hep]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hlin : ‖((θ / T : ℝ) : ℂ) * s‖ ≤ θ * M / T := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hθ hTpos.le), div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsM hθ) hTpos.le
    have hpowScale : neutralGammaPowerErrorConst θ M / T ^ 2 ≤
        neutralGammaPowerErrorConst θ M / T := by
      have hC0 : 0 ≤ neutralGammaPowerErrorConst θ M := by
        simp [neutralGammaPowerErrorConst]
        positivity
      exact div_le_div_of_nonneg_left hC0 hTpos (by nlinarith)
    refine le_trans (add_le_add hepBound hlin) ?_
    calc
      neutralGammaPowerErrorConst θ M / T ^ 2 + θ * M / T ≤
          neutralGammaPowerErrorConst θ M / T + θ * M / T :=
        add_le_add hpowScale le_rfl
      _ = (θ * M + neutralGammaPowerErrorConst θ M) / T := by ring
  have htail : ‖c / z + eq‖ ≤
      (2 * ‖c‖ + neutralGammaRatioErrorConst θ) / T := by
    refine le_trans (norm_add_le _ _) ?_
    have hC0 : 0 ≤ neutralGammaRatioErrorConst θ := by
      simp [neutralGammaRatioErrorConst, neutralGammaExponentErrorConst]
      positivity
    have heqScale : neutralGammaRatioErrorConst θ / T ^ 2 ≤
        neutralGammaRatioErrorConst θ / T :=
      div_le_div_of_nonneg_left hC0 hTpos (by nlinarith)
    refine le_trans (add_le_add hcOverZ heqBound) (le_trans (add_le_add le_rfl heqScale) ?_)
    ring_nf
    exact le_rfl
  have hRQ : neutralGammaRatio θ z / phase = P * Q := by
    rw [hP, hQ]
    field_simp [hphase0, hzpow0]
  have hmain : neutralGammaRatio θ z / phase -
        (1 + (neutralGammaAffineJet θ s) / (T : ℂ)) =
      ep + ec + eq + (P - 1) * (c / z + eq) := by
    have htheta : ((θ / T : ℝ) : ℂ) * s = (θ : ℂ) * s / (T : ℂ) := by
      push_cast
      field_simp [hTpos.ne']
    rw [hRQ, heq, hep, hec, neutralGammaAffineJet, hd]
    rw [htheta]
    field_simp [hTpos.ne']
    ring
  have hmainBound : ‖neutralGammaRatio θ z / phase -
        (1 + neutralGammaAffineJet θ s / (T : ℂ))‖ ≤
      neutralGammaScaledJetErrorConst θ M / T ^ 2 := by
    rw [hmain]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _)) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    have hPright0 : 0 ≤ (θ * M + neutralGammaPowerErrorConst θ M) / T :=
      le_trans (norm_nonneg (P - 1)) hPminus
    refine le_trans
      (add_le_add (add_le_add (add_le_add hepBound hecBound) heqBound)
        (mul_le_mul hPminus htail (norm_nonneg _) hPright0)) ?_
    rw [neutralGammaScaledJetErrorConst, ← hc]
    ring_nf
    exact le_rfl
  have hscaled : ((T : ℂ) / phase) * (neutralGammaRatio θ z - phase) -
      neutralGammaAffineJet θ s =
      (T : ℂ) * (neutralGammaRatio θ z / phase -
        (1 + neutralGammaAffineJet θ s / (T : ℂ))) := by
    field_simp [hphase0, hTpos.ne']
    ring
  rw [hscaled]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
  refine le_trans (mul_le_mul_of_nonneg_left hmainBound hTpos.le) (le_of_eq ?_)
  field_simp

/-- Locally uniform first-jet convergence on the open right half-plane. -/
theorem tendstoLocallyUniformly_neutralGamma_scaledPhaseJet_rePos {θ : ℝ} (hθ : 0 ≤ θ) :
    TendstoLocallyUniformly
      (fun T : ℝ => fun s : {z : ℂ // 0 < z.re} =>
        ((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (s.1 + Complex.I * (T : ℂ)) - neutralGammaPhase θ T))
      (fun s : {z : ℂ // 0 < z.re} => neutralGammaAffineJet θ s.1) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  set M : ℝ := ‖x.1‖ + 1 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  set D : ℝ := neutralGammaScaledJetErrorConst θ M with hD
  have hD0 : 0 ≤ D := by
    have hpow0 : 0 ≤ neutralGammaPowerErrorConst θ M := by
      simp [neutralGammaPowerErrorConst]
      positivity
    have hexp0 : 0 ≤ neutralGammaExponentErrorConst θ := by
      simp [neutralGammaExponentErrorConst]
      positivity
    have hratio0 : 0 ≤ neutralGammaRatioErrorConst θ := by
      simp [neutralGammaRatioErrorConst]
      positivity
    simp [D, neutralGammaScaledJetErrorConst]
    positivity
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  let K : ℝ := max (2 * M + 4) (max (4 * θ)
    (max (3 * θ * M) (max (2 * ‖neutralGammaFirstCoeff θ‖ +
      neutralGammaExponentErrorConst θ) (D / ε + 1))))
  filter_upwards [eventually_ge_atTop K] with T hTK
  intro y hy
  have hyM : ‖y.1‖ ≤ M := by
    have hdist : dist y x < 1 := Metric.mem_ball.mp hy
    have hsub : ‖y.1‖ - ‖x.1‖ ≤ ‖y.1 - x.1‖ := norm_sub_norm_le y.1 x.1
    have hdistval : ‖y.1 - x.1‖ < 1 := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hdist
    rw [hM]
    linarith
  have hmainT : 2 * M + 4 ≤ T := le_trans (le_max_left _ _) hTK
  have hθT : 4 * θ ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hTK)
  have hpowT : 3 * θ * M ≤ T :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hTK))
  have hratioT : 2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ ≤ T :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hTK)))
  have hDT : D / ε + 1 ≤ T :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) hTK)))
  have hT4 : (4 : ℝ) ≤ T := by nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT4
  have hsmallPow : 3 * θ * M / (2 * T) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * T)]
    nlinarith
  have hsmallRatio :
      (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) / T ≤ 1 := by
    rw [div_le_iff₀ hTpos]
    linarith
  have hbound := norm_neutralGamma_scaledPhaseJet_sub_le hθ hM0 hmainT hθT
    hsmallPow hsmallRatio y.1 y.2 hyM
  have hDeps : D / T < ε := by
    rw [div_lt_iff₀ hTpos]
    have hcross : D < T * ε := by
      have : D / ε < T := by linarith
      rw [div_lt_iff₀ hε] at this
      nlinarith
    simpa [mul_comm] using hcross
  have hbound' :
      ‖((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (y.1 + Complex.I * (T : ℂ)) - neutralGammaPhase θ T) -
        neutralGammaAffineJet θ y.1‖ ≤ D / T := by simpa [hD] using hbound
  rw [dist_eq_norm]
  calc
    ‖neutralGammaAffineJet θ y.1 -
        ((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (y.1 + Complex.I * (T : ℂ)) - neutralGammaPhase θ T)‖ =
      ‖((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (y.1 + Complex.I * (T : ℂ)) - neutralGammaPhase θ T) -
        neutralGammaAffineJet θ y.1‖ := norm_sub_rev _ _
    _ ≤ D / T := hbound'
    _ < ε := hDeps

/-- One factor in the finite Pochhammer quotient used to move a vertical Gamma ratio into the
open right half-plane. -/
def neutralGammaRecurrenceTerm (θ : ℝ) (j : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  -(Complex.I * (θ : ℂ)) /
    (s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ))

/-- Finite Pochhammer quotient transporting `G_θ(s+iT+n)` back to `G_θ(s+iT)`. -/
def neutralGammaRecurrenceFactor (θ : ℝ) (n : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 + neutralGammaRecurrenceTerm θ j T s)

lemma neutralGamma_recurrence_denom_norm_ge {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (s : ℂ) (hs : ‖s‖ ≤ M) (j : ℕ) :
    T / 2 ≤ ‖s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ)‖ := by
  let d : ℂ := s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ)
  have hsim : |s.im| ≤ M := le_trans (Complex.abs_im_le_norm s) hs
  have hdIm : d.im = s.im + T + θ := by simp [d]
  have hdImLower : T / 2 ≤ d.im := by
    rw [hdIm]
    have hsLow : -M ≤ s.im := le_trans (neg_le_neg hsim) (neg_abs_le s.im)
    nlinarith
  have himNorm : |d.im| ≤ ‖d‖ := Complex.abs_im_le_norm d
  have hdIm0 : 0 ≤ d.im := le_trans (by
    have : 0 ≤ T := by nlinarith
    positivity) hdImLower
  rw [abs_of_nonneg hdIm0] at himNorm
  exact le_trans hdImLower himNorm

lemma norm_neutralGammaRecurrenceTerm_le {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (s : ℂ) (hs : ‖s‖ ≤ M) (j : ℕ) :
    ‖neutralGammaRecurrenceTerm θ j T s‖ ≤ 2 * θ / T := by
  have hTpos : 0 < T := by nlinarith
  have hden := neutralGamma_recurrence_denom_norm_ge hθ hM hT s hs j
  have hdenpos : 0 < ‖s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ)‖ := by
    have : 0 < T / 2 := by positivity
    linarith
  rw [neutralGammaRecurrenceTerm, norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
  rw [div_le_div_iff₀ hdenpos hTpos]
  nlinarith

lemma norm_neutralGammaRecurrenceTerm_firstJet_le {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (s : ℂ) (hs : ‖s‖ ≤ M) (j : ℕ)
    (hj : j ≤ n) :
    ‖(T : ℂ) * neutralGammaRecurrenceTerm θ j T s + (θ : ℂ)‖ ≤
      2 * θ * (M + θ + n) / T := by
  have hTpos : 0 < T := by nlinarith
  let d : ℂ := s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ)
  have hden := neutralGamma_recurrence_denom_norm_ge hθ hM hT s hs j
  have hdenpos : 0 < ‖d‖ := by
    have : 0 < T / 2 := by positivity
    simpa [d] using lt_of_lt_of_le this hden
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdenpos
  have hd0' : s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ) ≠ 0 := by
    simpa [d] using hd0
  have hq0 : (T : ℂ) * Complex.I + Complex.I * (θ : ℂ) + s + (j : ℂ) ≠ 0 := by
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hd0'
  have hq1 : (θ : ℂ) * Complex.I + (T : ℂ) * Complex.I + s + (j : ℂ) ≠ 0 := by
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hd0'
  have heq :
      (T : ℂ) * neutralGammaRecurrenceTerm θ j T s + (θ : ℂ) =
        (θ : ℂ) * (s + Complex.I * (θ : ℂ) + (j : ℂ)) / d := by
    rw [neutralGammaRecurrenceTerm]
    change (T : ℂ) * (-(Complex.I * (θ : ℂ)) / d) + (θ : ℂ) =
      (θ : ℂ) * (s + Complex.I * (θ : ℂ) + (j : ℂ)) / d
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hcancel : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0
    calc
      (T : ℂ) * (-(Complex.I * (θ : ℂ)) * d⁻¹) + (θ : ℂ) =
          (T : ℂ) * (-(Complex.I * (θ : ℂ)) * d⁻¹) +
            (θ : ℂ) * (d * d⁻¹) := by rw [hcancel, mul_one]
      _ = (θ : ℂ) * (s + Complex.I * (θ : ℂ) + (j : ℂ)) * d⁻¹ := by
        dsimp [d]
        ring
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
  have hc : ‖s + Complex.I * (θ : ℂ) + (j : ℂ)‖ ≤ M + θ + n := by
    calc
      ‖s + Complex.I * (θ : ℂ) + (j : ℂ)‖
          ≤ ‖s‖ + ‖Complex.I * (θ : ℂ)‖ + ‖(j : ℂ)‖ := by
            calc
              _ ≤ ‖s + Complex.I * (θ : ℂ)‖ + ‖(j : ℂ)‖ := norm_add_le _ _
              _ ≤ (‖s‖ + ‖Complex.I * (θ : ℂ)‖) + ‖(j : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ = ‖s‖ + θ + j := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hθ, Complex.norm_natCast]
      _ ≤ M + θ + n := by
        have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
        exact add_le_add (add_le_add hs le_rfl) hjR
  rw [div_le_div_iff₀ hdenpos hTpos]
  have hC0 : 0 ≤ M + θ + (n : ℝ) := by positivity
  have hleft : θ * ‖s + Complex.I * (θ : ℂ) + (j : ℂ)‖ ≤
      θ * (M + θ + n) := mul_le_mul_of_nonneg_left hc hθ
  have hden2 : T ≤ 2 * ‖d‖ := by linarith
  calc
    θ * ‖s + Complex.I * (θ : ℂ) + (j : ℂ)‖ * T
        ≤ (θ * (M + θ + n)) * T := mul_le_mul_of_nonneg_right hleft hTpos.le
    _ ≤ (θ * (M + θ + n)) * (2 * ‖d‖) :=
      mul_le_mul_of_nonneg_left hden2 (mul_nonneg hθ hC0)
    _ = 2 * θ * (M + θ + n) * ‖d‖ := by ring

/-- Exact factorization of the Pochhammer transport factor into near-one resolvents. -/
lemma neutralGammaRecurrenceFactor_eq_pochhammer_div {θ T : ℝ} {n : ℕ} {s : ℂ}
    (hne : ∀ j ∈ Finset.range n,
      s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ) ≠ 0) :
    neutralGammaRecurrenceFactor θ n T s =
      (∏ j ∈ Finset.range n, (s + Complex.I * (T : ℂ) + (j : ℂ))) /
        (∏ j ∈ Finset.range n,
          (s + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) + (j : ℂ))) := by
  rw [neutralGammaRecurrenceFactor, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [neutralGammaRecurrenceTerm]
  field_simp [hne j hj]
  ring

lemma sum_norm_neutralGammaRecurrenceTerm_le {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (s : ℂ) (hs : ‖s‖ ≤ M) (n : ℕ) :
    ∑ j ∈ Finset.range n, ‖neutralGammaRecurrenceTerm θ j T s‖ ≤
      2 * n * θ / T := by
  have hTpos : 0 < T := by nlinarith
  calc
    ∑ j ∈ Finset.range n, ‖neutralGammaRecurrenceTerm θ j T s‖
        ≤ ∑ _j ∈ Finset.range n, 2 * θ / T := by
          apply Finset.sum_le_sum
          intro j hj
          exact norm_neutralGammaRecurrenceTerm_le hθ hM hT s hs j
    _ = 2 * n * θ / T := by simp; ring

lemma norm_neutralGammaRecurrenceFactor_le {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (hTθ : 2 * θ ≤ T)
    (s : ℂ) (hs : ‖s‖ ≤ M) (n : ℕ) :
    ‖neutralGammaRecurrenceFactor θ n T s‖ ≤ 2 ^ n := by
  have hTpos : 0 < T := by nlinarith
  rw [neutralGammaRecurrenceFactor, norm_prod]
  calc
    ∏ j ∈ Finset.range n, ‖1 + neutralGammaRecurrenceTerm θ j T s‖
        ≤ ∏ _j ∈ Finset.range n, (2 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            calc
              ‖1 + neutralGammaRecurrenceTerm θ j T s‖
                  ≤ 1 + ‖neutralGammaRecurrenceTerm θ j T s‖ := by
                    simpa only [norm_one] using
                      norm_add_le (1 : ℂ) (neutralGammaRecurrenceTerm θ j T s)
              _ ≤ 1 + 2 * θ / T := by
                gcongr
                exact norm_neutralGammaRecurrenceTerm_le hθ hM hT s hs j
              _ ≤ 2 := by
                have hfrac : 2 * θ / T ≤ 1 := (div_le_one hTpos).2 hTθ
                linarith
    _ = 2 ^ n := by simp

lemma norm_neutralGammaRecurrenceFactor_sub_one_le {θ M T : ℝ} {n : ℕ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (hTn : 2 * n * θ ≤ T)
    (s : ℂ) (hs : ‖s‖ ≤ M) :
    ‖neutralGammaRecurrenceFactor θ n T s - 1‖ ≤ 4 * n * θ / T := by
  have hTpos : 0 < T := by nlinarith
  let S : ℝ := ∑ j ∈ Finset.range n, ‖neutralGammaRecurrenceTerm θ j T s‖
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSbound : S ≤ 2 * n * θ / T :=
    sum_norm_neutralGammaRecurrenceTerm_le hθ hM hT s hs n
  have hSone : S ≤ 1 := by
    apply le_trans hSbound
    exact (div_le_one hTpos).2 hTn
  have hprod := Finset.norm_prod_one_add_sub_one_le
    (Finset.range n) (fun j => neutralGammaRecurrenceTerm θ j T s)
  have hexp : Real.exp S - 1 ≤ 2 * S := by
    have habs := Real.abs_exp_sub_one_le (x := S) (by rw [abs_of_nonneg hS0]; exact hSone)
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hS0))] at habs
    simpa [abs_of_nonneg hS0] using habs
  rw [← neutralGammaRecurrenceFactor] at hprod
  calc
    ‖neutralGammaRecurrenceFactor θ n T s - 1‖
        ≤ Real.exp S - 1 := by simpa [S] using hprod
    _ ≤ 2 * S := hexp
    _ ≤ 2 * (2 * n * θ / T) := mul_le_mul_of_nonneg_left hSbound (by norm_num)
    _ = 4 * n * θ / T := by ring

/-- Explicit error constant for the first jet of the finite recurrence factor. -/
def neutralGammaRecurrenceJetErrorConst (θ M : ℝ) (n : ℕ) : ℝ :=
  8 * n ^ 2 * θ ^ 2 + 2 * n * θ * (M + θ + n)

lemma norm_neutralGammaRecurrenceFactor_firstJet_le {θ M T : ℝ} {n : ℕ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (hTn : 2 * n * θ ≤ T)
    (s : ℂ) (hs : ‖s‖ ≤ M) :
    ‖(T : ℂ) * (neutralGammaRecurrenceFactor θ n T s - 1) + (n : ℂ) * (θ : ℂ)‖ ≤
      neutralGammaRecurrenceJetErrorConst θ M n / T := by
  have hTpos : 0 < T := by nlinarith
  let u : ℕ → ℂ := fun j => neutralGammaRecurrenceTerm θ j T s
  let S : ℝ := ∑ j ∈ Finset.range n, ‖u j‖
  let E : ℂ := neutralGammaRecurrenceFactor θ n T s - 1 -
    ∑ j ∈ Finset.range n, u j
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSbound : S ≤ 2 * n * θ / T := by
    simpa [S, u] using sum_norm_neutralGammaRecurrenceTerm_le hθ hM hT s hs n
  have hSone : S ≤ 1 := by
    apply le_trans hSbound
    exact (div_le_one hTpos).2 hTn
  have hEraw := norm_prod_one_add_sub_one_sub_sum_le (Finset.range n) u
  have hExp : Real.exp S - 1 ≤ 2 * S := by
    have habs := Real.abs_exp_sub_one_le (x := S) (by rw [abs_of_nonneg hS0]; exact hSone)
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hS0))] at habs
    simpa [abs_of_nonneg hS0] using habs
  have hE : ‖E‖ ≤ 8 * n ^ 2 * θ ^ 2 / T ^ 2 := by
    have hbase : ‖E‖ ≤ S * (Real.exp S - 1) := by
      simpa [E, u, neutralGammaRecurrenceFactor] using hEraw
    calc
      ‖E‖ ≤ S * (Real.exp S - 1) := hbase
      _ ≤ S * (2 * S) := mul_le_mul_of_nonneg_left hExp hS0
      _ ≤ (2 * n * θ / T) * (2 * (2 * n * θ / T)) := by
        have h2S : 2 * S ≤ 2 * (2 * n * θ / T) :=
          mul_le_mul_of_nonneg_left hSbound (by norm_num)
        exact mul_le_mul hSbound h2S (by positivity) (by positivity)
      _ = 8 * n ^ 2 * θ ^ 2 / T ^ 2 := by field_simp; ring
  have hsum :
      ‖∑ j ∈ Finset.range n, ((T : ℂ) * u j + (θ : ℂ))‖ ≤
        2 * n * θ * (M + θ + n) / T := by
    calc
      ‖∑ j ∈ Finset.range n, ((T : ℂ) * u j + (θ : ℂ))‖
          ≤ ∑ j ∈ Finset.range n, ‖(T : ℂ) * u j + (θ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 2 * θ * (M + θ + n) / T := by
        apply Finset.sum_le_sum
        intro j hj
        exact norm_neutralGammaRecurrenceTerm_firstJet_le hθ hM hT s hs j
          (Nat.le_of_lt (Finset.mem_range.mp hj))
      _ = 2 * n * θ * (M + θ + n) / T := by simp; ring
  have hdecomp :
      (T : ℂ) * (neutralGammaRecurrenceFactor θ n T s - 1) + (n : ℂ) * (θ : ℂ) =
        (T : ℂ) * E + ∑ j ∈ Finset.range n, ((T : ℂ) * u j + (θ : ℂ)) := by
    dsimp only [E]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [hdecomp]
  calc
    ‖(T : ℂ) * E + ∑ j ∈ Finset.range n, ((T : ℂ) * u j + (θ : ℂ))‖
        ≤ ‖(T : ℂ) * E‖ + ‖∑ j ∈ Finset.range n, ((T : ℂ) * u j + (θ : ℂ))‖ :=
          norm_add_le _ _
    _ ≤ T * (8 * n ^ 2 * θ ^ 2 / T ^ 2) +
        2 * n * θ * (M + θ + n) / T := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
      gcongr
    _ = neutralGammaRecurrenceJetErrorConst θ M n / T := by
      rw [neutralGammaRecurrenceJetErrorConst]
      field_simp

/-- Exact finite recurrence transporting a sufficiently high vertical Gamma ratio from `s+n`
back to `s`. -/
theorem neutralGammaRatio_eq_recurrenceFactor_mul_add_nat {θ M T : ℝ} (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hT : 2 * (M + θ + 1) ≤ T) (s : ℂ) (hs : ‖s‖ ≤ M) (n : ℕ) :
    neutralGammaRatio θ (s + Complex.I * (T : ℂ)) =
      neutralGammaRecurrenceFactor θ n T s *
        neutralGammaRatio θ (s + (n : ℂ) + Complex.I * (T : ℂ)) := by
  classical
  let z : ℂ := s + Complex.I * (T : ℂ)
  let P0 : ℂ := ∏ j ∈ Finset.range n, (z + (j : ℂ))
  let Pθ : ℂ := ∏ j ∈ Finset.range n, (z + Complex.I * (θ : ℂ) + (j : ℂ))
  have hT0 : 2 * (M + 0 + 1) ≤ T := by nlinarith
  have hP0Factors : ∀ j ∈ Finset.range n, z + (j : ℂ) ≠ 0 := by
    intro j hj
    have hnorm := neutralGamma_recurrence_denom_norm_ge (θ := 0) (M := M) (T := T)
      (by norm_num) hM hT0 s hs j
    have hTpos : 0 < T := by nlinarith
    have : 0 < ‖z + (j : ℂ)‖ := by
      have : 0 < T / 2 := by positivity
      simpa [z] using lt_of_lt_of_le this hnorm
    exact norm_pos_iff.mp this
  have hPθFactors : ∀ j ∈ Finset.range n,
      z + Complex.I * (θ : ℂ) + (j : ℂ) ≠ 0 := by
    intro j hj
    have hnorm := neutralGamma_recurrence_denom_norm_ge hθ hM hT s hs j
    have hTpos : 0 < T := by nlinarith
    have : 0 < ‖z + Complex.I * (θ : ℂ) + (j : ℂ)‖ := by
      have : 0 < T / 2 := by positivity
      simpa [z] using lt_of_lt_of_le this hnorm
    exact norm_pos_iff.mp this
  have hP0 : P0 ≠ 0 := by
    dsimp [P0]
    exact Finset.prod_ne_zero_iff.mpr hP0Factors
  have hPθ : Pθ ≠ 0 := by
    dsimp [Pθ]
    exact Finset.prod_ne_zero_iff.mpr hPθFactors
  have hΓz : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have him := congrArg Complex.im hm
    have hsim : |s.im| ≤ M := le_trans (Complex.abs_im_le_norm s) hs
    simp [z] at him
    nlinarith [neg_abs_le s.im]
  have hΓθ : Complex.Gamma (z + Complex.I * (θ : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have him := congrArg Complex.im hm
    have hsim : |s.im| ≤ M := le_trans (Complex.abs_im_le_norm s) hs
    simp [z] at him
    nlinarith [neg_abs_le s.im]
  have hΓ0shift : Complex.Gamma (z + (n : ℂ)) = P0 * Complex.Gamma z := by
    simpa [P0] using HTGeometry.Gamma_add_nat z n
      (fun j hj => hP0Factors j (Finset.mem_range.mpr hj))
  have hΓθshift :
      Complex.Gamma ((z + Complex.I * (θ : ℂ)) + (n : ℂ)) =
        Pθ * Complex.Gamma (z + Complex.I * (θ : ℂ)) := by
    simpa [Pθ, add_assoc] using HTGeometry.Gamma_add_nat
      (z + Complex.I * (θ : ℂ)) n
      (fun j hj => hPθFactors j (Finset.mem_range.mpr hj))
  have hR : neutralGammaRecurrenceFactor θ n T s = P0 / Pθ := by
    simpa [P0, Pθ, z, add_assoc] using
      neutralGammaRecurrenceFactor_eq_pochhammer_div (θ := θ) (T := T) (n := n) (s := s)
        (fun j hj => by simpa [z, add_assoc] using hPθFactors j hj)
  rw [neutralGammaRatio, neutralGammaRatio, hR]
  have hnumArg :
      s + (n : ℂ) + Complex.I * (T : ℂ) + Complex.I * (θ : ℂ) =
        (z + Complex.I * (θ : ℂ)) + (n : ℂ) := by dsimp [z]; ring
  have hdenArg : s + (n : ℂ) + Complex.I * (T : ℂ) = z + (n : ℂ) := by dsimp [z]; ring
  rw [hnumArg, hdenArg, hΓθshift, hΓ0shift]
  field_simp [hP0, hPθ, hΓz, hΓθ]
  simp [z, hΓz]

/-- Explicit error constant after transporting the right-half-plane Gamma first jet by `n`
recurrence steps. -/
def neutralGammaGlobalJetErrorConst (θ M : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * neutralGammaScaledJetErrorConst θ (M + n) +
    4 * n * θ * (θ * (M + n) + ‖neutralGammaAffineConstant θ‖) +
      neutralGammaRecurrenceJetErrorConst θ M n

/-- Quantitative Gamma-ratio first jet at an arbitrary bounded base point, after a finite shift
into the open right half-plane. -/
theorem norm_neutralGamma_scaledPhaseJet_sub_le_of_add_nat {θ M T : ℝ} {n : ℕ}
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hshift : 0 < (s + (n : ℂ)).re)
    (hs : ‖s‖ ≤ M) (hrecT : 2 * (M + θ + 1) ≤ T)
    (hcoreT : 2 * (M + n) + 4 ≤ T) (hθT : 4 * θ ≤ T)
    (hsmallPow : 3 * θ * (M + n) / (2 * T) ≤ 1)
    (hsmallRatio :
      (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) / T ≤ 1)
    (hTn : 2 * n * θ ≤ T) :
    ‖((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (s + Complex.I * (T : ℂ)) - neutralGammaPhase θ T) -
        neutralGammaAffineJet θ s‖ ≤ neutralGammaGlobalJetErrorConst θ M n / T := by
  let sN : ℂ := s + (n : ℂ)
  let phase : ℂ := neutralGammaPhase θ T
  let R : ℂ := neutralGammaRecurrenceFactor θ n T s
  let A : ℂ := ((T : ℂ) / phase) *
    (neutralGammaRatio θ (sN + Complex.I * (T : ℂ)) - phase)
  have hTpos : 0 < T := by nlinarith
  have hMN0 : 0 ≤ M + (n : ℝ) := by positivity
  have hsN : ‖sN‖ ≤ M + n := by
    calc
      ‖sN‖ ≤ ‖s‖ + ‖(n : ℂ)‖ := by simpa [sN] using norm_add_le s (n : ℂ)
      _ = ‖s‖ + n := by rw [Complex.norm_natCast]
      _ ≤ M + n := by simpa [add_comm] using add_le_add_right hs (n : ℝ)
  have hA : ‖A - neutralGammaAffineJet θ sN‖ ≤
      neutralGammaScaledJetErrorConst θ (M + n) / T := by
    simpa [A, phase, sN] using norm_neutralGamma_scaledPhaseJet_sub_le hθ hMN0
      hcoreT hθT hsmallPow hsmallRatio sN (by simpa [sN] using hshift) hsN
  have hRnorm : ‖R‖ ≤ 2 ^ n := by
    simpa [R] using norm_neutralGammaRecurrenceFactor_le hθ hM hrecT
      (by nlinarith : 2 * θ ≤ T) s hs n
  have hRsub : ‖R - 1‖ ≤ 4 * n * θ / T := by
    simpa [R] using norm_neutralGammaRecurrenceFactor_sub_one_le hθ hM hrecT hTn s hs
  have hRjet : ‖(T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ)‖ ≤
      neutralGammaRecurrenceJetErrorConst θ M n / T := by
    simpa [R] using norm_neutralGammaRecurrenceFactor_firstJet_le hθ hM hrecT hTn s hs
  have hphase0 : phase ≠ 0 := by
    have hb0 : Complex.I * (T : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hTpos.ne')
    dsimp only [phase]
    rw [neutralGammaPhase, Complex.cpow_def_of_ne_zero hb0]
    exact Complex.exp_ne_zero _
  have hrec := neutralGammaRatio_eq_recurrenceFactor_mul_add_nat hθ hM hrecT s hs n
  have htransport :
      ((T : ℂ) / phase) *
          (neutralGammaRatio θ (s + Complex.I * (T : ℂ)) - phase) =
        R * A + (T : ℂ) * (R - 1) := by
    rw [hrec]
    change ((T : ℂ) / phase) *
        (R * neutralGammaRatio θ (sN + Complex.I * (T : ℂ)) - phase) =
      R * A + (T : ℂ) * (R - 1)
    dsimp only [A]
    field_simp [hphase0]
    ring
  have hjetShift : neutralGammaAffineJet θ sN =
      neutralGammaAffineJet θ s + (n : ℂ) * (θ : ℂ) := by
    simp only [neutralGammaAffineJet]
    dsimp [sN]
    ring
  have hdecomp :
      ((T : ℂ) / phase) *
          (neutralGammaRatio θ (s + Complex.I * (T : ℂ)) - phase) -
        neutralGammaAffineJet θ s =
      R * (A - neutralGammaAffineJet θ sN) +
        (R - 1) * neutralGammaAffineJet θ sN +
          ((T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ)) := by
    rw [htransport, hjetShift]
    ring
  have hLN : ‖neutralGammaAffineJet θ sN‖ ≤
      θ * (M + n) + ‖neutralGammaAffineConstant θ‖ := by
    rw [neutralGammaAffineJet]
    calc
      ‖(θ : ℂ) * sN + neutralGammaAffineConstant θ‖
          ≤ ‖(θ : ℂ) * sN‖ + ‖neutralGammaAffineConstant θ‖ := norm_add_le _ _
      _ = θ * ‖sN‖ + ‖neutralGammaAffineConstant θ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
      _ ≤ θ * (M + n) + ‖neutralGammaAffineConstant θ‖ := by gcongr
  rw [hdecomp]
  calc
    ‖R * (A - neutralGammaAffineJet θ sN) +
        (R - 1) * neutralGammaAffineJet θ sN +
          ((T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ))‖
        ≤ ‖R * (A - neutralGammaAffineJet θ sN)‖ +
            ‖(R - 1) * neutralGammaAffineJet θ sN‖ +
              ‖(T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ)‖ := by
          calc
            _ ≤ ‖R * (A - neutralGammaAffineJet θ sN) +
                  (R - 1) * neutralGammaAffineJet θ sN‖ +
                ‖(T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ)‖ := norm_add_le _ _
            _ ≤ (‖R * (A - neutralGammaAffineJet θ sN)‖ +
                  ‖(R - 1) * neutralGammaAffineJet θ sN‖) +
                ‖(T : ℂ) * (R - 1) + (n : ℂ) * (θ : ℂ)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 2 ^ n * (neutralGammaScaledJetErrorConst θ (M + n) / T) +
          (4 * n * θ / T) *
            (θ * (M + n) + ‖neutralGammaAffineConstant θ‖) +
          neutralGammaRecurrenceJetErrorConst θ M n / T := by
      rw [norm_mul, norm_mul]
      gcongr
    _ = neutralGammaGlobalJetErrorConst θ M n / T := by
      rw [neutralGammaGlobalJetErrorConst]
      ring

/-- Locally uniform first-jet convergence of the neutral Gamma ratio on the whole complex plane. -/
theorem tendstoLocallyUniformly_neutralGamma_scaledPhaseJet {θ : ℝ} (hθ : 0 ≤ θ) :
    TendstoLocallyUniformly
      (fun T : ℝ => fun s : ℂ =>
        ((T : ℂ) / neutralGammaPhase θ T) *
          (neutralGammaRatio θ (s + Complex.I * (T : ℂ)) - neutralGammaPhase θ T))
      (neutralGammaAffineJet θ) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (-x.re + 2)
  let M : ℝ := ‖x‖ + 1
  let D : ℝ := neutralGammaGlobalJetErrorConst θ M n
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hExp0 : 0 ≤ neutralGammaExponentErrorConst θ := by
    simp [neutralGammaExponentErrorConst]
    positivity
  have hD0 : 0 ≤ D := by
    have hscaled0 : 0 ≤ neutralGammaScaledJetErrorConst θ (M + n) := by
      simp [neutralGammaScaledJetErrorConst, neutralGammaPowerErrorConst,
        neutralGammaRatioErrorConst, neutralGammaExponentErrorConst]
      positivity
    have hrec0 : 0 ≤ neutralGammaRecurrenceJetErrorConst θ M n := by
      simp [neutralGammaRecurrenceJetErrorConst]
      positivity
    simp [D, neutralGammaGlobalJetErrorConst]
    positivity
  let K : ℝ :=
    2 * (M + θ + 1) +
    (2 * (M + n) + 4) +
    4 * θ +
    3 * θ * (M + n) +
    (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) +
    2 * n * θ +
    (D / ε + 1)
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop K] with T hTK
  intro y hy
  have hyM : ‖y‖ ≤ M := by
    have hdist : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hnormdiff := norm_sub_norm_le y x
    dsimp [M]
    linarith
  have hyShift : 0 < (y + (n : ℂ)).re := by
    have hdist : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hre : |(y - x).re| ≤ ‖y - x‖ := Complex.abs_re_le_norm (y - x)
    change |y.re - x.re| ≤ ‖y - x‖ at hre
    have hlow : x.re - 1 < y.re := by
      have : -|(y - x).re| ≤ (y - x).re := neg_abs_le _
      change -|y.re - x.re| ≤ y.re - x.re at this
      linarith
    change 0 < y.re + (n : ℝ)
    nlinarith
  have hKrec0 : 0 ≤ 2 * (M + θ + 1) := by positivity
  have hKcore0 : 0 ≤ 2 * (M + (n : ℝ)) + 4 := by positivity
  have hKθ0 : 0 ≤ 4 * θ := by positivity
  have hKpow0 : 0 ≤ 3 * θ * (M + (n : ℝ)) := by positivity
  have hKratio0 :
      0 ≤ 2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ := by positivity
  have hKn0 : 0 ≤ 2 * (n : ℝ) * θ := by positivity
  have hKD0 : 0 ≤ D / ε + 1 := by positivity
  have hrecT : 2 * (M + θ + 1) ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hcoreT : 2 * (M + n) + 4 ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hθT : 4 * θ ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hpowT : 3 * θ * (M + n) ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hratioT :
      2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hnT : 2 * n * θ ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hDT : D / ε + 1 ≤ T := by
    dsimp [K] at hTK
    nlinarith
  have hTpos : 0 < T := by
    have : (4 : ℝ) ≤ T := by nlinarith
    positivity
  have hsmallPow : 3 * θ * (M + n) / (2 * T) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 2 * T)]
    nlinarith
  have hsmallRatio :
      (2 * ‖neutralGammaFirstCoeff θ‖ + neutralGammaExponentErrorConst θ) / T ≤ 1 :=
    (div_le_one hTpos).2 hratioT
  have hbound := norm_neutralGamma_scaledPhaseJet_sub_le_of_add_nat hθ hM0 hyShift hyM
    hrecT hcoreT hθT hsmallPow hsmallRatio hnT
  have hDeps : D / T < ε := by
    rw [div_lt_iff₀ hTpos]
    have : D / ε < T := by linarith
    rw [div_lt_iff₀ hε] at this
    nlinarith
  rw [dist_eq_norm]
  calc
    ‖neutralGammaAffineJet θ y -
        (T : ℂ) / neutralGammaPhase θ T *
          (neutralGammaRatio θ (y + Complex.I * (T : ℂ)) - neutralGammaPhase θ T)‖ =
      ‖(T : ℂ) / neutralGammaPhase θ T *
          (neutralGammaRatio θ (y + Complex.I * (T : ℂ)) - neutralGammaPhase θ T) -
        neutralGammaAffineJet θ y‖ := norm_sub_rev _ _
    _ ≤ D / T := by simpa [D, M] using hbound
    _ < ε := hDeps

/-- Positive logarithmic-resonance height freezing the neutral Gamma phase. -/
def neutralGammaFrozenHeight (θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (2 * Real.pi * n / θ)

/-- Frozen phase of the neutral Gamma ratio. -/
def neutralGammaFrozenPhase (θ : ℝ) : ℂ :=
  (Real.exp (-Real.pi * θ / 2) : ℝ)

lemma neutralGammaFrozenHeight_pos {θ : ℝ} (n : ℕ) :
    0 < neutralGammaFrozenHeight θ n := by
  exact Real.exp_pos _

/-- The selected exponential heights freeze the complex power phase exactly. -/
theorem neutralGammaPhase_frozenHeight {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    neutralGammaPhase θ (neutralGammaFrozenHeight θ n) = neutralGammaFrozenPhase θ := by
  let T : ℝ := neutralGammaFrozenHeight θ n
  have hT : 0 < T := neutralGammaFrozenHeight_pos n
  have hb0 : Complex.I * (T : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne')
  have harg : Complex.I.arg + ((T : ℂ)).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I, Complex.arg_ofReal_of_nonneg hT.le]
    constructor <;> nlinarith [Real.pi_pos]
  have hlog : Complex.log (Complex.I * (T : ℂ)) =
      (Real.log T : ℂ) + (Real.pi / 2 : ℂ) * Complex.I := by
    rw [Complex.log_mul Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne') harg,
      Complex.log_I]
    rw [← Complex.ofReal_log hT.le]
    ring
  have hlogT : Real.log T = 2 * Real.pi * n / θ := by
    rw [show T = Real.exp (2 * Real.pi * n / θ) by rfl, Real.log_exp]
  rw [neutralGammaPhase, Complex.cpow_def_of_ne_zero hb0, hlog, hlogT]
  have hexponent :
      (((2 * Real.pi * n / θ : ℝ) : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) *
          (Complex.I * (θ : ℂ)) =
        ((-Real.pi * θ / 2 : ℝ) : ℂ) +
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
    · ring
    · field_simp [hθ.ne']
  rw [hexponent]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp [neutralGammaFrozenPhase, Complex.ofReal_exp]

/-- Frozen heights escape to positive infinity. -/
theorem tendsto_neutralGammaFrozenHeight_atTop {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (neutralGammaFrozenHeight θ) atTop atTop := by
  have hc : 0 < 2 * Real.pi / θ := div_pos (by positivity) hθ
  have hlin : Tendsto (fun n : ℕ => (2 * Real.pi / θ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hexp := Real.tendsto_exp_atTop.comp hlin
  convert hexp using 1
  funext n
  simp only [Function.comp_apply, neutralGammaFrozenHeight]
  congr 1
  ring

/-- Exact frozen-sequence version of the locally uniform affine first-jet law. -/
theorem tendstoLocallyUniformly_neutralGamma_frozenFirstJet {θ : ℝ} (hθ : 0 < θ) :
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        ((neutralGammaFrozenHeight θ n : ℂ) / neutralGammaFrozenPhase θ) *
          (neutralGammaRatio θ
              (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)) -
            neutralGammaFrozenPhase θ))
      (neutralGammaAffineJet θ) atTop := by
  have hglobal := tendstoLocallyUniformly_neutralGamma_scaledPhaseJet hθ.le
  have hheight := tendsto_neutralGammaFrozenHeight_atTop hθ
  intro u hu x
  obtain ⟨t, ht, hev⟩ := hglobal u hu x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hheight.eventually hev] with n hn y hy
  simpa only [neutralGammaPhase_frozenHeight hθ] using hn y hy

/-- A convergent scalar sequence, regarded as constant functions, converges locally uniformly. -/
theorem tendstoLocallyUniformly_const_of_tendsto {c : ℕ → ℂ} {a : ℂ}
    (h : Tendsto c atTop (𝓝 a)) :
    TendstoLocallyUniformly (fun n : ℕ => fun _ : ℂ => c n) (fun _ : ℂ => a) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨Set.univ, univ_mem, ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp h ε hε] with n hn y hy
  simpa [dist_comm] using hn

/-- Locally uniform convergence is preserved by a fixed natural power. -/
theorem tendstoLocallyUniformly_pow {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hf : Continuous f) (m : ℕ) :
    TendstoLocallyUniformly (fun n s => (F n s) ^ m) (fun s => (f s) ^ m) atTop := by
  induction m with
  | zero =>
      simpa using tendstoLocallyUniformly_const_sequence (ι := ℕ) (fun _ : ℂ => (1 : ℂ))
  | succ m ih =>
      simpa [pow_succ] using tendstoLocallyUniformly_mul ih hF (hf.pow m) hf

/-- Polynomial evaluation preserves locally uniform convergence when the limit is continuous. -/
theorem tendstoLocallyUniformly_polynomial_eval (p : Polynomial ℂ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hf : Continuous f) :
    TendstoLocallyUniformly (fun n s => p.eval (F n s)) (fun s => p.eval (f s)) atTop := by
  classical
  have hterm : ∀ i : ℕ, TendstoLocallyUniformly
      (fun n s => p.coeff i * (F n s) ^ i)
      (fun s => p.coeff i * (f s) ^ i) atTop := by
    intro i
    have hc := tendstoLocallyUniformly_const_sequence (ι := ℕ) (l := atTop)
      (fun _ : ℂ => p.coeff i)
    exact tendstoLocallyUniformly_mul hc (tendstoLocallyUniformly_pow hF hf i)
      continuous_const (hf.pow i)
  have hsum : ∀ S : Finset ℕ, TendstoLocallyUniformly
      (fun n s => ∑ i ∈ S, p.coeff i * (F n s) ^ i)
      (fun s => ∑ i ∈ S, p.coeff i * (f s) ^ i) atTop := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa using tendstoLocallyUniformly_const_sequence (ι := ℕ) (fun _ : ℂ => (0 : ℂ))
    | @insert i S hi ih =>
        have hadd := (hterm i).add ih
        change TendstoLocallyUniformly
          (fun n s => p.coeff i * (F n s) ^ i +
            ∑ j ∈ S, p.coeff j * (F n s) ^ j)
          (fun s => p.coeff i * (f s) ^ i +
            ∑ j ∈ S, p.coeff j * (f s) ^ j) atTop at hadd
        simpa only [Finset.sum_insert hi] using hadd
  simpa [Polynomial.eval_eq_sum, Polynomial.sum_def] using hsum p.support

/-- Along frozen heights, the unscaled Gamma-ratio translates converge locally uniformly to the
frozen phase. -/
theorem tendstoLocallyUniformly_neutralGamma_frozenValue {θ : ℝ} (hθ : 0 < θ) :
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        neutralGammaRatio θ
          (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)))
      (fun _ : ℂ => neutralGammaFrozenPhase θ) atTop := by
  let F : ℕ → ℂ → ℂ := fun n s =>
    ((neutralGammaFrozenHeight θ n : ℂ) / neutralGammaFrozenPhase θ) *
      (neutralGammaRatio θ
          (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)) -
        neutralGammaFrozenPhase θ)
  let c : ℕ → ℂ := fun n =>
    neutralGammaFrozenPhase θ / (neutralGammaFrozenHeight θ n : ℂ)
  have hcR : Tendsto
      (fun n : ℕ => Real.exp (-Real.pi * θ / 2) / neutralGammaFrozenHeight θ n)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
        (tendsto_neutralGammaFrozenHeight_atTop hθ)
  have hc : Tendsto c atTop (𝓝 0) := by
    have hofReal := Complex.continuous_ofReal.tendsto 0
    have hcomp := hofReal.comp hcR
    convert hcomp using 1
    · funext n
      dsimp only [c, neutralGammaFrozenPhase, Function.comp_apply]
      exact (Complex.ofReal_div _ _).symm
    · norm_num
  have hF : TendstoLocallyUniformly F (neutralGammaAffineJet θ) atTop := by
    simpa [F] using tendstoLocallyUniformly_neutralGamma_frozenFirstJet hθ
  have hcLU := tendstoLocallyUniformly_const_of_tendsto hc
  have hLcont : Continuous (neutralGammaAffineJet θ) := by
    change Continuous (fun s : ℂ => (θ : ℂ) * s + neutralGammaAffineConstant θ)
    exact (continuous_const.mul continuous_id).add continuous_const
  have hprod := tendstoLocallyUniformly_mul hcLU hF continuous_const
    hLcont
  have hphaseConst := tendstoLocallyUniformly_const_sequence (ι := ℕ) (l := atTop)
    (fun _ : ℂ => neutralGammaFrozenPhase θ)
  have hadd := hphaseConst.add hprod
  change TendstoLocallyUniformly
    (fun n s => neutralGammaFrozenPhase θ + c n * F n s)
    (fun s => neutralGammaFrozenPhase θ + 0 * neutralGammaAffineJet θ s) atTop at hadd
  have heq : ∀ n s, neutralGammaFrozenPhase θ + c n * F n s =
      neutralGammaRatio θ
        (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)) := by
    intro n s
    have hT0 : (neutralGammaFrozenHeight θ n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (neutralGammaFrozenHeight_pos n).ne'
    have hA0 : neutralGammaFrozenPhase θ ≠ 0 := by
      rw [neutralGammaFrozenPhase]
      exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    dsimp only [c, F]
    field_simp [hT0, hA0]
    ring
  simpa using hadd.congr heq

/-- Frozen Gamma-ratio vanishing order becomes exactly the corresponding affine jet power. -/
theorem tendstoLocallyUniformly_neutralGamma_frozenPolynomialJet {θ : ℝ} (hθ : 0 < θ)
    (Q : Polynomial ℂ) :
    let A := neutralGammaFrozenPhase θ
    let m := Q.rootMultiplicity A
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        ((neutralGammaFrozenHeight θ n : ℂ) / A) ^ m *
          Q.eval (neutralGammaRatio θ
            (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ))))
      (fun s : ℂ =>
        ((Polynomial.derivative^[m] Q).eval A / (m.factorial : ℂ)) *
          (neutralGammaAffineJet θ s) ^ m) atTop := by
  dsimp only
  let A : ℂ := neutralGammaFrozenPhase θ
  let m : ℕ := Q.rootMultiplicity A
  let U : Polynomial ℂ := Q /ₘ (Polynomial.X - Polynomial.C A) ^ m
  let F : ℕ → ℂ → ℂ := fun n s =>
    ((neutralGammaFrozenHeight θ n : ℂ) / A) *
      (neutralGammaRatio θ
          (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)) - A)
  let G : ℕ → ℂ → ℂ := fun n s =>
    neutralGammaRatio θ
      (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ))
  have hF : TendstoLocallyUniformly F (neutralGammaAffineJet θ) atTop := by
    simpa [F, A] using tendstoLocallyUniformly_neutralGamma_frozenFirstJet hθ
  have hG : TendstoLocallyUniformly G (fun _ : ℂ => A) atTop := by
    simpa [G, A] using tendstoLocallyUniformly_neutralGamma_frozenValue hθ
  have hLcont : Continuous (neutralGammaAffineJet θ) := by
    change Continuous (fun s : ℂ => (θ : ℂ) * s + neutralGammaAffineConstant θ)
    exact (continuous_const.mul continuous_id).add continuous_const
  have hFpow := tendstoLocallyUniformly_pow hF hLcont m
  have hU := tendstoLocallyUniformly_polynomial_eval U hG continuous_const
  have hprod := tendstoLocallyUniformly_mul hFpow hU (hLcont.pow m) continuous_const
  have hfactor : (Polynomial.X - Polynomial.C A) ^ m * U = Q := by
    simpa [m, U] using Q.pow_mul_divByMonic_rootMultiplicity_eq A
  have hleft : ∀ n s,
      F n s ^ m * U.eval (G n s) =
        ((neutralGammaFrozenHeight θ n : ℂ) / A) ^ m * Q.eval (G n s) := by
    intro n s
    have hQeval := congrArg (fun p : Polynomial ℂ => p.eval (G n s)) hfactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hQeval
    rw [show F n s =
      ((neutralGammaFrozenHeight θ n : ℂ) / A) * (G n s - A) by rfl]
    rw [mul_pow]
    calc
      ((neutralGammaFrozenHeight θ n : ℂ) / A) ^ m * (G n s - A) ^ m * U.eval (G n s) =
          ((neutralGammaFrozenHeight θ n : ℂ) / A) ^ m *
            ((G n s - A) ^ m * U.eval (G n s)) := by ring
      _ = _ := by rw [hQeval]
  have hderiv := Polynomial.eval_iterate_derivative_rootMultiplicity (p := Q) (t := A)
  have hfact0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hUeval : U.eval A = (Polynomial.derivative^[m] Q).eval A / (m.factorial : ℂ) := by
    have hderiv' : (Polynomial.derivative^[m] Q).eval A =
        (m.factorial : ℂ) * U.eval A := by
      simpa only [m, U, nsmul_eq_mul] using hderiv
    rw [eq_div_iff hfact0]
    simpa [mul_comm] using hderiv'.symm
  change TendstoLocallyUniformly
    (fun n s => F n s ^ m * U.eval (G n s))
    (fun s => (neutralGammaAffineJet θ s) ^ m * U.eval A) atTop at hprod
  have hout := hprod.congr hleft
  rw [hUeval] at hout
  simpa [mul_comm] using hout

/-- Canonical meromorphic carrier represented by `Γ(s+iθ)/Γ(s)`. -/
def neutralGammaRatioMero (θ : ℝ) : Bottcher.meroField Set.univ :=
  (reducedVenezianoAmplitudeMero 0 (Complex.I * (θ : ℂ)))⁻¹

/-- Every nontrivial neutral imaginary Gamma ratio is hypertranscendental over `ℂ(s)`. -/
theorem hypertranscendentalOver_neutralGammaRatioMero {θ : ℝ} (hθ : θ ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) (neutralGammaRatioMero θ) := by
  rw [neutralGammaRatioMero]
  apply hypertranscendentalOver_inv_iff.mpr
  apply hypertranscendentalOver_reducedVenezianoAmplitudeMero_of_nonintegerShift
  intro k hk
  have him := congrArg Complex.im hk
  simp at him
  exact hθ him

/-- Every positive-height neutral Gamma phase lies on the fixed circle of radius
`exp (-πθ/2)`. -/
theorem norm_neutralGammaPhase {θ T : ℝ} (hT : 0 < T) :
    ‖neutralGammaPhase θ T‖ = Real.exp (-Real.pi * θ / 2) := by
  have hb0 : Complex.I * (T : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne')
  have hargRange : Complex.I.arg + ((T : ℂ)).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I, Complex.arg_ofReal_of_nonneg hT.le]
    constructor <;> nlinarith [Real.pi_pos]
  have harg : (Complex.I * (T : ℂ)).arg = Real.pi / 2 := by
    rw [Complex.arg_mul Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne') hargRange,
      Complex.arg_I, Complex.arg_ofReal_of_nonneg hT.le, add_zero]
  rw [neutralGammaPhase, Complex.norm_cpow_of_ne_zero hb0, harg]
  simp
  rw [← Real.exp_neg]
  congr 1
  ring

/-- Phase-height normalization scale for an arbitrary positive height sequence. -/
def neutralGammaPhaseHeightScale (θ : ℝ) (S : ℕ → ℝ) (A : ℂ) (n : ℕ) : ℝ :=
  ‖neutralGammaPhase θ (S n) - A‖ + (S n)⁻¹

/-- Every escaping height sequence admits normalized phase-error and inverse-height limits with
exact nontriviality identity `‖λ‖ + μ = 1`. -/
theorem exists_neutralGamma_phaseHeight_subsequence {θ : ℝ} (_hθ : 0 < θ)
    {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) :
    ∃ (φ : ℕ → ℕ) (A lam : ℂ) (μ : ℝ),
      StrictMono φ ∧
      (∀ n, 0 < S (φ n)) ∧
      ‖A‖ = Real.exp (-Real.pi * θ / 2) ∧
      0 ≤ μ ∧ ‖lam‖ + μ = 1 ∧
      Tendsto (fun n => neutralGammaPhase θ (S (φ n))) atTop (𝓝 A) ∧
      Tendsto (fun n =>
        (neutralGammaPhase θ (S (φ n)) - A) /
          neutralGammaPhaseHeightScale θ (S ∘ φ) A n) atTop (𝓝 lam) ∧
      Tendsto (fun n =>
        (S (φ n))⁻¹ / neutralGammaPhaseHeightScale θ (S ∘ φ) A n)
        atTop (𝓝 μ) := by
  have hSposEv : ∀ᶠ n in atTop, 0 < S n := hS.eventually_gt_atTop 0
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hSposEv)
  let φ0 : ℕ → ℕ := fun n => n + N
  have hφ0 : StrictMono φ0 := strictMono_id.add_const N
  have hSφ0 : Tendsto (S ∘ φ0) atTop atTop := hS.comp hφ0.tendsto_atTop
  have hSφ0pos : ∀ n, 0 < S (φ0 n) := by
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  let a0 : ℕ → ℂ := fun n => neutralGammaPhase θ (S (φ0 n))
  have ha0sphere : ∀ n, a0 n ∈ Metric.sphere (0 : ℂ)
      (Real.exp (-Real.pi * θ / 2)) := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_neutralGammaPhase (hSφ0pos n)
  obtain ⟨A, hAsphere, φ1, hφ1, hAconv⟩ :=
    (isCompact_sphere (0 : ℂ) (Real.exp (-Real.pi * θ / 2))).tendsto_subseq ha0sphere
  let φA : ℕ → ℕ := φ0 ∘ φ1
  have hφA : StrictMono φA := hφ0.comp hφ1
  have hSφA : Tendsto (S ∘ φA) atTop atTop := hS.comp hφA.tendsto_atTop
  have hSφApos : ∀ n, 0 < S (φA n) := by
    intro n
    exact hSφ0pos (φ1 n)
  let d : ℕ → ℝ := fun n => neutralGammaPhaseHeightScale θ (S ∘ φA) A n
  let b : ℕ → ℂ × ℝ := fun n =>
    ((neutralGammaPhase θ (S (φA n)) - A) / d n,
      (S (φA n))⁻¹ / d n)
  have hdpos : ∀ n, 0 < d n := by
    intro n
    dsimp [d, neutralGammaPhaseHeightScale]
    have hinv : 0 < (S (φA n))⁻¹ := inv_pos.mpr (hSφApos n)
    positivity
  have hbK : ∀ n, b n ∈
      Metric.closedBall (0 : ℂ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro n
    have hinv0 : 0 ≤ (S (φA n))⁻¹ := (inv_pos.mpr (hSφApos n)).le
    have hnorm0 : 0 ≤ ‖neutralGammaPhase θ (S (φA n)) - A‖ := norm_nonneg _
    have hfirst : ‖(neutralGammaPhase θ (S (φA n)) - A) / d n‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hdpos n),
        div_le_one (hdpos n)]
      dsimp [d, neutralGammaPhaseHeightScale]
      linarith
    have hsecond0 : 0 ≤ (S (φA n))⁻¹ / d n := div_nonneg hinv0 (hdpos n).le
    have hsecond1 : (S (φA n))⁻¹ / d n ≤ 1 := by
      rw [div_le_one (hdpos n)]
      dsimp [d, neutralGammaPhaseHeightScale]
      linarith
    exact ⟨by
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖(neutralGammaPhase θ (S (φA n)) - A) / d n‖ ≤ 1
      exact hfirst, ⟨hsecond0, hsecond1⟩⟩
  have hKcompact : IsCompact
      (Metric.closedBall (0 : ℂ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    IsCompact.prod (isCompact_closedBall (0 : ℂ) 1)
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  obtain ⟨p, hpK, ψ, hψ, hpconv⟩ := hKcompact.tendsto_subseq hbK
  let φ : ℕ → ℕ := φA ∘ ψ
  have hφ : StrictMono φ := hφA.comp hψ
  have hSφpos : ∀ n, 0 < S (φ n) := fun n => hSφApos (ψ n)
  have hAfinal : Tendsto (fun n => neutralGammaPhase θ (S (φ n))) atTop (𝓝 A) := by
    have hsub := hAconv.comp hψ.tendsto_atTop
    simpa [a0, φA, φ, Function.comp_def] using hsub
  have hlambda : Tendsto (fun n =>
      (neutralGammaPhase θ (S (φ n)) - A) /
        neutralGammaPhaseHeightScale θ (S ∘ φ) A n) atTop (𝓝 p.1) := by
    have hfst := continuous_fst.continuousAt.tendsto.comp hpconv
    simpa [b, d, φ, φA, neutralGammaPhaseHeightScale, Function.comp_def] using hfst
  have hmu : Tendsto (fun n =>
      (S (φ n))⁻¹ / neutralGammaPhaseHeightScale θ (S ∘ φ) A n)
      atTop (𝓝 p.2) := by
    have hsnd := continuous_snd.continuousAt.tendsto.comp hpconv
    simpa [b, d, φ, φA, neutralGammaPhaseHeightScale, Function.comp_def] using hsnd
  have hbsum : ∀ n, ‖(b n).1‖ + (b n).2 = 1 := by
    intro n
    rw [show (b n).1 =
        (neutralGammaPhase θ (S (φA n)) - A) / d n by rfl,
      show (b n).2 = (S (φA n))⁻¹ / d n by rfl,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hdpos n)]
    dsimp [d, neutralGammaPhaseHeightScale]
    rw [← add_div]
    apply div_self
    exact (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (inv_pos.mpr (hSφApos n))).ne'
  have hsumLim : Tendsto (fun n => ‖((b ∘ ψ) n).1‖ + ((b ∘ ψ) n).2)
      atTop (𝓝 (‖p.1‖ + p.2)) := by
    have hc : Continuous (fun q : ℂ × ℝ => ‖q.1‖ + q.2) :=
      (continuous_fst.norm.add continuous_snd)
    exact hc.continuousAt.tendsto.comp hpconv
  have hsumOne : Tendsto (fun n => ‖((b ∘ ψ) n).1‖ + ((b ∘ ψ) n).2)
      atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun n => by simpa using (hbsum (ψ n)).symm
  have hnormsum : ‖p.1‖ + p.2 = 1 := tendsto_nhds_unique hsumLim hsumOne
  refine ⟨φ, A, p.1, p.2, hφ, hSφpos, ?_, hpK.2.1, hnormsum,
    hAfinal, hlambda, hmu⟩
  simpa [Metric.mem_sphere, dist_zero_right] using hAsphere

/-- Affine compact-open limit forced by the joint phase-error/height normalization. -/
def neutralGammaAffineBlowUpLimit (θ : ℝ) (A lam : ℂ) (μ : ℝ) (s : ℂ) : ℂ :=
  lam + (μ : ℂ) * A * neutralGammaAffineJet θ s

/-- Every escaping height sequence has a subsequence on which the exactly normalized neutral
Gamma translates converge locally uniformly to a nonzero affine function. -/
theorem exists_neutralGamma_universalAffineBlowUp {θ : ℝ} (hθ : 0 < θ)
    {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) :
    ∃ (φ : ℕ → ℕ) (A lam : ℂ) (μ : ℝ),
      StrictMono φ ∧
      (∀ n, 0 < S (φ n)) ∧
      ‖A‖ = Real.exp (-Real.pi * θ / 2) ∧
      0 ≤ μ ∧ ‖lam‖ + μ = 1 ∧
      Tendsto (fun n => neutralGammaPhase θ (S (φ n))) atTop (𝓝 A) ∧
      TendstoLocallyUniformly
        (fun n : ℕ => fun s : ℂ =>
          (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
            (neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ))
        (neutralGammaAffineBlowUpLimit θ A lam μ) atTop ∧
      neutralGammaAffineBlowUpLimit θ A lam μ ≠ 0 := by
  obtain ⟨φ, A, lam, μ, hφ, hSφpos, hAnorm, hμnonneg, hsum,
    hA, hlam, hμ⟩ := exists_neutralGamma_phaseHeight_subsequence hθ hS
  let d : ℕ → ℝ := neutralGammaPhaseHeightScale θ (S ∘ φ) A
  let E : ℕ → ℂ → ℂ := fun n s =>
    ((S (φ n) : ℂ) / neutralGammaPhase θ (S (φ n))) *
      (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) -
        neutralGammaPhase θ (S (φ n)))
  have hSφ : Tendsto (S ∘ φ) atTop atTop := hS.comp hφ.tendsto_atTop
  have hE : TendstoLocallyUniformly E (neutralGammaAffineJet θ) atTop := by
    have hglobal := TendstoLocallyUniformly.comp_tendsto
      (tendstoLocallyUniformly_neutralGamma_scaledPhaseJet hθ.le) hSφ
    simpa [E, Function.comp_def] using hglobal
  have hlamLU := tendstoLocallyUniformly_const_of_tendsto hlam
  have hμC : Tendsto
      (fun n => (((S (φ n))⁻¹ / d n : ℝ) : ℂ)) atTop (𝓝 (μ : ℂ)) := by
    have hcomp := (Complex.continuous_ofReal.tendsto μ).comp hμ
    simpa [d, Function.comp_def] using hcomp
  have hμLU := tendstoLocallyUniformly_const_of_tendsto hμC
  have hALU := tendstoLocallyUniformly_const_of_tendsto hA
  have hμA := tendstoLocallyUniformly_mul hμLU hALU continuous_const continuous_const
  have hLcont : Continuous (neutralGammaAffineJet θ) := by
    change Continuous (fun s : ℂ => (θ : ℂ) * s + neutralGammaAffineConstant θ)
    exact (continuous_const.mul continuous_id).add continuous_const
  have hμAE := tendstoLocallyUniformly_mul hμA hE continuous_const hLcont
  have hadd := hlamLU.add hμAE
  change TendstoLocallyUniformly
    (fun n s =>
      ((neutralGammaPhase θ (S (φ n)) - A) / (d n : ℂ)) +
        (((S (φ n))⁻¹ / d n : ℝ) : ℂ) *
          neutralGammaPhase θ (S (φ n)) * E n s)
    (neutralGammaAffineBlowUpLimit θ A lam μ) atTop at hadd
  have heq : ∀ n s,
      ((neutralGammaPhase θ (S (φ n)) - A) / (d n : ℂ)) +
          (((S (φ n))⁻¹ / d n : ℝ) : ℂ) *
            neutralGammaPhase θ (S (φ n)) * E n s =
        (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
          (d n : ℂ) := by
    intro n s
    have hSn0 : S (φ n) ≠ 0 := (hSφpos n).ne'
    have hphase0 : neutralGammaPhase θ (S (φ n)) ≠ 0 := by
      rw [neutralGammaPhase]
      apply Complex.cpow_ne_zero_iff.mpr
      left
      exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hSn0)
    have hdpos : 0 < d n := by
      dsimp [d, neutralGammaPhaseHeightScale]
      exact add_pos_of_nonneg_of_pos (norm_nonneg _) (inv_pos.mpr (hSφpos n))
    have hd0 : (d n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
    dsimp only [E]
    push_cast
    field_simp [hSn0, hphase0, hd0]
    ring
  have hblowup : TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
          (neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ))
      (neutralGammaAffineBlowUpLimit θ A lam μ) atTop := by
    simpa [d] using hadd.congr heq
  have hlimit0 : neutralGammaAffineBlowUpLimit θ A lam μ ≠ 0 := by
    intro hzero
    have hz (s : ℂ) : neutralGammaAffineBlowUpLimit θ A lam μ s = 0 := by
      simpa using congrFun hzero s
    by_cases hμzero : μ = 0
    · have hlamzero : lam = 0 := by
        simpa [neutralGammaAffineBlowUpLimit, hμzero] using hz 0
      rw [hμzero, hlamzero, norm_zero, zero_add] at hsum
      norm_num at hsum
    · have hA0 : A ≠ 0 := by
        intro hAzero
        rw [hAzero, norm_zero] at hAnorm
        have hexp : 0 < Real.exp (-Real.pi * θ / 2) := Real.exp_pos _
        linarith
      have hcoeff0 : (μ : ℂ) * A * (θ : ℂ) = 0 := by
        calc
          (μ : ℂ) * A * (θ : ℂ) =
              neutralGammaAffineBlowUpLimit θ A lam μ 1 -
                neutralGammaAffineBlowUpLimit θ A lam μ 0 := by
                  simp [neutralGammaAffineBlowUpLimit, neutralGammaAffineJet]
                  ring
          _ = 0 := by rw [hz 1, hz 0, sub_self]
      exact (mul_ne_zero
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hμzero) hA0)
        (Complex.ofReal_ne_zero.mpr hθ.ne')).elim hcoeff0
  exact ⟨φ, A, lam, μ, hφ, hSφpos, hAnorm, hμnonneg, hsum, hA,
    hblowup, hlimit0⟩

/-- Root multiplicity converts an arbitrary nonzero affine blow-up into the corresponding
polynomial jet, with the exact iterated-derivative coefficient. -/
theorem tendstoLocallyUniformly_neutralGamma_polynomialJet_of_blowUp
    {θ : ℝ} {S : ℕ → ℝ} {φ : ℕ → ℕ} {A : ℂ} {H : ℂ → ℂ}
    (hS : Tendsto (S ∘ φ) atTop atTop)
    (hSpos : ∀ n, 0 < S (φ n))
    (hA : Tendsto (fun n => neutralGammaPhase θ (S (φ n))) atTop (𝓝 A))
    (hH : Continuous H)
    (hblowup : TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
          (neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)) H atTop)
    (Q : Polynomial ℂ) :
    let m := Q.rootMultiplicity A
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        ((neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)⁻¹) ^ m *
          Q.eval (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ))))
      (fun s : ℂ =>
        ((Polynomial.derivative^[m] Q).eval A / (m.factorial : ℂ)) * H s ^ m)
      atTop := by
  dsimp only
  let d : ℕ → ℝ := neutralGammaPhaseHeightScale θ (S ∘ φ) A
  let G : ℕ → ℂ → ℂ := fun n s =>
    neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ))
  let F : ℕ → ℂ → ℂ := fun n s => (G n s - A) / (d n : ℂ)
  let m : ℕ := Q.rootMultiplicity A
  let U : Polynomial ℂ := Q /ₘ (Polynomial.X - Polynomial.C A) ^ m
  have hphaseNorm : Tendsto
      (fun n => ‖neutralGammaPhase θ (S (φ n)) - A‖) atTop (𝓝 0) := by
    have hsub := hA.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
    have hnorm := hsub.norm
    simpa using hnorm
  have hinv : Tendsto (fun n => (S (φ n))⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hS
  have hdR : Tendsto d atTop (𝓝 0) := by
    change Tendsto
      (fun n => ‖neutralGammaPhase θ (S (φ n)) - A‖ + (S (φ n))⁻¹)
      atTop (𝓝 0)
    simpa only [add_zero] using hphaseNorm.add hinv
  have hdC : Tendsto (fun n => (d n : ℂ)) atTop (𝓝 0) := by
    have hcomp := (Complex.continuous_ofReal.tendsto 0).comp hdR
    simpa [Function.comp_def] using hcomp
  have hdLU := tendstoLocallyUniformly_const_of_tendsto hdC
  have hF : TendstoLocallyUniformly F H atTop := by
    simpa [F, G, d] using hblowup
  have hdF := tendstoLocallyUniformly_mul hdLU hF continuous_const hH
  have hALU := tendstoLocallyUniformly_const_sequence (ι := ℕ) (l := atTop)
    (fun _ : ℂ => A)
  have hGsum := hALU.add hdF
  change TendstoLocallyUniformly
    (fun n s => A + (d n : ℂ) * F n s)
    (fun s => A + 0 * H s) atTop at hGsum
  have hGidentity : ∀ n s, A + (d n : ℂ) * F n s = G n s := by
    intro n s
    have hdpos : 0 < d n := by
      dsimp [d, neutralGammaPhaseHeightScale]
      exact add_pos_of_nonneg_of_pos (norm_nonneg _) (inv_pos.mpr (hSpos n))
    have hd0 : (d n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
    dsimp only [F]
    field_simp [hd0]
    ring
  have hG : TendstoLocallyUniformly G (fun _ : ℂ => A) atTop := by
    simpa using hGsum.congr hGidentity
  have hFpow := tendstoLocallyUniformly_pow hF hH m
  have hU := tendstoLocallyUniformly_polynomial_eval U hG continuous_const
  have hprod := tendstoLocallyUniformly_mul hFpow hU (hH.pow m) continuous_const
  have hfactor : (Polynomial.X - Polynomial.C A) ^ m * U = Q := by
    simpa [m, U] using Q.pow_mul_divByMonic_rootMultiplicity_eq A
  have hleft : ∀ n s,
      F n s ^ m * U.eval (G n s) =
        ((d n : ℂ)⁻¹) ^ m * Q.eval (G n s) := by
    intro n s
    have hQeval := congrArg (fun p : Polynomial ℂ => p.eval (G n s)) hfactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hQeval
    rw [show F n s = (G n s - A) / (d n : ℂ) by rfl, div_eq_mul_inv, mul_pow]
    calc
      (G n s - A) ^ m * (d n : ℂ)⁻¹ ^ m * U.eval (G n s) =
          (d n : ℂ)⁻¹ ^ m * ((G n s - A) ^ m * U.eval (G n s)) := by ring
      _ = _ := by rw [hQeval]
  have hderiv := Polynomial.eval_iterate_derivative_rootMultiplicity (p := Q) (t := A)
  have hfact0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hUeval : U.eval A = (Polynomial.derivative^[m] Q).eval A / (m.factorial : ℂ) := by
    have hderiv' : (Polynomial.derivative^[m] Q).eval A =
        (m.factorial : ℂ) * U.eval A := by
      simpa only [m, U, nsmul_eq_mul] using hderiv
    rw [eq_div_iff hfact0]
    simpa [mul_comm] using hderiv'.symm
  change TendstoLocallyUniformly
    (fun n s => F n s ^ m * U.eval (G n s))
    (fun s => H s ^ m * U.eval A) atTop at hprod
  have hout := hprod.congr hleft
  rw [hUeval] at hout
  simpa [d, G, m, mul_comm] using hout

/-- Arbitrary-sequence polynomial jet capstone: one extracted nonzero affine limit controls the
exact root-multiplicity asymptotic of every fixed polynomial coordinate. -/
theorem exists_neutralGamma_universalPolynomialJet {θ : ℝ} (hθ : 0 < θ)
    {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) (Q : Polynomial ℂ) :
    ∃ (φ : ℕ → ℕ) (A lam : ℂ) (μ : ℝ),
      StrictMono φ ∧
      (∀ n, 0 < S (φ n)) ∧
      ‖A‖ = Real.exp (-Real.pi * θ / 2) ∧
      0 ≤ μ ∧ ‖lam‖ + μ = 1 ∧
      neutralGammaAffineBlowUpLimit θ A lam μ ≠ 0 ∧
      let m := Q.rootMultiplicity A
      TendstoLocallyUniformly
        (fun n : ℕ => fun s : ℂ =>
          ((neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)⁻¹) ^ m *
            Q.eval (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ))))
        (fun s : ℂ =>
          ((Polynomial.derivative^[m] Q).eval A / (m.factorial : ℂ)) *
            neutralGammaAffineBlowUpLimit θ A lam μ s ^ m) atTop := by
  obtain ⟨φ, A, lam, μ, hφ, hSφpos, hAnorm, hμnonneg, hsum, hA,
    hblowup, hlimit0⟩ := exists_neutralGamma_universalAffineBlowUp hθ hS
  have hSφ : Tendsto (S ∘ φ) atTop atTop := hS.comp hφ.tendsto_atTop
  have hH : Continuous (neutralGammaAffineBlowUpLimit θ A lam μ) := by
    change Continuous (fun s : ℂ =>
      lam + (μ : ℂ) * A * ((θ : ℂ) * s + neutralGammaAffineConstant θ))
    fun_prop
  have hpoly := tendstoLocallyUniformly_neutralGamma_polynomialJet_of_blowUp
    hSφ hSφpos hA hH hblowup Q
  exact ⟨φ, A, lam, μ, hφ, hSφpos, hAnorm, hμnonneg, hsum, hlimit0, hpoly⟩

/-- A vanishing normalization scale and a locally uniform blow-up recover convergence of the
unscaled translated Gamma ratio to its phase limit. -/
theorem tendstoLocallyUniformly_neutralGamma_value_of_blowUp
    {θ : ℝ} {S : ℕ → ℝ} {φ : ℕ → ℕ} {A : ℂ} {H : ℂ → ℂ}
    (hS : Tendsto (S ∘ φ) atTop atTop)
    (hSpos : ∀ n, 0 < S (φ n))
    (hA : Tendsto (fun n => neutralGammaPhase θ (S (φ n))) atTop (𝓝 A))
    (hH : Continuous H)
    (hblowup : TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
          (neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)) H atTop) :
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)))
      (fun _ : ℂ => A) atTop := by
  let d : ℕ → ℝ := neutralGammaPhaseHeightScale θ (S ∘ φ) A
  let F : ℕ → ℂ → ℂ := fun n s =>
    (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) / (d n : ℂ)
  have hphaseNorm : Tendsto
      (fun n => ‖neutralGammaPhase θ (S (φ n)) - A‖) atTop (𝓝 0) := by
    have hsub := hA.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
    simpa using hsub.norm
  have hinv : Tendsto (fun n => (S (φ n))⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hS
  have hdR : Tendsto d atTop (𝓝 0) := by
    change Tendsto
      (fun n => ‖neutralGammaPhase θ (S (φ n)) - A‖ + (S (φ n))⁻¹)
      atTop (𝓝 0)
    simpa only [add_zero] using hphaseNorm.add hinv
  have hdC : Tendsto (fun n => (d n : ℂ)) atTop (𝓝 0) := by
    have hcomp := (Complex.continuous_ofReal.tendsto 0).comp hdR
    simpa [Function.comp_def] using hcomp
  have hdLU := tendstoLocallyUniformly_const_of_tendsto hdC
  have hF : TendstoLocallyUniformly F H atTop := by
    simpa [F, d] using hblowup
  have hdF := tendstoLocallyUniformly_mul hdLU hF continuous_const hH
  have hALU := tendstoLocallyUniformly_const_sequence (ι := ℕ) (l := atTop)
    (fun _ : ℂ => A)
  have hsum := hALU.add hdF
  change TendstoLocallyUniformly
    (fun n s => A + (d n : ℂ) * F n s)
    (fun s => A + 0 * H s) atTop at hsum
  have heq : ∀ n s,
      A + (d n : ℂ) * F n s =
        neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) := by
    intro n s
    have hdpos : 0 < d n := by
      dsimp [d, neutralGammaPhaseHeightScale]
      exact add_pos_of_nonneg_of_pos (norm_nonneg _) (inv_pos.mpr (hSpos n))
    have hd0 : (d n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
    dsimp only [F]
    field_simp [hd0]
    ring
  simpa using hsum.congr heq

/-- Polynomial factorization at a phase point passes through an arbitrary locally uniform affine
blow-up. This is the common-order engine for finite polynomial tuples. -/
theorem tendstoLocallyUniformly_neutralGamma_polynomialJet_of_factor
    {θ : ℝ} {S : ℕ → ℝ} {φ : ℕ → ℕ} {A : ℂ} {H : ℂ → ℂ}
    (hH : Continuous H)
    (hvalue : TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)))
      (fun _ : ℂ => A) atTop)
    (hblowup : TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ)) - A) /
          (neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)) H atTop)
    (m : ℕ) (Q U : Polynomial ℂ)
    (hfactor : (Polynomial.X - Polynomial.C A) ^ m * U = Q) :
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        ((neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)⁻¹) ^ m *
          Q.eval (neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ))))
      (fun s : ℂ => U.eval A * H s ^ m) atTop := by
  let d : ℕ → ℝ := neutralGammaPhaseHeightScale θ (S ∘ φ) A
  let G : ℕ → ℂ → ℂ := fun n s =>
    neutralGammaRatio θ (s + Complex.I * (S (φ n) : ℂ))
  let F : ℕ → ℂ → ℂ := fun n s => (G n s - A) / (d n : ℂ)
  have hF : TendstoLocallyUniformly F H atTop := by
    simpa [F, G, d] using hblowup
  have hG : TendstoLocallyUniformly G (fun _ : ℂ => A) atTop := by
    simpa [G] using hvalue
  have hFpow := tendstoLocallyUniformly_pow hF hH m
  have hU := tendstoLocallyUniformly_polynomial_eval U hG continuous_const
  have hprod := tendstoLocallyUniformly_mul hFpow hU (hH.pow m) continuous_const
  have hleft : ∀ n s,
      F n s ^ m * U.eval (G n s) =
        ((d n : ℂ)⁻¹) ^ m * Q.eval (G n s) := by
    intro n s
    have hQeval := congrArg (fun p : Polynomial ℂ => p.eval (G n s)) hfactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hQeval
    rw [show F n s = (G n s - A) / (d n : ℂ) by rfl, div_eq_mul_inv, mul_pow]
    calc
      (G n s - A) ^ m * (d n : ℂ)⁻¹ ^ m * U.eval (G n s) =
          (d n : ℂ)⁻¹ ^ m * ((G n s - A) ^ m * U.eval (G n s)) := by ring
      _ = _ := by rw [hQeval]
  change TendstoLocallyUniformly
    (fun n s => F n s ^ m * U.eval (G n s))
    (fun s => H s ^ m * U.eval A) atTop at hprod
  have hout := hprod.congr hleft
  simpa [d, G, mul_comm] using hout

/-- Every finite nonzero polynomial tuple has, along every escaping height sequence, a subsequence
whose common phase-height normalization converges to one nonzero constant projective point times a
common power of a nonzero affine function. Zero tuple coordinates are retained exactly. -/
theorem exists_neutralGamma_finiteTupleConstantProjectiveBoundary
    {θ : ℝ} (hθ : 0 < θ) {S : ℕ → ℝ} (hS : Tendsto S atTop atTop)
    {r : ℕ} (Q : Fin r → Polynomial ℂ) (hQ : ∃ j, Q j ≠ 0) :
    ∃ (φ : ℕ → ℕ) (A lam : ℂ) (μ : ℝ) (m : ℕ) (c : Fin r → ℂ),
      StrictMono φ ∧
      (∀ n, 0 < S (φ n)) ∧
      ‖A‖ = Real.exp (-Real.pi * θ / 2) ∧
      0 ≤ μ ∧ ‖lam‖ + μ = 1 ∧
      neutralGammaAffineBlowUpLimit θ A lam μ ≠ 0 ∧
      (∀ j, Q j ≠ 0 → m ≤ (Q j).rootMultiplicity A) ∧
      (∃ j, Q j ≠ 0 ∧ (Q j).rootMultiplicity A = m ∧ c j ≠ 0) ∧
      (∀ j, Q j = 0 → c j = 0) ∧
      (∀ j, Q j ≠ 0 → (Q j).rootMultiplicity A = m →
        c j = ((Polynomial.derivative^[m] (Q j)).eval A / (m.factorial : ℂ))) ∧
      (∀ j, Q j ≠ 0 → m < (Q j).rootMultiplicity A → c j = 0) ∧
      ∀ j, TendstoLocallyUniformly
        (fun n : ℕ => fun s : ℂ =>
          ((neutralGammaPhaseHeightScale θ (S ∘ φ) A n : ℂ)⁻¹) ^ m *
            (Q j).eval (neutralGammaRatio θ
              (s + Complex.I * (S (φ n) : ℂ))))
        (fun s : ℂ => c j * neutralGammaAffineBlowUpLimit θ A lam μ s ^ m)
        atTop := by
  classical
  obtain ⟨φ, A, lam, μ, hφ, hSφpos, hAnorm, hμnonneg, hsum, hA,
    hblowup, hlimit0⟩ := exists_neutralGamma_universalAffineBlowUp hθ hS
  let J : Finset (Fin r) := Finset.univ.filter fun j => Q j ≠ 0
  have hJ : J.Nonempty := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let k : Fin r → ℕ := fun j => (Q j).rootMultiplicity A
  let m : ℕ := J.inf' hJ k
  let U : Fin r → Polynomial ℂ := fun j =>
    if Q j = 0 then 0
    else (Polynomial.X - Polynomial.C A) ^ (k j - m) *
      (Q j /ₘ (Polynomial.X - Polynomial.C A) ^ k j)
  let c : Fin r → ℂ := fun j => (U j).eval A
  have hm_le (j : Fin r) (hj : Q j ≠ 0) : m ≤ k j := by
    exact Finset.inf'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  obtain ⟨jmin, hjminJ, hjminle⟩ :=
    (Finset.inf'_le_iff hJ).mp (le_refl m)
  have hjmin0 : Q jmin ≠ 0 := (Finset.mem_filter.mp hjminJ).2
  have hjminEq : k jmin = m :=
    le_antisymm hjminle (hm_le jmin hjmin0)
  have hfactor (j : Fin r) :
      (Polynomial.X - Polynomial.C A) ^ m * U j = Q j := by
    by_cases hj : Q j = 0
    · simp [U, hj]
    · have hmj : m ≤ k j := hm_le j hj
      have hroot := (Q j).pow_mul_divByMonic_rootMultiplicity_eq A
      calc
        (Polynomial.X - Polynomial.C A) ^ m * U j =
            (Polynomial.X - Polynomial.C A) ^ m *
              ((Polynomial.X - Polynomial.C A) ^ (k j - m) *
                (Q j /ₘ (Polynomial.X - Polynomial.C A) ^ k j)) := by
                  simp only [U, hj, ↓reduceIte]
        _ = (Polynomial.X - Polynomial.C A) ^ k j *
              (Q j /ₘ (Polynomial.X - Polynomial.C A) ^ k j) := by
                rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmj]
        _ = Q j := by simpa [k] using hroot
  have hc_zero (j : Fin r) (hj : Q j = 0) : c j = 0 := by
    simp [c, U, hj]
  have hc_min (j : Fin r) (hj : Q j ≠ 0) (hkj : k j = m) :
      c j = ((Polynomial.derivative^[m] (Q j)).eval A / (m.factorial : ℂ)) := by
    have hderiv := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := Q j) (t := A)
    have hfact0 : ((k j).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k j)
    have hV :
        (Q j /ₘ (Polynomial.X - Polynomial.C A) ^ k j).eval A =
          ((Polynomial.derivative^[k j] (Q j)).eval A /
            ((k j).factorial : ℂ)) := by
      have hderiv' : (Polynomial.derivative^[k j] (Q j)).eval A =
          ((k j).factorial : ℂ) *
            (Q j /ₘ (Polynomial.X - Polynomial.C A) ^ k j).eval A := by
        simpa only [k, nsmul_eq_mul] using hderiv
      rw [eq_div_iff hfact0]
      simpa [mul_comm] using hderiv'.symm
    simpa [c, U, hj, hkj] using hV
  have hc_high (j : Fin r) (hj : Q j ≠ 0) (hhigh : m < k j) : c j = 0 := by
    have hsub0 : k j - m ≠ 0 := (Nat.sub_pos_of_lt hhigh).ne'
    simp [c, U, hj, Polynomial.eval_mul, hsub0]
  have hcmin0 : c jmin ≠ 0 := by
    have hV0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero A hjmin0
    simpa [c, U, hjmin0, hjminEq, k] using hV0
  have hH : Continuous (neutralGammaAffineBlowUpLimit θ A lam μ) := by
    change Continuous (fun s : ℂ =>
      lam + (μ : ℂ) * A * ((θ : ℂ) * s + neutralGammaAffineConstant θ))
    fun_prop
  have hSφ : Tendsto (S ∘ φ) atTop atTop := hS.comp hφ.tendsto_atTop
  have hvalue := tendstoLocallyUniformly_neutralGamma_value_of_blowUp
    hSφ hSφpos hA hH hblowup
  have hconv (j : Fin r) := tendstoLocallyUniformly_neutralGamma_polynomialJet_of_factor
    hH hvalue hblowup m (Q j) (U j) (hfactor j)
  refine ⟨φ, A, lam, μ, m, c, hφ, hSφpos, hAnorm, hμnonneg, hsum,
    hlimit0, ?_, ?_, hc_zero, ?_, ?_, hconv⟩
  · intro j hj
    simpa [k] using hm_le j hj
  · exact ⟨jmin, hjmin0, by simpa [k] using hjminEq, hcmin0⟩
  · intro j hj hroot
    apply hc_min j hj
    simpa [k] using hroot
  · intro j hj hroot
    apply hc_high j hj
    simpa [k] using hroot

/-- Exact constant functional-projective boundary interface. One common meromorphic normalization
turns every member of a finite nonzero tuple into a constant compact-open limit, with at least one
surviving coordinate. -/
def HasConstantFunctionalProjectiveBoundary (K : Set (ℂ → ℂ)) : Prop :=
  ∀ {r : ℕ} (a : Fin r → ℂ → ℂ)
    (_haK : ∀ j, a j ∈ K) (_ha : ∃ j, a j ≠ 0)
    (S : ℕ → ℝ) (_hS : Tendsto S atTop atTop),
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ normalization : ℕ → ℂ → ℂ,
      ∃ limit : Fin r → ℂ,
        (∃ j, limit j ≠ 0) ∧
        ∀ j, TendstoLocallyUniformly
          (fun k z => normalization k z *
            a j (z + Complex.I * (S (phi k) : ℂ)))
          (fun _ : ℂ => limit j) atTop

/-- The rational neutral-Gamma coordinate class has a constant functional-projective boundary.
Denominators are cleared exactly and the common maximum polynomial degree supplies the recession
normalization. -/
theorem hasConstantFunctionalProjectiveBoundary_neutralGammaRatioRationalClass
    {θ : ℝ} (hθ : 0 ≤ θ) :
    HasConstantFunctionalProjectiveBoundary (neutralGammaRatioRationalClass θ) := by
  classical
  intro r a haK ha S hS
  choose p q hq hfa using fun j => haK j
  have hbne : ∃ j, p j * ∏ l ∈ Finset.univ.erase j, q l ≠ 0 := by
    obtain ⟨j0, hj0⟩ := ha
    refine ⟨j0, ?_⟩
    have hp0 : p j0 ≠ 0 := by
      intro hzero
      apply hj0
      rw [hfa j0, hzero]
      funext z
      simp
    exact mul_ne_zero hp0 (Finset.prod_ne_zero_iff.mpr fun l _ => hq l)
  set b : Fin r → Polynomial ℂ :=
    fun j => p j * ∏ l ∈ Finset.univ.erase j, q l with hbdef
  set d := Finset.univ.sup (fun j => (b j).natDegree) with hd
  obtain ⟨j1, hj1⟩ := exists_coeff_sup_natDegree_ne_zero b hbne
  choose M hM using fun l => exists_norm_gt_eval_ne_zero (hq l)
  refine ⟨id, strictMono_id,
    fun k z => ((Complex.I * (S k : ℂ)) ^ d)⁻¹ *
      (neutralGammaRatio θ (z + Complex.I * (S k : ℂ)))⁻¹ *
      ∏ l, (q l).eval (z + Complex.I * (S k : ℂ)),
    fun j => (b j).coeff d, ⟨j1, hj1⟩, ?_⟩
  intro j
  have hdeg : (b j).natDegree ≤ d :=
    Finset.le_sup (f := fun j => (b j).natDegree) (Finset.mem_univ j)
  have hbase := TendstoLocallyUniformly.comp_tendsto
    (poly_scaled_translate_tendstoLocallyUniformly (b j) hdeg) hS
  show TendstoLocallyUniformly
    (fun (k : ℕ) (z : ℂ) =>
      ((Complex.I * (S (id k) : ℂ)) ^ d)⁻¹ *
        (neutralGammaRatio θ (z + Complex.I * (S (id k) : ℂ)))⁻¹ *
        (∏ l, (q l).eval (z + Complex.I * (S (id k) : ℂ))) *
        a j (z + Complex.I * (S (id k) : ℂ)))
    (fun _ : ℂ => (b j).coeff d) atTop
  simp only [id_eq]
  refine tendstoLocallyUniformly_congr_eventually_local hbase ?_
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  have hev1 : ∀ᶠ k in atTop, ‖x‖ + 1 < S k :=
    hS.eventually (eventually_gt_atTop _)
  have hev2 : ∀ᶠ k in atTop, ∀ l, M l + (‖x‖ + 1) < S k :=
    Filter.eventually_all.mpr fun l => hS.eventually (eventually_gt_atTop _)
  filter_upwards [hev1, hev2] with k hk1 hk2 y hy
  have hyx : ‖y‖ < ‖x‖ + 1 := by
    have hdist : dist y x < 1 := Metric.mem_ball.mp hy
    have h2 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
    rw [dist_eq_norm] at hdist
    linarith
  have hSpos : (0 : ℝ) < S k := by
    have := norm_nonneg x
    linarith
  have hnormIS : ‖Complex.I * (S k : ℂ)‖ = S k := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSpos]
  have hwnorm : S k - ‖y‖ ≤ ‖y + Complex.I * (S k : ℂ)‖ := by
    have h4 : ‖Complex.I * (S k : ℂ)‖ ≤
        ‖y + Complex.I * (S k : ℂ)‖ + ‖y‖ := by
      calc
        ‖Complex.I * (S k : ℂ)‖ = ‖(y + Complex.I * (S k : ℂ)) - y‖ := by
          congr 1
          ring
        _ ≤ ‖y + Complex.I * (S k : ℂ)‖ + ‖y‖ := norm_sub_le _ _
    rw [hnormIS] at h4
    linarith
  have him : 0 < (y + Complex.I * (S k : ℂ)).im := by
    have h6 : (y + Complex.I * (S k : ℂ)).im = y.im + S k := by simp
    have h7 : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    have h8 : -‖y‖ ≤ y.im := (abs_le.mp h7).1
    rw [h6]
    linarith
  have hGamma : neutralGammaRatio θ (y + Complex.I * (S k : ℂ)) ≠ 0 :=
    neutralGammaRatio_ne_zero hθ him
  have hql : ∀ l, (q l).eval (y + Complex.I * (S k : ℂ)) ≠ 0 := by
    intro l
    refine hM l _ ?_
    have := hk2 l
    linarith
  have hprod : (∏ l, (q l).eval (y + Complex.I * (S k : ℂ))) =
      (q j).eval (y + Complex.I * (S k : ℂ)) *
        ∏ l ∈ Finset.univ.erase j,
          (q l).eval (y + Complex.I * (S k : ℂ)) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
  rw [hfa j]
  simp only [hbdef, Polynomial.eval_mul, Polynomial.eval_prod, hprod]
  exact gamma_clearing_identity ((Complex.I * (S k : ℂ)) ^ d)
    (neutralGammaRatio θ (y + Complex.I * (S k : ℂ)))
    ((p j).eval (y + Complex.I * (S k : ℂ)))
    ((q j).eval (y + Complex.I * (S k : ℂ)))
    (∏ l ∈ Finset.univ.erase j,
      (q l).eval (y + Complex.I * (S k : ℂ))) hGamma (hql j)

/-- A constant functional-projective boundary converts every finite coefficient ADE for a
holomorphic strip-almost-periodic function into a nonzero autonomous ADE on the same strip. -/
theorem autonomous_relation_of_constantFunctionalProjectiveBoundary
    {K : Set (ℂ → ℂ)} (hK : HasConstantFunctionalProjectiveBoundary K)
    {σ R : ℝ} (hR : 0 < R) {Phi : ℂ → ℂ}
    (hPhi : DifferentiableOn ℂ Phi (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Phi σ R)
    {N : ℕ} (exps : Fin N → (ℕ →₀ ℕ)) (F : Fin N → ℂ → ℂ)
    (hFK : ∀ a, F a ∈ K) (hF0 : ∃ a, F a ≠ 0)
    (hrel : ∀ z ∈ verticalStrip σ R,
      ∑ a : Fin N, F a z * diffMonomial Phi (exps a) z = 0) :
    ∃ c : Fin N → ℂ, (∃ a, c a ≠ 0) ∧
      ∀ z ∈ verticalStrip σ R,
        ∑ a : Fin N, c a * diffMonomial Phi (exps a) z = 0 := by
  classical
  have hreturnHyp : ∀ r : ℝ, 0 < r → r < R →
      HasVerticalUniformReturn (closedVerticalStrip σ r) Phi := by
    intro r _ hr
    exact hasVerticalUniformReturn_of_isStripAlmostPeriodic hap hr
  obtain ⟨T, hT, hreturn⟩ :=
    exists_return_seq_tendstoLocallyUniformlyOn_openVerticalStrip hR hreturnHyp
  obtain ⟨phi, hphi, normalization, c, hc0, hcoeffLU⟩ := hK F hFK hF0 T hT
  let T' : ℕ → ℝ := T ∘ phi
  have hT' : Tendsto T' atTop atTop := hT.comp hphi.tendsto_atTop
  have hreturn' : TendstoLocallyUniformlyOn
      (fun l z => Phi (verticalTranslate (T' l) z)) Phi atTop
      (openVerticalStrip σ R) := by
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := hreturn u hu x hx
    refine ⟨t, ht, ?_⟩
    have hpull := hphi.tendsto_atTop.eventually hev
    simpa [T', Function.comp_def] using hpull
  refine ⟨c, hc0, ?_⟩
  intro z hz
  have hzOpen : z ∈ openVerticalStrip σ R := by
    simpa [verticalStrip, openVerticalStrip] using hz
  have hPhiOpen : DifferentiableOn ℂ Phi (openVerticalStrip σ R) := by
    simpa [verticalStrip, openVerticalStrip] using hPhi
  have hdiff : ∀ᶠ l in atTop,
      DifferentiableOn ℂ (fun w => Phi (w + (T' l : ℂ) * Complex.I))
        (openVerticalStrip σ R) :=
    Filter.Eventually.of_forall fun l =>
      differentiableOn_comp_verticalTranslate
        (isVerticallyInvariant_openVerticalStrip σ R) hPhiOpen (T' l)
  have hjet : ∀ j : ℕ, Tendsto
      (fun l => iteratedDeriv j Phi (z + (T' l : ℂ) * Complex.I))
      atTop (𝓝 (iteratedDeriv j Phi z)) := by
    intro j
    have hbridge := iteratedDeriv_tendsto_of_locallyUniform
      (isOpen_openVerticalStrip σ R) hreturn' hdiff j hzOpen
    refine hbridge.congr fun l => ?_
    exact congrFun
      (_root_.iteratedDeriv_comp_add_const j Phi ((T' l : ℂ) * Complex.I)) z
  have hmon : ∀ a : Fin N, Tendsto
      (fun l => diffMonomial Phi (exps a) (z + (T' l : ℂ) * Complex.I))
      atTop (𝓝 (diffMonomial Phi (exps a) z)) :=
    fun a => diffMonomial_return (exps a) hjet
  have hcoeff : ∀ a : Fin N, Tendsto
      (fun l => normalization l z * F a (z + (T' l : ℂ) * Complex.I))
      atTop (𝓝 (c a)) := by
    intro a
    have hpoint :=
      (hcoeffLU a).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
    simpa [T', Function.comp_def, mul_comm Complex.I] using hpoint
  have hlimit : Tendsto
      (fun l => ∑ a : Fin N,
        (normalization l z * F a (z + (T' l : ℂ) * Complex.I)) *
          diffMonomial Phi (exps a) (z + (T' l : ℂ) * Complex.I))
      atTop (𝓝 (∑ a : Fin N, c a * diffMonomial Phi (exps a) z)) := by
    exact tendsto_finsetSum _ fun a _ => (hcoeff a).mul (hmon a)
  have hzero : Tendsto
      (fun l => ∑ a : Fin N,
        (normalization l z * F a (z + (T' l : ℂ) * Complex.I)) *
          diffMonomial Phi (exps a) (z + (T' l : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun l => by
      symm
      have hzShift : z + (T' l : ℂ) * Complex.I ∈ verticalStrip σ R := by
        simpa [verticalStrip] using hz
      have hrelShift := hrel _ hzShift
      calc
        ∑ a : Fin N,
            (normalization l z * F a (z + (T' l : ℂ) * Complex.I)) *
              diffMonomial Phi (exps a) (z + (T' l : ℂ) * Complex.I) =
            normalization l z *
              ∑ a : Fin N, F a (z + (T' l : ℂ) * Complex.I) *
                diffMonomial Phi (exps a)
                  (z + (T' l : ℂ) * Complex.I) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
        _ = 0 := by rw [hrelShift, mul_zero]
  exact tendsto_nhds_unique hlimit hzero

/-- Recurrent rational-coordinate capstone. A holomorphic strip-almost-periodic solution of a
nonzero ADE with coefficients rational in the neutral Gamma coordinate satisfies a nonzero
autonomous ADE. Its Bohr hull and every continuous translation-equivariant carrier observable have
finite rational frequency rank. -/
theorem neutralGammaRational_recurrence_autonomous_finiteRank
    {θ : ℝ} (hθ : 0 < θ) {σ R : ℝ} (hR : 0 < R) {Phi : ℂ → ℂ}
    (hPhi : DifferentiableOn ℂ Phi (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Phi σ R)
    {N m : ℕ} (e : Fin N → Fin (m + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ)
    (hF : ∀ a, F a ∈ neutralGammaRatioRationalClass θ)
    (hF0 : ∃ a, F a ≠ 0)
    (hrel : ∀ z ∈ verticalStrip σ R,
      ∑ a : Fin N, F a z *
        ∏ j : Fin (m + 1), (iteratedDeriv (j : ℕ) Phi z) ^ (e a j) = 0)
    {f : ℝ →ᵇ ℂ}
    (hf : ∀ x : ℝ, f x = Phi ((σ : ℂ) + (x : ℂ) * Complex.I)) :
    ∃ (c : Fin N → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) (K : ℕ),
      (∃ a, c a ≠ 0) ∧ P ≠ 0 ∧
      (∀ z ∈ verticalStrip σ R,
        MvPolynomial.eval
          (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) Phi z) P = 0) ∧
      Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) ∧
      ∀ (Psi : BohrHull f → ℂ), Continuous Psi →
        Module.rank ℤ
          (AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Psi (bohrIota f t))))
          ≤ (K : Cardinal) := by
  classical
  have hrel' : ∀ z ∈ verticalStrip σ R,
      ∑ a : Fin N, F a z * diffMonomial Phi (jetExpFinsupp (e a)) z = 0 := by
    intro z hz
    simpa only [diffMonomial_jetExpFinsupp] using hrel z hz
  obtain ⟨c, hc0, hauto⟩ :=
    autonomous_relation_of_constantFunctionalProjectiveBoundary
      (hasConstantFunctionalProjectiveBoundary_neutralGammaRatioRationalClass hθ.le)
      hR hPhi hap (fun a => jetExpFinsupp (e a)) F hF hF0 hrel'
  let P : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ a : Fin N, MvPolynomial.C (c a) *
      ∏ j : Fin (m + 1),
        (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) ℂ) ^ (e a j)
  have hc0out := hc0
  obtain ⟨beta, hcbeta⟩ := hc0
  have hP0 : P ≠ 0 := by
    exact monomialSum_ne_zero c e he beta hcbeta
  have hPrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval
        (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) Phi z) P = 0 := by
    intro z hz
    have h := hauto z hz
    simp only [diffMonomial_jetExpFinsupp] at h
    simpa [P, map_sum] using h
  have hfap : _root_.HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfline : (fun x : ℝ => f x) =
        fun t : ℝ => Phi ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      exact hf x
    rw [hfline]
    exact isBohrAlmostPeriodic_line hR hap
  have hfu : UniformContinuous (fun x : ℝ => f x) :=
    uniformContinuous_of_isBohrAlmostPeriodic f.continuous hfap
  have hftb : HasTotallyBoundedOrbit (fun x : ℝ => f x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic f.continuous hfap
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  obtain ⟨K, hKrank⟩ := rank_finite_of_polynomial_relation
    (r := R / 3) (ρ := R / 3) (by linarith) (by linarith) (by linarith)
    hPhi hap hf hfu hftb m P hP0 hPrel
  refine ⟨c, P, K, hc0out, hP0, hPrel, hKrank, ?_⟩
  intro Psi hPsi
  have hsub : AddSubgroup.closure
      (bohrSpectrum (fun t : ℝ => Psi (bohrIota f t))) ≤ bohrHullFrequencies f :=
    AddSubgroup.closure_le _ |>.mpr
      (bohrSpectrum_observable_subset_bohrHullFrequencies hfu hftb Psi hPsi)
  exact le_trans (GaloisForLFunctions.rank_le_of_addSubgroup_le hsub) hKrank

/-- Polynomial realizing the affine neutral-Gamma first jet. -/
def neutralGammaAffineJetPolynomial (θ : ℝ) : Polynomial ℂ :=
  Polynomial.C (θ : ℂ) * Polynomial.X + Polynomial.C (neutralGammaAffineConstant θ)

theorem neutralGammaAffineJetPolynomial_eval (θ : ℝ) (s : ℂ) :
    (neutralGammaAffineJetPolynomial θ).eval s = neutralGammaAffineJet θ s := by
  simp [neutralGammaAffineJetPolynomial, neutralGammaAffineJet]

/-- Positive neutral parameter makes the affine jet polynomial nonconstant. -/
theorem neutralGammaAffineJetPolynomial_natDegree {θ : ℝ} (hθ : θ ≠ 0) :
    (neutralGammaAffineJetPolynomial θ).natDegree = 1 := by
  rw [neutralGammaAffineJetPolynomial]
  apply Polynomial.natDegree_linear
  exact Complex.ofReal_ne_zero.mpr hθ

/-- The `m`-th neutral-Gamma boundary jet has exact polynomial degree `m`. -/
theorem neutralGammaAffineJetPolynomial_pow_natDegree {θ : ℝ} (hθ : θ ≠ 0) (m : ℕ) :
    ((neutralGammaAffineJetPolynomial θ) ^ m).natDegree = m := by
  rw [Polynomial.natDegree_pow, neutralGammaAffineJetPolynomial_natDegree hθ]
  omega

/-- All-degree positive boundary law: every natural power of the nonconstant affine jet occurs as
the exact compact-open limit of the correspondingly normalized frozen neutral-Gamma coordinate. -/
theorem tendstoLocallyUniformly_neutralGamma_allDegreeJet {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    TendstoLocallyUniformly
      (fun n : ℕ => fun s : ℂ =>
        ((neutralGammaFrozenHeight θ n : ℂ) / neutralGammaFrozenPhase θ) ^ m *
          (neutralGammaRatio θ
            (s + Complex.I * (neutralGammaFrozenHeight θ n : ℂ)) -
              neutralGammaFrozenPhase θ) ^ m)
      (fun s : ℂ => (neutralGammaAffineJet θ s) ^ m) atTop := by
  have hLcont : Continuous (neutralGammaAffineJet θ) := by
    change Continuous (fun s : ℂ => (θ : ℂ) * s + neutralGammaAffineConstant θ)
    fun_prop
  have hpow := tendstoLocallyUniformly_pow
    (tendstoLocallyUniformly_neutralGamma_frozenFirstJet hθ) hLcont m
  simpa only [mul_pow] using hpow

end
end GaloisForLFunctions.HTGeometry
