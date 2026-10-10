import GaloisForLFunctions.RHTower.GaussianPrimeGapInghamOmega
import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.DigammaLeLog

/-!
# Complete archimedean bias of the central Gaussian prime gap

Let `P(y) = Σ Λ(n) n^{-1/2} e^{-yn²}` and `C(y) = ∫₁^∞ u^{-1/2} e^{-yu²} du`.

* **Archimedean bias** (`re_gaussianArchimedeanCurrent_half_le`).  The archimedean current at the
  centre is `A(½) = 2 + ψ(¼)/2 − (log π)/2`.  The recurrence `ψ(¼) = ψ(5/4) − 4` and `ψ ≤ log`
  give `A(½) ≤ ½ log(5/(4π)) ≤ −7/24`.
* **Critical germs** (`norm_criticalZeroGerm_le`).  For a zero on the critical line, two steps of
  the incomplete-Gamma recursion give `|e^{-y}/(ρ−½) + E(y, ρ−½)| ≤ 2(1+y)/|ρ|²`.
* **Near-rigidity under RH** (`eventually_abs_gaussianCentralGap_sub_bias_le`).  Under RH the
  germ field is at most `2(1+y)` times the Hermitian zero mass `Σ |ρ|^{-2}`, which equals the
  endpoint curvature `2 + γ − log 4π < 0.0924`.  Hence `|P − C − A(½)| ≤ 2(2 + γ − log 4π) + ε`
  for all small `y`, and `P(y) ≤ C(y) − 1/20` eventually: the bias is complete.
* **Sign law** (`riemannHypothesis_iff_eventually_gaussianCentralGap_neg`).  RH holds iff
  `P(y) < C(y)` for all sufficiently small `y`.  Equivalently `P − C` is eventually bounded above,
  or eventually bounded below.  Without RH, `P − C` exceeds every `K` and falls below every `−K`
  arbitrarily close to `0` (`gaussianCentralGap_dichotomy`).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-! ## The archimedean bias -/

/-- The archimedean current at the centre: `A(½) = 2 + ψ(¼)/2 − (log π)/2`. -/
theorem gaussianArchimedeanCurrent_half :
    gaussianArchimedeanCurrent (1 / 2 : ℂ) =
      2 + Complex.digamma (1 / 4) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  rw [gaussianArchimedeanCurrent, logDeriv_Gammaℝ_of_re_pos (by norm_num)]
  norm_num
  ring

/-- `Re ψ(¼) ≤ log(5/4) − 4`, from `ψ(5/4) = ψ(¼) + 4` and `ψ ≤ log` on the positive reals. -/
theorem re_digamma_quarter_le : (Complex.digamma (1 / 4)).re ≤ Real.log (5 / 4) - 4 := by
  have hne : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at h'
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hrec := Complex.digamma_apply_add_one (1 / 4 : ℂ) hne
  have hle := re_digamma_le_log (y := 5 / 4) (by norm_num)
  have h54 : ((5 / 4 : ℝ) : ℂ) = 1 / 4 + 1 := by push_cast; norm_num
  rw [h54, hrec, Complex.add_re] at hle
  have h4 : ((1 / 4 : ℂ)⁻¹).re = 4 := by norm_num
  rw [h4] at hle
  linarith

/-- **The archimedean bias is negative**: `Re A(½) ≤ ½ log(5/(4π)) ≤ −7/24`. -/
theorem re_gaussianArchimedeanCurrent_half_le :
    (gaussianArchimedeanCurrent (1 / 2 : ℂ)).re ≤ -7 / 24 := by
  rw [gaussianArchimedeanCurrent_half]
  have hψ := re_digamma_quarter_le
  have hre : (2 + Complex.digamma (1 / 4) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      2 + (Complex.digamma (1 / 4)).re / 2 - Real.log Real.pi / 2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    norm_num
  rw [hre]
  have hpi := Real.pi_gt_three
  have hlog : 7 / 12 ≤ Real.log Real.pi - Real.log (5 / 4) := by
    rw [← Real.log_div Real.pi_ne_zero (by norm_num)]
    have h := Real.one_sub_inv_le_log_of_pos (x := Real.pi / (5 / 4)) (by positivity)
    have hinv : (Real.pi / (5 / 4))⁻¹ ≤ 5 / 12 := by
      rw [inv_div, div_le_div_iff₀ Real.pi_pos (by norm_num)]
      linarith
    linarith
  linarith

/-- The endpoint curvature `2 + γ − log 4π` is below `0.0924`. -/
theorem xiEndpointCompletedCurvature_lt_231_div_2500 :
    xiEndpointCompletedCurvature < 231 / 2500 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  have hγ :=
    eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h12 : Real.log 12 ≤ Real.log (4 * Real.pi) :=
    Real.log_le_log (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hl12 : Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
    rw [show (12 : ℝ) = 3 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h3 := Real.log_three_gt_d9
  have h2 := Real.log_two_gt_d9
  norm_num at h3 h2 hγ ⊢
  linarith

/-! ## Critical zero germs -/

/-- **Germ of a critical zero.**  For `Re ρ = ½` and `y > 0`,
`|e^{-y}/(ρ−½) + E(y, ρ−½)| ≤ 2(1+y)/|ρ|²`: two recursion steps leave
`(2y/a)(−e^{-y}/(a+2) + (2y/(a+2)) E(y, a+4))` with `a = ρ − ½`, the remainder satisfies
`|E(y, a+4)| ≤ 1/(2y²)`, and `|a||a+2| ≥ |ρ|²` once `|Im ρ| > 1`. -/
theorem norm_criticalZeroGerm_le {y : ℝ} (hy : 0 < y) (q : XiZeroCopy)
    (hq : (xiZero q).re = 1 / 2) :
    ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))‖ ≤
      2 * (1 + y) * ‖(xiZero q)⁻¹‖ ^ 2 := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [hcast]
  set ρ : ℂ := xiZero q with hρ
  have him : 1 < |ρ.im| := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_abs_im_le_one h (xi_xiZero q)
  set a : ℂ := ρ - 1 / 2 with ha
  have hare : a.re = 0 := by rw [ha, Complex.sub_re, hq]; norm_num
  have haim : a.im = ρ.im := by rw [ha]; simp
  have ha0 : a ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    rw [haim, Complex.zero_im] at h'
    rw [h', abs_zero] at him
    linarith
  have ha2 : a + 2 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [Complex.add_re, hare] at h'
    norm_num at h'
  have hrec1 := gaussianIncompleteMellin_recursion hy ha0
  have hrec2 := gaussianIncompleteMellin_recursion hy ha2
  set e : ℂ := (Real.exp (-y) : ℂ) with he
  set E4 : ℂ := gaussianIncompleteMellin y (a + 2 + 2) with hE4
  have hgerm : e / a + gaussianIncompleteMellin y a =
      2 * y / a * (-e / (a + 2) + 2 * y / (a + 2) * E4) := by
    rw [hrec1, hrec2]
    ring
  rw [hgerm]
  -- the remainder
  have hE4b : ‖E4‖ ≤ y ^ (-((3 : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((3 : ℝ) + 1) / 2) :=
    norm_gaussianIncompleteMellin_le hy (by norm_num) (by
      rw [Complex.add_re, Complex.add_re, hare]; norm_num)
  have hpow : y ^ (-((3 : ℝ) + 1) / 2) = (y ^ 2)⁻¹ := by
    rw [show -((3 : ℝ) + 1) / 2 = -(2 : ℝ) by norm_num, Real.rpow_neg hy.le]
    norm_cast
  have hΓ : Real.Gamma (((3 : ℝ) + 1) / 2) = 1 := by
    rw [show ((3 : ℝ) + 1) / 2 = 2 by norm_num, Real.Gamma_two]
  rw [hpow, hΓ] at hE4b
  have hyE : 2 * y * ‖E4‖ ≤ y⁻¹ := by
    have h1 : 2 * y * ‖E4‖ ≤ 2 * y * ((y ^ 2)⁻¹ * (1 / 2) * 1) :=
      mul_le_mul_of_nonneg_left hE4b (by positivity)
    have h2 : 2 * y * ((y ^ 2)⁻¹ * (1 / 2) * 1) = y⁻¹ := by
      field_simp
    linarith
  have he1 : ‖e‖ ≤ 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  -- norms of the denominators
  set na : ℝ := ‖a‖ with hna
  set nb : ℝ := ‖a + 2‖ with hnb
  have hna0 : 0 < na := norm_pos_iff.2 ha0
  have hnb0 : 0 < nb := norm_pos_iff.2 ha2
  have hinner : ‖-e / (a + 2) + 2 * y / (a + 2) * E4‖ ≤ (1 + y⁻¹) / nb := by
    have h1 : ‖-e / (a + 2)‖ ≤ 1 / nb := by
      rw [norm_div, norm_neg]
      exact div_le_div_of_nonneg_right he1 hnb0.le
    have h2 : ‖2 * y / (a + 2) * E4‖ ≤ y⁻¹ / nb := by
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy,
        Complex.norm_two]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hnb0]
      exact hyE
    calc _ ≤ ‖-e / (a + 2)‖ + ‖2 * y / (a + 2) * E4‖ := norm_add_le _ _
      _ ≤ 1 / nb + y⁻¹ / nb := add_le_add h1 h2
      _ = (1 + y⁻¹) / nb := by ring
  have hmain : ‖2 * y / a * (-e / (a + 2) + 2 * y / (a + 2) * E4)‖ ≤
      2 * (1 + y) / (na * nb) := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy,
      Complex.norm_two]
    calc 2 * y / na * ‖-e / (a + 2) + 2 * y / (a + 2) * E4‖
        ≤ 2 * y / na * ((1 + y⁻¹) / nb) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 2 * (1 + y) / (na * nb) := by field_simp; ring
  -- `|a| |a+2| ≥ |ρ|²`
  set t : ℝ := ρ.im ^ 2 with ht
  have ht1 : 1 < t := by
    rw [ht, ← sq_abs]
    nlinarith [abs_nonneg ρ.im]
  have hna2 : na ^ 2 = t := by
    rw [hna, Complex.sq_norm, Complex.normSq_apply, hare, haim, ht]; ring
  have hnb2 : nb ^ 2 = 4 + t := by
    rw [hnb, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, hare, haim, ht]
    norm_num
    ring
  have hnr2 : ‖ρ‖ ^ 2 = 1 / 4 + t := by
    rw [Complex.sq_norm, Complex.normSq_apply, hq, ht]; ring
  have hprod : ‖ρ‖ ^ 2 ≤ na * nb := by
    have hsq : (‖ρ‖ ^ 2) ^ 2 ≤ (na * nb) ^ 2 := by
      rw [mul_pow, hna2, hnb2, hnr2]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  have hρ0 : 0 < ‖ρ‖ ^ 2 := by
    have : 0 < 1 / 4 + t := by linarith
    rwa [hnr2]
  calc _ ≤ 2 * (1 + y) / (na * nb) := hmain
    _ ≤ 2 * (1 + y) / ‖ρ‖ ^ 2 := div_le_div_of_nonneg_left (by positivity) hρ0 hprod
    _ = 2 * (1 + y) * ‖ρ⁻¹‖ ^ 2 := by rw [norm_inv, inv_pow, div_eq_mul_inv]

/-- **The critical germ field under RH** is at most `2(1+y)` times the endpoint curvature
`2 + γ − log 4π`, the Hermitian zero mass `Σ |ρ|^{-2}`. -/
theorem norm_tsum_criticalZeroGerm_le_of_riemannHypothesis (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 0 < y) :
    ‖∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ)))‖ ≤
      2 * (1 + y) * xiEndpointCompletedCurvature := by
  have hq : ∀ q : XiZeroCopy, (xiZero q).re = 1 / 2 :=
    fun q => xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hw : Summable fun q : XiZeroCopy => ‖(xiZero q)⁻¹‖ ^ 2 :=
    (summable_norm_inv_xiZero_pow (k := 2) le_rfl).congr fun q => norm_pow _ _
  have hb := fun q => norm_criticalZeroGerm_le hy q (hq q)
  have hsn : Summable fun q : XiZeroCopy => ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hw.mul_left _)
  have hmass : ∑' q : XiZeroCopy, ‖(xiZero q)⁻¹‖ ^ 2 = xiRawReciprocalHermitianMass := rfl
  have hle := xiRawReciprocalHermitianMass_le_endpointCurvature_iff_rh.2 hRH
  calc _ ≤ ∑' q : XiZeroCopy, ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' q : XiZeroCopy, 2 * (1 + y) * ‖(xiZero q)⁻¹‖ ^ 2 :=
        hsn.tsum_le_tsum hb (hw.mul_left _)
    _ = 2 * (1 + y) * xiRawReciprocalHermitianMass := by rw [tsum_mul_left, hmass]
    _ ≤ 2 * (1 + y) * xiEndpointCompletedCurvature :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## The central gap -/

/-- The real Gaussian gap at `σ > 0` is the archimedean transform minus the germ field. -/
theorem gaussianWeightedGap_eq_MB_sub_germField {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) :
    ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) =
      gaussianArchimedeanMB y 2 (σ : ℂ) -
        ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin y (xiZero q - σ)) := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hx : 0 < y / Real.pi := div_pos hy Real.pi_pos
  have hpy : Real.pi * (y / Real.pi) = y := mul_div_cancel₀ _ Real.pi_ne_zero
  have hid := (logDeriv_gaussianFormation_eq_sub_gap hx hs).symm.trans
    (logDeriv_gaussianFormation_eq_zeroField hx hs)
  rw [hpy] at hid
  rw [← gaussianPrimeContinuumGap_ofReal]
  linear_combination -hid

/-- **Near-rigidity under RH.**  Under RH, for every `ε > 0` and all small `y`,
`|P(y) − C(y) − Re A(½)| ≤ 2(2 + γ − log 4π) + ε`. -/
theorem eventually_abs_gaussianCentralGap_sub_bias_le (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[>] 0, |gaussianWeightedPrimeMass (1 / 2) y -
        gaussianWeightedContinuumMass (1 / 2) y - (gaussianArchimedeanCurrent (1 / 2 : ℂ)).re| ≤
      2 * xiEndpointCompletedCurvature + ε := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have hs : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have hA := (tendsto_gaussianArchimedeanCurrent_sub_MB two_pos hs).norm
  rw [norm_zero] at hA
  have hAev := hA.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hsmall : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < ε / 4 :=
    (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)).eventually
      (gt_mem_nhds (by positivity))
  have hκ1 : xiEndpointCompletedCurvature < 1 := xiEndpointCompletedCurvature_lt_one
  have hκ0 : 0 < xiEndpointCompletedCurvature := xiEndpointCompletedCurvature_pos
  filter_upwards [self_mem_nhdsWithin, hAev, hsmall] with y hy hAy hys
  have hy0 : (0 : ℝ) < y := hy
  have hgap := gaussianWeightedGap_eq_MB_sub_germField (σ := 1 / 2) (by norm_num) hy0
  have hZ := norm_tsum_criticalZeroGerm_le_of_riemannHypothesis hRH hy0
  set Z : ℂ := ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))) with hZdef
  set M : ℂ := gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) with hM
  set A : ℂ := gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) with hAdef
  have hAeq : gaussianArchimedeanCurrent (1 / 2 : ℂ) = A := by rw [hAdef, hcast]
  rw [hAeq]
  have hre : gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y - A.re =
      -(A - M).re - Z.re := by
    have := congrArg Complex.re hgap
    rw [Complex.ofReal_re, Complex.sub_re] at this
    rw [this, Complex.sub_re]
    ring
  rw [hre]
  have h1 : |(A - M).re| ≤ ε / 2 := (Complex.abs_re_le_norm _).trans hAy.le
  have h2 : |Z.re| ≤ 2 * (1 + y) * xiEndpointCompletedCurvature :=
    (Complex.abs_re_le_norm _).trans hZ
  have h3 : 2 * (1 + y) * xiEndpointCompletedCurvature ≤ 2 * xiEndpointCompletedCurvature + ε / 2 := by
    nlinarith
  calc |-(A - M).re - Z.re| ≤ |(A - M).re| + |Z.re| := by
        rw [show -(A - M).re - Z.re = -((A - M).re + Z.re) by ring, abs_neg]
        exact abs_add_le _ _
    _ ≤ 2 * xiEndpointCompletedCurvature + ε := by linarith

/-- **Complete bias under RH.**  Under RH, `P(y) ≤ C(y) − 1/20` for all small `y > 0`. -/
theorem eventually_gaussianCentralGap_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ y in 𝓝[>] 0,
      gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤ -1 / 20 := by
  filter_upwards [eventually_abs_gaussianCentralGap_sub_bias_le hRH
    (show (0 : ℝ) < 1 / 100 by norm_num)] with y hy
  have hA := re_gaussianArchimedeanCurrent_half_le
  have hκ := xiEndpointCompletedCurvature_lt_231_div_2500
  have := (abs_le.1 hy).2
  linarith

/-! ## The sign law -/

/-- Away from `0` the central gap is bounded: `|P(y) − C(y)| ≤ (e² + Γ(½)) δ^{-2}` on `[δ, 1]`. -/
theorem abs_gaussianCentralGap_le_of_ge {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hyδ : δ ≤ y) (hy1 : y ≤ 1) :
    |gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y| ≤
      (Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ) := by
  have hb := norm_gaussianPrimeContinuumGap_le (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)
    (hδ.trans_le hyδ) hy1
  rw [gaussianPrimeContinuumGap_ofReal, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hyδ (by norm_num))
    (by positivity))

/-- An eventual upper bound of the central gap implies RH. -/
theorem riemannHypothesis_of_eventually_gaussianCentralGap_le {B : ℝ}
    (h : ∀ᶠ y in 𝓝[>] 0,
      gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤ B) :
    RiemannHypothesis := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have hδ0 : (0 : ℝ) < δ := hδ
  set K : ℝ := max ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B with hKdef
  refine riemannHypothesis_iff_gaussianCentralPrimeBudget.2 ⟨K, fun y hy hy1 => ?_⟩
  by_cases hyδ : y < δ
  · have : gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤ B :=
      hsub ⟨hy, hyδ⟩
    have := le_max_right ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B
    linarith
  · push Not at hyδ
    have := (abs_le.1 (abs_gaussianCentralGap_le_of_ge hδ0 hyδ hy1)).2
    have := le_max_left ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B
    linarith

/-- An eventual lower bound of the central gap implies RH. -/
theorem riemannHypothesis_of_eventually_gaussianCentralGap_ge {B : ℝ}
    (h : ∀ᶠ y in 𝓝[>] 0,
      -B ≤ gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y) :
    RiemannHypothesis := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have hδ0 : (0 : ℝ) < δ := hδ
  set K : ℝ := max ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B with hKdef
  rw [rh_iff_xi_ne_zero_right]
  intro s hs
  refine xi_ne_zero_of_gaussianPrimeBudget_lower (σ := 1 / 2) (by norm_num) (B := K)
    (fun y hy hy1 => ?_) (mem_rightHalf.1 hs)
  by_cases hyδ : y < δ
  · have : -B ≤ gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y :=
      hsub ⟨hy, hyδ⟩
    have := le_max_right ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B
    linarith
  · push Not at hyδ
    have := (abs_le.1 (abs_gaussianCentralGap_le_of_ge hδ0 hyδ hy1)).1
    have := le_max_left ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B
    linarith

/-- **Sign law.**  RH holds iff the central Gaussian prime mass `Σ Λ(n) n^{-1/2} e^{-yn²}` lies
strictly below its continuum `∫₁^∞ u^{-1/2} e^{-yu²} du` for all sufficiently small `y > 0`. -/
theorem riemannHypothesis_iff_eventually_gaussianCentralGap_neg :
    RiemannHypothesis ↔ ∀ᶠ y in 𝓝[>] 0,
      gaussianWeightedPrimeMass (1 / 2) y < gaussianWeightedContinuumMass (1 / 2) y := by
  constructor
  · intro hRH
    filter_upwards [eventually_gaussianCentralGap_le_of_riemannHypothesis hRH] with y hy
    linarith
  · intro h
    exact riemannHypothesis_of_eventually_gaussianCentralGap_le (B := 0)
      (h.mono fun y hy => by linarith)

/-- RH holds iff the central gap is eventually bounded below. -/
theorem riemannHypothesis_iff_eventually_gaussianCentralGap_bddBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ᶠ y in 𝓝[>] 0,
      -B ≤ gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y := by
  constructor
  · intro hRH
    refine ⟨-((gaussianArchimedeanCurrent (1 / 2 : ℂ)).re - 2 * xiEndpointCompletedCurvature - 1),
      ?_⟩
    filter_upwards [eventually_abs_gaussianCentralGap_sub_bias_le hRH one_pos] with y hy
    have := (abs_le.1 hy).1
    linarith
  · rintro ⟨B, hB⟩
    exact riemannHypothesis_of_eventually_gaussianCentralGap_ge hB

/-- **Dichotomy.**  Either the central gap is eventually below `−1/20` (exactly when RH holds), or
it exceeds every `K` and falls below every `−K` arbitrarily close to `0`. -/
theorem gaussianCentralGap_dichotomy :
    (∀ᶠ y in 𝓝[>] 0,
      gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤ -1 / 20) ∨
    ∀ K : ℝ, (∃ᶠ y in 𝓝[>] 0,
        K < gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y) ∧
      ∃ᶠ y in 𝓝[>] 0,
        gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y < -K := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl (eventually_gaussianCentralGap_le_of_riemannHypothesis hRH)
  · refine Or.inr fun K => ⟨?_, ?_⟩
    · by_contra hf
      rw [Filter.not_frequently] at hf
      exact hRH (riemannHypothesis_of_eventually_gaussianCentralGap_le (B := K)
        (hf.mono fun y hy => not_lt.1 hy))
    · by_contra hf
      rw [Filter.not_frequently] at hf
      exact hRH (riemannHypothesis_of_eventually_gaussianCentralGap_ge (B := K)
        (hf.mono fun y hy => not_lt.1 hy))

end

end RHTower
