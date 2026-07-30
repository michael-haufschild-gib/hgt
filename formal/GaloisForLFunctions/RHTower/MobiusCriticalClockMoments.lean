import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import Mathlib.NumberTheory.LSeries.Deriv

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators Topology LSeries.notation Moebius

noncomputable section

namespace RHTower

private abbrev squarefreeMobiusLSeriesCoefficient : ℕ → ℂ :=
  fun n => ((μ n : ℤ) : ℂ) * ((μ n : ℤ) : ℂ)

private theorem abscissaOfAbsConv_squarefreeMobius_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv squarefreeMobiusLSeriesCoefficient < s.re := by
  let r : ℝ := (1 + s.re) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrs : r < s.re := by dsimp [r]; linarith
  have hsum : LSeriesSummable squarefreeMobiusLSeriesCoefficient (r : ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ (by simpa using hr)
    intro n hn
    change ‖(((μ n : ℤ) : ℂ) * ((μ n : ℤ) : ℂ))‖ ≤ 1
    rw [norm_mul, norm_intCast]
    have hμ : |((μ n : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    nlinarith [abs_nonneg (((μ n : ℤ) : ℝ))]
  exact lt_of_le_of_lt hsum.abscissaOfAbsConv_le (by simpa using hrs)

private theorem iterate_logMul_squarefreeMobiusLSeriesCoefficient (m n : ℕ) :
    (logMul^[m] squarefreeMobiusLSeriesCoefficient) n =
      Complex.log n ^ m * squarefreeMobiusLSeriesCoefficient n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change Complex.log n *
        (logMul^[m] squarefreeMobiusLSeriesCoefficient) n = _
      rw [ih]
      ring

private theorem term_iterate_logMul_squarefreeMobiusLSeriesCoefficient_eq
    (m : ℕ) (sigma : ℝ) (n : ℕ) :
    term (logMul^[m] squarefreeMobiusLSeriesCoefficient) (sigma : ℂ) n =
      ((squarefreeMobiusMass sigma n * Real.log n ^ m : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term, squarefreeMobiusMass, not_squarefree_zero]
  · rw [term_of_ne_zero hn, iterate_logMul_squarefreeMobiusLSeriesCoefficient,
      Complex.ofReal_mul, ofReal_squarefreeMobiusMass_eq,
      Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [squarefreeMobiusLSeriesCoefficient]
    rw [show (((μ n : ℤ) : ℂ) * ((μ n : ℤ) : ℂ)) =
        if Squarefree n then 1 else 0 by
      rw [← pow_two]
      exact_mod_cast (ArithmeticFunction.moebius_sq (n := n))]
    split_ifs <;> ring

/-- The `m`-th logarithmic moment of the normalized squarefree Mobius mass. -/
def squarefreeMobiusLogMoment (m : ℕ) (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, squarefreeMobiusProbability sigma n * Real.log n ^ m

/-- Every logarithmic moment is summable in the strict Euler half-plane. -/
theorem summable_squarefreeMobiusLogMoment
    (m : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n * Real.log n ^ m) := by
  have htotal : 0 < squarefreeMobiusTotal sigma := squarefreeMobiusTotal_pos hsigma
  have hmajor :=
    (summable_abs_log_natCast_pow_mul_rpow_neg m sigma hsigma).div_const
      (squarefreeMobiusTotal sigma)
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ =>
      |Real.log n| ^ m * (n : ℝ) ^ (-sigma) /
        squarefreeMobiusTotal sigma) ?_ ?_ hmajor
  · intro n
    exact mul_nonneg (squarefreeMobiusProbability_nonneg hsigma n)
      (pow_nonneg (Real.log_natCast_nonneg n) m)
  · intro n
    unfold squarefreeMobiusProbability squarefreeMobiusMass
    by_cases hsq : Squarefree n
    · rw [if_pos hsq]
      rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
      ring_nf
      exact le_rfl
    · rw [if_neg hsq, zero_div, zero_mul]
      positivity

private theorem ofReal_squarefreeMobiusLogMoment_eq_LSeries
    (m : ℕ) (sigma : ℝ) :
    (squarefreeMobiusLogMoment m sigma : ℂ) =
      LSeries (logMul^[m] squarefreeMobiusLSeriesCoefficient) (sigma : ℂ) /
        squarefreeMobiusTotal sigma := by
  rw [squarefreeMobiusLogMoment,
    Complex.ofReal_tsum]
  have hterm : (fun n : ℕ =>
      ((squarefreeMobiusProbability sigma n * Real.log n ^ m : ℝ) : ℂ)) =
      fun n : ℕ =>
        ((squarefreeMobiusMass sigma n * Real.log n ^ m : ℝ) : ℂ) /
          (squarefreeMobiusTotal sigma : ℂ) := by
    funext n
    simp only [squarefreeMobiusProbability, Complex.ofReal_mul, Complex.ofReal_div]
    ring
  rw [hterm, tsum_div_const]
  congr 1
  unfold LSeries
  exact tsum_congr fun n =>
    (term_iterate_logMul_squarefreeMobiusLSeriesCoefficient_eq m sigma n).symm

private theorem ofReal_squarefreeMobiusLogMoment_eq_iteratedDeriv_div
    (m : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusLogMoment m sigma : ℂ) =
      (-1 : ℂ) ^ m *
        iteratedDeriv m _root_.GaloisForLFunctions.squarefreePartition sigma /
          _root_.GaloisForLFunctions.squarefreePartition sigma := by
  rw [ofReal_squarefreeMobiusLogMoment_eq_LSeries]
  have htotal : (squarefreeMobiusTotal sigma : ℂ) =
      _root_.GaloisForLFunctions.squarefreePartition sigma := by
    simpa [_root_.GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma
  rw [htotal]
  have habs := abscissaOfAbsConv_squarefreeMobius_lt_re
    (s := (sigma : ℂ)) (by simpa using hsigma)
  have hiter := LSeries_iteratedDeriv
    (f := squarefreeMobiusLSeriesCoefficient) m habs
  have heq : LSeries squarefreeMobiusLSeriesCoefficient =ᶠ[nhds (sigma : ℂ)]
      _root_.GaloisForLFunctions.squarefreePartition := by
    have hopen : {z : ℂ | 1 < z.re} ∈ nhds (sigma : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hsigma)
    filter_upwards [hopen] with z hz
    simpa [squarefreeMobiusLSeriesCoefficient,
      _root_.GaloisForLFunctions.squarefreePartition] using
      LSeries_squarefree_eq_riemannZeta_div hz
  rw [heq.iteratedDeriv_eq m] at hiter
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  congr 1
  calc
    LSeries (logMul^[m] squarefreeMobiusLSeriesCoefficient) (sigma : ℂ) =
        1 * LSeries (logMul^[m] squarefreeMobiusLSeriesCoefficient) (sigma : ℂ) := by ring
    _ = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
          LSeries (logMul^[m] squarefreeMobiusLSeriesCoefficient) (sigma : ℂ) := by rw [hsign]
    _ = (-1 : ℂ) ^ m *
          iteratedDeriv m _root_.GaloisForLFunctions.squarefreePartition sigma := by
      rw [hiter]
      ring

/-- The first squarefree logarithmic moment is the fixed squarefree current. -/
theorem ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusLogMoment 1 sigma : ℂ) =
      _root_.GaloisForLFunctions.squarefreeFixedCurrent sigma := by
  rw [ofReal_squarefreeMobiusLogMoment_eq_iteratedDeriv_div 1 hsigma]
  simp only [pow_one, neg_mul, one_mul, iteratedDeriv_one]
  simpa [logDeriv_apply, neg_div] using
    (_root_.GaloisForLFunctions.neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent
      (s := (sigma : ℂ)) (by simpa using hsigma))

private theorem tendsto_ofReal_nhdsWithin_one : Tendsto
    (fun sigma : ℝ => (sigma : ℂ))
    (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
  simpa using! Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem tendsto_ofReal_nhdsWithin_one_nhdsNE : Tendsto
    (fun sigma : ℝ => (sigma : ℂ))
    (nhdsWithin 1 (Ioi 1)) (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_ofReal_nhdsWithin_one, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  simpa using hsigma.ne'

/-- The rescaled squarefree logarithmic first moment tends to the unit exponential moment. -/
theorem tendsto_squarefreeMobiusLogMoment_one_critical :
    Tendsto (fun sigma : ℝ =>
      (sigma - 1) * squarefreeMobiusLogMoment 1 sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have hprime := neg_logDeriv_zeta_residue.comp
    tendsto_ofReal_nhdsWithin_one_nhdsNE
  have hmain : Tendsto (fun sigma : ℝ =>
      ((sigma - 1 : ℝ) : ℂ) * infinitePrimeFlux sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    simpa [infinitePrimeFlux, logDeriv_apply, neg_div] using! hprime
  have htwo : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (2 : ℂ)) := by
    simpa using tendsto_const_nhds.mul tendsto_ofReal_nhdsWithin_one
  have hfluxContinuous : ContinuousAt infinitePrimeFlux (2 : ℂ) := by
    have hdiff := differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := (2 : ℂ)) (by norm_num)
    simpa [infinitePrimeFlux, logDeriv_apply, neg_div] using! hdiff.continuousAt
  have hfluxTwo := hfluxContinuous.tendsto.comp htwo
  have hepsilon : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℂ))
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
    simpa using (tendsto_ofReal_nhdsWithin_one.sub hone)
  have hcorrection : Tendsto (fun sigma : ℝ =>
      ((sigma - 1 : ℝ) : ℂ) * (2 * infinitePrimeFlux (2 * sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using hepsilon.mul (tendsto_const_nhds.mul hfluxTwo)
  have hcurrent : Tendsto (fun sigma : ℝ =>
      ((sigma - 1 : ℝ) : ℂ) *
        _root_.GaloisForLFunctions.squarefreeFixedCurrent sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have h := hmain.sub hcorrection
    have hfun : (fun sigma : ℝ =>
        ((sigma - 1 : ℝ) : ℂ) *
          _root_.GaloisForLFunctions.squarefreeFixedCurrent sigma) =
        fun sigma : ℝ =>
          ((sigma - 1 : ℝ) : ℂ) * infinitePrimeFlux sigma -
            ((sigma - 1 : ℝ) : ℂ) * (2 * infinitePrimeFlux (2 * sigma)) := by
      funext sigma
      simp only [_root_.GaloisForLFunctions.squarefreeFixedCurrent]
      ring
    rw [hfun]
    simpa using h
  have hmoment : Tendsto (fun sigma : ℝ =>
      (((sigma - 1) * squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    apply hcurrent.congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    rw [Complex.ofReal_mul,
      ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma]
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hmoment
  convert hre using 1
  · funext sigma
    norm_num
  · norm_num

private theorem analyticAt_squarefreePartition_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ _root_.GaloisForLFunctions.squarefreePartition s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      one_re] at hre
    linarith
  unfold _root_.GaloisForLFunctions.squarefreePartition
  exact (analyticOn_riemannZeta s hs1).div
    ((analyticOn_riemannZeta (2 * s) h2one).comp
      (show AnalyticAt ℂ (fun z : ℂ => 2 * z) s by fun_prop))
    (riemannZeta_ne_zero_of_one_lt_re h2re)

private theorem ofReal_squarefreeMobiusLogMoment_two_eq_fixedCurrent_sq_sub_deriv
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusLogMoment 2 sigma : ℂ) =
      _root_.GaloisForLFunctions.squarefreeFixedCurrent sigma ^ 2 -
        deriv _root_.GaloisForLFunctions.squarefreeFixedCurrent sigma := by
  let F := _root_.GaloisForLFunctions.squarefreePartition
  let C := _root_.GaloisForLFunctions.squarefreeFixedCurrent
  let s : ℂ := sigma
  have hs : 1 < s.re := by simpa [s] using hsigma
  have hFana : AnalyticAt ℂ F s := by
    simpa [F] using analyticAt_squarefreePartition_of_one_lt_re hs
  have hFne : F s ≠ 0 := by
    simpa [F] using _root_.GaloisForLFunctions.squarefreePartition_ne_zero hs
  have hcurrent : -logDeriv F s = C s := by
    simpa [F, C] using
      (_root_.GaloisForLFunctions.neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent
        (s := s) hs)
  have hcurrentEq : (fun z => -logDeriv F z) =ᶠ[nhds s] C := by
    have hopen : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hopen] with z hz
    simpa [F, C] using
      (_root_.GaloisForLFunctions.neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent
        (s := z) hz)
  have hquot : HasDerivAt (fun z => -deriv F z / F z)
      (((-deriv (deriv F) s) * F s - (-deriv F s) * deriv F s) / F s ^ 2) s := by
    exact hFana.deriv.differentiableAt.hasDerivAt.neg.div
      hFana.differentiableAt.hasDerivAt hFne
  have hCderiv : deriv C s =
      ((-deriv (deriv F) s) * F s - (-deriv F s) * deriv F s) / F s ^ 2 := by
    rw [← hcurrentEq.deriv_eq]
    rw [show (fun z => -logDeriv F z) = fun z => -deriv F z / F z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact hquot.deriv
  rw [ofReal_squarefreeMobiusLogMoment_eq_iteratedDeriv_div 2 hsigma]
  simp only [Even.neg_one_pow (by norm_num : Even 2), one_mul]
  change iteratedDeriv 2 F s / F s = C s ^ 2 - deriv C s
  have hCval : C s = -deriv F s / F s := by
    rw [← hcurrent, logDeriv_apply]
    ring
  rw [hCval, hCderiv]
  have hiter : iteratedDeriv 2 F s = deriv (deriv F) s := by
    rw [show 2 = Nat.succ 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  field_simp [hFne]
  ring

private noncomputable def squarefreeMobiusRegularCurrent (s : ℂ) : ℂ :=
  -logDeriv zetaResidueUnit s - 2 * infinitePrimeFlux (2 * s)

private theorem analyticAt_squarefreeMobiusRegularCurrent_one :
    AnalyticAt ℂ squarefreeMobiusRegularCurrent 1 := by
  have hGne : zetaResidueUnit 1 ≠ 0 := by
    rw [zetaResidueUnit_one]
    norm_num
  have hlog : AnalyticAt ℂ (logDeriv zetaResidueUnit) 1 := by
    simpa [logDeriv_apply] using!
      zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt hGne
  have hflux : AnalyticAt ℂ (fun z : ℂ => infinitePrimeFlux (2 * z)) 1 :=
    _root_.GaloisForLFunctions.analyticOnNhd_infinitePrimeFlux_two_mul_rightHalf
      (x := (1 : ℂ)) (by norm_num)
  exact hlog.neg.sub
    ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) 1).mul hflux)

private theorem squarefreeFixedCurrent_eq_inv_add_regularCurrent
    {s : ℂ} (hs : s ≠ 1) (hG : zetaResidueUnit s ≠ 0) :
    _root_.GaloisForLFunctions.squarefreeFixedCurrent s =
      (s - 1)⁻¹ + squarefreeMobiusRegularCurrent s := by
  rw [_root_.GaloisForLFunctions.squarefreeFixedCurrent]
  rw [infinitePrimeFlux, logDeriv_zeta_eq hs hG]
  unfold squarefreeMobiusRegularCurrent
  ring

private theorem deriv_squarefreeFixedCurrent_eq_regularCurrent
    {s : ℂ} (hs : s ≠ 1) (hG : zetaResidueUnit s ≠ 0)
    (hregular : AnalyticAt ℂ squarefreeMobiusRegularCurrent s) :
    deriv _root_.GaloisForLFunctions.squarefreeFixedCurrent s =
      -1 / (s - 1) ^ 2 + deriv squarefreeMobiusRegularCurrent s := by
  have hGcont : ContinuousAt zetaResidueUnit s :=
    (zetaResidueUnit_diffAt hs).continuousAt
  have hcurrentEq : _root_.GaloisForLFunctions.squarefreeFixedCurrent =ᶠ[nhds s]
      fun z => (z - 1)⁻¹ + squarefreeMobiusRegularCurrent z := by
    filter_upwards [eventually_ne_nhds hs, hGcont.eventually_ne hG] with z hz hGz
    exact squarefreeFixedCurrent_eq_inv_add_regularCurrent hz hGz
  have hderiv : HasDerivAt
      (fun z : ℂ => (z - 1)⁻¹ + squarefreeMobiusRegularCurrent z)
      (-1 / (s - 1) ^ 2 + deriv squarefreeMobiusRegularCurrent s) s :=
    (((hasDerivAt_id s).sub_const 1).inv (sub_ne_zero.mpr hs)).add
      hregular.differentiableAt.hasDerivAt
  rw [hcurrentEq.deriv_eq]
  exact hderiv.deriv

/-- The rescaled squarefree logarithmic second moment tends to the unit exponential moment `2`. -/
theorem tendsto_squarefreeMobiusLogMoment_two_critical :
    Tendsto (fun sigma : ℝ =>
      (sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
  let B := squarefreeMobiusRegularCurrent
  have hB : AnalyticAt ℂ B 1 := by
    simpa [B] using analyticAt_squarefreeMobiusRegularCurrent_one
  have hepsilon : Tendsto (fun sigma : ℝ => (((sigma - 1 : ℝ) : ℂ)))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℂ))
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := tendsto_const_nhds
    simpa using tendsto_ofReal_nhdsWithin_one.sub hone
  have hBlim : Tendsto (fun sigma : ℝ => B sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds (B 1)) :=
    hB.continuousAt.tendsto.comp tendsto_ofReal_nhdsWithin_one
  have hBderivLim : Tendsto (fun sigma : ℝ => deriv B sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds (deriv B 1)) :=
    hB.deriv.continuousAt.tendsto.comp tendsto_ofReal_nhdsWithin_one
  have hmodel : Tendsto (fun sigma : ℝ =>
      (2 : ℂ) + 2 * ((sigma - 1 : ℝ) : ℂ) * B sigma +
        ((sigma - 1 : ℝ) : ℂ) ^ 2 * (B sigma ^ 2 - deriv B sigma))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
    have hlinear : Tendsto (fun sigma : ℝ =>
        (2 : ℂ) * ((sigma - 1 : ℝ) : ℂ) * B sigma)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hepsilon).mul hBlim
    have hquadratic : Tendsto (fun sigma : ℝ =>
        ((sigma - 1 : ℝ) : ℂ) ^ 2 * (B sigma ^ 2 - deriv B sigma))
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      simpa using (hepsilon.pow 2).mul (hBlim.pow 2 |>.sub hBderivLim)
    simpa using (tendsto_const_nhds.add hlinear).add hquadratic
  have hcomplex : Tendsto (fun sigma : ℝ =>
      ((((sigma - 1) ^ 2 * squarefreeMobiusLogMoment 2 sigma : ℝ) : ℂ)))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
    apply hmodel.congr'
    have hGeventually : ∀ᶠ sigma : ℝ in nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)),
        zetaResidueUnit (sigma : ℂ) ≠ 0 :=
      tendsto_ofReal_nhdsWithin_one.eventually zetaResidueUnit_ne_zero_eventually
    have hBeventually : ∀ᶠ sigma : ℝ in nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)),
        AnalyticAt ℂ B (sigma : ℂ) :=
      tendsto_ofReal_nhdsWithin_one.eventually hB.eventually_analyticAt
    filter_upwards [self_mem_nhdsWithin, hGeventually, hBeventually] with
      sigma hsigma hGsigma hBsigma
    have hsigmaOne : (sigma : ℂ) ≠ 1 := by
      exact_mod_cast hsigma.ne'
    rw [Complex.ofReal_mul, Complex.ofReal_pow,
      ofReal_squarefreeMobiusLogMoment_two_eq_fixedCurrent_sq_sub_deriv hsigma]
    rw [squarefreeFixedCurrent_eq_inv_add_regularCurrent hsigmaOne hGsigma]
    rw [deriv_squarefreeFixedCurrent_eq_regularCurrent hsigmaOne hGsigma
      (by simpa [B] using hBsigma)]
    simp only [B, Complex.ofReal_sub, Complex.ofReal_one]
    change (2 : ℂ) + 2 * ((sigma : ℂ) - 1) *
          squarefreeMobiusRegularCurrent sigma +
        ((sigma : ℂ) - 1) ^ 2 *
          (squarefreeMobiusRegularCurrent sigma ^ 2 -
            deriv squarefreeMobiusRegularCurrent sigma) =
      (((sigma : ℂ) - 1) ^ 2) *
        (((((sigma : ℂ) - 1)⁻¹ + squarefreeMobiusRegularCurrent sigma) ^ 2) -
          (-1 / ((sigma : ℂ) - 1) ^ 2 +
            deriv squarefreeMobiusRegularCurrent sigma))
    field_simp [sub_ne_zero.mpr hsigmaOne]
    ring
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  convert hre using 1
  · funext sigma
    simp only [Function.comp_apply, Complex.ofReal_re, pow_two]
  · norm_num

end RHTower
