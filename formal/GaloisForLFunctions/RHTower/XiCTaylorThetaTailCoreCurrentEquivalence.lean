import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteCoefficientGate
import GaloisForLFunctions.RHTower.BoundedClockZeroTransfer

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Under RH the scheduled theta-tail core current is absolutely, rather than merely one-sided,
sublinear relative to the scaled squared Taylor value.  The proof uses only local nonvanishing of
`XiC` on the left-strip fibre and uniform convergence of the scheduled value and derivative. -/
theorem eventually_abs_xiCTaylorThetaTailCoreCurrent_lt_scaled_normSq_of_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hRH : RiemannHypothesis)
    (sigma : ℂ) (hsigmaHalf : sigma.re < 1 / 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |orientedPolynomialCurrent
          (xiCTaylorThetaTailCorePolynomial
            (D (xiCTaylorAnisotropicScheduleStage sigma n)))
          (xiCTaylorAnisotropicCenteredPoint sigma n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  let alpha : ℂ := xiCTaylorCenteredPoint sigma
  have halphaIm : 0 < alpha.im := by
    dsimp [alpha, xiCTaylorCenteredPoint]
    simp only [mul_im, neg_re, I_re, neg_im, I_im, sub_re]
    norm_num
    linarith
  have hXiNe : XiC alpha ≠ 0 := by
    intro hzero
    have := xiC_zero_im_eq_zero_of_riemannHypothesis hRH hzero
    linarith
  let c : ℝ := ‖XiC alpha‖ / 4
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hXiNe) (by norm_num)
  have hXiTend : Tendsto
      (fun n : ℕ => ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖)
      atTop (nhds ‖XiC alpha‖) := by
    have hcont : ContinuousAt XiC alpha :=
      (XiC_analytic alpha (Set.mem_univ alpha)).continuousAt
    exact hcont.norm.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have hXiLower : ∀ᶠ n : ℕ in atTop,
      2 * c < ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ := by
    have hlt : 2 * c < ‖XiC alpha‖ := by
      dsimp [c]
      linarith [norm_pos_iff.mpr hXiNe]
    exact hXiTend.eventually (eventually_gt_nhds hlt)
  have htolTend : Tendsto (fun n : ℕ =>
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n))
      atTop (nhds 0) := by
    simpa using tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma 0
  have htolSmall : ∀ᶠ n : ℕ in atTop,
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) < c :=
    htolTend.eventually (eventually_lt_nhds hc)
  obtain ⟨Cval, _hCval, hvalueUpper⟩ :=
    eventually_xiC_anisotropic_value_upper sigma
  obtain ⟨Cder, _hCder, hderivUpper⟩ :=
    eventually_xiC_anisotropic_deriv_upper sigma
  let K : ℝ := (Cder + 2) * (Cval + 2)
  have hnLarge : ∀ᶠ n : ℕ in atTop,
      K < epsilon * ((n + 1 : ℕ) : ℝ) * c ^ 2 := by
    have hslope : 0 < epsilon * c ^ 2 := mul_pos hepsilon (sq_pos_of_pos hc)
    have hq : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hprod := hq.atTop_mul_const hslope
    filter_upwards [hprod.eventually_gt_atTop K] with n hn
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hn
  filter_upwards [hXiLower, htolSmall, hvalueUpper, hderivUpper, hnLarge]
      with n hnXi hnTol hnVal hnDer hnK
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let d : ℕ := D k
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let E : Polynomial ℂ := xiCTaylorThetaTailTopDefectPolynomial d
  let U : Polynomial ℂ := xiCTaylorThetaTailCorePolynomial d
  let tol : ℝ := xiCTaylorScheduleTolerance k
  have happ := xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint hD.1 sigma n
  have hvalueErr : ‖P.eval z - XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_eval, dist_eq_norm, norm_sub_rev] using happ.1
  have hderivErr : ‖P.derivative.eval z - deriv XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_derivative_eval,
      dist_eq_norm, norm_sub_rev] using happ.2
  have hdefect := xiCTaylorThetaTailTopDefect_at_anisotropicCenteredPoint hD sigma n
  have hE : ‖E.eval z‖ < tol := by
    simpa only [E, d, z, k] using hdefect.1
  have hEderiv : ‖E.derivative.eval z‖ < tol := by
    simpa only [E, d, z, k] using hdefect.2
  have htolOne : tol ≤ 1 := xiCTaylorScheduleTolerance_le_one k
  have hPUpper : ‖P.eval z‖ ≤ Cval + 1 := by
    calc
      ‖P.eval z‖ = ‖XiC z + (P.eval z - XiC z)‖ := by congr 1; ring
      _ ≤ ‖XiC z‖ + ‖P.eval z - XiC z‖ := norm_add_le _ _
      _ ≤ Cval + 1 := add_le_add hnVal (hvalueErr.le.trans htolOne)
  have hPderUpper : ‖P.derivative.eval z‖ ≤ Cder + 1 := by
    calc
      ‖P.derivative.eval z‖ =
          ‖deriv XiC z + (P.derivative.eval z - deriv XiC z)‖ := by congr 1; ring
      _ ≤ ‖deriv XiC z‖ + ‖P.derivative.eval z - deriv XiC z‖ := norm_add_le _ _
      _ ≤ Cder + 1 := add_le_add hnDer (hderivErr.le.trans htolOne)
  have hsplit : U = P + E := by
    dsimp [U, P, E, d, k, xiCTaylorOddDegreeSchedule]
    have h := xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect (D k)
    rw [h]
    ring
  have hUUpper : ‖U.eval z‖ ≤ Cval + 2 := by
    rw [hsplit, eval_add]
    calc
      ‖P.eval z + E.eval z‖ ≤ ‖P.eval z‖ + ‖E.eval z‖ := norm_add_le _ _
      _ ≤ (Cval + 1) + 1 := add_le_add hPUpper (hE.le.trans htolOne)
      _ = Cval + 2 := by ring
  have hUderUpper : ‖U.derivative.eval z‖ ≤ Cder + 2 := by
    rw [hsplit, derivative_add, eval_add]
    calc
      ‖P.derivative.eval z + E.derivative.eval z‖ ≤
          ‖P.derivative.eval z‖ + ‖E.derivative.eval z‖ := norm_add_le _ _
      _ ≤ (Cder + 1) + 1 := add_le_add hPderUpper (hEderiv.le.trans htolOne)
      _ = Cder + 2 := by ring
  have hPLower : c < ‖P.eval z‖ := by
    have htri : ‖XiC z‖ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := by
      calc
        ‖XiC z‖ = ‖P.eval z - (P.eval z - XiC z)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have htol : tol < c := by simpa only [tol, k] using hnTol
    have hxi : 2 * c < ‖XiC z‖ := by simpa only [z] using hnXi
    linarith [hvalueErr]
  have hcurrent : |orientedPolynomialCurrent U z| ≤ K := by
    calc
      |orientedPolynomialCurrent U z| ≤
          ‖U.derivative.eval z * (starRingEnd ℂ) (U.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖U.derivative.eval z‖ * ‖U.eval z‖ := by simp
      _ ≤ (Cder + 2) * (Cval + 2) :=
        mul_le_mul hUderUpper hUUpper (norm_nonneg _) (by positivity)
      _ = K := rfl
  have hnormSq : c ^ 2 < Complex.normSq (P.eval z) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (P.eval z)]
  calc
    |orientedPolynomialCurrent U z| ≤ K := hcurrent
    _ < epsilon * ((n + 1 : ℕ) : ℝ) * c ^ 2 := hnK
    _ < (epsilon * ((n + 1 : ℕ) : ℝ)) * Complex.normSq (P.eval z) := by
      gcongr

theorem xiCTaylorThetaTailCoreCurrentSublinearUpper_of_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hRH : RiemannHypothesis) :
    XiCTaylorThetaTailCoreCurrentSublinearUpper D := by
  intro sigma _hsigma0 hsigmaHalf epsilon hepsilon
  filter_upwards
    [eventually_abs_xiCTaylorThetaTailCoreCurrent_lt_scaled_normSq_of_riemannHypothesis
      hD hRH sigma hsigmaHalf epsilon hepsilon] with n hn
  exact lt_of_abs_lt hn
/-- Exact logical status of the finite theta-tail core-current condition on any source-selected
odd super-accurate schedule.  The forward implication is the finite source gate; the reverse
implication uses RH only to keep the limiting Xi value away from zero on each open left-strip
fibre. -/
theorem xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorThetaTailCoreCurrentSublinearUpper D ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper hD
  · exact xiCTaylorThetaTailCoreCurrentSublinearUpper_of_riemannHypothesis hD

/-- RH also discharges the unreduced finite theta-tail envelope: the top-defect cross terms are
already controlled unconditionally from superaccuracy. -/
theorem xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hRH : RiemannHypothesis) :
    XiCTaylorThetaTailCoreInterferenceSublinearUpper D :=
  xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_coreCurrent hD
    (xiCTaylorThetaTailCoreCurrentSublinearUpper_of_riemannHypothesis hD hRH)

/-- **Exact finite theta-tail envelope criterion on every source-selected schedule.** -/
theorem xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorThetaTailCoreInterferenceSublinearUpper D ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiCTaylorThetaTailCoreInterferenceSublinearUpper hD.1,
    xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_riemannHypothesis hD⟩

/-- Existence of one source-selected schedule satisfying the core-current condition is exactly RH.
The schedule premise is internalized by the unconditional source construction. -/
theorem exists_xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis :
    (∃ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D ∧
      XiCTaylorThetaTailCoreCurrentSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨D, hD, hcurrent⟩
    exact
      (xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis hD).1
        hcurrent
  · intro hRH
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact ⟨D, hD,
      (xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis hD).2 hRH⟩

/-- Requiring the core-current condition on every source-selected schedule is also exactly RH. -/
theorem forall_xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis :
    (∀ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      XiCTaylorThetaTailCoreCurrentSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact
      (xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis hD).1
        (hall D hD)
  · intro hRH D hD
    exact
      (xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis hD).2 hRH

/-- Existence of one source-selected schedule satisfying the full interference bound is exactly
RH. -/
theorem exists_xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis :
    (∃ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D ∧
      XiCTaylorThetaTailCoreInterferenceSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨D, hD, hinterference⟩
    exact
      (xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis hD).1
        hinterference
  · intro hRH
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact ⟨D, hD,
      (xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis hD).2 hRH⟩

/-- Requiring the full interference bound on every source-selected schedule is exactly RH. -/
theorem forall_xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis :
    (∀ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      XiCTaylorThetaTailCoreInterferenceSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact
      (xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis hD).1
        (hall D hD)
  · intro hRH D hD
    exact
      (xiCTaylorThetaTailCoreInterferenceSublinearUpper_iff_riemannHypothesis hD).2 hRH

end

end RHTower
