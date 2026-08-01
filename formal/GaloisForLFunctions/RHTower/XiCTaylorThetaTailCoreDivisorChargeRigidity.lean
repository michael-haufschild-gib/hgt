import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicGaugeCharge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCurrentEquivalence

/-!
# Multiplicity-exact divisor charge of the finite theta-tail core

The raw theta-tail core left by the Route H source decomposition is not an uncontrolled error
term.  At every hypothetical Xi zero, every source-selected odd superaccurate schedule makes its
anisotropic normalized current converge to the exact analytic multiplicity.

The proof transfers exact Taylor logarithmic-residue charge through the superaccurate top defect.
The already proved cross-interference estimate is strong enough because the horizontal mesh step
is `O(1/n)`.  This is unconditional divisor tomography, not RH.
-/

open Complex Metric Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Removing a perturbation changes oriented current by at most twice the two unsigned cross
terms once the perturbation value is no larger than the unperturbed value. -/
theorem abs_orientedPolynomialCurrent_sub_sub_le_two_cross
    (U E : Polynomial ℂ) (z : ℂ) (hEU : ‖E.eval z‖ ≤ ‖U.eval z‖) :
    |orientedPolynomialCurrent U z - orientedPolynomialCurrent (U - E) z| ≤
      2 * (‖U.derivative.eval z‖ * ‖E.eval z‖ +
        ‖E.derivative.eval z‖ * ‖U.eval z‖) := by
  let A : ℝ := (U.derivative.eval z * (starRingEnd ℂ) (E.eval z)).im
  let B : ℝ := (E.derivative.eval z * (starRingEnd ℂ) (U.eval z)).im
  let JE : ℝ := orientedPolynomialCurrent E z
  have hA : |A| ≤ ‖U.derivative.eval z‖ * ‖E.eval z‖ := by
    calc
      |A| ≤ ‖U.derivative.eval z * (starRingEnd ℂ) (E.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖U.derivative.eval z‖ * ‖E.eval z‖ := by simp
  have hB : |B| ≤ ‖E.derivative.eval z‖ * ‖U.eval z‖ := by
    calc
      |B| ≤ ‖E.derivative.eval z * (starRingEnd ℂ) (U.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖E.derivative.eval z‖ * ‖U.eval z‖ := by simp
  have hJE : |JE| ≤ ‖E.derivative.eval z‖ * ‖E.eval z‖ := by
    calc
      |JE| ≤ ‖E.derivative.eval z * (starRingEnd ℂ) (E.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖E.derivative.eval z‖ * ‖E.eval z‖ := by simp
  have hJE' : |JE| ≤ ‖E.derivative.eval z‖ * ‖U.eval z‖ :=
    hJE.trans (mul_le_mul_of_nonneg_left hEU (norm_nonneg _))
  have heq :
      orientedPolynomialCurrent U z - orientedPolynomialCurrent (U - E) z =
        A + B - JE := by
    rw [orientedPolynomialCurrent_sub_exact]
    dsimp only [A, B, JE]
    ring
  rw [heq]
  calc
    |A + B - JE| ≤ |A + B| + |JE| := abs_sub _ _
    _ ≤ (|A| + |B|) + |JE| := add_le_add (abs_add_le A B) le_rfl
    _ ≤ (‖U.derivative.eval z‖ * ‖E.eval z‖ +
          ‖E.derivative.eval z‖ * ‖U.eval z‖) +
        ‖E.derivative.eval z‖ * ‖U.eval z‖ :=
      add_le_add (add_le_add hA hB) hJE'
    _ ≤ 2 * (‖U.derivative.eval z‖ * ‖E.eval z‖ +
          ‖E.derivative.eval z‖ * ‖U.eval z‖) := by
      nlinarith [mul_nonneg (norm_nonneg (U.derivative.eval z))
          (norm_nonneg (E.eval z)),
        mul_nonneg (norm_nonneg (E.derivative.eval z))
          (norm_nonneg (U.eval z))]

/-- On a source-selected schedule, the top-defect value is eventually less than half the actual
Taylor value. -/
theorem eventually_two_norm_xiCTaylorThetaTailTopDefect_lt_norm_taylor
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) :
    ∀ᶠ n : ℕ in atTop,
      2 * ‖(xiCTaylorThetaTailTopDefectPolynomial
          (D (xiCTaylorAnisotropicScheduleStage sigma n))).eval
            (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
        ‖(xiCTaylorPolynomial
          (xiCTaylorOddDegreeSchedule D
            (xiCTaylorAnisotropicScheduleStage sigma n))).eval
              (xiCTaylorAnisotropicCenteredPoint sigma n)‖ := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  obtain ⟨c, hc, hXiLower⟩ := eventually_xiC_anisotropic_value_lower sigma
  have htol := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma m
  have htolSmall : ∀ᶠ n : ℕ in atTop,
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ m) < c / 4 :=
    htol.eventually (eventually_lt_nhds (div_pos hc (by norm_num)))
  filter_upwards [hXiLower, htolSmall] with n hnXi hnTol
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let d : ℕ := D k
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let E : Polynomial ℂ := xiCTaylorThetaTailTopDefectPolynomial d
  let tol : ℝ := xiCTaylorScheduleTolerance k
  let q : ℝ := ((n + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqpow : 0 < q ^ m := pow_pos hq _
  have happ := xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint hD.1 sigma n
  have hvalueErr : ‖P.eval z - XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_eval, dist_eq_norm, norm_sub_rev]
      using happ.1
  have hdefect := xiCTaylorThetaTailTopDefect_at_anisotropicCenteredPoint hD sigma n
  have hE : ‖E.eval z‖ < tol := by
    simpa only [E, d, z, k] using hdefect.1
  have hnXi' : c / q ^ m ≤ ‖XiC z‖ := by
    simpa only [z, q, one_div_pow, mul_one_div, m] using hnXi
  have hnTol' : tol * q ^ m < c / 4 := by
    simpa only [tol, k, q, m] using hnTol
  have htolDiv : tol < c / (4 * q ^ m) := by
    rw [lt_div_iff₀ (mul_pos (by norm_num) hqpow)]
    nlinarith
  have htri : ‖XiC z‖ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := by
    calc
      ‖XiC z‖ = ‖P.eval z - (P.eval z - XiC z)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hPLower : c / q ^ m - tol < ‖P.eval z‖ := by
    linarith
  have htwoTol : 2 * tol < ‖P.eval z‖ := by
    have hcdiv : 0 < c / q ^ m := div_pos hc hqpow
    have htolQuarter : tol < (c / q ^ m) / 4 := by
      calc
        tol < c / (4 * q ^ m) := htolDiv
        _ = (c / q ^ m) / 4 := by ring
    nlinarith [htolQuarter]
  exact (mul_lt_mul_of_pos_left hE (by norm_num)).trans htwoTol

/-- The top-defect value is eventually dominated by the theta-tail core value itself. -/
theorem eventually_norm_xiCTaylorThetaTailTopDefect_le_norm_core
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) :
    ∀ᶠ n : ℕ in atTop,
      ‖(xiCTaylorThetaTailTopDefectPolynomial
          (D (xiCTaylorAnisotropicScheduleStage sigma n))).eval
            (xiCTaylorAnisotropicCenteredPoint sigma n)‖ ≤
        ‖(xiCTaylorThetaTailCorePolynomial
          (D (xiCTaylorAnisotropicScheduleStage sigma n))).eval
            (xiCTaylorAnisotropicCenteredPoint sigma n)‖ := by
  filter_upwards
      [eventually_two_norm_xiCTaylorThetaTailTopDefect_lt_norm_taylor hD sigma]
      with n hn
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let d : ℕ := D k
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let U : Polynomial ℂ := xiCTaylorThetaTailCorePolynomial d
  let E : Polynomial ℂ := xiCTaylorThetaTailTopDefectPolynomial d
  have hsplit : U = P + E := by
    dsimp [U, P, E, d, k, xiCTaylorOddDegreeSchedule]
    rw [xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect]
    ring
  have htri : ‖P.eval z‖ ≤ ‖U.eval z‖ + ‖E.eval z‖ := by
    have hPE : P = U - E := by rw [hsplit]; ring
    rw [hPE, eval_sub]
    exact norm_sub_le _ _
  have hn' : 2 * ‖E.eval z‖ < ‖P.eval z‖ := by
    simpa only [E, d, z, P, k] using hn
  nlinarith

/-- The theta-tail core and its actual Taylor section have the same anisotropic divisor charge. -/
theorem tendsto_xiCTaylorThetaTailCoreCurrent_sub_taylorCurrent_horizontalCharge
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (orientedPolynomialCurrent
              (xiCTaylorThetaTailCorePolynomial
                (D (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n) -
            orientedPolynomialCurrent
              (xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)) /
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)))
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hcross := eventually_xiCTaylorThetaTailCrossInterference_lt_scaled_normSq
    hD sigma (show 0 < epsilon / 4 by positivity)
  have hdom := eventually_norm_xiCTaylorThetaTailTopDefect_le_norm_core hD sigma
  have htwo := eventually_two_norm_xiCTaylorThetaTailTopDefect_lt_norm_taylor hD sigma
  filter_upwards [hcross, hdom, htwo] with n hnCross hnDom hnTwo
  let N : ℕ := n + 1
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let d : ℕ := D k
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let U : Polynomial ℂ := xiCTaylorThetaTailCorePolynomial d
  let E : Polynomial ℂ := xiCTaylorThetaTailTopDefectPolynomial d
  let x : ℝ := xiTaylorAnisotropicHorizontalStep sigma n
  let cross : ℝ := xiCTaylorThetaTailCrossInterference d z
  let ns : ℝ := Complex.normSq (P.eval z)
  have hN : 0 < N := by dsimp [N]; omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxgeom := xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hN
  have hx : 0 < x := by
    dsimp only [x, xiTaylorAnisotropicHorizontalStep, N]
    exact lt_of_lt_of_le (by positivity) hxgeom.1
  have hxN : x * (N : ℝ) < 2 := by
    dsimp only [x, xiTaylorAnisotropicHorizontalStep, N]
    rw [div_eq_mul_inv, lt_div_iff₀ hNR] at hxgeom
    simpa only [mul_comm] using hxgeom.2
  have hP : P.eval z ≠ 0 := by
    apply norm_pos_iff.mp
    have hn : 2 * ‖E.eval z‖ < ‖P.eval z‖ := by
      simpa only [E, d, z, P, k] using hnTwo
    exact lt_of_le_of_lt (by positivity) hn
  have hns : 0 < ns := by
    exact Complex.normSq_pos.mpr hP
  have hsplit : U - E = P := by
    dsimp [U, P, E, d, k, xiCTaylorOddDegreeSchedule]
    exact (xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect _).symm
  have hdiff :
      |orientedPolynomialCurrent U z - orientedPolynomialCurrent P z| ≤ 2 * cross := by
    rw [← hsplit]
    simpa only [cross, xiCTaylorThetaTailCrossInterference] using
      abs_orientedPolynomialCurrent_sub_sub_le_two_cross U E z
        (by simpa only [E, d, z, U] using hnDom)
  have hcross' : cross < ((epsilon / 4) * (N : ℝ)) * ns := by
    simpa only [cross, d, z, N, ns, P, k] using hnCross
  have habs :
      x * |orientedPolynomialCurrent U z - orientedPolynomialCurrent P z| <
        epsilon * ns := by
    calc
      x * |orientedPolynomialCurrent U z - orientedPolynomialCurrent P z| ≤
          x * (2 * cross) := mul_le_mul_of_nonneg_left hdiff hx.le
      _ < x * (2 * (((epsilon / 4) * (N : ℝ)) * ns)) := by
        exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hcross' (by norm_num)) hx
      _ = (epsilon * ns / 2) * (x * (N : ℝ)) := by ring
      _ < (epsilon * ns / 2) * 2 :=
        mul_lt_mul_of_pos_left hxN (by positivity)
      _ = epsilon * ns := by ring
  rw [Real.dist_eq, sub_zero, abs_div, abs_mul, abs_of_pos hx, abs_of_pos hns]
  rw [div_lt_iff₀ hns]
  simpa only [x, U, P, z, ns] using habs

/-- Route H's raw finite theta-tail core is a multiplicity-exact divisor transducer. -/
theorem xiCTaylorThetaTailCore_anisotropicDivisorCharge_tendsto
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          orientedPolynomialCurrent
            (xiCTaylorThetaTailCorePolynomial
              (D (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) /
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have hTaylorLog :=
    xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto hD.1 sigma
  have hTaylorCurrent : Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          orientedPolynomialCurrent
            (xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) /
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
    convert hTaylorLog using 1
    funext n
    rw [show xiCTaylorApprox
          (xiCTaylorOddDegreeSchedule D
            (xiCTaylorAnisotropicScheduleStage sigma n)) =
        fun w : ℂ =>
          (xiCTaylorPolynomial
            (xiCTaylorOddDegreeSchedule D
              (xiCTaylorAnisotropicScheduleStage sigma n))).eval w by
      funext w
      exact (xiCTaylorPolynomial_eval _ w).symm]
    rw [polynomial_logDeriv_im_eq_orientedCurrent_div_normSq]
    ring
  have hDifference :=
    tendsto_xiCTaylorThetaTailCoreCurrent_sub_taylorCurrent_horizontalCharge hD sigma
  have hsum := hTaylorCurrent.add hDifference
  convert hsum using 1
  · funext n
    ring
  · ring

/-- At an Xi zero the raw theta-core charge has a strictly positive multiplicity tail. -/
theorem eventually_half_xiOrder_lt_xiCTaylorThetaTailCore_anisotropicDivisorCharge
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {sigma : ℂ} (hzero : xi sigma = 0) :
    ∀ᶠ n : ℕ in atTop,
      ((analyticOrderAt xi sigma).toNat : ℝ) / 2 <
        xiTaylorAnisotropicHorizontalStep sigma n *
          orientedPolynomialCurrent
            (xiCTaylorThetaTailCorePolynomial
              (D (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) /
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlimit := xiCTaylorThetaTailCore_anisotropicDivisorCharge_tendsto hD sigma
  exact hlimit.eventually (eventually_gt_nhds (by linarith))

end

end RHTower
