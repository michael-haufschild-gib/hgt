import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay

/-!
# Theta-tail finite coefficient gate for anisotropic Xi Taylor flux

This module packages the exact theta-tail core/top-defect decomposition as a pointwise and
anisotropic-mesh sufficient condition for upper logarithmic-derivative flux.  It also constructs
an odd-degree super-accurate Taylor schedule, so the decomposition applies at every scheduled
cutoff.  The module does not prove the remaining theta-tail core-current estimate.
-/

open Complex Metric Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Odd Taylor degree attached to a source index. -/
def xiCTaylorOddDegreeSchedule (D : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * (D n + 1) + 1

/-- The canonical Xi Taylor family admits a source-selected super-accurate schedule consisting
entirely of the odd cutoffs required by the theta-tail telescope. -/
theorem exists_xiCTaylorSuperaccurateOddSchedule :
    ∃ D : ℕ → ℕ, XiCTaylorSuperaccurateSchedule (xiCTaylorOddDegreeSchedule D) := by
  have hthreshold : ∀ n : ℕ, ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (XiC z) (xiCTaylorApprox m z) < xiCTaylorScheduleTolerance n) ∧
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (deriv XiC z) (deriv (xiCTaylorApprox m) z) <
          xiCTaylorScheduleTolerance n) := by
    intro n
    have hfun : TendstoUniformlyOn xiCTaylorApprox XiC atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hderiv : TendstoUniformlyOn (deriv ∘ xiCTaylorApprox) (deriv XiC) atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_deriv_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hevFun := (Metric.tendstoUniformlyOn_iff.mp hfun)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    have hevDeriv := (Metric.tendstoUniformlyOn_iff.mp hderiv)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hevFun.and hevDeriv)
    refine ⟨k, fun m hm => ?_⟩
    obtain ⟨hfm, hdm⟩ := hk m hm
    refine ⟨hfm, ?_⟩
    intro z hz
    simpa only [Function.comp_apply] using hdm z hz
  choose K hK using hthreshold
  let D : ℕ → ℕ := fun n => Nat.rec (K 0)
    (fun j previous => max (previous + 1) (K (j + 1))) n
  have hD_zero : D 0 = K 0 := by rfl
  have hD_succ (n : ℕ) : D (n + 1) = max (D n + 1) (K (n + 1)) := by rfl
  have hKD : ∀ n : ℕ, K n ≤ D n := by
    intro n
    induction n with
    | zero => rw [hD_zero]
    | succ n _ =>
        rw [hD_succ]
        exact Nat.le_max_right _ _
  have hDstrict : StrictMono D := strictMono_nat_of_lt_succ fun n => by
    rw [hD_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self (D n)) (Nat.le_max_left _ _)
  refine ⟨D, ?_, ?_⟩
  · intro a b hab
    unfold xiCTaylorOddDegreeSchedule
    have hDab := hDstrict hab
    omega
  · intro n z hz
    have hKN : K n ≤ xiCTaylorOddDegreeSchedule D n := by
      exact (hKD n).trans (by unfold xiCTaylorOddDegreeSchedule; omega)
    obtain ⟨hvalue, hderiv⟩ := hK n _ hKN
    exact ⟨hvalue z hz, hderiv z hz⟩

/-- An odd schedule is theta-tail super-accurate when the canonical Taylor value and derivative,
and also the explicit top defect and its derivative, are all below the same expanding-ball
tolerance. -/
def XiCTaylorOddThetaTailSuperaccurateSchedule (D : ℕ → ℕ) : Prop :=
  XiCTaylorSuperaccurateSchedule (xiCTaylorOddDegreeSchedule D) ∧
    ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) n,
      ‖(xiCTaylorThetaTailTopDefectPolynomial (D n)).eval z‖ <
          xiCTaylorScheduleTolerance n ∧
        ‖(xiCTaylorThetaTailTopDefectPolynomial (D n)).derivative.eval z‖ <
          xiCTaylorScheduleTolerance n

/-- A source-selected odd schedule can simultaneously make the canonical Taylor approximation
and the explicit theta-tail top defect super-accurate on every expanding ball. -/
theorem exists_xiCTaylorOddThetaTailSuperaccurateSchedule :
    ∃ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D := by
  have hTaylor : ∀ n : ℕ, ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (XiC z) (xiCTaylorApprox m z) < xiCTaylorScheduleTolerance n) ∧
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (deriv XiC z) (deriv (xiCTaylorApprox m) z) <
          xiCTaylorScheduleTolerance n) := by
    intro n
    have hfun : TendstoUniformlyOn xiCTaylorApprox XiC atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hderiv : TendstoUniformlyOn (deriv ∘ xiCTaylorApprox) (deriv XiC) atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_deriv_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hevFun := (Metric.tendstoUniformlyOn_iff.mp hfun)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    have hevDeriv := (Metric.tendstoUniformlyOn_iff.mp hderiv)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hevFun.and hevDeriv)
    refine ⟨k, fun m hm => ?_⟩
    obtain ⟨hfm, hdm⟩ := hk m hm
    refine ⟨hfm, ?_⟩
    intro z hz
    simpa only [Function.comp_apply] using hdm z hz
  have hDefect : ∀ n : ℕ, ∃ k : ℕ, ∀ d : ℕ, k ≤ d →
      ∀ z ∈ closedBall (0 : ℂ) n,
        ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ <
            xiCTaylorScheduleTolerance n ∧
          ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ <
            xiCTaylorScheduleTolerance n := by
    intro n
    have hev := eventually_norm_xiCTaylorThetaTailTopDefect_lt_on_closedBall
      (R := (n : ℝ)) (epsilon := xiCTaylorScheduleTolerance n)
      (Nat.cast_nonneg n) (xiCTaylorScheduleTolerance_pos n)
    exact Filter.eventually_atTop.mp hev
  choose KT hKT using hTaylor
  choose KE hKE using hDefect
  let K : ℕ → ℕ := fun n => max (KT n) (KE n)
  let D : ℕ → ℕ := fun n => Nat.rec (K 0)
    (fun j previous => max (previous + 1) (K (j + 1))) n
  have hD_zero : D 0 = K 0 := by rfl
  have hD_succ (n : ℕ) : D (n + 1) = max (D n + 1) (K (n + 1)) := by rfl
  have hKD : ∀ n : ℕ, K n ≤ D n := by
    intro n
    induction n with
    | zero => rw [hD_zero]
    | succ n _ =>
        rw [hD_succ]
        exact Nat.le_max_right _ _
  have hDstrict : StrictMono D := strictMono_nat_of_lt_succ fun n => by
    rw [hD_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self (D n)) (Nat.le_max_left _ _)
  refine ⟨D, ?_, ?_⟩
  · constructor
    · intro a b hab
      unfold xiCTaylorOddDegreeSchedule
      have hDab := hDstrict hab
      omega
    · intro n z hz
      have hKTN : KT n ≤ xiCTaylorOddDegreeSchedule D n := by
        exact (Nat.le_max_left _ _).trans ((hKD n).trans
          (by unfold xiCTaylorOddDegreeSchedule; omega))
      obtain ⟨hvalue, hderiv⟩ := hKT n _ hKTN
      exact ⟨hvalue z hz, hderiv z hz⟩
  · intro n z hz
    have hKEN : KE n ≤ D n := (Nat.le_max_right _ _).trans (hKD n)
    exact hKE n (D n) hKEN z hz

/-- The explicit finite upper envelope: theta-tail core current plus the two top-defect
cross-interference norms. -/
def xiCTaylorThetaTailCoreInterference (d : ℕ) (z : ℂ) : ℝ :=
  orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z +
    ‖(xiCTaylorThetaTailCorePolynomial d).derivative.eval z‖ *
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ +
    ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ *
      ‖(xiCTaylorThetaTailCorePolynomial d).eval z‖

/-- The two explicit cross terms are the entire unsigned cost of removing the favorable top
defect from the theta-tail core. -/
def xiCTaylorThetaTailCrossInterference (d : ℕ) (z : ℂ) : ℝ :=
  ‖(xiCTaylorThetaTailCorePolynomial d).derivative.eval z‖ *
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ +
    ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ *
      ‖(xiCTaylorThetaTailCorePolynomial d).eval z‖

theorem xiCTaylorThetaTailCoreInterference_eq (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailCoreInterference d z =
      orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z +
        xiCTaylorThetaTailCrossInterference d z := by
  unfold xiCTaylorThetaTailCoreInterference xiCTaylorThetaTailCrossInterference
  ring

theorem xiCTaylorThetaTailCrossInterference_le_taylor_add_defect
    (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailCrossInterference d z ≤
      (‖(xiCTaylorPolynomial (2 * (d + 1) + 1)).derivative.eval z‖ +
          ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖) *
        ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ +
      ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ *
        (‖(xiCTaylorPolynomial (2 * (d + 1) + 1)).eval z‖ +
          ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖) := by
  have hsplit :=
    xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect d
  have hcore : xiCTaylorThetaTailCorePolynomial d =
      xiCTaylorPolynomial (2 * (d + 1) + 1) +
        xiCTaylorThetaTailTopDefectPolynomial d := by
    rw [hsplit]
    ring
  unfold xiCTaylorThetaTailCrossInterference
  rw [hcore, derivative_add, eval_add, eval_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))

/-- Pointwise finite coefficient theorem.  A strict bound for the explicit theta-tail envelope
forces nonvanishing and the same upper bound for the logarithmic derivative of the actual
canonical Xi Taylor section. -/
theorem xiCTaylor_logDeriv_im_lt_of_thetaTailCoreInterference_lt
    (d : ℕ) {z : ℂ} (hz : 0 ≤ z.im) {B : ℝ}
    (hfinite : xiCTaylorThetaTailCoreInterference d z <
      B * Complex.normSq
        ((xiCTaylorPolynomial (2 * (d + 1) + 1)).eval z)) :
    (xiCTaylorPolynomial (2 * (d + 1) + 1)).eval z ≠ 0 ∧
      (logDeriv (xiCTaylorApprox (2 * (d + 1) + 1)) z).im < B := by
  have hcurrent :
      orientedPolynomialCurrent (xiCTaylorPolynomial (2 * (d + 1) + 1)) z <
        B * Complex.normSq
          ((xiCTaylorPolynomial (2 * (d + 1) + 1)).eval z) :=
    (xiCTaylor_orientedCurrent_le_thetaTailCore_add_interference d hz).trans_lt hfinite
  have h := polynomial_logDeriv_im_lt_of_orientedCurrent_lt
    (xiCTaylorPolynomial (2 * (d + 1) + 1)) z hcurrent
  refine ⟨h.1, ?_⟩
  simpa only [xiCTaylorPolynomial_eval] using h.2

/-- Source-facing finite theta-tail condition on every left-strip anisotropic mesh fibre. -/
def XiCTaylorThetaTailCoreInterferenceSublinearUpper (D : ℕ → ℕ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        xiCTaylorThetaTailCoreInterference
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n) <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n))

/-- The irreducible source obligation after the favorable top defect and its cross terms have
been removed: sublinear upper current for the finite theta-tail core itself. -/
def XiCTaylorThetaTailCoreCurrentSublinearUpper (D : ℕ → ℕ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        orientedPolynomialCurrent
            (xiCTaylorThetaTailCorePolynomial
              (D (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n))

theorem eventually_xiCTaylorAnisotropicCenteredPoint_im_pos
    (sigma : ℂ) (hsigma : sigma.re < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < (xiCTaylorAnisotropicCenteredPoint sigma n).im := by
  have htend := tendsto_xiCTaylorAnisotropicCenteredPoint sigma
  have him : Tendsto (fun n => (xiCTaylorAnisotropicCenteredPoint sigma n).im) atTop
      (nhds (xiCTaylorCenteredPoint sigma).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp htend
  have htarget : 0 < (xiCTaylorCenteredPoint sigma).im := by
    rw [xiCTaylorCenteredPoint, mul_im]
    simp only [neg_re, I_re, neg_im, I_im]
    rw [sub_re]
    norm_num
    linarith
  exact him.eventually (eventually_gt_nhds htarget)

theorem eventually_xiC_anisotropic_value_upper (sigma : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ ≤ C := by
  let alpha : ℂ := xiCTaylorCenteredPoint sigma
  let C : ℝ := ‖XiC alpha‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hXiCont : ContinuousAt XiC alpha :=
    (XiC_analytic alpha (Set.mem_univ alpha)).continuousAt
  have htend : Tendsto
      (fun n : ℕ => ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖)
      atTop (nhds ‖XiC alpha‖) :=
    hXiCont.norm.tendsto.comp (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have hev : ∀ᶠ n : ℕ in atTop,
      ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ < C :=
    htend.eventually (eventually_lt_nhds (by dsimp [C]; linarith))
  exact hev.mono fun _ hn => hn.le

theorem xiCTaylorThetaTailTopDefect_at_anisotropicCenteredPoint
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (n : ℕ) :
    ‖(xiCTaylorThetaTailTopDefectPolynomial
        (D (xiCTaylorAnisotropicScheduleStage sigma n))).eval
          (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
        xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) ∧
      ‖(xiCTaylorThetaTailTopDefectPolynomial
        (D (xiCTaylorAnisotropicScheduleStage sigma n))).derivative.eval
          (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
        xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) := by
  exact hD.2 _ _ (xiCTaylorAnisotropicCenteredPoint_mem_closedBall_stage sigma n)

theorem xiCTaylorScheduleTolerance_le_one (k : ℕ) :
    xiCTaylorScheduleTolerance k ≤ 1 := by
  unfold xiCTaylorScheduleTolerance
  rw [inv_le_one₀ (by positivity)]
  exact one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))

/-- For a theta-tail super-accurate odd schedule, the two top-defect cross terms are
unconditionally negligible relative to the scaled squared Taylor value on every anisotropic
fibre.  No zero-free hypothesis is used: the local analytic order supplies the polynomial lower
bound, while the source-selected defect tolerance beats every fixed power. -/
theorem eventually_xiCTaylorThetaTailCrossInterference_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      xiCTaylorThetaTailCrossInterference
          (D (xiCTaylorAnisotropicScheduleStage sigma n))
          (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  obtain ⟨c, hc, hvalueLower⟩ := eventually_xiC_anisotropic_value_lower sigma
  obtain ⟨Cder, hCder, hderivUpper⟩ := eventually_xiC_anisotropic_deriv_upper sigma
  obtain ⟨Cval, hCval, hvalueUpper⟩ := eventually_xiC_anisotropic_value_upper sigma
  let K : ℝ := Cder + Cval + 4
  have hK : 0 < K := by dsimp [K]; linarith
  have htolM := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma m
  have htolTwoM := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma (2 * m)
  have hsmallValue : ∀ᶠ n : ℕ in atTop,
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ m) < c / 2 :=
    htolM.eventually (eventually_lt_nhds (half_pos hc))
  have hsmallInterference : ∀ᶠ n : ℕ in atTop,
      K * (xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
        (((n + 1 : ℕ) : ℝ) ^ (2 * m))) < epsilon * c ^ (2 : ℕ) / 4 := by
    have htend : Tendsto (fun n : ℕ =>
        K * (xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ (2 * m)))) atTop (𝓝 0) := by
      simpa using htolTwoM.const_mul K
    have htarget : 0 < epsilon * c ^ (2 : ℕ) / 4 := by positivity
    exact htend.eventually (eventually_lt_nhds htarget)
  filter_upwards [hvalueLower, hderivUpper, hvalueUpper,
    hsmallValue, hsmallInterference] with n hnLower hnDeriv hnValue hnSmall hnInterference
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let d : ℕ := D k
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let E : Polynomial ℂ := xiCTaylorThetaTailTopDefectPolynomial d
  let tol : ℝ := xiCTaylorScheduleTolerance k
  let q : ℝ := ((n + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqpow : 0 < q ^ m := pow_pos hq _
  have htolPos : 0 < tol := xiCTaylorScheduleTolerance_pos k
  have htolOne : tol ≤ 1 := xiCTaylorScheduleTolerance_le_one k
  have happ := xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint hD.1 sigma n
  have hvalueErr : ‖P.eval z - XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_eval, dist_eq_norm, norm_sub_rev] using happ.1
  have hderivErr : ‖P.derivative.eval z - deriv XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_derivative_eval,
      dist_eq_norm, norm_sub_rev] using happ.2
  have hdefect := xiCTaylorThetaTailTopDefect_at_anisotropicCenteredPoint hD sigma n
  have hE : ‖E.eval z‖ < tol := by simpa only [E, d, z, k] using hdefect.1
  have hEderiv : ‖E.derivative.eval z‖ < tol := by
    simpa only [E, d, z, k] using hdefect.2
  have hPValueUpper : ‖P.eval z‖ ≤ Cval + 1 := by
    calc
      ‖P.eval z‖ = ‖XiC z + (P.eval z - XiC z)‖ := by congr 1; ring
      _ ≤ ‖XiC z‖ + ‖P.eval z - XiC z‖ := norm_add_le _ _
      _ ≤ Cval + 1 := add_le_add hnValue (hvalueErr.le.trans htolOne)
  have hPDerivUpper : ‖P.derivative.eval z‖ ≤ Cder + 1 := by
    calc
      ‖P.derivative.eval z‖ =
          ‖deriv XiC z + (P.derivative.eval z - deriv XiC z)‖ := by congr 1; ring
      _ ≤ ‖deriv XiC z‖ + ‖P.derivative.eval z - deriv XiC z‖ := norm_add_le _ _
      _ ≤ Cder + 1 := add_le_add hnDeriv (hderivErr.le.trans htolOne)
  have hXiTriangle : ‖XiC z‖ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := by
    calc
      ‖XiC z‖ = ‖P.eval z - (P.eval z - XiC z)‖ := by congr 1; ring
      _ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := norm_sub_le _ _
  have hnLower' : c / q ^ m ≤ ‖XiC z‖ := by
    simpa only [z, q, m, one_div_pow, mul_one_div] using hnLower
  have hnSmall' : tol * q ^ m < c / 2 := by simpa only [tol, q, k, m] using hnSmall
  have hPValueLowerMul : c / 2 < ‖P.eval z‖ * q ^ m := by
    have htriMul : ‖XiC z‖ * q ^ m ≤
        (‖P.eval z‖ + ‖P.eval z - XiC z‖) * q ^ m :=
      mul_le_mul_of_nonneg_right hXiTriangle (pow_nonneg hq.le m)
    have hlowerMul : c ≤ ‖XiC z‖ * q ^ m := by
      exact (div_le_iff₀ hqpow).mp hnLower'
    have herrMul : ‖P.eval z - XiC z‖ * q ^ m < c / 2 :=
      (mul_lt_mul_of_pos_right hvalueErr hqpow).trans hnSmall'
    nlinarith
  have hPValueLower : c / (2 * q ^ m) < ‖P.eval z‖ := by
    rw [div_lt_iff₀ (mul_pos (by norm_num) hqpow)]
    nlinarith
  have hcross := xiCTaylorThetaTailCrossInterference_le_taylor_add_defect d z
  have hcrossUpper : xiCTaylorThetaTailCrossInterference d z ≤ K * tol := by
    calc
      xiCTaylorThetaTailCrossInterference d z ≤
          (‖P.derivative.eval z‖ + ‖E.derivative.eval z‖) * ‖E.eval z‖ +
            ‖E.derivative.eval z‖ * (‖P.eval z‖ + ‖E.eval z‖) := by
        simpa only [P, E, d, xiCTaylorOddDegreeSchedule] using hcross
      _ ≤ ((Cder + 1) + tol) * tol + tol * ((Cval + 1) + tol) := by
        gcongr
      _ ≤ K * tol := by
        dsimp [K]
        nlinarith [htolPos.le, htolOne]
  have hnInterference' : K * (tol * q ^ (2 * m)) < epsilon * c ^ (2 : ℕ) / 4 := by
    simpa only [K, tol, q, k, m] using hnInterference
  have hcrossVsBase : K * tol <
      (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) := by
    have hqOne : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpowEq : q ^ (2 * m) = (q ^ m) ^ (2 : ℕ) := by
      rw [show 2 * m = m * 2 by omega, pow_mul]
    rw [show (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) =
        (epsilon * q * c ^ (2 : ℕ) / 4) / (q ^ m) ^ (2 : ℕ) by
          field_simp
          ring]
    rw [lt_div_iff₀ (sq_pos_of_pos hqpow)]
    rw [hpowEq] at hnInterference'
    have hnInterference'' : K * tol * (q ^ m) ^ (2 : ℕ) < epsilon * c ^ (2 : ℕ) / 4 := by
      calc
        K * tol * (q ^ m) ^ (2 : ℕ) = K * (tol * (q ^ m) ^ (2 : ℕ)) := by ring
        _ < epsilon * c ^ (2 : ℕ) / 4 := hnInterference'
    have htargetMono : epsilon * c ^ (2 : ℕ) / 4 ≤ epsilon * q * c ^ (2 : ℕ) / 4 := by
      have hnonneg : 0 ≤ epsilon * c ^ (2 : ℕ) / 4 := by positivity
      calc
        epsilon * c ^ (2 : ℕ) / 4 = 1 * (epsilon * c ^ (2 : ℕ) / 4) := by ring
        _ ≤ q * (epsilon * c ^ (2 : ℕ) / 4) :=
          mul_le_mul_of_nonneg_right hqOne hnonneg
        _ = epsilon * q * c ^ (2 : ℕ) / 4 := by ring
    exact hnInterference''.trans_le htargetMono
  have hbaseSq : (c / (2 * q ^ m)) ^ (2 : ℕ) ≤ ‖P.eval z‖ ^ (2 : ℕ) := by
    have ha : 0 ≤ c / (2 * q ^ m) := by positivity
    have hb : 0 ≤ ‖P.eval z‖ := norm_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hPValueLower.le) (add_nonneg hb ha)]
  calc
    xiCTaylorThetaTailCrossInterference d z ≤ K * tol := hcrossUpper
    _ < (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) := hcrossVsBase
    _ ≤ (epsilon * q) * Complex.normSq (P.eval z) := by
      rw [Complex.normSq_eq_norm_sq]
      exact mul_le_mul_of_nonneg_left hbaseSq (mul_nonneg hepsilon.le hq.le)

/-- On a source-selected theta-tail super-accurate schedule, the core-current condition alone
implies the full finite envelope condition; the top-defect cross terms are discharged
unconditionally. -/
theorem xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_coreCurrent
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hcore : XiCTaylorThetaTailCoreCurrentSublinearUpper D) :
    XiCTaylorThetaTailCoreInterferenceSublinearUpper D := by
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  have hepsilonHalf : 0 < epsilon / 2 := half_pos hepsilon
  have hcoreEv := hcore sigma hsigmaPos hsigmaHalf (epsilon / 2) hepsilonHalf
  have hcrossEv :=
    eventually_xiCTaylorThetaTailCrossInterference_lt_scaled_normSq
      hD sigma hepsilonHalf
  filter_upwards [hcoreEv, hcrossEv] with n hnCore hnCross
  rw [xiCTaylorThetaTailCoreInterference_eq]
  calc
    orientedPolynomialCurrent
          (xiCTaylorThetaTailCorePolynomial
            (D (xiCTaylorAnisotropicScheduleStage sigma n)))
          (xiCTaylorAnisotropicCenteredPoint sigma n) +
        xiCTaylorThetaTailCrossInterference
          (D (xiCTaylorAnisotropicScheduleStage sigma n))
          (xiCTaylorAnisotropicCenteredPoint sigma n) <
      ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) +
        ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) :=
      add_lt_add hnCore hnCross
    _ = (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by ring

/-- The finite theta-tail envelope condition forces the denominator-cleared oriented coefficient
condition for the odd Taylor schedule. -/
theorem xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_thetaTailCoreInterference
    {D : ℕ → ℕ}
    (hfinite : XiCTaylorThetaTailCoreInterferenceSublinearUpper D) :
    XiCTaylorAnisotropicOrientedCoefficientSublinearUpper
      (xiCTaylorOddDegreeSchedule D) := by
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  have hbound := hfinite sigma hsigmaPos hsigmaHalf epsilon hepsilon
  have him := eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  filter_upwards [hbound, him] with n hn hz
  exact (xiCTaylor_orientedCurrent_le_thetaTailCore_add_interference
    (D (xiCTaylorAnisotropicScheduleStage sigma n)) hz.le).trans_lt hn

/-- A source-selected odd super-accurate schedule satisfying the finite theta-tail envelope
condition has sublinear upper logarithmic-derivative flux on every anisotropic mesh fibre. -/
theorem xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreInterference
    {D : ℕ → ℕ}
    (hfinite : XiCTaylorThetaTailCoreInterferenceSublinearUpper D) :
    XiCTaylorAnisotropicLogDerivSublinearUpper (xiCTaylorOddDegreeSchedule D) :=
  xiCTaylorAnisotropicLogDerivSublinearUpper_of_orientedCoefficient
    (xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_thetaTailCoreInterference hfinite)

/-- Terminal theorem: the source-selected finite theta-tail coefficient inequality proves RH. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCoreInterferenceSublinearUpper
    {D : ℕ → ℕ}
    (hD : XiCTaylorSuperaccurateSchedule (xiCTaylorOddDegreeSchedule D))
    (hfinite : XiCTaylorThetaTailCoreInterferenceSublinearUpper D) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorAnisotropicOrientedCoefficientSublinearUpper hD
    (xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_thetaTailCoreInterference hfinite)

/-- The reduced core-current condition forces anisotropic sublinear upper flux; all top-defect
terms have already been discharged from the explicit theta source. -/
theorem xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreCurrent
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hcore : XiCTaylorThetaTailCoreCurrentSublinearUpper D) :
    XiCTaylorAnisotropicLogDerivSublinearUpper (xiCTaylorOddDegreeSchedule D) :=
  xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreInterference
    (xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_coreCurrent hD hcore)

/-- Final reduced endpoint: on an unconditionally existing source-selected schedule, proving the
finite theta-tail core-current inequality is sufficient for RH. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hcore : XiCTaylorThetaTailCoreCurrentSublinearUpper D) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorThetaTailCoreInterferenceSublinearUpper hD.1
    (xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_coreCurrent hD hcore)

/-- A fixed source-selected odd theta-tail schedule.  Its existence uses only the canonical Xi
Taylor coefficients and the explicit theta-tail top defect; it contains no zero-location input. -/
noncomputable def xiCTaylorOddThetaTailCanonicalSchedule : ℕ → ℕ :=
  Classical.choose exists_xiCTaylorOddThetaTailSuperaccurateSchedule

theorem xiCTaylorOddThetaTailCanonicalSchedule_spec :
    XiCTaylorOddThetaTailSuperaccurateSchedule
      xiCTaylorOddThetaTailCanonicalSchedule :=
  Classical.choose_spec exists_xiCTaylorOddThetaTailSuperaccurateSchedule

/-- Interface-free Taylor endpoint.  For the fixed canonical source schedule, the raw theta-tail
core-current inequality is the only remaining hypothesis on the chain to RH. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCanonicalCoreCurrentSublinearUpper
    (hcore : XiCTaylorThetaTailCoreCurrentSublinearUpper
      xiCTaylorOddThetaTailCanonicalSchedule) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper
    xiCTaylorOddThetaTailCanonicalSchedule_spec hcore

end

end RHTower
