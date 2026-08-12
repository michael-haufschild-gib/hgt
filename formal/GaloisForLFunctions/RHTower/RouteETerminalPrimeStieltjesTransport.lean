import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO
import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation

/-!
# Route E terminal-prime Stieltjes transport

This module supplies the arithmetic bridge missing from the critical terminal-frame minimax law.
It keeps the literal oscillatory prime frame and rewrites it, exactly, as its continuous terminal
integral plus the two endpoint values and one integral of the unconditional Chebyshev error
`theta(y) - y`.  No short-interval prime number theorem and no arithmetic hypothesis enter.
-/

namespace RHTower

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics
open scoped BigOperators

noncomputable section

/-- Real squared modulus of the terminal antiscale phase `1 + y^(it)`. -/
def routeETerminalPhaseEnergy (t y : ℝ) : ℝ :=
  2 + 2 * Real.cos (t * Real.log y)

/-- Exact chain-rule derivative of terminal phase energy on the positive half-line. -/
def routeETerminalPhaseDerivative (t y : ℝ) : ℝ :=
  2 * (-Real.sin (t * Real.log y) * (t * y⁻¹))

/-- Abel weight which removes the logarithmic jump of `theta`. -/
def routeETerminalAbelWeight (r t y : ℝ) : ℝ :=
  y ^ (-r) * routeETerminalPhaseEnergy t y / Real.log y

/-- Explicit derivative of the terminal Abel weight on the positive half-line. -/
def routeETerminalAbelDerivative (r t y : ℝ) : ℝ :=
  (((-r) * y ^ (-r - 1) * routeETerminalPhaseEnergy t y
      + y ^ (-r) * routeETerminalPhaseDerivative t y) * Real.log y
    - y ^ (-r) * routeETerminalPhaseEnergy t y * y⁻¹) / Real.log y ^ 2

/-- Literal terminal prime frame on `(X/e, X]`, extended by zero off primes. -/
def routeETerminalPrimeFrame (r X t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊X / Real.exp 1⌋₊ ⌊X⌋₊,
    if k.Prime then (k : ℝ) ^ (-r) * routeETerminalPhaseEnergy t k else 0

/-- Continuous comparison integral for the terminal prime frame. -/
def routeETerminalPrimeMain (r X t : ℝ) : ℝ :=
  ∫ y in Ioc (X / Real.exp 1) X, y ^ (-r) * routeETerminalPhaseEnergy t y / Real.log y

theorem routeETerminalPhaseEnergy_nonneg (t y : ℝ) :
    0 ≤ routeETerminalPhaseEnergy t y := by
  rw [routeETerminalPhaseEnergy]
  nlinarith [Real.neg_one_le_cos (t * Real.log y)]

theorem routeETerminalPhaseEnergy_le_four (t y : ℝ) :
    routeETerminalPhaseEnergy t y ≤ 4 := by
  rw [routeETerminalPhaseEnergy]
  nlinarith [Real.cos_le_one (t * Real.log y)]

theorem abs_routeETerminalPhaseDerivative_le {t y : ℝ} (hy : 0 < y) :
    |routeETerminalPhaseDerivative t y| ≤ 2 * |t| / y := by
  have hsin := Real.abs_sin_le_one (t * Real.log y)
  calc
    |routeETerminalPhaseDerivative t y| =
        2 * |Real.sin (t * Real.log y)| * |t| / y := by
      rw [routeETerminalPhaseDerivative, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [abs_mul, abs_neg, abs_mul, abs_inv, abs_of_pos hy]
      rw [div_eq_mul_inv]
      ring
    _ ≤ 2 * |t| / y := by
      have hsnonneg : 0 ≤ |Real.sin (t * Real.log y)| := abs_nonneg _
      have hty : 0 ≤ |t| / y := by positivity
      calc
        2 * |Real.sin (t * Real.log y)| * |t| / y =
            2 * |Real.sin (t * Real.log y)| * (|t| / y) := by ring
        _ ≤ 2 * 1 * (|t| / y) := by gcongr
        _ = 2 * |t| / y := by ring

theorem abs_routeETerminalAbelWeight_le {r t y : ℝ} (hy : 1 < y) :
    |routeETerminalAbelWeight r t y| ≤ 4 * y ^ (-r) / Real.log y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hp : 0 ≤ y ^ (-r) := Real.rpow_nonneg hy0.le _
  have hphase0 := routeETerminalPhaseEnergy_nonneg t y
  have hphase4 := routeETerminalPhaseEnergy_le_four t y
  rw [routeETerminalAbelWeight, abs_div, abs_mul, abs_of_nonneg hp,
    abs_of_nonneg hphase0, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hphase4 hp) hlog.le

/-- Pointwise derivative majorant used by terminal PNT transport. -/
def routeETerminalDerivativeMajorant (r t y : ℝ) : ℝ :=
  ((4 * |r| * y ^ (-r - 1) + 2 * |t| * y ^ (-r) / y) * Real.log y
      + 4 * y ^ (-r) / y) / Real.log y ^ 2

theorem routeETerminalDerivativeMajorant_nonneg {r t y : ℝ} (hy : 1 < y) :
    0 ≤ routeETerminalDerivativeMajorant r t y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  unfold routeETerminalDerivativeMajorant
  positivity

theorem abs_routeETerminalAbelDerivative_le {r t y : ℝ} (hy : 1 < y) :
    |routeETerminalAbelDerivative r t y| ≤
      routeETerminalDerivativeMajorant r t y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hp : 0 ≤ y ^ (-r) := Real.rpow_nonneg hy0.le _
  have hp' : 0 ≤ y ^ (-r - 1) := Real.rpow_nonneg hy0.le _
  have hphase0 := routeETerminalPhaseEnergy_nonneg t y
  have hphase4 := routeETerminalPhaseEnergy_le_four t y
  have hphaseDeriv := abs_routeETerminalPhaseDerivative_le (t := t) hy0
  let A : ℝ := (-r) * y ^ (-r - 1) * routeETerminalPhaseEnergy t y
    + y ^ (-r) * routeETerminalPhaseDerivative t y
  have hA : |A| ≤ 4 * |r| * y ^ (-r - 1) + 2 * |t| * y ^ (-r) / y := by
    have htri := abs_add_le
      ((-r) * y ^ (-r - 1) * routeETerminalPhaseEnergy t y)
      (y ^ (-r) * routeETerminalPhaseDerivative t y)
    have hfirst : |(-r) * y ^ (-r - 1) * routeETerminalPhaseEnergy t y| ≤
        4 * |r| * y ^ (-r - 1) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hp', abs_of_nonneg hphase0]
      nlinarith [mul_le_mul_of_nonneg_left hphase4 (mul_nonneg (abs_nonneg r) hp')]
    have hsecond : |y ^ (-r) * routeETerminalPhaseDerivative t y| ≤
        2 * |t| * y ^ (-r) / y := by
      rw [abs_mul, abs_of_nonneg hp]
      have hm := mul_le_mul_of_nonneg_left hphaseDeriv hp
      calc
        y ^ (-r) * |routeETerminalPhaseDerivative t y|
            ≤ y ^ (-r) * (2 * |t| / y) := hm
        _ = 2 * |t| * y ^ (-r) / y := by ring
    dsimp [A]
    linarith
  have hboundary :
      |y ^ (-r) * routeETerminalPhaseEnergy t y * y⁻¹| ≤ 4 * y ^ (-r) / y := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hphase0,
      abs_inv, abs_of_pos hy0]
    have hyi : 0 ≤ y⁻¹ := inv_nonneg.mpr hy0.le
    have := mul_le_mul_of_nonneg_right hphase4 (mul_nonneg hp hyi)
    rw [div_eq_mul_inv]
    nlinarith
  have hnum :
      |A * Real.log y - y ^ (-r) * routeETerminalPhaseEnergy t y * y⁻¹| ≤
        (4 * |r| * y ^ (-r - 1) + 2 * |t| * y ^ (-r) / y) * Real.log y
          + 4 * y ^ (-r) / y := by
    have htri := abs_sub (A * Real.log y)
      (y ^ (-r) * routeETerminalPhaseEnergy t y * y⁻¹)
    rw [abs_mul, abs_of_pos hlog] at htri
    have hm := mul_le_mul_of_nonneg_right hA hlog.le
    linarith
  rw [routeETerminalAbelDerivative, routeETerminalDerivativeMajorant, abs_div,
    abs_of_pos (sq_pos_of_pos hlog)]
  change |A * Real.log y - y ^ (-r) * routeETerminalPhaseEnergy t y * y⁻¹| /
      Real.log y ^ 2 ≤ _
  exact div_le_div_of_nonneg_right hnum (sq_nonneg (Real.log y))

theorem hasDerivAt_routeETerminalAbelWeight {r t y : ℝ} (hy : 0 < y)
    (hy1 : y ≠ 1) :
    HasDerivAt (routeETerminalAbelWeight r t)
      (routeETerminalAbelDerivative r t y) y := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hlog0 : Real.log y ≠ 0 := (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
  have hp : HasDerivAt (fun z : ℝ => z ^ (-r))
      ((-r) * y ^ (-r - 1)) y := by
    simpa using Real.hasDerivAt_rpow_const (x := y) (p := -r) (Or.inl hy0)
  have hphase : HasDerivAt (routeETerminalPhaseEnergy t)
      (routeETerminalPhaseDerivative t y) y := by
    have harg : HasDerivAt (fun z : ℝ => t * Real.log z) (t * y⁻¹) y := by
      simpa using (Real.hasDerivAt_log hy0).const_mul t
    exact (harg.cos.const_mul 2).const_add 2
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0
  unfold routeETerminalAbelWeight routeETerminalAbelDerivative
  exact (hp.mul hphase).div hlog hlog0

theorem deriv_routeETerminalAbelWeight {r t y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    deriv (routeETerminalAbelWeight r t) y = routeETerminalAbelDerivative r t y :=
  (hasDerivAt_routeETerminalAbelWeight hy hy1).deriv

theorem continuousAt_routeETerminalAbelDerivative {r t y : ℝ} (hy : 0 < y)
    (hy1 : y ≠ 1) :
    ContinuousAt (routeETerminalAbelDerivative r t) y := by
  unfold routeETerminalAbelDerivative routeETerminalPhaseEnergy
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hlog0 : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hp : ContinuousAt (fun z : ℝ => z ^ (-r)) y :=
    Real.continuousAt_rpow_const y (-r) (Or.inl hy0)
  have hp' : ContinuousAt (fun z : ℝ => z ^ (-r - 1)) y :=
    Real.continuousAt_rpow_const y (-r - 1) (Or.inl hy0)
  have hlog : ContinuousAt Real.log y := Real.continuousAt_log hy0
  have hcos : ContinuousAt (fun z : ℝ => Real.cos (t * Real.log z)) y :=
    Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hlog)
  have hsin : ContinuousAt (fun z : ℝ => Real.sin (t * Real.log z)) y :=
    Real.continuous_sin.continuousAt.comp (continuousAt_const.mul hlog)
  have hinv : ContinuousAt (fun z : ℝ => z⁻¹) y := continuousAt_inv₀ hy0
  have hphase : ContinuousAt
      (fun z : ℝ => 2 + 2 * Real.cos (t * Real.log z)) y :=
    continuousAt_const.add (continuousAt_const.mul hcos)
  have hphaseDeriv : ContinuousAt
      (routeETerminalPhaseDerivative t) y := by
    unfold routeETerminalPhaseDerivative
    exact continuousAt_const.mul (hsin.neg.mul (continuousAt_const.mul hinv))
  have hnum : ContinuousAt
      (fun z : ℝ =>
        ((-r) * z ^ (-r - 1) * (2 + 2 * Real.cos (t * Real.log z))
          + z ^ (-r) * routeETerminalPhaseDerivative t z) * Real.log z
        - z ^ (-r) * (2 + 2 * Real.cos (t * Real.log z)) * z⁻¹) y :=
    (((continuousAt_const.mul hp').mul hphase).add
      (hp.mul hphaseDeriv)).mul hlog |>.sub ((hp.mul hphase).mul hinv)
  exact hnum.div (hlog.pow 2) (pow_ne_zero 2 hlog0)

theorem continuousOn_routeETerminalAbelDerivative {r t u v : ℝ}
    (hu : 1 < u) :
    ContinuousOn (routeETerminalAbelDerivative r t) (Icc u v) := by
  intro y hy
  exact (continuousAt_routeETerminalAbelDerivative
    (lt_trans zero_lt_one (hu.trans_le hy.1)) (ne_of_gt (hu.trans_le hy.1))).continuousWithinAt

theorem integrableOn_deriv_routeETerminalAbelWeight {r t u v : ℝ}
    (hu : 1 < u) :
    IntegrableOn (deriv (routeETerminalAbelWeight r t)) (Icc u v) := by
  have hcont := continuousOn_routeETerminalAbelDerivative (r := r) (t := t) (v := v) hu
  refine hcont.integrableOn_Icc.congr_fun (fun y hy => ?_) measurableSet_Icc
  exact (deriv_routeETerminalAbelWeight
    (lt_trans (by norm_num) (hu.trans_le hy.1)) (ne_of_gt (hu.trans_le hy.1))).symm

theorem routeETerminalAbelWeight_mul_primeLogWeight {r t : ℝ} {k : ℕ}
    (hk : 1 < k) :
    routeETerminalAbelWeight r t k * primeLogWeight k =
      if k.Prime then (k : ℝ) ^ (-r) * routeETerminalPhaseEnergy t k else 0 := by
  rw [routeETerminalAbelWeight, primeLogWeight]
  split_ifs with hp
  · have hlog : Real.log (k : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hk))
    field_simp
  · simp

/-- Exact Stieltjes/Abel formula for the literal moving terminal-prime frame. -/
theorem routeETerminalPrimeFrame_eq_thetaAbel {r X t : ℝ}
    (hX : 1 < X / Real.exp 1) :
    routeETerminalPrimeFrame r X t =
      routeETerminalAbelWeight r t X * Chebyshev.theta X
        - routeETerminalAbelWeight r t (X / Real.exp 1) *
            Chebyshev.theta (X / Real.exp 1)
        - ∫ y in Ioc (X / Real.exp 1) X,
            deriv (routeETerminalAbelWeight r t) y * Chebyshev.theta y := by
  have hle : X / Real.exp 1 ≤ X := by
    have hquot : 0 < X / Real.exp 1 := lt_trans zero_lt_one hX
    have hX0 : 0 < X := (div_pos_iff_of_pos_right (Real.exp_pos 1)).mp hquot
    have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff.mpr (by norm_num))
    exact div_le_self hX0.le he
  have hdiff : ∀ y ∈ Icc (X / Real.exp 1) X,
      DifferentiableAt ℝ (routeETerminalAbelWeight r t) y := by
    intro y hy
    exact (hasDerivAt_routeETerminalAbelWeight
      (lt_trans (by norm_num) (hX.trans_le hy.1)) (ne_of_gt (hX.trans_le hy.1))).differentiableAt
  have hint : IntegrableOn (deriv (routeETerminalAbelWeight r t))
      (Icc (X / Real.exp 1) X) :=
    integrableOn_deriv_routeETerminalAbelWeight hX
  have habel := sum_mul_eq_sub_sub_integral_mul (c := primeLogWeight)
    (f := routeETerminalAbelWeight r t) (a := X / Real.exp 1) (b := X)
    (le_trans (by norm_num) hX.le) hle hdiff hint
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [routeETerminalPrimeFrame, ← habel]
  exact Finset.sum_congr rfl fun k hk => by
    have hfloor : ⌊X / Real.exp 1⌋₊ < k := (Finset.mem_Ioc.mp hk).1
    have hsucc : ⌊X / Real.exp 1⌋₊ + 1 ≤ k := by omega
    have hlowk : X / Real.exp 1 < (k : ℝ) :=
      lt_of_lt_of_le (Nat.lt_floor_add_one (X / Real.exp 1)) (by exact_mod_cast hsucc)
    exact (routeETerminalAbelWeight_mul_primeLogWeight
      (by exact_mod_cast hX.trans hlowk)).symm

/-- Integration by parts reassembles the identity contribution into the continuous prime main
term.  This is exact on the same half-open terminal interval used by the finite prime frame. -/
theorem routeETerminalPrimeMain_eq_boundary_sub_deriv {r X t : ℝ}
    (hX : 1 < X / Real.exp 1) :
    routeETerminalPrimeMain r X t =
      routeETerminalAbelWeight r t X * X
        - routeETerminalAbelWeight r t (X / Real.exp 1) * (X / Real.exp 1)
        - ∫ y in Ioc (X / Real.exp 1) X,
            deriv (routeETerminalAbelWeight r t) y * y := by
  let u : ℝ := X / Real.exp 1
  have hX0 : 0 < X := by
    have hu0 : 0 < u := lt_trans zero_lt_one hX
    exact (div_pos_iff_of_pos_right (Real.exp_pos 1)).mp hu0
  have hle : u ≤ X := by
    exact div_le_self hX0.le (Real.one_le_exp_iff.mpr (by norm_num))
  have hweightDeriv : ∀ y ∈ uIcc u X,
      HasDerivAt (routeETerminalAbelWeight r t)
        (deriv (routeETerminalAbelWeight r t) y) y := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    have hyu : u ≤ y := hy.1
    have hyd := hasDerivAt_routeETerminalAbelWeight (r := r) (t := t)
      (lt_trans zero_lt_one (hX.trans_le hyu)) (ne_of_gt (hX.trans_le hyu))
    simpa only [hyd.deriv] using hyd
  have hweightInt : IntervalIntegrable (routeETerminalAbelWeight r t) volume u X := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr ?_
    have hcont : ContinuousOn (routeETerminalAbelWeight r t) (Icc u X) := by
      intro y hy
      exact (hweightDeriv y (by simpa [uIcc_of_le hle] using hy)).continuousAt.continuousWithinAt
    exact hcont.integrableOn_Icc
  have hderivInt : IntervalIntegrable (deriv (routeETerminalAbelWeight r t)) volume u X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact integrableOn_deriv_routeETerminalAbelWeight hX
  have hidInt : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume u X :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ : ℝ => 1)
    (v := routeETerminalAbelWeight r t)
    (v' := deriv (routeETerminalAbelWeight r t))
    (fun _ _ => hasDerivAt_id _) hweightDeriv hidInt hderivInt
  have hmain : routeETerminalPrimeMain r X t =
      ∫ y in u..X, routeETerminalAbelWeight r t y := by
    rw [routeETerminalPrimeMain]
    rw [← intervalIntegral.integral_of_le hle]
    rfl
  rw [hmain]
  have hprod : (∫ y in u..X,
      y * deriv (routeETerminalAbelWeight r t) y) =
      X * routeETerminalAbelWeight r t X
        - u * routeETerminalAbelWeight r t u
        - ∫ y in u..X, routeETerminalAbelWeight r t y := by
    simpa only [one_mul] using hibp
  have hderivSet : (∫ y in Ioc u X,
      deriv (routeETerminalAbelWeight r t) y * y) =
      ∫ y in u..X, y * deriv (routeETerminalAbelWeight r t) y := by
    rw [← intervalIntegral.integral_of_le hle]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hderivSet, hprod]
  dsimp [u]
  ring

/-- **Exact terminal PNT-defect identity.**  Literal prime frame minus continuous main term is
precisely two boundary Chebyshev errors and one derivative-weighted Chebyshev-error integral. -/
theorem routeETerminalPrimeFrame_sub_main_eq_thetaError {r X t : ℝ}
    (hX : 1 < X / Real.exp 1) :
    routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t =
      routeETerminalAbelWeight r t X * (Chebyshev.theta X - X)
        - routeETerminalAbelWeight r t (X / Real.exp 1) *
            (Chebyshev.theta (X / Real.exp 1) - X / Real.exp 1)
        - ∫ y in Ioc (X / Real.exp 1) X,
            deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y) := by
  let u : ℝ := X / Real.exp 1
  have hX0 : 0 < X := by
    have hu0 : 0 < u := lt_trans zero_lt_one hX
    exact (div_pos_iff_of_pos_right (Real.exp_pos 1)).mp hu0
  have hle : u ≤ X := div_le_self hX0.le (Real.one_le_exp_iff.mpr (by norm_num))
  have hderivCont : ContinuousOn (deriv (routeETerminalAbelWeight r t)) (Icc u X) := by
    refine (continuousOn_routeETerminalAbelDerivative (r := r) (t := t) (v := X) hX).congr
      (fun y hy => ?_)
    exact (deriv_routeETerminalAbelWeight
      (lt_trans zero_lt_one (hX.trans_le hy.1)) (ne_of_gt (hX.trans_le hy.1)))
  have hthetaError : IntegrableOn (fun y : ℝ => Chebyshev.theta y - y) (Icc u X) := by
    exact (MonotoneOn.integrableOn_isCompact isCompact_Icc
      (Chebyshev.theta_mono.monotoneOn _)).sub
        (continuous_id.continuousOn.integrableOn_Icc)
  have hderivInt : IntegrableOn (deriv (routeETerminalAbelWeight r t)) (Icc u X) :=
    integrableOn_deriv_routeETerminalAbelWeight hX
  have hid : IntegrableOn (fun y : ℝ => y) (Icc u X) :=
    continuous_id.continuousOn.integrableOn_Icc
  have htheta : IntegrableOn Chebyshev.theta (Icc u X) :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc (Chebyshev.theta_mono.monotoneOn _)
  have hmulTheta : IntegrableOn
      (fun y : ℝ => deriv (routeETerminalAbelWeight r t) y * Chebyshev.theta y) (Icc u X) :=
    htheta.mul_continuousOn hderivCont isCompact_Icc |>.congr_fun
      (fun y _ => by ring) measurableSet_Icc
  have hmulId : IntegrableOn
      (fun y : ℝ => deriv (routeETerminalAbelWeight r t) y * y) (Icc u X) :=
    hid.mul_continuousOn hderivCont isCompact_Icc |>.congr_fun
      (fun y _ => by ring) measurableSet_Icc
  have hmulError : IntegrableOn
      (fun y : ℝ => deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y))
      (Icc u X) :=
    hthetaError.mul_continuousOn hderivCont isCompact_Icc |>.congr_fun
      (fun y _ => by ring) measurableSet_Icc
  have hsplit : (∫ y in Ioc u X,
      deriv (routeETerminalAbelWeight r t) y * Chebyshev.theta y) =
      (∫ y in Ioc u X, deriv (routeETerminalAbelWeight r t) y * y)
        + ∫ y in Ioc u X,
            deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y) := by
    rw [← MeasureTheory.integral_add
      (hmulId.mono_set Ioc_subset_Icc_self)
      (hmulError.mono_set Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [routeETerminalPrimeFrame_eq_thetaAbel hX,
    routeETerminalPrimeMain_eq_boundary_sub_deriv hX]
  change _ - _ = _
  rw [show (∫ y in Ioc (X / Real.exp 1) X,
      deriv (routeETerminalAbelWeight r t) y * Chebyshev.theta y) =
      (∫ y in Ioc (X / Real.exp 1) X,
        deriv (routeETerminalAbelWeight r t) y * y)
      + ∫ y in Ioc (X / Real.exp 1) X,
        deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y) by
        simpa [u] using hsplit]
  ring

/-- Finite-volume terminal transport estimate.  Uniform bounds for Abel weight, its derivative,
and Chebyshev error are retained without discarding either terminal endpoint. -/
theorem abs_routeETerminalPrimeFrame_sub_main_le_of_uniform
    {r X t W D E : ℝ} (hX : 1 < X / Real.exp 1)
    (hW : ∀ y ∈ Icc (X / Real.exp 1) X,
      |routeETerminalAbelWeight r t y| ≤ W)
    (hD : ∀ y ∈ Icc (X / Real.exp 1) X,
      |deriv (routeETerminalAbelWeight r t) y| ≤ D)
    (hE : ∀ y ∈ Icc (X / Real.exp 1) X,
      |Chebyshev.theta y - y| ≤ E) :
    |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤
      2 * W * E + (X - X / Real.exp 1) * D * E := by
  let u : ℝ := X / Real.exp 1
  have hX0 : 0 < X := by
    have hu0 : 0 < u := lt_trans zero_lt_one hX
    exact (div_pos_iff_of_pos_right (Real.exp_pos 1)).mp hu0
  have hle : u ≤ X := div_le_self hX0.le (Real.one_le_exp_iff.mpr (by norm_num))
  have hu_mem : u ∈ Icc u X := ⟨le_rfl, hle⟩
  have hX_mem : X ∈ Icc u X := ⟨hle, le_rfl⟩
  have hWE0 : 0 ≤ W * E := by
    have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW u (by simpa [u] using hu_mem))
    have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hE u (by simpa [u] using hu_mem))
    positivity
  have hDE0 : 0 ≤ D * E := by
    have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD u (by simpa [u] using hu_mem))
    have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hE u (by simpa [u] using hu_mem))
    positivity
  have hint :
      |∫ y in Ioc u X,
          deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y)| ≤
        D * E * (X - u) := by
    rw [← intervalIntegral.integral_of_le hle, ← Real.norm_eq_abs,
      show X - u = |X - u| by rw [abs_of_nonneg (sub_nonneg.mpr hle)]]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hle] at hy
    have hy' : y ∈ Icc u X := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hD y (by simpa [u] using hy'))
      (hE y (by simpa [u] using hy')) (abs_nonneg _) (le_trans (abs_nonneg _) (hD y (by simpa [u] using hy')))
  rw [routeETerminalPrimeFrame_sub_main_eq_thetaError hX]
  have htermX :
      |routeETerminalAbelWeight r t X * (Chebyshev.theta X - X)| ≤ W * E := by
    rw [abs_mul]
    exact mul_le_mul (hW X (by simpa [u] using hX_mem))
      (hE X (by simpa [u] using hX_mem)) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hW X (by simpa [u] using hX_mem)))
  have htermu :
      |routeETerminalAbelWeight r t u * (Chebyshev.theta u - u)| ≤ W * E := by
    rw [abs_mul]
    exact mul_le_mul (hW u (by simpa [u] using hu_mem))
      (hE u (by simpa [u] using hu_mem)) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hW u (by simpa [u] using hu_mem)))
  have htri1 := abs_sub
    (routeETerminalAbelWeight r t X * (Chebyshev.theta X - X)
      - routeETerminalAbelWeight r t u * (Chebyshev.theta u - u))
    (∫ y in Ioc u X,
      deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y))
  have htri2 := abs_sub
    (routeETerminalAbelWeight r t X * (Chebyshev.theta X - X))
    (routeETerminalAbelWeight r t u * (Chebyshev.theta u - u))
  change
    |routeETerminalAbelWeight r t X * (Chebyshev.theta X - X)
      - routeETerminalAbelWeight r t u * (Chebyshev.theta u - u)
      - ∫ y in Ioc u X,
          deriv (routeETerminalAbelWeight r t) y * (Chebyshev.theta y - y)| ≤ _
  dsimp [u] at hint ⊢
  nlinarith

/-! ## Uniform terminal-band geometry -/

theorem routeETerminal_band_one_lt {X y : ℝ}
    (hL : 4 ≤ Real.log X) (hy : y ∈ Icc (X / Real.exp 1) X) :
    1 < X / Real.exp 1 ∧ 1 < y := by
  have hdivle : X / Real.exp 1 ≤ X := hy.1.trans hy.2
  have hXnonneg : 0 ≤ X := by
    by_contra h
    have hXneg : X < 0 := lt_of_not_ge h
    have hmul := (div_le_iff₀ (Real.exp_pos 1)).mp hdivle
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith
  have hX0 : 0 < X := hXnonneg.lt_of_ne (by
    intro h
    rw [← h, Real.log_zero] at hL
    norm_num at hL)
  have hlogXpos : 0 < Real.log X := by linarith
  have hX1 : 1 < X := (Real.log_pos_iff hXnonneg).mp hlogXpos
  have hlogu : Real.log (X / Real.exp 1) = Real.log X - 1 := by
    rw [Real.log_div hX0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hlogupos : 0 < Real.log (X / Real.exp 1) := by rw [hlogu]; linarith
  have hu1 : 1 < X / Real.exp 1 :=
    (Real.log_pos_iff (div_nonneg hX0.le (Real.exp_pos 1).le)).mp hlogupos
  exact ⟨hu1, hu1.trans_le hy.1⟩

theorem routeETerminal_band_log_lower {X y : ℝ}
    (hL : 4 ≤ Real.log X) (hy : y ∈ Icc (X / Real.exp 1) X) :
    Real.log X / 2 ≤ Real.log y := by
  have hones := routeETerminal_band_one_lt hL hy
  have hu0 : 0 < X / Real.exp 1 := lt_trans zero_lt_one hones.1
  have hX0 : 0 < X := lt_of_lt_of_le hu0 (hy.1.trans hy.2)
  have hlogu : Real.log (X / Real.exp 1) = Real.log X - 1 := by
    rw [Real.log_div hX0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hmono : Real.log (X / Real.exp 1) ≤ Real.log y :=
    Real.log_le_log hu0 hy.1
  rw [hlogu] at hmono
  linarith

theorem routeETerminal_band_rpow_le {r X y : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 4 ≤ Real.log X)
    (hy : y ∈ Icc (X / Real.exp 1) X) :
    y ^ (-r) ≤ Real.exp 1 * X ^ (-r) := by
  have hones := routeETerminal_band_one_lt hL hy
  have hu0 : 0 < X / Real.exp 1 := lt_trans zero_lt_one hones.1
  have hX0 : 0 < X := by
    have := mul_pos hu0 (Real.exp_pos 1)
    rwa [div_mul_cancel₀ X (Real.exp_ne_zero 1)] at this
  have hanti : y ^ (-r) ≤ (X / Real.exp 1) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hu0 hy.1 (neg_nonpos.mpr hr0)
  have hformula : (X / Real.exp 1) ^ (-r) = X ^ (-r) * Real.exp r := by
    rw [Real.div_rpow hX0.le (Real.exp_pos 1).le, Real.exp_one_rpow, Real.exp_neg]
    field_simp
  have hexp : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr hr1
  have hpow : 0 ≤ X ^ (-r) := Real.rpow_nonneg hX0.le _
  rw [hformula] at hanti
  exact hanti.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hexp hpow)

theorem routeETerminal_band_rpow_sub_one_le {r X y : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 4 ≤ Real.log X)
    (hy : y ∈ Icc (X / Real.exp 1) X) :
    y ^ (-r - 1) ≤ Real.exp 2 * X ^ (-r) / X := by
  have hones := routeETerminal_band_one_lt hL hy
  have hu0 : 0 < X / Real.exp 1 := lt_trans zero_lt_one hones.1
  have hX0 : 0 < X := by
    have := mul_pos hu0 (Real.exp_pos 1)
    rwa [div_mul_cancel₀ X (Real.exp_ne_zero 1)] at this
  have hexponent : -r - 1 ≤ 0 := by linarith
  have hanti : y ^ (-r - 1) ≤ (X / Real.exp 1) ^ (-r - 1) :=
    Real.rpow_le_rpow_of_nonpos hu0 hy.1 hexponent
  have hformula : (X / Real.exp 1) ^ (-r - 1) =
      X ^ (-r) / X * Real.exp (r + 1) := by
    rw [Real.div_rpow hX0.le (Real.exp_pos 1).le, Real.exp_one_rpow]
    have hXpow : X ^ (-r - 1) = X ^ (-r) * X ^ (-1 : ℝ) := by
      rw [show -r - 1 = -r + (-1 : ℝ) by ring, Real.rpow_add hX0]
    rw [hXpow, Real.rpow_neg_one, show -r - 1 = -(r + 1) by ring, Real.exp_neg]
    field_simp
  have hexp : Real.exp (r + 1) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  have hpow : 0 ≤ X ^ (-r) / X := by positivity
  rw [hformula] at hanti
  calc
    y ^ (-r - 1) ≤ X ^ (-r) / X * Real.exp (r + 1) := hanti
    _ ≤ X ^ (-r) / X * Real.exp 2 := mul_le_mul_of_nonneg_left hexp hpow
    _ = Real.exp 2 * X ^ (-r) / X := by ring

theorem abs_routeETerminalAbelWeight_band_le {r X t y : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 4 ≤ Real.log X)
    (hy : y ∈ Icc (X / Real.exp 1) X) :
    |routeETerminalAbelWeight r t y| ≤
      8 * Real.exp 1 * X ^ (-r) / Real.log X := by
  have hones := routeETerminal_band_one_lt hL hy
  have hpoint := abs_routeETerminalAbelWeight_le (r := r) (t := t) hones.2
  have hpow := routeETerminal_band_rpow_le hr0 hr1 hL hy
  have hlog := routeETerminal_band_log_lower hL hy
  have hL0 : 0 < Real.log X := by linarith
  have hlog0 : 0 < Real.log y := Real.log_pos hones.2
  have hX0 : 0 < X := lt_of_lt_of_le
    (lt_trans zero_lt_one hones.1) (hy.1.trans hy.2)
  have hp0 : 0 ≤ y ^ (-r) := Real.rpow_nonneg (lt_trans zero_lt_one hones.2).le _
  have hP0 : 0 ≤ Real.exp 1 * X ^ (-r) := by positivity
  calc
    |routeETerminalAbelWeight r t y| ≤ 4 * y ^ (-r) / Real.log y := hpoint
    _ ≤ (4 * (Real.exp 1 * X ^ (-r))) / (Real.log X / 2) := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      · linarith
      · exact hlog
    _ = 8 * Real.exp 1 * X ^ (-r) / Real.log X := by field_simp; ring

theorem rpow_div_eq_rpow_sub_one {r y : ℝ} (hy : 0 < y) :
    y ^ (-r) / y = y ^ (-r - 1) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one y,
    ← Real.rpow_add hy]
  congr 1

theorem abs_deriv_routeETerminalAbelWeight_band_le {r X t y : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 4 ≤ Real.log X)
    (hy : y ∈ Icc (X / Real.exp 1) X) :
    |deriv (routeETerminalAbelWeight r t) y| ≤
      28 * Real.exp 2 * (1 + |t|) * X ^ (-r) / (X * Real.log X) := by
  have hones := routeETerminal_band_one_lt hL hy
  have hy0 : 0 < y := lt_trans zero_lt_one hones.2
  have hX0 : 0 < X := lt_of_lt_of_le
    (lt_trans zero_lt_one hones.1) (hy.1.trans hy.2)
  have hL0 : 0 < Real.log X := by linarith
  have hlog0 : 0 < Real.log y := Real.log_pos hones.2
  have hlogLower := routeETerminal_band_log_lower hL hy
  have hlogUpper : Real.log y ≤ Real.log X := Real.log_le_log hy0 hy.2
  have hpow := routeETerminal_band_rpow_sub_one_le hr0 hr1 hL hy
  have hderivEq := deriv_routeETerminalAbelWeight (r := r) (t := t) hy0
    (ne_of_gt hones.2)
  have hpoint := abs_routeETerminalAbelDerivative_le (r := r) (t := t) hones.2
  rw [hderivEq]
  refine hpoint.trans ?_
  let P : ℝ := y ^ (-r - 1)
  let Q : ℝ := Real.exp 2 * X ^ (-r) / X
  let T : ℝ := |t|
  let L : ℝ := Real.log X
  let ell : ℝ := Real.log y
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hL4 : 4 ≤ L := by simpa [L] using hL
  have hLpos : 0 < L := by linarith
  have hellpos : 0 < ell := by simpa [ell] using hlog0
  have hellLower : L / 2 ≤ ell := by simpa [L, ell] using hlogLower
  have hellUpper : ell ≤ L := by simpa [L, ell] using hlogUpper
  have hPQ : P ≤ Q := by simpa [P, Q] using hpow
  have hdiv : y ^ (-r) / y = P := by simpa [P] using rpow_div_eq_rpow_sub_one (r := r) hy0
  have hdiv' : y ^ (-r) / y = y ^ (-r - 1) :=
    rpow_div_eq_rpow_sub_one (r := r) hy0
  have hrabs : |r| = r := abs_of_nonneg hr0
  have hrewrite : routeETerminalDerivativeMajorant r t y =
      ((4 * r * P + 2 * T * P) * ell + 4 * P) / ell ^ 2 := by
    rw [routeETerminalDerivativeMajorant, hrabs]
    simp only [T, ell, P]
    have hterm2 : 2 * |t| * y ^ (-r) / y = 2 * |t| * y ^ (-r - 1) := by
      calc
        2 * |t| * y ^ (-r) / y = 2 * |t| * (y ^ (-r) / y) := by ring
        _ = 2 * |t| * y ^ (-r - 1) := by rw [hdiv']
    have hterm4 : 4 * y ^ (-r) / y = 4 * y ^ (-r - 1) := by
      calc
        4 * y ^ (-r) / y = 4 * (y ^ (-r) / y) := by ring
        _ = 4 * y ^ (-r - 1) := by rw [hdiv']
    rw [hterm2, hterm4]
  rw [hrewrite]
  have hA : 4 * r * P + 2 * T * P ≤ (4 + 2 * T) * Q := by
    have hrP : r * P ≤ 1 * Q :=
      (mul_le_mul hr1 hPQ hP0 (by norm_num : (0 : ℝ) ≤ 1))
    have hTP : T * P ≤ T * Q := mul_le_mul_of_nonneg_left hPQ hT0
    nlinarith
  have hA0 : 0 ≤ 4 * r * P + 2 * T * P := by positivity
  have hcoef0 : 0 ≤ 4 + 2 * T := by positivity
  have hmulLog : (4 * r * P + 2 * T * P) * ell ≤ (4 + 2 * T) * Q * L :=
    (mul_le_mul hA hellUpper hellpos.le (mul_nonneg hcoef0 hQ0))
  have hfour : 4 * P ≤ Q * L := by
    have h4Q : 4 * P ≤ 4 * Q := mul_le_mul_of_nonneg_left hPQ (by norm_num)
    have hQL : 4 * Q ≤ Q * L := by nlinarith [mul_le_mul_of_nonneg_left hL4 hQ0]
    exact h4Q.trans hQL
  have hnum : (4 * r * P + 2 * T * P) * ell + 4 * P ≤
      (5 + 2 * T) * Q * L := by
    nlinarith
  have hden : L ^ 2 / 4 ≤ ell ^ 2 := by
    nlinarith [sq_nonneg (ell - L / 2)]
  have hnum0 : 0 ≤ (4 * r * P + 2 * T * P) * ell + 4 * P := by positivity
  calc
    ((4 * r * P + 2 * T * P) * ell + 4 * P) / ell ^ 2
        ≤ ((5 + 2 * T) * Q * L) / (L ^ 2 / 4) := by
      apply div_le_div₀
      · positivity
      · exact hnum
      · positivity
      · exact hden
    _ = 4 * (5 + 2 * T) * Q / L := by field_simp
    _ ≤ 28 * (1 + T) * Q / L := by
      apply div_le_div_of_nonneg_right _ hLpos.le
      have hcoef : 4 * (5 + 2 * T) ≤ 28 * (1 + T) := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoef hQ0
    _ = 28 * Real.exp 2 * (1 + |t|) * X ^ (-r) / (X * Real.log X) := by
      dsimp [Q, T, L]
      field_simp

/-! ## Unconditional Chebyshev transport -/

/-- The corpus PNT error is uniform on the complete moving terminal band after losing only half
of its square-root-log exponent. -/
theorem exists_chebyshevTheta_terminalBand_exp_bound :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in atTop, ∀ y ∈ Icc (X / Real.exp 1) X,
      |Chebyshev.theta y - y| ≤
        K * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  obtain ⟨c, hc, htheta⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at htheta
  obtain ⟨C, hC⟩ := htheta
  obtain ⟨Y, hY⟩ := (eventually_atTop.1 hC)
  refine ⟨c, hc, |C| + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1 * max Y 2),
    Real.tendsto_log_atTop.eventually_ge_atTop 4] with X hXY hL
  intro y hy
  have hones := routeETerminal_band_one_lt hL hy
  have hy0 : 0 < y := lt_trans zero_lt_one hones.2
  have hX0 : 0 < X := lt_of_lt_of_le
    (lt_trans zero_lt_one hones.1) (hy.1.trans hy.2)
  have hmax0 : 0 ≤ max Y 2 := le_trans (by norm_num) (le_max_right Y 2)
  have huY : Y ≤ X / Real.exp 1 := by
    have hmul : Real.exp 1 * max Y 2 ≤ X := hXY
    have hdiv : max Y 2 ≤ X / Real.exp 1 :=
      (le_div_iff₀ (Real.exp_pos 1)).mpr (by simpa [mul_comm] using hmul)
    exact (le_max_left Y 2).trans hdiv
  have hraw := hY y (huY.trans hy.1)
  have hshape : ‖y * Real.exp (-c * Real.sqrt (Real.log y))‖ =
      y * Real.exp (-c * Real.sqrt (Real.log y)) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hy0 (Real.exp_pos _))]
  rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hshape] at hraw
  have hrawAbs : |Chebyshev.theta y - y| ≤
      |C| * (y * Real.exp (-c * Real.sqrt (Real.log y))) := by
    have hshape0 : 0 ≤ y * Real.exp (-c * Real.sqrt (Real.log y)) := by positivity
    exact hraw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hshape0)
  have hlogLower := routeETerminal_band_log_lower hL hy
  have hlogX0 : 0 ≤ Real.log X := by linarith
  have hlogy0 : 0 ≤ Real.log y := (Real.log_pos hones.2).le
  have hsX0 : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  have hsy0 : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hsXsq : Real.sqrt (Real.log X) ^ 2 = Real.log X :=
    Real.sq_sqrt hlogX0
  have hsysq : Real.sqrt (Real.log y) ^ 2 = Real.log y :=
    Real.sq_sqrt hlogy0
  have hsqrt : Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log y) := by
    nlinarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log y)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hyX : y ≤ X := hy.2
  have hphase0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y)) := (Real.exp_pos _).le
  have hphaseX0 : 0 ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := (Real.exp_pos _).le
  have hYX : y * Real.exp (-c * Real.sqrt (Real.log y)) ≤
      X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) :=
    (mul_le_mul hyX hexp hphase0 hX0.le)
  have hCabs0 : 0 ≤ |C| := abs_nonneg C
  have hmain := mul_le_mul_of_nonneg_left hYX hCabs0
  have htail :
      |C| * (X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) ≤
        (|C| + 1) * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    have hXE : 0 ≤ X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by positivity
    nlinarith
  calc
    |Chebyshev.theta y - y| ≤
        |C| * (y * Real.exp (-c * Real.sqrt (Real.log y))) := hrawAbs
    _ ≤ |C| * (X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := hmain
    _ ≤ (|C| + 1) * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := htail

/-- **Unconditional moving-frequency terminal-prime transport.**  Uniformly for all
`0 < r ≤ 1` and all real frequencies, the literal prime frame differs from its continuous
terminal integral by the square-root-log PNT error times exactly one derivative factor
`1 + |t|`. -/
theorem exists_routeETerminalPrimeFrame_sub_main_exp_bound :
    ∃ c > 0, ∃ A > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤
          A * (1 + |t|) * X ^ (1 - r) / Real.log X *
            Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨c, hc, K, hK, htheta⟩ := exists_chebyshevTheta_terminalBand_exp_bound
  let A : ℝ := (16 * Real.exp 1 + 28 * Real.exp 2) * K
  refine ⟨c / 2, by positivity, A, ?_, ?_⟩
  · dsimp [A]
    positivity
  filter_upwards [htheta, Real.tendsto_log_atTop.eventually_ge_atTop 4,
    eventually_ge_atTop (1 : ℝ)] with X hthetaX hL hX1
  intro r hr t
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ 1 := hr.2
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hL0 : 0 < Real.log X := by linarith
  have hlogu : Real.log (X / Real.exp 1) = Real.log X - 1 := by
    rw [Real.log_div hX0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hXband : 1 < X / Real.exp 1 := by
    apply (Real.log_pos_iff (div_nonneg hX0.le (Real.exp_pos 1).le)).mp
    rw [hlogu]
    linarith
  let W : ℝ := 8 * Real.exp 1 * X ^ (-r) / Real.log X
  let D : ℝ := 28 * Real.exp 2 * (1 + |t|) * X ^ (-r) / (X * Real.log X)
  let E : ℝ := K * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hfinite := abs_routeETerminalPrimeFrame_sub_main_le_of_uniform
    (r := r) (t := t) hXband
    (W := W) (D := D) (E := E)
    (fun y hy => by
      simpa [W] using abs_routeETerminalAbelWeight_band_le hr0 hr1 hL hy)
    (fun y hy => by
      simpa [D] using abs_deriv_routeETerminalAbelWeight_band_le hr0 hr1 hL hy)
    (fun y hy => by simpa [E] using hthetaX y hy)
  have hlen : X - X / Real.exp 1 ≤ X := by
    have hu0 : 0 ≤ X / Real.exp 1 := div_nonneg hX0.le (Real.exp_pos 1).le
    linarith
  have hlenTerm : (X - X / Real.exp 1) * D * E ≤ X * D * E := by
    have hDE0 : 0 ≤ D * E := mul_nonneg hD0 hE0
    nlinarith [mul_le_mul_of_nonneg_right hlen hDE0]
  have hXPow : X * X ^ (-r) = X ^ (1 - r) := by
    calc
      X * X ^ (-r) = X ^ (1 : ℝ) * X ^ (-r) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-r)) := (Real.rpow_add hX0 1 (-r)).symm
      _ = X ^ (1 - r) := by ring_nf
  let S : ℝ := Real.exp (-(c / 2) * Real.sqrt (Real.log X))
  have hS0 : 0 ≤ S := (Real.exp_pos _).le
  have hT0 : 0 ≤ |t| := abs_nonneg t
  have hbase0 : 0 ≤ X ^ (1 - r) / Real.log X * S := by positivity
  have hfirst : 2 * W * E =
      16 * Real.exp 1 * K * (X ^ (1 - r) / Real.log X * S) := by
    dsimp [W, E, S]
    field_simp
    nlinarith [hXPow]
  have hsecond : X * D * E =
      28 * Real.exp 2 * K * (1 + |t|) *
        (X ^ (1 - r) / Real.log X * S) := by
    dsimp [D, E, S]
    field_simp
    nlinarith [hXPow]
  have hfirstLe : 2 * W * E ≤
      16 * Real.exp 1 * K * (1 + |t|) *
        (X ^ (1 - r) / Real.log X * S) := by
    rw [hfirst]
    have hcoef0 : 0 ≤ 16 * Real.exp 1 * K := by positivity
    have hfac : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hfacbase : X ^ (1 - r) / Real.log X * S ≤
        (1 + |t|) * (X ^ (1 - r) / Real.log X * S) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hbase0
    calc
      16 * Real.exp 1 * K * (X ^ (1 - r) / Real.log X * S)
          ≤ 16 * Real.exp 1 * K *
            ((1 + |t|) * (X ^ (1 - r) / Real.log X * S)) :=
        mul_le_mul_of_nonneg_left hfacbase hcoef0
      _ = 16 * Real.exp 1 * K * (1 + |t|) *
          (X ^ (1 - r) / Real.log X * S) := by ring
  calc
    |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t|
        ≤ 2 * W * E + (X - X / Real.exp 1) * D * E := hfinite
    _ ≤ 2 * W * E + X * D * E := by linarith
    _ ≤ (16 * Real.exp 1 + 28 * Real.exp 2) * K * (1 + |t|) *
        (X ^ (1 - r) / Real.log X * S) := by
      rw [hsecond]
      nlinarith
    _ = A * (1 + |t|) * X ^ (1 - r) / Real.log X *
        Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      dsimp [A, S]
      ring

theorem tendsto_log_sq_mul_exp_neg_sqrt_log {d : ℝ} (hd : 0 < d) :
    Tendsto (fun X : ℝ => Real.log X ^ 2 *
      Real.exp (-d * Real.sqrt (Real.log X))) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hscale : Tendsto (fun X : ℝ => d * Real.sqrt (Real.log X)) atTop atTop :=
    hsqrt.const_mul_atTop hd
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hscale
  have hscaled := hbase.const_mul (d⁻¹ ^ 4)
  rw [mul_zero] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with X hlog
  have hs : Real.sqrt (Real.log X) ^ 2 = Real.log X := Real.sq_sqrt hlog
  have hd0 : d ≠ 0 := ne_of_gt hd
  dsimp
  rw [show -(d * Real.sqrt (Real.log X)) = -d * Real.sqrt (Real.log X) by ring]
  field_simp
  nlinarith [hs]

/-- On the absolute subexponential frequency window supplied by the PNT exponent, terminal-prime
transport error is negligible at the sharp minimax normalization `log(X)^3 / X^(1-r)`. -/
theorem exists_routeETerminalPrimeFrame_normalizedError_uniform_subexp :
    ∃ κ > 0, ∀ ε > 0, ∀ᶠ X : ℝ in atTop,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
        |t| ≤ Real.exp (κ * Real.sqrt (Real.log X)) →
        Real.log X ^ 3 / X ^ (1 - r) *
            |routeETerminalPrimeFrame r X t - routeETerminalPrimeMain r X t| ≤ ε := by
  obtain ⟨c, hc, A, hA, hbound⟩ := exists_routeETerminalPrimeFrame_sub_main_exp_bound
  let κ : ℝ := c / 2
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro ε hε
  have hdecay := tendsto_log_sq_mul_exp_neg_sqrt_log (d := c / 2) (by positivity)
  have hsmall : ∀ᶠ X : ℝ in atTop,
      2 * A * (Real.log X ^ 2 *
        Real.exp (-(c / 2) * Real.sqrt (Real.log X))) ≤ ε := by
    have htend := hdecay.const_mul (2 * A)
    rw [mul_zero] at htend
    exact ((tendsto_order.1 htend).2 ε hε).mono fun _ h => h.le
  filter_upwards [hbound, hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with X hBX hsmallX hL hX1
  intro r hr t ht
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hlog0 : 0 < Real.log X := by linarith
  have hpow0 : 0 < X ^ (1 - r) := Real.rpow_pos_of_pos hX0 _
  have hs0 : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  have hexpκ : 1 ≤ Real.exp (κ * Real.sqrt (Real.log X)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by dsimp [κ]; positivity) hs0)
  have htOne : 1 + |t| ≤ 2 * Real.exp (κ * Real.sqrt (Real.log X)) := by
    linarith
  have hraw := hBX r hr t
  have hscale0 : 0 ≤ Real.log X ^ 3 / X ^ (1 - r) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hraw hscale0
  have hcancel :
      Real.log X ^ 3 / X ^ (1 - r) *
        (A * (1 + |t|) * X ^ (1 - r) / Real.log X *
          Real.exp (-c * Real.sqrt (Real.log X))) =
      A * (1 + |t|) * Real.log X ^ 2 *
        Real.exp (-c * Real.sqrt (Real.log X)) := by
    field_simp
  rw [hcancel] at hscaled
  have hfreq :
      A * (1 + |t|) * Real.log X ^ 2 *
          Real.exp (-c * Real.sqrt (Real.log X)) ≤
        2 * A * (Real.log X ^ 2 *
          Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
    have hA0 : 0 ≤ A := hA.le
    have hLsq0 : 0 ≤ Real.log X ^ 2 := sq_nonneg _
    have hExp0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log X)) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right htOne
      (mul_nonneg hA0 (mul_nonneg hLsq0 hExp0))
    have hexpCombine : Real.exp (κ * Real.sqrt (Real.log X)) *
        Real.exp (-c * Real.sqrt (Real.log X)) =
        Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      rw [← Real.exp_add]
      dsimp [κ]
      congr 1
      ring
    calc
      A * (1 + |t|) * Real.log X ^ 2 * Real.exp (-c * Real.sqrt (Real.log X))
          ≤ A * (2 * Real.exp (κ * Real.sqrt (Real.log X))) *
            Real.log X ^ 2 * Real.exp (-c * Real.sqrt (Real.log X)) := by
              have := mul_le_mul_of_nonneg_left htOne hA0
              nlinarith [mul_le_mul_of_nonneg_right this
                (mul_nonneg hLsq0 hExp0)]
      _ = 2 * A * (Real.log X ^ 2 *
          Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
            rw [← hexpCombine]
            ring
  exact hscaled.trans (hfreq.trans hsmallX)

end

end RHTower
