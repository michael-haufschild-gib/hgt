import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Marked half-character compact recurrence and lifted action

Exact compact-path, winding-parity, positive-energy, and absolutely-continuous lifted-phase action
clauses from the Stage-2 marked half-character card.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Coarse compact recurrence path `z_n(t)=exp(2πint/T)`. -/
def compactCoarseHolonomy (T : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * t / T : ℝ) : ℂ) * Complex.I)

/-- Marked square-root path `u_n(t)=exp(πint/T)`. -/
def compactHalfCharacterLift (T : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * (n : ℝ) * t / T : ℝ) : ℂ) * Complex.I)

/-- The marked compact path is a pointwise square root of the coarse path. -/
theorem compactHalfCharacterLift_sq
    (T : ℝ) (n : ℤ) (t : ℝ) :
    compactHalfCharacterLift T n t ^ 2 = compactCoarseHolonomy T n t := by
  rw [compactHalfCharacterLift, compactCoarseHolonomy, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

@[simp]
theorem compactCoarseHolonomy_zero (T : ℝ) (n : ℤ) :
    compactCoarseHolonomy T n 0 = 1 := by
  simp [compactCoarseHolonomy]

@[simp]
theorem compactHalfCharacterLift_zero (T : ℝ) (n : ℤ) :
    compactHalfCharacterLift T n 0 = 1 := by
  simp [compactHalfCharacterLift]

/-- Every nonzero-period coarse path closes at time `T`. -/
theorem compactCoarseHolonomy_period {T : ℝ} (hT : T ≠ 0) (n : ℤ) :
    compactCoarseHolonomy T n T = 1 := by
  rw [compactCoarseHolonomy]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  push_cast
  field_simp [hTC]

/-- The marked lift closes with the exact winding-parity sheet `(-1)^n`. -/
theorem compactHalfCharacterLift_period {T : ℝ} (hT : T ≠ 0) (n : ℤ) :
    compactHalfCharacterLift T n T = (-1 : ℂ) ^ n := by
  rw [compactHalfCharacterLift]
  calc
    Complex.exp ((((Real.pi * (n : ℝ) * T / T : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
          congr 1
          have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT
          push_cast
          field_simp [hTC]
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I) ^ n := Complex.exp_int_mul _ _
    _ = (-1 : ℂ) ^ n := by rw [Complex.exp_pi_mul_I]

/-- Endpoint-only observation loses winding, while the marked endpoint retains its parity. -/
theorem compactRecurrence_endpoint_and_parity {T : ℝ} (hT : T ≠ 0) (n : ℤ) :
    compactCoarseHolonomy T n 0 = compactCoarseHolonomy T n T ∧
      compactHalfCharacterLift T n T = (-1 : ℂ) ^ n * compactHalfCharacterLift T n 0 := by
  rw [compactCoarseHolonomy_zero, compactCoarseHolonomy_period hT,
    compactHalfCharacterLift_period hT, compactHalfCharacterLift_zero, mul_one]
  exact ⟨rfl, rfl⟩

/-- Endpoint-only coarse observation cannot determine winding: windings zero and one close at the
same endpoint. -/
theorem compactCoarseEndpoint_does_not_determine_winding
    {T : ℝ} (hT : T ≠ 0) :
    compactCoarseHolonomy T 0 T = compactCoarseHolonomy T 1 T ∧
      (0 : ℤ) ≠ 1 := by
  rw [compactCoarseHolonomy_period hT, compactCoarseHolonomy_period hT]
  exact ⟨rfl, by norm_num⟩

/-- Odd compact soldering coordinate, written directly on the marked lift. -/
def compactOddSoldering (T : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  compactHalfCharacterLift T n t - (compactHalfCharacterLift T n t)⁻¹

/-- Exact trigonometric form `S(u_n)=2i sin(πnt/T)`. -/
theorem compactOddSoldering_eq_sin (T : ℝ) (n : ℤ) (t : ℝ) :
    compactOddSoldering T n t =
      2 * Complex.I * Real.sin (Real.pi * (n : ℝ) * t / T) := by
  let theta : ℝ := Real.pi * (n : ℝ) * t / T
  have hneg :
      (compactHalfCharacterLift T n t)⁻¹ =
        Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) := by
    rw [compactHalfCharacterLift, show Real.pi * (n : ℝ) * t / T = theta from rfl,
      ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [compactOddSoldering, hneg, compactHalfCharacterLift,
    show Real.pi * (n : ℝ) * t / T = theta from rfl,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- Compact Laurent square is the negative trigonometric energy. -/
theorem compactOddSoldering_sq (T : ℝ) (n : ℤ) (t : ℝ) :
    compactOddSoldering T n t ^ 2 =
      -4 * (Real.sin (Real.pi * (n : ℝ) * t / T) : ℂ) ^ 2 := by
  rw [compactOddSoldering_eq_sin]
  rw [pow_two]
  calc
    2 * Complex.I * (Real.sin (Real.pi * (n : ℝ) * t / T) : ℂ) *
          (2 * Complex.I * (Real.sin (Real.pi * (n : ℝ) * t / T) : ℂ)) =
        4 * (Complex.I * Complex.I) *
          (Real.sin (Real.pi * (n : ℝ) * t / T) : ℂ) ^ 2 := by ring
    _ = -4 * (Real.sin (Real.pi * (n : ℝ) * t / T) : ℂ) ^ 2 := by
      rw [Complex.I_mul_I]
      ring

/-- Dagger-positive compact energy is `4 sin²(πnt/T)`. -/
theorem norm_compactOddSoldering_sq (T : ℝ) (n : ℤ) (t : ℝ) :
    ‖compactOddSoldering T n t‖ ^ 2 =
      4 * Real.sin (Real.pi * (n : ℝ) * t / T) ^ 2 := by
  rw [compactOddSoldering_eq_sin, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I, Real.norm_eq_abs]
  norm_num
  nlinarith [sq_abs (Real.sin (Real.pi * (n : ℝ) * t / T))]

/-- For every nonzero winding, integrated compact soldering energy is exactly `2T`. -/
theorem integral_norm_compactOddSoldering_sq
    {T : ℝ} (hT : 0 < T) {n : ℤ} (hn : n ≠ 0) :
    ∫ t in (0 : ℝ)..T, ‖compactOddSoldering T n t‖ ^ 2 = 2 * T := by
  have hc : Real.pi * (n : ℝ) / T ≠ 0 := by
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr hn)) hT.ne'
  simp_rw [norm_compactOddSoldering_sq]
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Real.sin x ^ 2) hc (a := (0 : ℝ)) (b := T)
  change (∫ t in (0 : ℝ)..T,
      Real.sin ((Real.pi * (n : ℝ) / T) * t) ^ 2) = _ at hsub
  have harg : ∀ x : ℝ,
      Real.pi * (n : ℝ) * x / T = (Real.pi * (n : ℝ) / T) * x := by
    intro x
    ring
  simp_rw [harg]
  rw [hsub, integral_sin_sq]
  have hzero : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hend : Real.pi * (n : ℝ) / T * T = (n : ℝ) * Real.pi := by
    field_simp
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul, sub_zero, hend, hzero,
    zero_add]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero, hnR, hT.ne']
  norm_num

/-- Integrated compact soldering energy determines neither winding magnitude nor parity: the
distinct windings one and two have equal energy and opposite root parity. -/
theorem integral_compactOddSoldering_does_not_determine_magnitude_or_parity
    {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ‖compactOddSoldering T 1 t‖ ^ 2) =
        ∫ t in (0 : ℝ)..T, ‖compactOddSoldering T 2 t‖ ^ 2 ∧
      (1 : ℤ) ≠ 2 ∧
      (-1 : ℂ) ^ (1 : ℤ) ≠ (-1 : ℂ) ^ (2 : ℤ) := by
  rw [integral_norm_compactOddSoldering_sq hT (by norm_num : (1 : ℤ) ≠ 0),
    integral_norm_compactOddSoldering_sq hT (by norm_num : (2 : ℤ) ≠ 0)]
  norm_num

/-! ## Absolutely-continuous lifted-phase action -/

/-- Kinetic action of a real phase lift on `[0,T]`.  For `u=exp(iφ)`, this is
`∫ |u̇/u|²`. -/
def liftedPhaseAction (T : ℝ) (phi : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, deriv phi t ^ 2

/-- Cauchy--Schwarz lower bound for every absolutely-continuous phase lift with integer endpoint
increment `πn`. -/
theorem liftedPhaseAction_lowerBound
    {T : ℝ} (hT : 0 < T) {n : ℤ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hwinding : phi T - phi 0 = Real.pi * (n : ℝ))
    (henergy : IntervalIntegrable (fun t => deriv phi t ^ 2) volume 0 T) :
    Real.pi ^ 2 * (n : ℝ) ^ 2 / T ≤ liftedPhaseAction T phi := by
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have hderiv : Integrable (deriv phi) mu := hphi.intervalIntegrable_deriv.1
  have hsq : Integrable (fun t => deriv phi t ^ 2) mu := henergy.1
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) T) volume
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have honeSq : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) mu := by
    simpa only [one_pow] using hone
  have hcs := sq_integral_mul_le (μ := mu)
    hone.aestronglyMeasurable hderiv.aestronglyMeasurable
    honeSq hsq
  have hmu : mu.real univ = T := by
    simp [mu, Measure.real, Real.volume_Ioc, hT.le]
  have hderivIntegral : ∫ t, deriv phi t ∂mu = Real.pi * (n : ℝ) := by
    rw [show (∫ t, deriv phi t ∂mu) = ∫ t in (0 : ℝ)..T, deriv phi t by
      rw [intervalIntegral.integral_of_le hT.le]]
    rw [hphi.integral_deriv_eq_sub, hwinding]
  have henergyIntegral :
      ∫ t, deriv phi t ^ 2 ∂mu = liftedPhaseAction T phi := by
    rw [liftedPhaseAction, intervalIntegral.integral_of_le hT.le]
  simp only [one_mul, one_pow] at hcs
  rw [MeasureTheory.integral_const] at hcs
  simp only [smul_eq_mul, mul_one] at hcs
  rw [hmu, hderivIntegral, henergyIntegral] at hcs
  rw [div_le_iff₀ hT]
  nlinarith [hcs]

/-- Exact variance decomposition behind the sharp lifted-action inequality. -/
theorem integral_deriv_sub_mean_sq_eq_action_sub_minimum
    {T : ℝ} (hT : 0 < T) {n : ℤ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hwinding : phi T - phi 0 = Real.pi * (n : ℝ))
    (henergy : IntervalIntegrable (fun t => deriv phi t ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T,
        (deriv phi t - Real.pi * (n : ℝ) / T) ^ 2) =
      liftedPhaseAction T phi - Real.pi ^ 2 * (n : ℝ) ^ 2 / T := by
  let c : ℝ := Real.pi * (n : ℝ) / T
  have hderiv := hphi.intervalIntegrable_deriv
  have hlinear : IntervalIntegrable (fun t => 2 * c * deriv phi t) volume 0 T :=
    hderiv.const_mul (2 * c)
  have hconst : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 T :=
    intervalIntegrable_const
  have hfirst : IntervalIntegrable
      (fun t => deriv phi t ^ 2 - 2 * c * deriv phi t) volume 0 T :=
    henergy.sub hlinear
  have hexpand :
      (fun t => (deriv phi t - c) ^ 2) =
        fun t => deriv phi t ^ 2 - 2 * c * deriv phi t + c ^ 2 := by
    funext t
    ring
  change (∫ t in (0 : ℝ)..T, (deriv phi t - c) ^ 2) = _
  rw [hexpand,
    intervalIntegral.integral_add hfirst hconst,
    intervalIntegral.integral_sub henergy hlinear,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,
    hphi.integral_deriv_eq_sub, hwinding]
  rw [liftedPhaseAction]
  dsimp [c]
  field_simp [hT.ne']
  ring

/-- Equality in the lifted-action bound holds exactly when phase velocity is constant almost
everywhere on the period interval. -/
theorem liftedPhaseAction_eq_minimum_iff_ae_constantSpeed
    {T : ℝ} (hT : 0 < T) {n : ℤ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hwinding : phi T - phi 0 = Real.pi * (n : ℝ))
    (henergy : IntervalIntegrable (fun t => deriv phi t ^ 2) volume 0 T) :
    liftedPhaseAction T phi = Real.pi ^ 2 * (n : ℝ) ^ 2 / T ↔
      deriv phi =ᵐ[volume.restrict (Ioc (0 : ℝ) T)]
        fun _ => Real.pi * (n : ℝ) / T := by
  let c : ℝ := Real.pi * (n : ℝ) / T
  have hderiv := hphi.intervalIntegrable_deriv
  have hlinear : IntervalIntegrable (fun t => 2 * c * deriv phi t) volume 0 T :=
    hderiv.const_mul (2 * c)
  have hconst : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 T :=
    intervalIntegrable_const
  have hvar : IntervalIntegrable (fun t => (deriv phi t - c) ^ 2) volume 0 T := by
    have hfirst : IntervalIntegrable
        (fun t => deriv phi t ^ 2 - 2 * c * deriv phi t) volume 0 T :=
      henergy.sub hlinear
    convert hfirst.add hconst using 1
    funext t
    ring
  constructor
  · intro heq
    have hzero : ∫ t in (0 : ℝ)..T, (deriv phi t - c) ^ 2 = 0 := by
      rw [integral_deriv_sub_mean_sq_eq_action_sub_minimum hT hphi hwinding henergy,
        heq, sub_self]
    have hsquareZero :
        (fun t => (deriv phi t - c) ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] 0 :=
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
        (Filter.Eventually.of_forall fun t => sq_nonneg (deriv phi t - c)) hvar).1 hzero
    filter_upwards [hsquareZero] with t ht
    simp only [Pi.zero_apply] at ht
    have hsub : deriv phi t - c = 0 := by
      nlinarith [sq_nonneg (deriv phi t - c)]
    exact sub_eq_zero.mp hsub
  · intro hspeed
    rw [liftedPhaseAction, intervalIntegral.integral_of_le hT.le]
    rw [MeasureTheory.integral_congr_ae (hspeed.mono fun t ht => by rw [ht])]
    rw [MeasureTheory.setIntegral_const]
    simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT.le, sub_zero,
      smul_eq_mul]
    field_simp [hT.ne']

/-- Constant-speed phase lift attaining the sharp action bound. -/
def constantSpeedPhaseLift (T : ℝ) (n : ℤ) (phi0 : ℝ) (t : ℝ) : ℝ :=
  phi0 + Real.pi * (n : ℝ) * t / T

/-- Constant-speed phase has exact winding increment. -/
theorem constantSpeedPhaseLift_winding
    {T : ℝ} (hT : T ≠ 0) (n : ℤ) (phi0 : ℝ) :
    constantSpeedPhaseLift T n phi0 T - constantSpeedPhaseLift T n phi0 0 =
      Real.pi * (n : ℝ) := by
  simp [constantSpeedPhaseLift]
  field_simp

/-- Constant-speed phase realizes the exact minimum `π²n²/T`. -/
theorem liftedPhaseAction_constantSpeed
    {T : ℝ} (hT : 0 < T) (n : ℤ) (phi0 : ℝ) :
    liftedPhaseAction T (constantSpeedPhaseLift T n phi0) =
      Real.pi ^ 2 * (n : ℝ) ^ 2 / T := by
  have hT0 := hT.ne'
  have hderiv (t : ℝ) :
      deriv (constantSpeedPhaseLift T n phi0) t = Real.pi * (n : ℝ) / T := by
    have hfun : constantSpeedPhaseLift T n phi0 =
        fun x => phi0 + (Real.pi * (n : ℝ) / T) * x := by
      funext x
      simp only [constantSpeedPhaseLift]
      ring
    rw [hfun]
    have hfun' : (fun x : ℝ => phi0 + (Real.pi * (n : ℝ) / T) * x) =
        (fun _ : ℝ => phi0) + fun y => (Real.pi * (n : ℝ) / T) * y := by
      rfl
    rw [hfun']
    convert ((hasDerivAt_const t phi0).add
      ((hasDerivAt_id' t).const_mul (Real.pi * (n : ℝ) / T))).deriv using 1
    all_goals ring
  rw [liftedPhaseAction]
  simp_rw [hderiv]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hT0]

/-- Equality forces the absolutely-continuous phase itself to be the constant-speed lift on the
whole closed period interval, not merely to have the same energy. -/
theorem phase_eq_constantSpeed_of_liftedPhaseAction_eq_minimum
    {T : ℝ} (hT : 0 < T) {n : ℤ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hwinding : phi T - phi 0 = Real.pi * (n : ℝ))
    (henergy : IntervalIntegrable (fun t => deriv phi t ^ 2) volume 0 T)
    (heq : liftedPhaseAction T phi = Real.pi ^ 2 * (n : ℝ) ^ 2 / T) :
    ∀ t ∈ Icc (0 : ℝ) T,
      phi t = constantSpeedPhaseLift T n (phi 0) t := by
  let c : ℝ := Real.pi * (n : ℝ) / T
  have hspeed :
      deriv phi =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] fun _ => c := by
    exact (liftedPhaseAction_eq_minimum_iff_ae_constantSpeed
      hT hphi hwinding henergy).1 heq
  have hspeedIcc :
      deriv phi =ᵐ[volume.restrict (Icc (0 : ℝ) T)] fun _ => c := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    exact hspeed
  have hspeedAll : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → deriv phi t = c :=
    (ae_restrict_iff' measurableSet_Icc).1 hspeedIcc
  have hlinearDiff : ContDiff ℝ 1 (constantSpeedPhaseLift T n (phi 0)) := by
    unfold constantSpeedPhaseLift
    fun_prop
  have hlinearAC :
      AbsolutelyContinuousOnInterval (constantSpeedPhaseLift T n (phi 0)) 0 T :=
    hlinearDiff.contDiffOn.absolutelyContinuousOnInterval
  let g : ℝ → ℝ := fun t => phi t - constantSpeedPhaseLift T n (phi 0) t
  have hgAC : AbsolutelyContinuousOnInterval g 0 T := hphi.sub hlinearAC
  have hlinearDeriv (t : ℝ) :
      HasDerivAt (constantSpeedPhaseLift T n (phi 0)) c t := by
    have hfun : constantSpeedPhaseLift T n (phi 0) =
        fun x => phi 0 + c * x := by
      funext x
      simp only [constantSpeedPhaseLift]
      dsimp [c]
      ring
    rw [hfun]
    exact (hasDerivAt_const_mul c).const_add (phi 0)
  have hgDerivZero : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) T → HasDerivAt g 0 t := by
    filter_upwards [hphi.ae_differentiableAt, hspeedAll] with t hdiff hspeedAt ht
    have htIcc : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT.le] using ht
    have hgDeriv : HasDerivAt g (deriv phi t - c) t :=
      (hdiff ht).hasDerivAt.sub (hlinearDeriv t)
    rw [hspeedAt htIcc, sub_self] at hgDeriv
    exact hgDeriv
  obtain ⟨C, hC⟩ := hgAC.const_of_ae_hasDerivAt_zero hgDerivZero
  have hzero : g 0 = 0 := by
    simp [g, constantSpeedPhaseLift]
  have hCzero : C = 0 := by
    have := hC 0 (by simp [hT.le])
    rw [hzero] at this
    exact this.symm
  intro t ht
  have htg : g t = C := hC t (by simpa only [uIcc_of_le hT.le] using ht)
  rw [hCzero] at htg
  exact sub_eq_zero.mp htg

/-- Fubini--Study kinetic convention used by the framed two-level fibre. -/
def fubiniStudyLiftedPhaseAction (T : ℝ) (phi : ℝ → ℝ) : ℝ :=
  liftedPhaseAction T phi / 2

/-- Sharp Fubini--Study lower bound `π²n²/(2T)`. -/
theorem fubiniStudyLiftedPhaseAction_lowerBound
    {T : ℝ} (hT : 0 < T) {n : ℤ} {phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hwinding : phi T - phi 0 = Real.pi * (n : ℝ))
    (henergy : IntervalIntegrable (fun t => deriv phi t ^ 2) volume 0 T) :
    Real.pi ^ 2 * (n : ℝ) ^ 2 / (2 * T) ≤
      fubiniStudyLiftedPhaseAction T phi := by
  rw [fubiniStudyLiftedPhaseAction]
  have h := liftedPhaseAction_lowerBound hT hphi hwinding henergy
  calc
    Real.pi ^ 2 * (n : ℝ) ^ 2 / (2 * T) =
        (Real.pi ^ 2 * (n : ℝ) ^ 2 / T) / 2 := by
          field_simp [hT.ne']
    _ ≤ liftedPhaseAction T phi / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)

/-- Constant-speed lift attains the exact Fubini--Study minimum. -/
theorem fubiniStudyLiftedPhaseAction_constantSpeed
    {T : ℝ} (hT : 0 < T) (n : ℤ) (phi0 : ℝ) :
    fubiniStudyLiftedPhaseAction T (constantSpeedPhaseLift T n phi0) =
      Real.pi ^ 2 * (n : ℝ) ^ 2 / (2 * T) := by
  rw [fubiniStudyLiftedPhaseAction, liftedPhaseAction_constantSpeed hT]
  field_simp [hT.ne']

/-! ## Algebraic quantum-rotor core -/

/-- Finite-support invariant core of the quantum rotor `ell²(ℤ)`. -/
abbrev RotorCore := ℤ →₀ ℂ

/-- Rotor basis ket `|k⟩` on the finite-support core. -/
def rotorKet (k : ℤ) : RotorCore := Finsupp.single k 1

/-- Unbounded number operator on its finite-support invariant core. -/
def rotorNumberCore : RotorCore →ₗ[ℂ] RotorCore :=
  Finsupp.linearCombination ℂ
    (fun k : ℤ => (k : ℂ) • rotorKet k)

/-- Bilateral forward shift `V|k⟩=|k+1⟩`. -/
def rotorShiftCore : RotorCore →ₗ[ℂ] RotorCore :=
  Finsupp.lmapDomain ℂ ℂ (fun k : ℤ => k + 1)

/-- Inverse bilateral shift `V⁻¹|k⟩=|k-1⟩`, equal to `V*` after Hilbert completion. -/
def rotorShiftInvCore : RotorCore →ₗ[ℂ] RotorCore :=
  Finsupp.lmapDomain ℂ ℂ (fun k : ℤ => k - 1)

/-- Winding-parity operator `Γ|k⟩=(-1)^k|k⟩`. -/
def rotorParityCore : RotorCore →ₗ[ℂ] RotorCore :=
  Finsupp.linearCombination ℂ
    (fun k : ℤ => ((-1 : ℂ) ^ k) • rotorKet k)

/-- Quadratic rotor Hamiltonian `H=N²` on the invariant core. -/
def rotorHamiltonianCore : RotorCore →ₗ[ℂ] RotorCore :=
  rotorNumberCore.comp rotorNumberCore

@[simp]
theorem rotorNumberCore_ket (k : ℤ) :
    rotorNumberCore (rotorKet k) = (k : ℂ) • rotorKet k := by
  simp [rotorNumberCore, rotorKet]

@[simp]
theorem rotorShiftCore_ket (k : ℤ) :
    rotorShiftCore (rotorKet k) = rotorKet (k + 1) := by
  simp [rotorShiftCore, rotorKet, Finsupp.lmapDomain_apply]

@[simp]
theorem rotorShiftInvCore_ket (k : ℤ) :
    rotorShiftInvCore (rotorKet k) = rotorKet (k - 1) := by
  simp [rotorShiftInvCore, rotorKet, Finsupp.lmapDomain_apply]

@[simp]
theorem rotorParityCore_ket (k : ℤ) :
    rotorParityCore (rotorKet k) = ((-1 : ℂ) ^ k) • rotorKet k := by
  simp [rotorParityCore, rotorKet]

@[simp]
theorem rotorHamiltonianCore_ket (k : ℤ) :
    rotorHamiltonianCore (rotorKet k) = (k : ℂ) ^ 2 • rotorKet k := by
  simp [rotorHamiltonianCore, LinearMap.comp_apply, smul_smul, pow_two]

/-- Exact number/shift covariance `V⁻¹NV=N+1` on the full finite-support core. -/
theorem rotorShiftInv_number_shift_conjugation :
    rotorShiftInvCore.comp (rotorNumberCore.comp rotorShiftCore) =
      rotorNumberCore + LinearMap.id := by
  apply Finsupp.lhom_ext
  intro k z
  have hsingle : Finsupp.single k z = z • rotorKet k := by
    ext j
    simp [rotorKet]
  rw [hsingle]
  simp only [map_smul, rotorShiftCore_ket, LinearMap.comp_apply, rotorNumberCore_ket,
    rotorShiftInvCore_ket, LinearMap.add_apply, LinearMap.id_apply]
  rw [show k + 1 - 1 = k by omega, smul_add, smul_smul, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- Exact parity/shift anticommutation `ΓVΓ=-V` on the full finite-support core. -/
theorem rotorParity_shift_anticommutation :
    rotorParityCore.comp (rotorShiftCore.comp rotorParityCore) = -rotorShiftCore := by
  apply Finsupp.lhom_ext
  intro k z
  have hsingle : Finsupp.single k z = z • rotorKet k := by
    ext j
    simp [rotorKet]
  rw [hsingle]
  simp only [map_smul, rotorParityCore_ket, LinearMap.comp_apply, rotorShiftCore_ket,
    LinearMap.neg_apply]
  have hpow : (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    norm_num
  rw [hpow, smul_smul]
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact (show Even (k + k) from ⟨k, rfl⟩).neg_one_zpow
  rw [smul_neg, ← neg_smul]
  rw [smul_smul, show k + 1 = 1 + k by ring]
  apply congrArg (fun a : ℂ => a • rotorKet (1 + k))
  calc
    z * (-1 : ℂ) ^ k * -((-1 : ℂ) ^ k) =
        -z * (((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k)) := by ring
    _ = -z := by rw [hsq, mul_one]

end GaloisForLFunctions.HTGeometry
