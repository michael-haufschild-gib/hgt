import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPrimeCommutatorTorque
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticTranslate
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Suzuki position torque and completed Xi curvature

For Suzuki's restricted Weil kernel, commutation with position multiplies every translation
lag by that lag.  Against the free even/odd response pair `cosh,sinh`, the overlap is a tent.
This file closes the exact scalar and Euler-half-plane bridge:

* the principal-value and Gamma-remainder terms collapse to
  `t (exp(-t/2)/2 - sinh(3t/2))`;
* the visible prime layer is the finite Mangoldt tent sum already supplied by
  `SuzukiWeilPrimeCommutatorTorque`;
* one tent has Laplace transform `exp(-σh)/σ²`;
* differentiating the completed `+2` shift identity exposes exactly the
  logarithmically weighted filtered Mangoldt series;
* after the half-shift, the complete continuation is

  `((xi'/xi)'(s-1/2) - (xi'/xi)'(s+3/2)) / (2s²)`.

All statements are unconditional.  The file contains no numerical computation and makes no
Riemann-hypothesis assumption.
-/

open Complex Function Filter MeasureTheory Set Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-! ## Exact archimedean collapse -/

/-- Suzuki's smooth remainder second derivative on the positive lag axis.  This is
`r₀''+r₁''` from the restricted Weil kernel:

`-2 cosh(t/2) + exp(t/2)/(2 sinh t) - 1/(2t)`.

The value at zero is immaterial for integration; Lean's totalized division fixes it
canonically. -/
def suzukiWeilRemainderSecondDerivative (t : ℝ) : ℝ :=
  -2 * Real.cosh (t / 2) +
    Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t)

/-- Multiplication by position removes the principal-value singularity, and the resulting
`1/2` contribution cancels the `-1/(2t)` term of Suzuki's smooth remainder.  The entire
principal-value--Gamma sector becomes one elementary kernel. -/
theorem suzukiWeil_positionArchKernel_eq (t : ℝ) :
    (1 / 2 + t * suzukiWeilRemainderSecondDerivative t) * Real.sinh t =
      t * (Real.exp (-t / 2) / 2 - Real.sinh (3 * t / 2)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [suzukiWeilRemainderSecondDerivative]
  have hsinh : Real.sinh t ≠ 0 := (Real.sinh_ne_zero).2 ht
  have hcoeff :
      (1 / 2 + t * suzukiWeilRemainderSecondDerivative t) * Real.sinh t =
        t * (-2 * Real.cosh (t / 2) * Real.sinh t +
          Real.exp (t / 2) / 2) := by
    rw [suzukiWeilRemainderSecondDerivative]
    field_simp [ht, hsinh]
    ring
  have hproduct :
      2 * Real.cosh (t / 2) * Real.sinh t =
        Real.sinh (3 * t / 2) + Real.sinh (t / 2) := by
    have hadd := Real.sinh_add t (t / 2)
    have hsub := Real.sinh_sub t (t / 2)
    rw [show t + t / 2 = 3 * t / 2 by ring] at hadd
    rw [show t - t / 2 = t / 2 by ring] at hsub
    nlinarith
  have hexpSinh :
      Real.exp (t / 2) / 2 - Real.sinh (t / 2) =
        Real.exp (-t / 2) / 2 := by
    rw [Real.sinh_eq]
    ring
  rw [hcoeff, show -2 * Real.cosh (t / 2) * Real.sinh t =
    -(2 * Real.cosh (t / 2) * Real.sinh t) by ring, hproduct]
  rw [← hexpSinh]
  ring

/-- Principal-value plus Gamma-remainder contribution to the free-profile position torque
at aperture length `L=2a`, before cancellation. -/
def suzukiFreeUnreducedArchPositionTorque (L : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L,
    (1 / 2 + t * suzukiWeilRemainderSecondDerivative t) *
      (L - t) * Real.sinh t

/-- Reduced elementary form of the same archimedean torque. -/
def suzukiFreeArchPositionTorque (L : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L,
    t * (L - t) *
      (Real.exp (-t / 2) / 2 - Real.sinh (3 * t / 2))

/-- Exact cancellation at the integrated finite-aperture level. -/
theorem suzukiFreeUnreducedArchPositionTorque_eq (L : ℝ) :
    suzukiFreeUnreducedArchPositionTorque L =
      suzukiFreeArchPositionTorque L := by
  rw [suzukiFreeUnreducedArchPositionTorque,
    suzukiFreeArchPositionTorque]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  rw [show
    (1 / 2 + t * suzukiWeilRemainderSecondDerivative t) *
        (L - t) * Real.sinh t =
      ((1 / 2 + t * suzukiWeilRemainderSecondDerivative t) *
        Real.sinh t) * (L - t) by ring,
    suzukiWeil_positionArchKernel_eq]
  ring

/-- Elementary finite-interval tent transform against a real exponential. -/
theorem integral_tent_mul_exp_interval
    (k L : ℝ) (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..L, t * (L - t) * Real.exp (k * t)) =
      (Real.exp (k * L) * (k * L - 2) + k * L + 2) / k ^ 3 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt
        (fun x =>
          Real.exp (k * x) *
            (-k ^ 2 * x ^ 2 + L * k ^ 2 * x + 2 * k * x - L * k - 2) /
              k ^ 3)
        (t * (L - t) * Real.exp (k * t)) t := by
    intro t
    have hkt : HasDerivAt (fun x : ℝ => k * x) k t := by
      simpa using (hasDerivAt_id t).const_mul k
    have hexp := hkt.exp
    have hpoly : HasDerivAt
        (fun x : ℝ =>
          -k ^ 2 * x ^ 2 + L * k ^ 2 * x + 2 * k * x - L * k - 2)
        (-k ^ 2 * (2 * t) + L * k ^ 2 + 2 * k) t := by
      have hquad := ((hasDerivAt_id t).pow 2).const_mul (-k ^ 2)
      have hlin1 := (hasDerivAt_id t).const_mul (L * k ^ 2)
      have hlin2 := (hasDerivAt_id t).const_mul (2 * k)
      convert (((hquad.add hlin1).add hlin2).sub_const (L * k)).sub_const 2 using 1 <;>
        try rfl
      all_goals
        simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    have hraw := (hexp.mul hpoly).div_const (k ^ 3)
    apply hraw.congr_deriv
    field_simp [hk]
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => t * (L - t) * Real.exp (k * t)) volume 0 L := by
    exact
      ((continuous_id.mul (continuous_const.sub continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hderiv t) hint]
  field_simp [hk]
  norm_num [Real.exp_zero]
  ring

/-- Closed form of Suzuki's full principal-value--Gamma position torque.  Its leading term
is `-(2L/9 - 8/27) exp(3L/2)`, the scale against which the prime tent layer competes. -/
theorem suzukiFreeArchPositionTorque_closedForm (L : ℝ) :
    suzukiFreeArchPositionTorque L =
      -(2 * L / 9 - 8 / 27) * Real.exp (3 * L / 2) +
        (2 * L + 8) * Real.exp (-L / 2) +
        (2 * L / 9 + 8 / 27) * Real.exp (-3 * L / 2) +
        2 * L - 232 / 27 := by
  rw [suzukiFreeArchPositionTorque]
  have hnegHalf := integral_tent_mul_exp_interval (-1 / 2) L (by norm_num)
  have hthreeHalf := integral_tent_mul_exp_interval (3 / 2) L (by norm_num)
  have hnegThreeHalf := integral_tent_mul_exp_interval (-3 / 2) L (by norm_num)
  have hsplit :
      (fun t : ℝ =>
        t * (L - t) *
          (Real.exp (-t / 2) / 2 - Real.sinh (3 * t / 2))) =
        fun t =>
          (1 / 2) * (t * (L - t) * Real.exp ((-1 / 2) * t)) -
          (1 / 2) * (t * (L - t) * Real.exp ((3 / 2) * t)) +
          (1 / 2) * (t * (L - t) * Real.exp ((-3 / 2) * t)) := by
    funext t
    rw [Real.sinh_eq]
    ring
  let f1 : ℝ → ℝ := fun t =>
    (1 / 2) * (t * (L - t) * Real.exp ((-1 / 2) * t))
  let f2 : ℝ → ℝ := fun t =>
    (1 / 2) * (t * (L - t) * Real.exp ((3 / 2) * t))
  let f3 : ℝ → ℝ := fun t =>
    (1 / 2) * (t * (L - t) * Real.exp ((-3 / 2) * t))
  have hf1 : IntervalIntegrable f1 volume 0 L :=
    (by
      dsimp only [f1]
      fun_prop : Continuous f1).intervalIntegrable _ _
  have hf2 : IntervalIntegrable f2 volume 0 L :=
    (by
      dsimp only [f2]
      fun_prop : Continuous f2).intervalIntegrable _ _
  have hf3 : IntervalIntegrable f3 volume 0 L :=
    (by
      dsimp only [f3]
      fun_prop : Continuous f3).intervalIntegrable _ _
  rw [hsplit]
  change (∫ t in (0 : ℝ)..L, ((f1 - f2) t + f3 t)) = _
  calc
    (∫ t in (0 : ℝ)..L, ((f1 - f2) t + f3 t)) =
        (∫ t in (0 : ℝ)..L, (f1 - f2) t) +
          ∫ t in (0 : ℝ)..L, f3 t :=
      intervalIntegral.integral_add (hf1.sub hf2) hf3
    _ = ((∫ t in (0 : ℝ)..L, f1 t) -
          ∫ t in (0 : ℝ)..L, f2 t) +
          ∫ t in (0 : ℝ)..L, f3 t := by
      have hsub :
          (∫ t in (0 : ℝ)..L, (f1 - f2) t) =
            (∫ t in (0 : ℝ)..L, f1 t) -
              ∫ t in (0 : ℝ)..L, f2 t := by
        simpa only [Pi.sub_apply] using
          intervalIntegral.integral_sub hf1 hf2
      rw [hsub]
    _ = _ := by
      dsimp only [f1, f2, f3]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        hnegHalf, hthreeHalf, hnegThreeHalf]
      ring_nf

/-! ## Actual visible finite prime layer -/

/-- Integer translation lags visible in aperture length `L`. -/
def suzukiVisibleWeilIndices (L : ℝ) : Finset ℕ :=
  Finset.Icc 2 ⌊Real.exp L⌋₊

/-- Actual finite prime-power position torque of the free profile at aperture `a=L/2`. -/
def suzukiFreePrimePositionTorque (L : ℝ) : ℝ :=
  suzukiFiniteWeilPrimeTorque (suzukiVisibleWeilIndices L) (L / 2)
    Real.cosh Real.sinh

/-- The visible prime layer is the exact Mangoldt tent sum. -/
theorem suzukiFreePrimePositionTorque_eq (L : ℝ) :
    suzukiFreePrimePositionTorque L =
      ∑ n ∈ suzukiVisibleWeilIndices L,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.log n * (L - Real.log n) * Real.sinh (Real.log n) := by
  rw [suzukiFreePrimePositionTorque,
    suzukiFiniteWeilPrimeTorque_cosh_sinh]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Complete prime--Gamma free-profile position torque extracted from Suzuki's finite-aperture
restricted Weil kernel. -/
def suzukiFreePositionTorque (L : ℝ) : ℝ :=
  suzukiFreeArchPositionTorque L + suzukiFreePrimePositionTorque L

/-- Exact source decomposition of the complete torque. -/
theorem suzukiFreePositionTorque_eq (L : ℝ) :
    suzukiFreePositionTorque L =
      (∫ t in (0 : ℝ)..L,
        t * (L - t) *
          (Real.exp (-t / 2) / 2 - Real.sinh (3 * t / 2))) +
      ∑ n ∈ suzukiVisibleWeilIndices L,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.log n * (L - Real.log n) * Real.sinh (Real.log n) := by
  rw [suzukiFreePositionTorque, suzukiFreeArchPositionTorque,
    suzukiFreePrimePositionTorque_eq]

/-! ## The tent transform -/

/-- Every lag tent contributes the universal factor `exp(-σh)/σ²` to the real Laplace
transform.  This is the mechanism that changes Suzuki's finite-aperture tent sum into a
logarithmically differentiated Dirichlet series. -/
theorem integral_suzukiPositionTent_mul_exp (σ h : ℝ) (hσ : 0 < σ) :
    (∫ L in Ioi h, (L - h) * Real.exp (-σ * L)) =
      Real.exp (-σ * h) / σ ^ 2 := by
  rw [← integral_Ioi_comp_add_eq_integral_Ioi
    (fun L : ℝ => (L - h) * Real.exp (-σ * L)) h]
  have hbase :
      (∫ u in Ioi (0 : ℝ), u * Real.exp (-σ * u)) = 1 / σ ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : ℝ)) (r := σ) (by norm_num) hσ
    have h' :
        (∫ u in Ioi (0 : ℝ), u * Real.exp (-σ * u)) =
          (1 / σ) ^ (2 : ℝ) * Real.Gamma 2 := by
      calc
        (∫ u in Ioi (0 : ℝ), u * Real.exp (-σ * u)) =
            ∫ u in Ioi (0 : ℝ),
              u ^ ((2 : ℝ) - 1) * Real.exp (-(σ * u)) := by
                refine setIntegral_congr_fun measurableSet_Ioi (fun u _hu => ?_)
                rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
                congr 1
                ring
        _ = _ := h
    rw [show Real.Gamma (2 : ℝ) = 1 by
      simpa using Real.Gamma_nat_eq_factorial 1] at h'
    rw [h', Real.rpow_two]
    field_simp [ne_of_gt hσ]
  have hcongr :
      (fun u : ℝ => ((u + h - h) * Real.exp (-σ * (u + h)))) =
        fun u => Real.exp (-σ * h) * (u * Real.exp (-σ * u)) := by
    funext u
    rw [show -σ * (u + h) = -σ * h + -σ * u by ring, Real.exp_add]
    ring
  rw [hcongr, integral_const_mul, hbase]
  ring

/-! ## Differentiated completed shift and torque continuation -/

/-- The filtered Mangoldt coefficient has absolute-convergence abscissa at most one. -/
theorem abscissaOfAbsConv_filteredVonMangoldtCoeff_le_one :
    LSeries.abscissaOfAbsConv filteredVonMangoldtCoeff ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact LSeriesSummable_filteredVonMangoldtCoeff (by simpa using hy)

private theorem deriv_suzukiPositionRationalShift
    (s : ℂ) (h2 : s + 2 ≠ 0) (h1 : s + 1 ≠ 0) (hm : s - 1 ≠ 0) :
    deriv
      (fun z : ℂ => 1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1)) s =
        -(1 / (s + 2) ^ 2) - 1 / (s + 1) ^ 2 + 1 / (s - 1) ^ 2 := by
  have hd2 := ((hasDerivAt_id s).add_const 2).inv h2
  have hd1 := ((hasDerivAt_id s).add_const 1).inv h1
  have hdm := ((hasDerivAt_id s).sub_const 1).inv hm
  let R : ℂ → ℂ :=
    (fun x : ℂ => x + 2)⁻¹ + (fun x : ℂ => x + 1)⁻¹ -
      (fun x : ℂ => x - 1)⁻¹
  have hfun :
      (fun z : ℂ => 1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1)) = R := by
    funext z
    simp only [R, one_div, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
  rw [hfun]
  dsimp only [R]
  have hder := ((hd2.add hd1).sub hdm).deriv
  convert hder using 1
  · simp only [id_eq]
  · simp only [id_eq]
    ring

/-- **Differentiated completed shift exposure.**  On `Re s>1`, the curvature difference of
the actual completed Xi logarithmic derivative is the logarithmically weighted filtered
Mangoldt series plus the exact rational Gamma/boundary curvature. -/
theorem xi_logDeriv_curvature_shift_two_exposes_position_source
    {s : ℂ} (hs : 1 < s.re) :
    deriv (logDeriv xi) s - deriv (logDeriv xi) (s + 2) =
      LSeries (LSeries.logMul filteredVonMangoldtCoeff) s +
        (1 / (s + 2) ^ 2 + 1 / (s + 1) ^ 2 - 1 / (s - 1) ^ 2) := by
  let U : Set ℂ := {z | 1 < z.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hs
  have hEq :
      (fun z : ℂ =>
        logDeriv xi (z + 2) - logDeriv xi z -
          (1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1))) =ᶠ[𝓝 s]
        fun z => LSeries filteredVonMangoldtCoeff z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hz
    have h := xi_logDeriv_shift_two_exposes_prime_source hz
    rw [show (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (1 - (n : ℂ) ^ (-(2 : ℂ)))) = filteredVonMangoldtCoeff by rfl] at h
    exact h
  have hd := hEq.deriv_eq
  have hseries :
      deriv (LSeries filteredVonMangoldtCoeff) s =
        -LSeries (LSeries.logMul filteredVonMangoldtCoeff) s := by
    apply LSeries_deriv
    exact lt_of_le_of_lt abscissaOfAbsConv_filteredVonMangoldtCoeff_le_one
      (by exact_mod_cast hs)
  have h2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have h1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hm : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re] at hre
    linarith
  have hlogShift : DifferentiableAt ℂ (fun z => logDeriv xi (z + 2)) s := by
    rw [show (fun z => logDeriv xi (z + 2)) =
        fun z => deriv xi (z + 2) / xi (z + 2) by
      funext z
      rw [logDeriv_apply]]
    have hxi : DifferentiableAt ℂ xi (s + 2) := xi_differentiable (s + 2)
    have hxid : DifferentiableAt ℂ (deriv xi) (s + 2) := xi_differentiable.deriv (s + 2)
    have hne : xi (s + 2) ≠ 0 := xi_ne_zero_of_one_lt_re (by
      norm_num [Complex.add_re]
      linarith)
    have hinner : HasDerivAt (fun z : ℂ => z + 2) 1 s := by
      simpa using (hasDerivAt_id s).add_const 2
    have hfun :
        ((deriv xi / xi) ∘ fun z : ℂ => z + 2) =
          fun z => deriv xi (z + 2) / xi (z + 2) := by
      rfl
    rw [← hfun]
    exact ((hxid.div hxi hne).hasDerivAt.comp s hinner).differentiableAt
  have hlog : DifferentiableAt ℂ (logDeriv xi) s := by
    rw [show logDeriv xi = fun z => deriv xi z / xi z by
      funext z
      rw [logDeriv_apply]]
    exact (xi_differentiable.deriv s).div (xi_differentiable s)
      (xi_ne_zero_of_one_lt_re hs)
  have hrat : DifferentiableAt ℂ
      (fun z : ℂ => 1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1)) s := by
    have hd2 := ((hasDerivAt_id s).add_const 2).inv h2
    have hd1 := ((hasDerivAt_id s).add_const 1).inv h1
    have hdm := ((hasDerivAt_id s).sub_const 1).inv hm
    let R : ℂ → ℂ :=
      (fun x : ℂ => x + 2)⁻¹ + (fun x : ℂ => x + 1)⁻¹ -
        (fun x : ℂ => x - 1)⁻¹
    have hfun :
        (fun z : ℂ => 1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1)) = R := by
      funext z
      simp only [R, one_div, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    rw [hfun]
    exact ((hd2.add hd1).sub hdm).differentiableAt
  change deriv
    (((fun z : ℂ => logDeriv xi (z + 2)) - logDeriv xi) -
      fun z : ℂ => 1 / (z + 2) + 1 / (z + 1) - 1 / (z - 1)) s =
        deriv (LSeries filteredVonMangoldtCoeff) s at hd
  rw [deriv_sub (hlogShift.sub hlog) hrat,
    deriv_sub hlogShift hlog, deriv_comp_add_const,
    deriv_suzukiPositionRationalShift s h2 h1 hm, hseries] at hd
  linear_combination -hd

/-- Meromorphic continuation dictated by the complete position torque transform. -/
def suzukiPositionTorqueLaplaceContinuation (s : ℂ) : ℂ :=
  (deriv (logDeriv xi) (s - 1 / 2) -
    deriv (logDeriv xi) (s + 3 / 2)) / (2 * s ^ 2)

/-- Euler-half-plane prime--Gamma expression produced by the finite-aperture torque. -/
def suzukiPositionTorqueEulerSource (s : ℂ) : ℂ :=
  (LSeries (LSeries.logMul filteredVonMangoldtCoeff) (s - 1 / 2) +
    (1 / (s + 3 / 2) ^ 2 + 1 / (s + 1 / 2) ^ 2 -
      1 / (s - 3 / 2) ^ 2)) / (2 * s ^ 2)

/-- **Exact source-to-Xi curvature identity.**  To the right of the torque's elementary
exponential type, the prime--Gamma Euler expression equals the completed Xi curvature
difference. -/
theorem suzukiPositionTorqueLaplaceContinuation_eq_eulerSource
    {s : ℂ} (hs : 3 / 2 < s.re) :
    suzukiPositionTorqueLaplaceContinuation s =
      suzukiPositionTorqueEulerSource s := by
  have h := xi_logDeriv_curvature_shift_two_exposes_position_source
    (s := s - 1 / 2) (by
      norm_num [Complex.sub_re]
      linarith)
  rw [show (s - 1 / 2) + 2 = s + 3 / 2 by ring] at h
  rw [show (s - 1 / 2) + 1 = s + 1 / 2 by ring,
    show (s - 1 / 2) - 1 = s - 3 / 2 by ring] at h
  rw [suzukiPositionTorqueLaplaceContinuation,
    suzukiPositionTorqueEulerSource, h]

end

end RHTower
