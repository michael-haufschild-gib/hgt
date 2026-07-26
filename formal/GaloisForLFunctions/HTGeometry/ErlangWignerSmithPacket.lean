import GaloisForLFunctions.HTGeometry.MatrixWignerSmithHermitian
import GaloisForLFunctions.HTGeometry.FiniteJetConstraintSourceBoundary
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Positive Erlang Wigner--Smith packets

This module constructs the normalized third-order Erlang wave packet, proves its
first-derivative-domain data and exact scalar Wigner--Smith time-pairing identity,
derives the three half-line recovery recurrences by integration by parts, and
proves that the third-order recovery relation preserves the DA/HT class.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology
open GaloisForLFunctions


namespace GaloisForLFunctions.HTGeometry

noncomputable section

def erlangOneKernel (ε s : ℝ) : ℝ :=
  Real.exp (-s / ε) / ε

def erlangTwoKernel (ε s : ℝ) : ℝ :=
  s * Real.exp (-s / ε) / ε ^ 2

def erlangThreeKernel (ε s : ℝ) : ℝ :=
  s ^ 2 * Real.exp (-s / ε) / (2 * ε ^ 3)

def erlangWaveAmplitude (ε s : ℝ) : ℝ :=
  if 0 ≤ s then
    s * Real.exp (-s / (2 * ε)) / (Real.sqrt 2 * ε ^ (3 / 2 : ℝ))
  else 0

def erlangWaveAmplitudeDerivative (ε s : ℝ) : ℝ :=
  if 0 < s then
    Real.exp (-s / (2 * ε)) * (1 - s / (2 * ε)) /
      (Real.sqrt 2 * ε ^ (3 / 2 : ℝ))
  else 0

theorem erlangThreeKernel_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ erlangThreeKernel ε s := by
  unfold erlangThreeKernel
  positivity

theorem integral_Ioi_erlangThreeKernel_eq_one {ε : ℝ} (hε : 0 < ε) :
    (∫ s : ℝ in Ioi 0, erlangThreeKernel ε s) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := ε⁻¹) (by norm_num) (inv_pos.mpr hε)
  rw [show (3 : ℝ) - 1 = 2 by norm_num] at h
  have hmoment :
      (∫ s : ℝ in Ioi 0, s ^ 2 * Real.exp (-(ε⁻¹ * s))) = 2 * ε ^ 3 := by
    calc
      (∫ s : ℝ in Ioi 0, s ^ 2 * Real.exp (-(ε⁻¹ * s))) =
          (1 / ε⁻¹) ^ (3 : ℝ) * Real.Gamma 3 := by simpa using h
      _ = 2 * ε ^ 3 := by
        have hgamma : Real.Gamma 3 = 2 := by
          simpa using Real.Gamma_nat_eq_factorial 2
        rw [hgamma]
        norm_num [one_div, hε.ne']
        ring
  rw [show (∫ s : ℝ in Ioi 0, erlangThreeKernel ε s) =
      (2 * ε ^ 3)⁻¹ *
        ∫ s : ℝ in Ioi 0, s ^ 2 * Real.exp (-(ε⁻¹ * s)) by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    unfold erlangThreeKernel
    rw [show -s / ε = -(ε⁻¹ * s) by field_simp]
    ring]
  rw [hmoment]
  field_simp

theorem erlangWaveAmplitude_sq_eq_kernel {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : 0 ≤ s) :
    erlangWaveAmplitude ε s ^ 2 = erlangThreeKernel ε s := by
  unfold erlangWaveAmplitude erlangThreeKernel
  rw [if_pos hs]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hpow : ε ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_ne_zero hε.le (by norm_num)).2 hε.ne'
  have hden : (Real.sqrt 2 * ε ^ (3 / 2 : ℝ)) ^ 2 = 2 * ε ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_mul_natCast hε.le]
    norm_num
  rw [div_pow, mul_pow, ← Real.exp_nat_mul]
  have hexp : (2 : ℝ) * (-s / (2 * ε)) = -s / ε := by
    field_simp [hε.ne']
  norm_num only [Nat.cast_ofNat]
  rw [hexp, hden]

theorem integral_Ioi_erlangWaveAmplitude_sq_eq_one {ε : ℝ} (hε : 0 < ε) :
    (∫ s : ℝ in Ioi 0, erlangWaveAmplitude ε s ^ 2) = 1 := by
  rw [← integral_Ioi_erlangThreeKernel_eq_one hε]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact erlangWaveAmplitude_sq_eq_kernel hε hs.le

theorem integrableOn_erlangThreeKernel {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (erlangThreeKernel ε) (Ioi 0) := by
  have hmoment : IntegrableOn
      (fun s : ℝ => s ^ 2 * Real.exp (-(ε⁻¹ * s))) (Ioi 0) := by
    simpa [Real.rpow_two] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (2 : ℝ)) (b := ε⁻¹)
      (by norm_num) (by norm_num) (inv_pos.mpr hε)
  have hscaled : IntegrableOn
      (fun s : ℝ => 1 / (2 * ε ^ 3) *
        (s ^ 2 * Real.exp (-(ε⁻¹ * s)))) (Ioi 0) :=
    hmoment.const_mul (1 / (2 * ε ^ 3))
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro s _
  unfold erlangThreeKernel
  rw [show -s / ε = -(ε⁻¹ * s) by field_simp]
  ring

theorem integrableOn_sq_erlangWaveAmplitude {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => erlangWaveAmplitude ε s ^ 2) (Ioi 0) := by
  apply (integrableOn_erlangThreeKernel hε).congr_fun _ measurableSet_Ioi
  intro s hs
  exact (erlangWaveAmplitude_sq_eq_kernel hε hs.le).symm

theorem hasDerivAt_erlangWaveAmplitude_of_pos {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (erlangWaveAmplitude ε)
      (erlangWaveAmplitudeDerivative ε s) s := by
  have harg : HasDerivAt (fun t : ℝ => -t / (2 * ε)) (-1 / (2 * ε)) s := by
    simpa using (hasDerivAt_id s).neg.div_const (2 * ε)
  have hcore := ((hasDerivAt_id s).mul
    ((Real.hasDerivAt_exp (-s / (2 * ε))).comp s harg)).div_const
      (Real.sqrt 2 * ε ^ (3 / 2 : ℝ))
  have hlocal : (erlangWaveAmplitude ε) =ᶠ[𝓝 s]
      fun t => t * Real.exp (-t / (2 * ε)) /
        (Real.sqrt 2 * ε ^ (3 / 2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    simp [erlangWaveAmplitude, ht0]
  have hcore' : HasDerivAt
      (fun t => t * Real.exp (-t / (2 * ε)) /
        (Real.sqrt 2 * ε ^ (3 / 2 : ℝ)))
      ((1 * Real.exp (-s / (2 * ε)) +
        s * (Real.exp (-s / (2 * ε)) * (-1 / (2 * ε)))) /
          (Real.sqrt 2 * ε ^ (3 / 2 : ℝ))) s := by
    simpa only [id_eq, Function.comp_apply] using hcore
  have hfinal := hcore'.congr_of_eventuallyEq hlocal
  convert hfinal using 1
  simp [erlangWaveAmplitudeDerivative, hs]
  field_simp [hε.ne']
  ring

theorem integrableOn_sq_erlangWaveAmplitudeDerivative {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => erlangWaveAmplitudeDerivative ε s ^ 2) (Ioi 0) := by
  have hb : 0 < ε⁻¹ := inv_pos.mpr hε
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-(ε⁻¹ * s))) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (b := ε⁻¹) (by norm_num) (by norm_num) hb
  have h1 : IntegrableOn (fun s : ℝ => s * Real.exp (-(ε⁻¹ * s))) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := ε⁻¹) (by norm_num) (by norm_num) hb
  have h2 : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-(ε⁻¹ * s))) (Ioi 0) := by
    simpa [Real.rpow_two] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (2 : ℝ)) (b := ε⁻¹) (by norm_num) (by norm_num) hb
  have hsum : IntegrableOn
      (fun s : ℝ =>
        1 / (2 * ε ^ 3) * Real.exp (-(ε⁻¹ * s)) -
          1 / (2 * ε ^ 4) * (s * Real.exp (-(ε⁻¹ * s))) +
            1 / (8 * ε ^ 5) * (s ^ 2 * Real.exp (-(ε⁻¹ * s)))) (Ioi 0) :=
    ((h0.const_mul (1 / (2 * ε ^ 3))).sub
      (h1.const_mul (1 / (2 * ε ^ 4)))).add
        (h2.const_mul (1 / (8 * ε ^ 5)))
  apply hsum.congr_fun _ measurableSet_Ioi
  intro s hs
  have hs0 : 0 < s := hs
  simp only [erlangWaveAmplitudeDerivative, if_pos hs0]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hpow : ε ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_ne_zero hε.le (by norm_num)).2 hε.ne'
  have hden : (Real.sqrt 2 * ε ^ (3 / 2 : ℝ)) ^ 2 = 2 * ε ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_mul_natCast hε.le]
    norm_num
  rw [div_pow, mul_pow, ← Real.exp_nat_mul, hden]
  have hexp : (2 : ℝ) * (-s / (2 * ε)) = -(ε⁻¹ * s) := by
    field_simp [hε.ne']
  norm_num only [Nat.cast_ofNat]
  rw [hexp]
  field_simp [hε.ne']
  ring

/-- Concrete first-derivative-domain data for the one-sided packet.  The
amplitude vanishes at and below the lower edge, is normalized and square
integrable, has the displayed classical derivative off the edge, and that
derivative is square integrable.  These are the elementary `H¹` data used by
the time-pairing theorem below. -/
structure ErlangWavePacketFirstDerivativeData (ε : ℝ) : Prop where
  lowerEdge_zero : erlangWaveAmplitude ε 0 = 0
  below_lowerEdge_zero : ∀ {s : ℝ}, s < 0 → erlangWaveAmplitude ε s = 0
  amplitude_sq_integrable :
    IntegrableOn (fun s : ℝ => erlangWaveAmplitude ε s ^ 2) (Ioi 0)
  normalized : (∫ s : ℝ in Ioi 0, erlangWaveAmplitude ε s ^ 2) = 1
  hasDerivAt_of_pos : ∀ {s : ℝ}, 0 < s →
    HasDerivAt (erlangWaveAmplitude ε)
      (erlangWaveAmplitudeDerivative ε s) s
  derivative_sq_integrable :
    IntegrableOn (fun s : ℝ => erlangWaveAmplitudeDerivative ε s ^ 2) (Ioi 0)

theorem erlangWavePacket_firstDerivativeData {ε : ℝ} (hε : 0 < ε) :
    ErlangWavePacketFirstDerivativeData ε where
  lowerEdge_zero := by simp [erlangWaveAmplitude]
  below_lowerEdge_zero := by
    intro s hs
    simp [erlangWaveAmplitude, not_le.mpr hs]
  amplitude_sq_integrable := integrableOn_sq_erlangWaveAmplitude hε
  normalized := integral_Ioi_erlangWaveAmplitude_sq_eq_one hε
  hasDerivAt_of_pos := fun hs => hasDerivAt_erlangWaveAmplitude_of_pos hε hs
  derivative_sq_integrable := integrableOn_sq_erlangWaveAmplitudeDerivative hε

def scalarTimePairingIntegrand
    (ψ ψ' : ℝ → ℂ) (E : ℝ) : ℂ :=
  star (ψ E) * (-Complex.I * ψ' E)

def scalarWignerSmithDelay
    (S S' : ℝ → ℂ) (E : ℝ) : ℂ :=
  -Complex.I * star (S E) * S' E

def erlangComplexWaveAmplitude (ε s : ℝ) : ℂ :=
  erlangWaveAmplitude ε s

def erlangComplexWaveAmplitudeDerivative (ε s : ℝ) : ℂ :=
  erlangWaveAmplitudeDerivative ε s

theorem scalarWignerSmith_timePairing_integrand
    {S S' ψ ψ' : ℝ → ℂ} {E : ℝ}
    (hunit : star (S E) * S E = 1) :
    scalarTimePairingIntegrand (fun t => S t * ψ t)
        (fun t => S' t * ψ t + S t * ψ' t) E -
      scalarTimePairingIntegrand ψ ψ' E =
        star (ψ E) * ψ E * scalarWignerSmithDelay S S' E := by
  simp only [scalarTimePairingIntegrand, scalarWignerSmithDelay]
  rw [star_mul]
  linear_combination (star (ψ E) * (-Complex.I * ψ' E)) * hunit

theorem scalarWignerSmith_timePairing_integral
    {S S' ψ ψ' : ℝ → ℂ} {A : Set ℝ}
    (hA : MeasurableSet A)
    (hunit : ∀ E ∈ A, star (S E) * S E = 1)
    (hscattered : IntegrableOn
      (scalarTimePairingIntegrand (fun t => S t * ψ t)
        (fun t => S' t * ψ t + S t * ψ' t)) A)
    (hfree : IntegrableOn (scalarTimePairingIntegrand ψ ψ') A) :
    (∫ E in A, scalarTimePairingIntegrand (fun t => S t * ψ t)
        (fun t => S' t * ψ t + S t * ψ' t) E) -
      ∫ E in A, scalarTimePairingIntegrand ψ ψ' E =
        ∫ E in A, star (ψ E) * ψ E * scalarWignerSmithDelay S S' E := by
  rw [← MeasureTheory.integral_sub hscattered hfree]
  apply setIntegral_congr_fun hA
  intro E hE
  exact scalarWignerSmith_timePairing_integrand (hunit E hE)

/-- **Ladder derivative of the Erlang power kernel.**  Differentiating `s ↦ s^k e^{-s/ε} / c` moves
one step down the Erlang ladder and subtracts a copy of itself scaled by `1/ε`.  The statement is
uniform in `k`: no `1 ≤ k` side condition is needed, because the cast `((0 : ℕ) : ℝ) = 0` annihilates
the first term and the truncated subtraction `0 - 1 = 0` is therefore harmless. -/
theorem hasDerivAt_powExpKernel {ε : ℝ} (hε : ε ≠ 0) (k : ℕ) (c : ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ k * Real.exp (-t / ε) / c)
      ((k : ℝ) * (s ^ (k - 1) * Real.exp (-s / ε) / c)
        - (s ^ k * Real.exp (-s / ε) / c) / ε) s := by
  have harg : HasDerivAt (fun t : ℝ => -t / ε) (-1 / ε) s := by
    simpa using (hasDerivAt_id s).neg.div_const ε
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t / ε))
      (Real.exp (-s / ε) * (-1 / ε)) s := by
    simpa using (Real.hasDerivAt_exp (-s / ε)).comp s harg
  have h := ((hasDerivAt_pow k s).mul hexp).div_const c
  convert h using 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
    field_simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hk1 : s ^ (m + 1) = s * s ^ m := by rw [pow_succ']
    field_simp
    rw [hk1]
    ring

theorem hasDerivAt_erlangOneKernel {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (erlangOneKernel ε)
      (-erlangOneKernel ε s / ε) s := by
  have h := hasDerivAt_powExpKernel (ε := ε) hε.ne' 0 ε s
  have hfun : (fun t : ℝ => t ^ 0 * Real.exp (-t / ε) / ε) = erlangOneKernel ε := by
    funext t; simp [erlangOneKernel]
  rw [hfun] at h
  convert h using 1
  simp [erlangOneKernel]
  field_simp

theorem hasDerivAt_erlangTwoKernel {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (erlangTwoKernel ε)
      ((erlangOneKernel ε s - erlangTwoKernel ε s) / ε) s := by
  have h := hasDerivAt_powExpKernel (ε := ε) hε.ne' 1 (ε ^ 2) s
  have hfun : (fun t : ℝ => t ^ 1 * Real.exp (-t / ε) / ε ^ 2) = erlangTwoKernel ε := by
    funext t; simp [erlangTwoKernel]
  rw [hfun] at h
  convert h using 1
  simp only [erlangOneKernel, erlangTwoKernel, pow_one, Nat.cast_one, one_mul,
    Nat.sub_self, pow_zero]
  field_simp

theorem hasDerivAt_erlangThreeKernel {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (erlangThreeKernel ε)
      ((erlangTwoKernel ε s - erlangThreeKernel ε s) / ε) s := by
  have h := hasDerivAt_powExpKernel (ε := ε) hε.ne' 2 (2 * ε ^ 3) s
  have hfun : (fun t : ℝ => t ^ 2 * Real.exp (-t / ε) / (2 * ε ^ 3)) =
      erlangThreeKernel ε := by
    funext t; simp [erlangThreeKernel]
  rw [hfun] at h
  convert h using 1
  simp only [erlangTwoKernel, erlangThreeKernel, Nat.cast_ofNat]
  field_simp
  ring

def erlangAverageOne (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, erlangOneKernel ε s * f (x + s)

def erlangAverageTwo (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, erlangTwoKernel ε s * f (x + s)

def erlangAverageThree (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, erlangThreeKernel ε s * f (x + s)

def erlangFirstOrderRecover (ε : ℝ) (R : ℝ → ℝ) : ℝ → ℝ :=
  fun x => R x - ε * deriv R x

/-- Exact analytic hypotheses used by the half-line integration-by-parts
proof.  These are convergence and differentiation-under-the-integral
hypotheses, not the recovery conclusion. -/
structure ErlangRecoveryAdmissible (ε : ℝ) (f f' : ℝ → ℝ) : Prop where
  source_hasDeriv : ∀ x, HasDerivAt f (f' x) x
  integrable_one : ∀ x, IntegrableOn
    (fun s => erlangOneKernel ε s * f (x + s)) (Ioi 0)
  integrable_one_deriv : ∀ x, IntegrableOn
    (fun s => erlangOneKernel ε s * f' (x + s)) (Ioi 0)
  integrable_two : ∀ x, IntegrableOn
    (fun s => erlangTwoKernel ε s * f (x + s)) (Ioi 0)
  integrable_two_deriv : ∀ x, IntegrableOn
    (fun s => erlangTwoKernel ε s * f' (x + s)) (Ioi 0)
  integrable_three : ∀ x, IntegrableOn
    (fun s => erlangThreeKernel ε s * f (x + s)) (Ioi 0)
  integrable_three_deriv : ∀ x, IntegrableOn
    (fun s => erlangThreeKernel ε s * f' (x + s)) (Ioi 0)
  boundary_one_zero : ∀ x, Tendsto
    (fun s => erlangOneKernel ε s * f (x + s)) (𝓝[>] 0) (𝓝 (f x / ε))
  boundary_two_zero : ∀ x, Tendsto
    (fun s => erlangTwoKernel ε s * f (x + s)) (𝓝[>] 0) (𝓝 0)
  boundary_three_zero : ∀ x, Tendsto
    (fun s => erlangThreeKernel ε s * f (x + s)) (𝓝[>] 0) (𝓝 0)
  boundary_one_top : ∀ x, Tendsto
    (fun s => erlangOneKernel ε s * f (x + s)) atTop (𝓝 0)
  boundary_two_top : ∀ x, Tendsto
    (fun s => erlangTwoKernel ε s * f (x + s)) atTop (𝓝 0)
  boundary_three_top : ∀ x, Tendsto
    (fun s => erlangThreeKernel ε s * f (x + s)) atTop (𝓝 0)
  average_one_hasDeriv : ∀ x,
    HasDerivAt (erlangAverageOne ε f) (erlangAverageOne ε f' x) x
  average_two_hasDeriv : ∀ x,
    HasDerivAt (erlangAverageTwo ε f) (erlangAverageTwo ε f' x) x
  average_three_hasDeriv : ∀ x,
    HasDerivAt (erlangAverageThree ε f) (erlangAverageThree ε f' x) x

private theorem hasDerivAt_shift
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x s : ℝ) :
    HasDerivAt (fun t => f (x + t)) (f' (x + s)) s := by
  have hadd : HasDerivAt (fun t : ℝ => x + t) 1 s := by
    simpa using (hasDerivAt_const s x).add (hasDerivAt_id s)
  simpa only [Function.comp_apply, mul_one] using (hf (x + s)).comp s hadd

theorem erlangAverageOne_integral_recovery
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') (x : ℝ) :
    erlangAverageOne ε f x - ε * erlangAverageOne ε f' x = f x := by
  let u' : ℝ → ℝ := fun s => -erlangOneKernel ε s / ε
  have hu'v : IntegrableOn
      (fun s => u' s * f (x + s)) (Ioi 0) := by
    have hi := (h.integrable_one x).const_mul (-1 / ε)
    simpa [u', div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := f x / ε) (b' := 0)
    (u := erlangOneKernel ε) (u' := u')
    (v := fun s => f (x + s)) (v' := fun s => f' (x + s))
    (fun s _ => hasDerivAt_erlangOneKernel hε s)
    (fun s _ => hasDerivAt_shift h.source_hasDeriv x s)
    (h.integrable_one_deriv x) hu'v
    (h.boundary_one_zero x) (h.boundary_one_top x)
  have hu'int :
      (∫ s : ℝ in Ioi 0, u' s * f (x + s)) =
        (-1 / ε) * erlangAverageOne ε f x := by
    rw [erlangAverageOne, ← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp [u']
    ring
  change erlangAverageOne ε f' x =
      0 - f x / ε - ∫ s : ℝ in Ioi 0, u' s * f (x + s) at hibp
  rw [hu'int] at hibp
  field_simp [hε.ne'] at hibp ⊢
  linarith

theorem erlangAverageTwo_integral_recovery
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') (x : ℝ) :
    erlangAverageTwo ε f x - ε * erlangAverageTwo ε f' x =
      erlangAverageOne ε f x := by
  let u' : ℝ → ℝ := fun s =>
    (erlangOneKernel ε s - erlangTwoKernel ε s) / ε
  have hu'v : IntegrableOn
      (fun s => u' s * f (x + s)) (Ioi 0) := by
    have hi := ((h.integrable_one x).sub (h.integrable_two x)).const_mul (1 / ε)
    apply hi.congr
    filter_upwards with s
    dsimp [u']
    ring
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := 0) (b' := 0)
    (u := erlangTwoKernel ε) (u' := u')
    (v := fun s => f (x + s)) (v' := fun s => f' (x + s))
    (fun s _ => hasDerivAt_erlangTwoKernel hε s)
    (fun s _ => hasDerivAt_shift h.source_hasDeriv x s)
    (h.integrable_two_deriv x) hu'v
    (h.boundary_two_zero x) (h.boundary_two_top x)
  have hu'int :
      (∫ s : ℝ in Ioi 0, u' s * f (x + s)) =
        (1 / ε) * (erlangAverageOne ε f x - erlangAverageTwo ε f x) := by
    rw [show (fun s => u' s * f (x + s)) =
        fun s => (1 / ε) *
          (erlangOneKernel ε s * f (x + s) -
            erlangTwoKernel ε s * f (x + s)) by
      funext s
      dsimp [u']
      ring]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (h.integrable_one x) (h.integrable_two x),
      erlangAverageOne, erlangAverageTwo]
  change erlangAverageTwo ε f' x =
      0 - 0 - ∫ s : ℝ in Ioi 0, u' s * f (x + s) at hibp
  rw [hu'int] at hibp
  field_simp [hε.ne'] at hibp ⊢
  linarith

theorem erlangAverageThree_integral_recovery
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') (x : ℝ) :
    erlangAverageThree ε f x - ε * erlangAverageThree ε f' x =
      erlangAverageTwo ε f x := by
  let u' : ℝ → ℝ := fun s =>
    (erlangTwoKernel ε s - erlangThreeKernel ε s) / ε
  have hu'v : IntegrableOn
      (fun s => u' s * f (x + s)) (Ioi 0) := by
    have hi := ((h.integrable_two x).sub (h.integrable_three x)).const_mul (1 / ε)
    apply hi.congr
    filter_upwards with s
    dsimp [u']
    ring
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := 0) (b' := 0)
    (u := erlangThreeKernel ε) (u' := u')
    (v := fun s => f (x + s)) (v' := fun s => f' (x + s))
    (fun s _ => hasDerivAt_erlangThreeKernel hε s)
    (fun s _ => hasDerivAt_shift h.source_hasDeriv x s)
    (h.integrable_three_deriv x) hu'v
    (h.boundary_three_zero x) (h.boundary_three_top x)
  have hu'int :
      (∫ s : ℝ in Ioi 0, u' s * f (x + s)) =
        (1 / ε) * (erlangAverageTwo ε f x - erlangAverageThree ε f x) := by
    rw [show (fun s => u' s * f (x + s)) =
        fun s => (1 / ε) *
          (erlangTwoKernel ε s * f (x + s) -
            erlangThreeKernel ε s * f (x + s)) by
      funext s
      dsimp [u']
      ring]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (h.integrable_two x) (h.integrable_three x),
      erlangAverageTwo, erlangAverageThree]
  change erlangAverageThree ε f' x =
      0 - 0 - ∫ s : ℝ in Ioi 0, u' s * f (x + s) at hibp
  rw [hu'int] at hibp
  field_simp [hε.ne'] at hibp ⊢
  linarith

theorem erlangFirstOrderRecover_averageOne
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') :
    erlangFirstOrderRecover ε (erlangAverageOne ε f) = f := by
  funext x
  unfold erlangFirstOrderRecover
  rw [(h.average_one_hasDeriv x).deriv]
  exact erlangAverageOne_integral_recovery hε h x

theorem erlangFirstOrderRecover_averageTwo
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') :
    erlangFirstOrderRecover ε (erlangAverageTwo ε f) = erlangAverageOne ε f := by
  funext x
  unfold erlangFirstOrderRecover
  rw [(h.average_two_hasDeriv x).deriv]
  exact erlangAverageTwo_integral_recovery hε h x

theorem erlangFirstOrderRecover_averageThree
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') :
    erlangFirstOrderRecover ε (erlangAverageThree ε f) = erlangAverageTwo ε f := by
  funext x
  unfold erlangFirstOrderRecover
  rw [(h.average_three_hasDeriv x).deriv]
  exact erlangAverageThree_integral_recovery hε h x

/-- The exact third-order Erlang recovery identity `(1-εD)^3 R = f`. -/
theorem erlangAverageThree_exact_recovery
    {ε : ℝ} (hε : 0 < ε) {f f' : ℝ → ℝ}
    (h : ErlangRecoveryAdmissible ε f f') :
    erlangFirstOrderRecover ε
        (erlangFirstOrderRecover ε
          (erlangFirstOrderRecover ε (erlangAverageThree ε f))) = f := by
  rw [erlangFirstOrderRecover_averageThree hε h,
    erlangFirstOrderRecover_averageTwo hε h,
    erlangFirstOrderRecover_averageOne hε h]

theorem erlangWavePacket_timePairing_eq_averageThree
    {ε : ℝ} (hε : 0 < ε) (x : ℝ)
    {S S' : ℝ → ℂ} {Q : ℝ → ℝ}
    (hunit : ∀ E : ℝ, star (S E) * S E = 1)
    (hQ : ∀ E : ℝ, scalarWignerSmithDelay S S' E = Q E)
    (hscattered : IntegrableOn
      (scalarTimePairingIntegrand
        (fun s => S (x + s) * erlangComplexWaveAmplitude ε s)
        (fun s => S' (x + s) * erlangComplexWaveAmplitude ε s +
          S (x + s) * erlangComplexWaveAmplitudeDerivative ε s)) (Ioi 0))
    (hfree : IntegrableOn
      (scalarTimePairingIntegrand (erlangComplexWaveAmplitude ε)
        (erlangComplexWaveAmplitudeDerivative ε)) (Ioi 0)) :
    (∫ s in Ioi 0, scalarTimePairingIntegrand
        (fun t => S (x + t) * erlangComplexWaveAmplitude ε t)
        (fun t => S' (x + t) * erlangComplexWaveAmplitude ε t +
          S (x + t) * erlangComplexWaveAmplitudeDerivative ε t) s) -
      ∫ s in Ioi 0, scalarTimePairingIntegrand
        (erlangComplexWaveAmplitude ε)
        (erlangComplexWaveAmplitudeDerivative ε) s =
        erlangAverageThree ε Q x := by
  rw [scalarWignerSmith_timePairing_integral measurableSet_Ioi
    (fun s _ => hunit (x + s)) hscattered hfree]
  rw [erlangAverageThree]
  calc
    (∫ s in Ioi 0, star (erlangComplexWaveAmplitude ε s) *
        erlangComplexWaveAmplitude ε s *
          scalarWignerSmithDelay (fun t => S (x + t))
            (fun t => S' (x + t)) s) =
        ∫ s in Ioi 0, ((erlangThreeKernel ε s * Q (x + s) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change star (erlangComplexWaveAmplitude ε s) *
          erlangComplexWaveAmplitude ε s * scalarWignerSmithDelay S S' (x + s) =
        ((erlangThreeKernel ε s * Q (x + s) : ℝ) : ℂ)
      rw [hQ]
      simp only [erlangComplexWaveAmplitude, Complex.star_def,
        Complex.conj_ofReal, Complex.ofReal_mul]
      norm_cast
      rw [← pow_two (erlangWaveAmplitude ε s),
        erlangWaveAmplitude_sq_eq_kernel hε hs.le]
    _ = (∫ s in Ioi 0, erlangThreeKernel ε s * Q (x + s)) := by
      exact _root_.integral_ofReal


/-! ## Differential-algebraic recovery -/

def erlangThirdRecoveryElement
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (ε : F) (r : E) : E :=
  r - 3 * algebraMap F E ε * differentialJet 1 r +
    3 * (algebraMap F E ε) ^ 2 * differentialJet 2 r -
      (algebraMap F E ε) ^ 3 * differentialJet 3 r

theorem differentialAlgebraicOver_erlangThirdRecoveryElement
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (ε : F) {r : E} (hr : DifferentialAlgebraicOver F r) :
    DifferentialAlgebraicOver F (erlangThirdRecoveryElement ε r) := by
  have hε := differentialAlgebraicOver_algebraMap (F := F) (E := E) ε
  have h1 := differentialAlgebraicOver_deriv hr
  have h2 := differentialAlgebraicOver_deriv h1
  have h3 := differentialAlgebraicOver_deriv h2
  have hj1 : DifferentialAlgebraicOver F (differentialJet 1 r) := by simpa using h1
  have hj2 : DifferentialAlgebraicOver F (differentialJet 2 r) := by
    simpa [differentialJet_succ] using h2
  have hj3 : DifferentialAlgebraicOver F (differentialJet 3 r) := by
    simpa [differentialJet_succ] using h3
  have hthree : DifferentialAlgebraicOver F (3 : E) := by
    simpa only [map_ofNat] using
      differentialAlgebraicOver_algebraMap (F := F) (E := E) (3 : F)
  unfold erlangThirdRecoveryElement
  exact differentialAlgebraicOver_sub
    (differentialAlgebraicOver_add
      (differentialAlgebraicOver_sub hr
        (differentialAlgebraicOver_mul
          (differentialAlgebraicOver_mul
            hthree hε) hj1))
      (differentialAlgebraicOver_mul
        (differentialAlgebraicOver_mul
          hthree
          (differentialAlgebraicOver_pow hε 2)) hj2))
    (differentialAlgebraicOver_mul (differentialAlgebraicOver_pow hε 3) hj3)

theorem differentialAlgebraicOver_of_erlangThirdRecoveryElement_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (ε : F) (hε : ε ≠ 0) {q r : E}
    (hq : DifferentialAlgebraicOver F q)
    (hrel : erlangThirdRecoveryElement ε r = q) :
    DifferentialAlgebraicOver F r := by
  let B := differentialAdjoin F ({q} : Set E)
  let εB : B := algebraMap F B ε
  let qB : B := ⟨q, subset_differentialAdjoin F ({q} : Set E) rfl⟩
  let P : MvPolynomial (Fin 4) B :=
    MvPolynomial.X 0 - MvPolynomial.C (3 * εB) * MvPolynomial.X 1 +
      MvPolynomial.C (3 * εB ^ 2) * MvPolynomial.X 2 -
        MvPolynomial.C (εB ^ 3) * MvPolynomial.X 3 - MvPolynomial.C qB
  have hεB : εB ≠ 0 := by
    intro hzero
    apply hε
    apply (algebraMap F B).injective
    simpa [εB] using hzero
  have hP : P ≠ 0 := by
    intro hzero
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.single (3 : Fin 4) 1)) hzero
    simp only [P, MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_single_X,
      MvPolynomial.coeff_C] at hc
    norm_num at hc
    have hsingle : (0 : Fin 4 →₀ ℕ) ≠
        Finsupp.single (3 : Fin 4) 1 := by
      intro heq
      have := congrArg (fun f : Fin 4 →₀ ℕ => f (3 : Fin 4)) heq
      simp at this
    rw [if_neg hsingle] at hc
    have h03 : (0 : Fin 4) ≠ 3 := by decide
    have h13 : (1 : Fin 4) ≠ 3 := by decide
    have h23 : (2 : Fin 4) ≠ 3 := by decide
    simp [h03, h13, h23] at hc
    exact hεB hc
  apply differentialAlgebraicOver_of_finiteJetConstraint_over_singleton hq hP
  change MvPolynomial.aeval
    (fun j : Fin 4 => differentialJet (j : ℕ) r) P = 0
  simp [P, εB, qB]
  rw [← hrel]
  simp [erlangThirdRecoveryElement]
  have hthreeB : ((3 : B) : E) = (3 : E) := by
    change (3 : E) = 3
    rfl
  rw [hthreeB]
  ring

theorem hypertranscendentalOver_erlangThirdRecoveryElement_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (ε : F) (hε : ε ≠ 0) {q r : E}
    (hrel : erlangThirdRecoveryElement ε r = q) :
    HypertranscendentalOver F r ↔ HypertranscendentalOver F q := by
  constructor
  · intro hr hq
    exact hr (differentialAlgebraicOver_of_erlangThirdRecoveryElement_eq ε hε hq hrel)
  · intro hq hr
    exact hq (hrel ▸ differentialAlgebraicOver_erlangThirdRecoveryElement ε hr)

end

end GaloisForLFunctions.HTGeometry
