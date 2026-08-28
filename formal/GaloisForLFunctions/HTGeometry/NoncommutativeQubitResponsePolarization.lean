import GaloisForLFunctions.HTGeometry.NoncommutativeQubitExponentialFormation
import GaloisForLFunctions.HTGeometry.ResponsePolarizationFisherTailJeffreysEscape
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.HTGeometry.MonotoneSymbolTailEstimate
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.HTGeometry.LogMaxSublinear
import GaloisForLFunctions.HTGeometry.PowerTailAsymptotics
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Noncommutative qubit response polarization

Exact BKM response of the transverse Pauli exponential family, cubic response and finite Fisher
completion, diagonal-observer quartic response, logarithmic observed work, and linear hidden deficit.
-/

open Filter MeasureTheory Set Topology
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-dimensional Bogoliubov--Kubo--Mori response of the qubit family. -/
def qubitResponse (b t : ℝ) : ℝ :=
  b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) +
    t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2

/-- Probability of the `Z=+1` outcome under diagonal observation. -/
def qubitObservedProbability (b t : ℝ) : ℝ :=
  (1 + qubitMean b t) / 2

/-- Classical Fisher response of the observed Bernoulli family. -/
def qubitObservedResponse (b t : ℝ) : ℝ :=
  qubitResponse b t ^ 2 / (1 - qubitMean b t ^ 2)

/-- Reflected complete quantum work. -/
def qubitReflectedQuantumWork (b t : ℝ) : ℝ :=
  qubitQuantumJeffreys b t (-t)

/-- Reflected Jeffreys work of the diagonal Bernoulli observer. -/
def qubitObservedWork (b t : ℝ) : ℝ :=
  2 * qubitMean b t *
    Real.log ((1 + qubitMean b t) / (1 - qubitMean b t))

/-- Complete quantum work missing from diagonal observation. -/
def qubitMeasurementDeficit (b t : ℝ) : ℝ :=
  qubitReflectedQuantumWork b t - qubitObservedWork b t

/-- Classical relative entropy of two Bernoulli laws. -/
def bernoulliRelativeEntropy (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Symmetrized relative entropy of two Bernoulli laws. -/
def bernoulliJeffreys (p q : ℝ) : ℝ :=
  bernoulliRelativeEntropy p q + bernoulliRelativeEntropy q p

theorem bernoulliJeffreys_reflection_eq {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliJeffreys p (1 - p) =
      2 * (2 * p - 1) * Real.log (p / (1 - p)) := by
  have hp0 : p ≠ 0 := hp.ne'
  have h1p0 : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hratio : (1 - p) / p = (p / (1 - p))⁻¹ := by
    field_simp
  rw [bernoulliJeffreys, bernoulliRelativeEntropy,
    bernoulliRelativeEntropy]
  simp only [sub_sub_cancel]
  rw [hratio, Real.log_inv]
  ring

theorem qubitRadius_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitRadius b u) (t / qubitRadius b t) t := by
  have hpoly : HasDerivAt (fun u : ℝ => u ^ 2 + b ^ 2) (2 * t) t := by
    simpa [id_eq] using
      ((hasDerivAt_id t).pow 2).add_const (b ^ 2)
  have harg : t ^ 2 + b ^ 2 ≠ 0 := by positivity
  have h := (Real.hasDerivAt_sqrt harg).comp t hpoly
  have hcoef : 1 / (2 * Real.sqrt (t ^ 2 + b ^ 2)) * (2 * t) =
      t / qubitRadius b t := by
    rw [qubitRadius]
    have hsqrt : Real.sqrt (t ^ 2 + b ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by positivity)
    field_simp
  simpa [qubitRadius, Function.comp_def] using h.congr_deriv hcoef

theorem qubitFreeEnergy_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitFreeEnergy b u) (qubitMean b t) t := by
  have hr := qubitRadius_hasDerivAt hb t
  have hcosh := hr.cosh.const_mul 2
  have hlog := hcosh.log
    (show 2 * Real.cosh (qubitRadius b t) ≠ 0 by positivity)
  have hcoef : (2 * (Real.sinh (qubitRadius b t) *
      (t / qubitRadius b t))) / (2 * Real.cosh (qubitRadius b t)) =
      qubitMean b t := by
    rw [qubitMean, Real.tanh_eq_sinh_div_cosh]
    field_simp [(qubitRadius_pos hb t).ne', (Real.cosh_pos _).ne']
  simpa [qubitFreeEnergy, Function.comp_def] using hlog.congr_deriv hcoef

theorem qubitMean_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitMean b u) (qubitResponse b t) t := by
  have hr := qubitRadius_hasDerivAt hb t
  have hr0 : qubitRadius b t ≠ 0 := (qubitRadius_pos hb t).ne'
  have hratio := (hasDerivAt_id t).div hr hr0
  have htanh := (HTGeometry.hasDerivAt_tanh (qubitRadius b t)).comp t hr
  have h := hratio.mul htanh
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hb2 : b ^ 2 = qubitRadius b t ^ 2 - t ^ 2 := by
    nlinarith [hr2]
  have hcoef :
      ((1 * qubitRadius b t - t * (t / qubitRadius b t)) /
          qubitRadius b t ^ 2) * Real.tanh (qubitRadius b t) +
        (t / qubitRadius b t) *
          (1 / Real.cosh (qubitRadius b t) ^ 2 *
            (t / qubitRadius b t)) = qubitResponse b t := by
    rw [qubitResponse, hb2]
    field_simp [hr0, (Real.cosh_pos _).ne']
  refine (h.congr_deriv hcoef).congr_of_eventuallyEq ?_
  filter_upwards with u
  simp only [qubitMean, Function.comp_apply, id_eq, Pi.div_apply, Pi.mul_apply]

theorem qubitResponse_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitResponse b t := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htanh : 0 < Real.tanh (qubitRadius b t) := by
    have h := HTGeometry.tanh_strictMono hr
    simpa only [Real.tanh_zero] using h
  rw [qubitResponse]
  positivity

theorem continuous_qubitResponse {b : ℝ} (hb : 0 < b) :
    Continuous (qubitResponse b) := by
  have hrC : Continuous (fun t : ℝ => qubitRadius b t) := by
    change Continuous (fun t : ℝ => Real.sqrt (t ^ 2 + b ^ 2))
    fun_prop
  have htanhC : Continuous Real.tanh := by
    rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')
  have hcoshC : Continuous (fun t : ℝ => Real.cosh (qubitRadius b t)) :=
    Real.continuous_cosh.comp hrC
  change Continuous (fun t : ℝ =>
    b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) +
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2)
  exact (((continuous_const.pow 2).div (hrC.pow 3)
      (fun t => pow_ne_zero 3 (qubitRadius_pos hb t).ne')).mul
        (htanhC.comp hrC)).add
    (((continuous_id.pow 2).div (hrC.pow 2)
      (fun t => pow_ne_zero 2 (qubitRadius_pos hb t).ne')).div
        (hcoshC.pow 2) (fun t => pow_ne_zero 2 (Real.cosh_pos _).ne'))

theorem integral_qubitResponse {b : ℝ} (hb : 0 < b) (a c : ℝ) :
    (∫ t : ℝ in a..c, qubitResponse b t) =
      qubitMean b c - qubitMean b a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => qubitMean_hasDerivAt hb t)
    ((continuous_qubitResponse hb).intervalIntegrable a c)

theorem qubitQuantumJeffreys_eq_integral {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    qubitQuantumJeffreys b s t =
      |s - t| * ∫ u : ℝ in min s t..max s t, qubitResponse b u := by
  rw [qubitQuantumJeffreys_eq hb, integral_qubitResponse hb]
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, max_eq_right hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [min_eq_right hts, max_eq_left hts, abs_of_nonneg (sub_nonneg.mpr hts)]

@[simp] theorem qubitRadius_neg (b t : ℝ) :
    qubitRadius b (-t) = qubitRadius b t := by
  simp [qubitRadius]

@[simp] theorem qubitMean_neg (b t : ℝ) :
    qubitMean b (-t) = -qubitMean b t := by
  rw [qubitMean, qubitMean, qubitRadius_neg]
  ring

@[simp] theorem qubitResponse_neg (b t : ℝ) :
    qubitResponse b (-t) = qubitResponse b t := by
  simp [qubitResponse]

theorem abs_lt_qubitRadius {b : ℝ} (hb : 0 < b) (t : ℝ) :
    |t| < qubitRadius b t := by
  rw [qubitRadius, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg t) (by nlinarith [sq_pos_of_pos hb])

theorem tendsto_qubitRadius_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitRadius b) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  filter_upwards [eventually_ge_atTop (max A 0)] with t ht
  have htA : A ≤ t := (le_max_left A 0).trans ht
  have ht0 : 0 ≤ t := (le_max_right A 0).trans ht
  exact htA.trans ((le_abs_self t).trans (abs_lt_qubitRadius hb t).le)

theorem tendsto_qubitRadius_div_self {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitRadius b t / t) atTop (𝓝 1) := by
  have hbt : Tendsto (fun t : ℝ => b / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (1 + (b / t) ^ 2))
      atTop (𝓝 1) := by
    simpa using (hone.add (hbt.pow 2)).sqrt
  refine hroot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hlhs0 : 0 ≤ qubitRadius b t / t := div_nonneg (qubitRadius_pos hb t).le ht.le
  have hrhs0 : 0 ≤ Real.sqrt (1 + (b / t) ^ 2) := Real.sqrt_nonneg _
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hlhs2 : (qubitRadius b t / t) ^ 2 = 1 + (b / t) ^ 2 := by
    field_simp
    nlinarith [hr2]
  have hrhs2 : Real.sqrt (1 + (b / t) ^ 2) ^ 2 = 1 + (b / t) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith

theorem tendsto_self_div_qubitRadius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t / qubitRadius b t) atTop (𝓝 1) := by
  have h := (tendsto_qubitRadius_div_self hb).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using h

private theorem tanh_eq_expNegTwoRatio (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have hexp : Real.exp (-(2 * x)) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [Real.tanh_eq, hexp]
  field_simp [Real.exp_ne_zero x, Real.exp_ne_zero (-x)]

theorem tendsto_tanh_atTop_one : Tendsto Real.tanh atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero (by norm_num)
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := (hone.sub he).div (hone.add he)
    (by norm_num : (1 + (0 : ℝ)) ≠ 0)
  have h' : Tendsto
      ((fun x : ℝ => 1 - Real.exp (-(2 * x))) /
        (fun x : ℝ => 1 + Real.exp (-(2 * x)))) atTop (𝓝 1) := by
    simpa only [sub_zero, add_zero, div_one] using h
  rw [show Real.tanh = fun x : ℝ =>
    (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) by
      funext x
      exact tanh_eq_expNegTwoRatio x]
  refine h'.congr' ?_
  filter_upwards with x
  rfl

theorem tendsto_tanh_qubitRadius_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.tanh (qubitRadius b t)) atTop (𝓝 1) :=
  tendsto_tanh_atTop_one.comp (tendsto_qubitRadius_atTop hb)

private def qubitTanhRatio (x : ℝ) : ℝ := Real.tanh x / x

private theorem qubitTanhRatio_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt qubitTanhRatio
      ((x / Real.cosh x ^ 2 - Real.tanh x) / x ^ 2) x := by
  have h := (HTGeometry.hasDerivAt_tanh x).div (hasDerivAt_id x) hx.ne'
  have hcoef :
      (1 / Real.cosh x ^ 2 * x - Real.tanh x * 1) / x ^ 2 =
        (x / Real.cosh x ^ 2 - Real.tanh x) / x ^ 2 := by
    field_simp
  refine (h.congr_deriv hcoef).congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

theorem qubitTanhRatio_antitoneOn : AntitoneOn qubitTanhRatio (Ioi 0) := by
  have hderivNonpos : ∀ x ∈ Ioi (0 : ℝ),
      ((x / Real.cosh x ^ 2 - Real.tanh x) / x ^ 2) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := hx
    have hc : 0 < Real.cosh x := Real.cosh_pos x
    have hs : 0 ≤ Real.sinh x :=
      hx0.le.trans (HTGeometry.self_le_sinh_of_nonneg hx0.le)
    have hxc : x ≤ Real.sinh x * Real.cosh x := by
      calc
        x ≤ Real.sinh x := HTGeometry.self_le_sinh_of_nonneg hx0.le
        _ ≤ Real.sinh x * Real.cosh x := by
          nlinarith [Real.one_le_cosh x]
    have hsinhDiv : Real.sinh x / Real.cosh x =
        (Real.sinh x * Real.cosh x) / Real.cosh x ^ 2 := by
      field_simp [hc.ne']
    have hnum : x / Real.cosh x ^ 2 - Real.tanh x ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, hsinhDiv]
      apply sub_nonpos.mpr
      rw [div_le_div_iff₀ (sq_pos_of_pos hc) (sq_pos_of_pos hc)]
      gcongr
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg x)
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · intro x hx
    exact (qubitTanhRatio_hasDerivAt hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    exact (qubitTanhRatio_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(qubitTanhRatio_hasDerivAt hx).deriv]
    exact hderivNonpos x hx

theorem qubitMean_le_tanh {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    qubitMean b t ≤ Real.tanh t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [qubitMean]
  · have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
    have htr : t ≤ qubitRadius b t :=
      (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
    have hratio : qubitTanhRatio (qubitRadius b t) ≤ qubitTanhRatio t :=
      qubitTanhRatio_antitoneOn ht hr htr
    calc
      qubitMean b t = t * qubitTanhRatio (qubitRadius b t) := by
        rw [qubitMean, qubitTanhRatio]
        ring
      _ ≤ t * qubitTanhRatio t := mul_le_mul_of_nonneg_left hratio ht.le
      _ = Real.tanh t := by
        rw [qubitTanhRatio]
        field_simp [ht.ne']

theorem tendsto_qubitMean_atTop_one {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitMean b) atTop (𝓝 1) := by
  change Tendsto (fun t : ℝ => t / qubitRadius b t *
    Real.tanh (qubitRadius b t)) atTop (𝓝 1)
  simpa only [mul_one] using
    (tendsto_self_div_qubitRadius hb).mul (tendsto_tanh_qubitRadius_atTop hb)

/-- Transverse Pauli-`X` coordinate of the qubit density. -/
def qubitTransverseMean (b t : ℝ) : ℝ :=
  b / qubitRadius b t * Real.tanh (qubitRadius b t)

@[simp] theorem qubitTransverseMean_neg (b t : ℝ) :
    qubitTransverseMean b (-t) = qubitTransverseMean b t := by
  simp [qubitTransverseMean]

theorem tendsto_qubitTransverseMean_atTop_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitTransverseMean b) atTop (nhds 0) := by
  have hratio : Tendsto (fun t : ℝ => b / qubitRadius b t)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_qubitRadius_atTop hb)
  change Tendsto (fun t : ℝ => b / qubitRadius b t *
    Real.tanh (qubitRadius b t)) atTop (nhds 0)
  simpa only [zero_mul] using
    hratio.mul (tendsto_tanh_qubitRadius_atTop hb)

/-- Positive pure-state boundary law of the qubit orbit. -/
def qubitPositiveBoundaryDensity : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + QuantumAlg.pauliZ)

/-- Negative pure-state boundary law of the qubit orbit. -/
def qubitNegativeBoundaryDensity : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) - QuantumAlg.pauliZ)

theorem qubitDensity_pauli_decomposition {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitDensity b t =
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        (qubitMean b t : ℂ) • QuantumAlg.pauliZ +
        (qubitTransverseMean b t : ℂ) • QuantumAlg.pauliX) := by
  rw [qubitDensity_closed hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitHamiltonian, QuantumAlg.pauliX, QuantumAlg.pauliZ,
      qubitMean, qubitTransverseMean] <;> ring

theorem qubitDensity_commutator_entry_zero_one {b : ℝ} (hb : 0 < b)
    (s t : ℝ) :
    (qubitDensity b s * qubitDensity b t -
        qubitDensity b t * qubitDensity b s) 0 1 =
      ((b * (s - t) * Real.tanh (qubitRadius b s) *
        Real.tanh (qubitRadius b t) /
          (2 * qubitRadius b s * qubitRadius b t) : ℝ) : ℂ) := by
  rw [qubitDensity_pauli_decomposition hb,
    qubitDensity_pauli_decomposition hb]
  simp [Matrix.mul_apply, Fin.sum_univ_two, QuantumAlg.pauliX,
    QuantumAlg.pauliZ, qubitMean, qubitTransverseMean]
  field_simp [(qubitRadius_pos hb s).ne', (qubitRadius_pos hb t).ne']
  ring

/-- Distinct finite-parameter density matrices genuinely fail to commute. -/
theorem qubitDensity_commutator_ne_zero {b s t : ℝ}
    (hb : 0 < b) (hst : s ≠ t) :
    qubitDensity b s * qubitDensity b t -
        qubitDensity b t * qubitDensity b s ≠ 0 := by
  have hsTanh : Real.tanh (qubitRadius b s) ≠ 0 := by
    have h := HTGeometry.tanh_strictMono (qubitRadius_pos hb s)
    simpa only [Real.tanh_zero] using h.ne'
  have htTanh : Real.tanh (qubitRadius b t) ≠ 0 := by
    have h := HTGeometry.tanh_strictMono (qubitRadius_pos hb t)
    simpa only [Real.tanh_zero] using h.ne'
  have hcoef :
      b * (s - t) * Real.tanh (qubitRadius b s) *
        Real.tanh (qubitRadius b t) /
          (2 * qubitRadius b s * qubitRadius b t) ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero hb.ne' (sub_ne_zero.mpr hst)) hsTanh)
        htTanh)
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (qubitRadius_pos hb s).ne')
        (qubitRadius_pos hb t).ne')
  intro hzero
  have h01 := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
  rw [qubitDensity_commutator_entry_zero_one hb] at h01
  exact (Complex.ofReal_ne_zero.mpr hcoef) h01

/-- Positive pure-state boundary law at the completed Fisher endpoint. -/
theorem tendsto_qubitDensity_atTop_positiveBoundary {b : ℝ} (hb : 0 < b) :
    Tendsto (qubitDensity b) atTop (nhds qubitPositiveBoundaryDensity) := by
  have hpair : Tendsto (fun t : ℝ =>
      (qubitMean b t, qubitTransverseMean b t)) atTop (nhds (1, 0)) :=
    by
      simpa only [nhds_prod_eq] using
        (tendsto_qubitMean_atTop_one hb).prodMk
          (tendsto_qubitTransverseMean_atTop_zero hb)
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        (p.1 : ℂ) • QuantumAlg.pauliZ +
        (p.2 : ℂ) • QuantumAlg.pauliX)) := by
    fun_prop
  have hlim := Filter.Tendsto.comp hmap.continuousAt hpair
  have hlim' : Tendsto (fun t : ℝ =>
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        (qubitMean b t : ℂ) • QuantumAlg.pauliZ +
        (qubitTransverseMean b t : ℂ) • QuantumAlg.pauliX))
      atTop (nhds ((1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((1 : ℝ) : ℂ) • QuantumAlg.pauliZ +
        ((0 : ℝ) : ℂ) • QuantumAlg.pauliX))) := by
    refine hlim.congr' ?_
    filter_upwards with t
    rfl
  have htarget :
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((1 : ℝ) : ℂ) • QuantumAlg.pauliZ +
        ((0 : ℝ) : ℂ) • QuantumAlg.pauliX) =
        qubitPositiveBoundaryDensity := by
    simp [qubitPositiveBoundaryDensity]
  rw [htarget] at hlim'
  refine hlim'.congr' ?_
  filter_upwards with t
  exact (qubitDensity_pauli_decomposition hb t).symm

/-- Reflected negative pure-state boundary law. -/
theorem tendsto_qubitDensity_neg_atTop_negativeBoundary {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitDensity b (-t)) atTop
      (nhds qubitNegativeBoundaryDensity) := by
  have hpair : Tendsto (fun t : ℝ =>
      (-qubitMean b t, qubitTransverseMean b t)) atTop (nhds (-1, 0)) :=
    by
      simpa only [nhds_prod_eq] using
        (tendsto_qubitMean_atTop_one hb).neg.prodMk
          (tendsto_qubitTransverseMean_atTop_zero hb)
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        (p.1 : ℂ) • QuantumAlg.pauliZ +
        (p.2 : ℂ) • QuantumAlg.pauliX)) := by
    fun_prop
  have hlim := Filter.Tendsto.comp hmap.continuousAt hpair
  have hlim' : Tendsto (fun t : ℝ =>
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((-qubitMean b t : ℝ) : ℂ) • QuantumAlg.pauliZ +
        (qubitTransverseMean b t : ℂ) • QuantumAlg.pauliX))
      atTop (nhds ((1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((-1 : ℝ) : ℂ) • QuantumAlg.pauliZ +
        ((0 : ℝ) : ℂ) • QuantumAlg.pauliX))) := by
    refine hlim.congr' ?_
    filter_upwards with t
    rfl
  have htarget :
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((-1 : ℝ) : ℂ) • QuantumAlg.pauliZ +
        ((0 : ℝ) : ℂ) • QuantumAlg.pauliX) =
        qubitNegativeBoundaryDensity := by
    simp [qubitNegativeBoundaryDensity, sub_eq_add_neg]
  rw [htarget] at hlim'
  refine hlim'.congr' ?_
  filter_upwards with t
  rw [qubitDensity_pauli_decomposition hb, qubitMean_neg,
    qubitTransverseMean_neg]

theorem inv_cosh_sq_le_four_exp_neg_two {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.cosh x ^ 2 ≤ 4 * Real.exp (-(2 * x)) := by
  have h := HTGeometry.cosh_rpow_neg_le (s := (2 : ℝ)) (by norm_num) x
  rw [show (-(2 : ℝ)) = -(2 : ℝ) by rfl,
    Real.rpow_neg (Real.cosh_pos x).le,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, abs_of_nonneg hx] at h
  norm_num at h ⊢
  simpa only [one_div] using h

private theorem tendsto_qubitResponse_cubic_first {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 *
      (b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t)))
      atTop (𝓝 (b ^ 2)) := by
  have hlim : Tendsto (fun t : ℝ =>
      b ^ 2 * (t / qubitRadius b t) ^ 3 * Real.tanh (qubitRadius b t))
      atTop (𝓝 (b ^ 2)) := by
    simpa only [one_pow, mul_one] using
      ((tendsto_const_nhds.mul ((tendsto_self_div_qubitRadius hb).pow 3)).mul
        (tendsto_tanh_qubitRadius_atTop hb))
  refine hlim.congr' ?_
  filter_upwards with t
  field_simp [(qubitRadius_pos hb t).ne']

private theorem qubitResponse_cubic_second_bounds {b : ℝ} (hb : 0 < b)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2) ∧
    t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2) ≤
      4 * t ^ 3 * Real.exp (-(2 * t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hfrac : t ^ 2 / qubitRadius b t ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hr)]
    nlinarith [sq_nonneg b]
  have hsech := inv_cosh_sq_le_four_exp_neg_two hr.le
  have hexp : Real.exp (-(2 * qubitRadius b t)) ≤ Real.exp (-(2 * t)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · positivity
  · have hinner : t ^ 2 / qubitRadius b t ^ 2 /
        Real.cosh (qubitRadius b t) ^ 2 ≤
        4 * Real.exp (-(2 * qubitRadius b t)) := by
      calc
        t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2
            ≤ 1 / Real.cosh (qubitRadius b t) ^ 2 := by
              gcongr
        _ ≤ 4 * Real.exp (-(2 * qubitRadius b t)) := hsech
    calc
      t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
          Real.cosh (qubitRadius b t) ^ 2)
          ≤ t ^ 3 * (4 * Real.exp (-(2 * qubitRadius b t))) := by
            gcongr
      _ ≤ t ^ 3 * (4 * Real.exp (-(2 * t))) := by
            gcongr
      _ = 4 * t ^ 3 * Real.exp (-(2 * t)) := by ring

private theorem tendsto_qubitResponse_cubic_second {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
      Real.cosh (qubitRadius b t) ^ 2)) atTop (𝓝 0) := by
  have hdom : Tendsto (fun t : ℝ => 4 * t ^ 3 * Real.exp (-(2 * t)))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_mul_atTop (b := (2 : ℝ)) (by norm_num) 3).const_mul 4
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with t
    ring
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitResponse_cubic_second_bounds hb ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitResponse_cubic_second_bounds hb ht).2

theorem tendsto_cubic_mul_qubitResponse {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 3 * qubitResponse b t) atTop (𝓝 (b ^ 2)) := by
  rw [show (fun t : ℝ => t ^ 3 * qubitResponse b t) =
      fun t : ℝ =>
        t ^ 3 * (b ^ 2 / qubitRadius b t ^ 3 *
          Real.tanh (qubitRadius b t)) +
        t ^ 3 * (t ^ 2 / qubitRadius b t ^ 2 /
          Real.cosh (qubitRadius b t) ^ 2) by
    funext t
    rw [qubitResponse]
    ring]
  simpa only [add_zero] using
    (tendsto_qubitResponse_cubic_first hb).add
      (tendsto_qubitResponse_cubic_second hb)

/-- Full square-root Fisher response has exact `t⁻³ᐟ²` coefficient `b`. -/
theorem tendsto_rpow_three_halves_mul_sqrt_qubitResponse
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ =>
      t ^ ((3 : ℝ) / 2) * Real.sqrt (qubitResponse b t))
      atTop (𝓝 b) := by
  have hroot := Filter.Tendsto.comp Real.continuous_sqrt.continuousAt
    (tendsto_cubic_mul_qubitResponse hb)
  change Tendsto (fun t : ℝ =>
    Real.sqrt (t ^ 3 * qubitResponse b t)) atTop
      (𝓝 (Real.sqrt (b ^ 2))) at hroot
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hb] at hroot
  refine hroot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hrpow : (t ^ ((3 : ℝ) / 2)) ^ 2 = t ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hsq :
      (t ^ ((3 : ℝ) / 2) * Real.sqrt (qubitResponse b t)) ^ 2 =
        t ^ 3 * qubitResponse b t := by
    rw [mul_pow, hrpow, Real.sq_sqrt (qubitResponse_pos hb t).le]
  rw [← hsq, Real.sqrt_sq]
  positivity

theorem qubitReflectedQuantumWork_eq {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitReflectedQuantumWork b t =
      4 * t ^ 2 / qubitRadius b t * Real.tanh (qubitRadius b t) := by
  rw [qubitReflectedQuantumWork, qubitQuantumJeffreys_eq hb, qubitMean_neg,
    qubitMean]
  ring

theorem tendsto_qubitReflectedQuantumWork_div_four_mul {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitReflectedQuantumWork b t / (4 * t))
      atTop (𝓝 1) := by
  refine (tendsto_qubitMean_atTop_one hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [qubitReflectedQuantumWork_eq hb, qubitMean]
  field_simp [ht.ne', (qubitRadius_pos hb t).ne']

theorem one_sub_self_div_qubitRadius {b : ℝ} (hb : 0 < b) (t : ℝ) :
    1 - t / qubitRadius b t =
      b ^ 2 / (qubitRadius b t * (qubitRadius b t + t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have hsum : 0 < qubitRadius b t + t := by
    linarith [abs_lt_qubitRadius hb t, neg_le_abs t]
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  field_simp [hr.ne', hsum.ne']
  nlinarith

/-- NQP.17: longitudinal mean defect splits into radial and thermal defects. -/
theorem one_sub_qubitMean_eq_radial_add_thermal_defect (b t : ℝ) :
    1 - qubitMean b t =
      (1 - t / qubitRadius b t) +
        (t / qubitRadius b t) *
          (1 - Real.tanh (qubitRadius b t)) := by
  rw [qubitMean]
  ring

private theorem tendsto_sq_mul_one_sub_self_div_qubitRadius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - t / qubitRadius b t))
      atTop (𝓝 (b ^ 2 / 2)) := by
  have hr := tendsto_qubitRadius_div_self hb
  have hden : Tendsto (fun t : ℝ =>
      (qubitRadius b t / t) * (qubitRadius b t / t + 1))
      atTop (𝓝 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hraw := hr.mul (hr.add hone)
    norm_num at hraw
    exact hraw
  have hquot : Tendsto (fun t : ℝ => b ^ 2 /
      ((qubitRadius b t / t) * (qubitRadius b t / t + 1)))
      atTop (𝓝 (b ^ 2 / 2)) :=
    tendsto_const_nhds.div hden (by norm_num)
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [one_sub_self_div_qubitRadius hb]
  field_simp [ht.ne', (qubitRadius_pos hb t).ne']

theorem one_sub_tanh_le_two_exp_neg_two {x : ℝ} :
    1 - Real.tanh x ≤ 2 * Real.exp (-(2 * x)) := by
  rw [tanh_eq_expNegTwoRatio]
  have he : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-(2 * x)) := by positivity
  rw [show 1 - (1 - Real.exp (-(2 * x))) /
      (1 + Real.exp (-(2 * x))) =
      2 * Real.exp (-(2 * x)) / (1 + Real.exp (-(2 * x))) by
    field_simp
    ring]
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (Real.exp (-(2 * x)))]

private theorem qubitMean_defect_second_bounds {b : ℝ} (hb : 0 < b)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ 2 * (t / qubitRadius b t) *
        (1 - Real.tanh (qubitRadius b t)) ∧
    t ^ 2 * (t / qubitRadius b t) *
        (1 - Real.tanh (qubitRadius b t)) ≤
      2 * t ^ 2 * Real.exp (-(2 * t)) := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hratio0 : 0 ≤ t / qubitRadius b t := div_nonneg ht hr.le
  have hratio1 : t / qubitRadius b t ≤ 1 := (div_le_one hr).mpr htr
  have hdefect0 : 0 ≤ 1 - Real.tanh (qubitRadius b t) :=
    sub_nonneg.mpr (Real.tanh_lt_one _).le
  have hdefect := one_sub_tanh_le_two_exp_neg_two (x := qubitRadius b t)
  have hexp : Real.exp (-(2 * qubitRadius b t)) ≤ Real.exp (-(2 * t)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · positivity
  · calc
      t ^ 2 * (t / qubitRadius b t) *
          (1 - Real.tanh (qubitRadius b t))
          ≤ t ^ 2 * 1 * (2 * Real.exp (-(2 * qubitRadius b t))) := by
            gcongr
      _ ≤ t ^ 2 * 1 * (2 * Real.exp (-(2 * t))) := by
            gcongr
      _ = 2 * t ^ 2 * Real.exp (-(2 * t)) := by ring

private theorem tendsto_qubitMean_defect_second {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (t / qubitRadius b t) *
      (1 - Real.tanh (qubitRadius b t))) atTop (𝓝 0) := by
  have hdom : Tendsto (fun t : ℝ => 2 * t ^ 2 * Real.exp (-(2 * t)))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_mul_atTop (b := (2 : ℝ)) (by norm_num) 2).const_mul 2
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with t
    ring
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitMean_defect_second_bounds hb ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (qubitMean_defect_second_bounds hb ht).2

theorem tendsto_sq_mul_one_sub_qubitMean {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - qubitMean b t))
      atTop (𝓝 (b ^ 2 / 2)) := by
  rw [show (fun t : ℝ => t ^ 2 * (1 - qubitMean b t)) =
      fun t : ℝ =>
        t ^ 2 * (1 - t / qubitRadius b t) +
        t ^ 2 * (t / qubitRadius b t) *
          (1 - Real.tanh (qubitRadius b t)) by
    funext t
    rw [qubitMean]
    ring]
  simpa only [add_zero] using
    (tendsto_sq_mul_one_sub_self_div_qubitRadius hb).add
      (tendsto_qubitMean_defect_second hb)

theorem tendsto_sq_mul_one_sub_qubitMean_sq {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * (1 - qubitMean b t ^ 2))
      atTop (𝓝 (b ^ 2)) := by
  have hsum : Tendsto (fun t : ℝ => 1 + qubitMean b t) atTop (𝓝 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := hone.add (tendsto_qubitMean_atTop_one hb)
    norm_num at h
    exact h
  have hprod := (tendsto_sq_mul_one_sub_qubitMean hb).mul hsum
  have hprod' : Tendsto (fun t : ℝ =>
      (t ^ 2 * (1 - qubitMean b t)) * (1 + qubitMean b t))
      atTop (𝓝 (b ^ 2)) := by
    norm_num at hprod
    exact hprod
  refine hprod'.congr' ?_
  filter_upwards with t
  ring

theorem tendsto_qubitObservedOddsScale {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ =>
      (1 + qubitMean b t) / (t ^ 2 * (1 - qubitMean b t)))
      atTop (nhds (4 / b ^ 2)) := by
  have hsum : Tendsto (fun t : ℝ => 1 + qubitMean b t) atTop (nhds 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := hone.add (tendsto_qubitMean_atTop_one hb)
    norm_num at h
    exact h
  have hraw := hsum.div (tendsto_sq_mul_one_sub_qubitMean hb)
    (by positivity : b ^ 2 / 2 ≠ 0)
  have hlimit : 2 / (b ^ 2 / 2) = 4 / b ^ 2 := by
    field_simp [hb.ne']
    norm_num
  rw [hlimit] at hraw
  change Tendsto (fun t : ℝ =>
    (1 + qubitMean b t) / (t ^ 2 * (1 - qubitMean b t)))
      atTop (nhds (4 / b ^ 2)) at hraw
  exact hraw

theorem abs_qubitMean_lt_one {b : ℝ} (hb : 0 < b) (t : ℝ) :
    |qubitMean b t| < 1 := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have hratio : |t| / qubitRadius b t < 1 :=
    (div_lt_one hr).mpr (abs_lt_qubitRadius hb t)
  have hratio0 : 0 ≤ |t| / qubitRadius b t := div_nonneg (abs_nonneg t) hr.le
  have htanh : |Real.tanh (qubitRadius b t)| < 1 :=
    (abs_lt).mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  rw [qubitMean, abs_mul, abs_div, abs_of_pos hr]
  calc
    |t| / qubitRadius b t * |Real.tanh (qubitRadius b t)|
        ≤ |t| / qubitRadius b t * 1 :=
          mul_le_mul_of_nonneg_left htanh.le hratio0
    _ < 1 := by simpa only [mul_one] using hratio

theorem qubitObservedProbability_hasDerivAt {b : ℝ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u : ℝ => qubitObservedProbability b u)
      (qubitResponse b t / 2) t := by
  have h := ((hasDerivAt_const t 1).add (qubitMean_hasDerivAt hb t)).div_const 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with u
  simp only [qubitObservedProbability, Pi.add_apply]

@[simp] theorem qubitObservedProbability_neg (b t : ℝ) :
    qubitObservedProbability b (-t) = 1 - qubitObservedProbability b t := by
  rw [qubitObservedProbability, qubitObservedProbability, qubitMean_neg]
  ring

theorem qubitObservedProbability_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitObservedProbability b t := by
  rw [qubitObservedProbability]
  have h := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
  linarith

theorem qubitObservedProbability_lt_one {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitObservedProbability b t < 1 := by
  rw [qubitObservedProbability]
  have h := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
  linarith

/-- The observed work is the literal reflected Bernoulli Jeffreys divergence. -/
theorem bernoulliJeffreys_qubitObservedProbability_reflection_eq
    {b : ℝ} (hb : 0 < b) (t : ℝ) :
    bernoulliJeffreys (qubitObservedProbability b t)
        (1 - qubitObservedProbability b t) =
      qubitObservedWork b t := by
  rw [bernoulliJeffreys_reflection_eq
    (qubitObservedProbability_pos hb t)
    (qubitObservedProbability_lt_one hb t), qubitObservedWork]
  have hm1 : 1 - qubitMean b t ≠ 0 := by
    have h := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
    linarith
  have hcenter : 2 * qubitObservedProbability b t - 1 = qubitMean b t := by
    rw [qubitObservedProbability]
    ring
  have hratio :
      qubitObservedProbability b t / (1 - qubitObservedProbability b t) =
        (1 + qubitMean b t) / (1 - qubitMean b t) := by
    rw [qubitObservedProbability]
    rw [show 1 - (1 + qubitMean b t) / 2 =
      (1 - qubitMean b t) / 2 by ring]
    field_simp [hm1]
  rw [hcenter, hratio]

theorem qubitObservedResponse_eq_fisher {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (qubitResponse b t / 2) ^ 2 /
        (qubitObservedProbability b t * (1 - qubitObservedProbability b t)) =
      qubitObservedResponse b t := by
  have hm : 1 - qubitMean b t ^ 2 ≠ 0 := by
    have hleft := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
    have hright := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
    have hp : 0 < (1 - qubitMean b t) * (1 + qubitMean b t) :=
      mul_pos (by linarith) (by linarith)
    have heq : (1 - qubitMean b t) * (1 + qubitMean b t) =
        1 - qubitMean b t ^ 2 := by ring
    rw [heq] at hp
    exact hp.ne'
  have hq : qubitObservedProbability b t * (1 - qubitObservedProbability b t) =
      (1 - qubitMean b t ^ 2) / 4 := by
    rw [qubitObservedProbability]
    ring
  rw [hq, qubitObservedResponse]
  field_simp [hm]
  ring

theorem tendsto_quartic_mul_qubitObservedResponse {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 4 * qubitObservedResponse b t)
      atTop (nhds (b ^ 2)) := by
  have hraw := ((tendsto_cubic_mul_qubitResponse hb).pow 2).div
    (tendsto_sq_mul_one_sub_qubitMean_sq hb) (pow_ne_zero 2 hb.ne')
  have hlimit : (b ^ 2) ^ 2 / b ^ 2 = b ^ 2 := by
    field_simp [hb.ne']
  rw [hlimit] at hraw
  change Tendsto (fun t : ℝ =>
    (t ^ 3 * qubitResponse b t) ^ 2 /
      (t ^ 2 * (1 - qubitMean b t ^ 2))) atTop (nhds (b ^ 2)) at hraw
  refine hraw.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hm : 1 - qubitMean b t ^ 2 ≠ 0 := by
    have hleft := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
    have hright := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
    nlinarith
  rw [qubitObservedResponse]
  field_simp [ht.ne', hm]

theorem one_sub_qubitMean_sq_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < 1 - qubitMean b t ^ 2 := by
  have hleft := (abs_lt.mp (abs_qubitMean_lt_one hb t)).1
  have hright := (abs_lt.mp (abs_qubitMean_lt_one hb t)).2
  nlinarith

theorem qubitObservedResponse_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitObservedResponse b t := by
  rw [qubitObservedResponse]
  exact div_pos (sq_pos_of_pos (qubitResponse_pos hb t))
    (one_sub_qubitMean_sq_pos hb t)

@[simp] theorem qubitObservedResponse_neg (b t : ℝ) :
    qubitObservedResponse b (-t) = qubitObservedResponse b t := by
  simp [qubitObservedResponse]

theorem continuous_qubitObservedResponse {b : ℝ} (hb : 0 < b) :
    Continuous (qubitObservedResponse b) := by
  have hmC : Continuous (qubitMean b) :=
    continuous_iff_continuousAt.mpr fun t =>
      (qubitMean_hasDerivAt hb t).continuousAt
  change Continuous (fun t : ℝ =>
    qubitResponse b t ^ 2 / (1 - qubitMean b t ^ 2))
  exact ((continuous_qubitResponse hb).pow 2).div
    (continuous_const.sub (hmC.pow 2))
    (fun t => (one_sub_qubitMean_sq_pos hb t).ne')

/-- Observed square-root Fisher response has exact quadratic tail coefficient `b`. -/
theorem tendsto_sq_mul_sqrt_qubitObservedResponse {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * Real.sqrt (qubitObservedResponse b t))
      atTop (nhds b) := by
  have hroot := Filter.Tendsto.comp Real.continuous_sqrt.continuousAt
    (tendsto_quartic_mul_qubitObservedResponse hb)
  change Tendsto (fun t : ℝ =>
    Real.sqrt (t ^ 4 * qubitObservedResponse b t)) atTop
      (nhds (Real.sqrt (b ^ 2))) at hroot
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hb] at hroot
  refine hroot.congr' ?_
  filter_upwards with t
  have hsq :
      (t ^ 2 * Real.sqrt (qubitObservedResponse b t)) ^ 2 =
        t ^ 4 * qubitObservedResponse b t := by
    rw [mul_pow, Real.sq_sqrt (qubitObservedResponse_pos hb t).le]
    ring
  rw [← hsq, Real.sqrt_sq]
  positivity

theorem exists_integrableOn_Ioi_sqrt_qubitObservedResponse
    {b : ℝ} (hb : 0 < b) :
    ∃ T : ℝ, 1 < T ∧
      IntegrableOn (fun t : ℝ => Real.sqrt (qubitObservedResponse b t))
        (Ioi T) := by
  have hlim := tendsto_sq_mul_sqrt_qubitObservedResponse hb
  have hev : ∀ᶠ t : ℝ in atTop,
      t ^ 2 * Real.sqrt (qubitObservedResponse b t) < b + 1 ∧ 1 < t :=
    (hlim.eventually (Iio_mem_nhds (by linarith))).and
      (eventually_gt_atTop 1)
  rcases (eventually_atTop.1 hev) with ⟨T, hT⟩
  have hT1 : 1 < T := (hT T le_rfl).2
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Ioi T) :=
    (integrableOn_Ioi_rpow_iff (by linarith)).2 (by norm_num)
  have hdom : IntegrableOn (fun t : ℝ =>
      (b + 1) * t ^ (-(2 : ℝ))) (Ioi T) :=
    hpow.const_mul (b + 1)
  refine ⟨T, hT1, ?_⟩
  change Integrable (fun t : ℝ => Real.sqrt (qubitObservedResponse b t))
    (volume.restrict (Ioi T))
  change Integrable (fun t : ℝ => (b + 1) * t ^ (-(2 : ℝ)))
    (volume.restrict (Ioi T)) at hdom
  apply hdom.mono
    (Real.continuous_sqrt.comp
      (continuous_qubitObservedResponse hb)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 < t := lt_trans hT1 ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have hbound := (hT t ht.le).1.le
  change |Real.sqrt (qubitObservedResponse b t)| ≤
    |(b + 1) * t ^ (-(2 : ℝ))|
  rw [abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le _))]
  calc
    Real.sqrt (qubitObservedResponse b t) =
        (t ^ 2 * Real.sqrt (qubitObservedResponse b t)) *
          t ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg ht0.le]
      field_simp [ht0.ne']
      congr 1
      exact Real.rpow_natCast t 2
    _ ≤ (b + 1) * t ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg ht0.le _)

theorem tendsto_log_qubitObservedOddsScale {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.log
      ((1 + qubitMean b t) / (t ^ 2 * (1 - qubitMean b t))))
      atTop (nhds (Real.log (4 / b ^ 2))) := by
  have h := Filter.Tendsto.comp
    (Real.continuousAt_log (by positivity : 4 / b ^ 2 ≠ 0))
    (tendsto_qubitObservedOddsScale hb)
  change Tendsto (fun t : ℝ => Real.log
    ((1 + qubitMean b t) / (t ^ 2 * (1 - qubitMean b t))))
      atTop (nhds (Real.log (4 / b ^ 2))) at h
  exact h

theorem tendsto_qubitObservedLogOdds_div_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ =>
      Real.log ((1 + qubitMean b t) / (1 - qubitMean b t)) /
        Real.log t) atTop (nhds 2) := by
  have hlogScale := tendsto_log_qubitObservedOddsScale hb
  have hinvLog : Tendsto (fun t : ℝ => (Real.log t)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmallRaw := hlogScale.mul hinvLog
  have hsmall : Tendsto (fun t : ℝ =>
      Real.log ((1 + qubitMean b t) /
        (t ^ 2 * (1 - qubitMean b t))) / Real.log t)
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hsmallRaw
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hsum := htwo.add hsmall
  norm_num at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hm := abs_lt.mp (abs_qubitMean_lt_one hb t)
  have hminus : 1 - qubitMean b t ≠ 0 := by linarith
  have hscale :
      (1 + qubitMean b t) / (t ^ 2 * (1 - qubitMean b t)) ≠ 0 := by
    exact div_ne_zero (by linarith)
      (mul_ne_zero (pow_ne_zero 2 ht0) hminus)
  have hfactor :
      (1 + qubitMean b t) / (1 - qubitMean b t) =
        t ^ 2 * ((1 + qubitMean b t) /
          (t ^ 2 * (1 - qubitMean b t))) := by
    field_simp [ht0, hminus]
  rw [hfactor, Real.log_mul (pow_ne_zero 2 ht0) hscale,
    Real.log_pow]
  field_simp [hlog0]
  ring

theorem tendsto_qubitObservedWork_div_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitObservedWork b t / Real.log t)
      atTop (nhds 4) := by
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hprod := (htwo.mul (tendsto_qubitMean_atTop_one hb)).mul
    (tendsto_qubitObservedLogOdds_div_log hb)
  norm_num at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  rw [qubitObservedWork]
  field_simp [hlog0]

theorem tendsto_qubitObservedWork_div_four_mul {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitObservedWork b t / (4 * t))
      atTop (nhds 0) := by
  have hraw := ((tendsto_qubitObservedWork_div_log hb).mul
    tendsto_log_div_atTop).div_const 4
  norm_num at hraw
  refine hraw.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  field_simp [ht0, hlog0]

theorem tendsto_qubitMeasurementDeficit_div_four_mul {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => qubitMeasurementDeficit b t / (4 * t))
      atTop (nhds 1) := by
  have hraw := (tendsto_qubitReflectedQuantumWork_div_four_mul hb).sub
    (tendsto_qubitObservedWork_div_four_mul hb)
  norm_num at hraw
  refine hraw.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [qubitMeasurementDeficit]
  field_simp [ht.ne']

theorem log_tanh_odds_eq_two_mul (t : ℝ) :
    Real.log ((1 + Real.tanh t) / (1 - Real.tanh t)) = 2 * t := by
  have hratio : (1 + Real.tanh t) / (1 - Real.tanh t) =
      Real.exp (2 * t) := by
    rw [Real.tanh_eq]
    rw [show Real.exp (2 * t) = Real.exp t / Real.exp (-t) by
      rw [← Real.exp_sub]
      congr 1
      ring]
    field_simp [Real.exp_ne_zero]
    ring
  rw [hratio, Real.log_exp]

theorem qubitMean_nonneg {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    0 ≤ qubitMean b t := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htanh : 0 ≤ Real.tanh (qubitRadius b t) := by
    have h := HTGeometry.tanh_strictMono hr
    simpa only [Real.tanh_zero] using h.le
  rw [qubitMean]
  positivity

theorem qubitObservedWork_le_qubitReflectedQuantumWork
    {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    qubitObservedWork b t ≤ qubitReflectedQuantumWork b t := by
  have hmAbs := abs_lt.mp (abs_qubitMean_lt_one hb t)
  have hm0 := qubitMean_nonneg hb ht
  have hmt := qubitMean_le_tanh hb ht
  have htanhAbs : |Real.tanh t| < 1 :=
    (abs_lt).2 ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  have htanhBounds := abs_lt.mp htanhAbs
  have hmDen : 0 < 1 - qubitMean b t := by linarith
  have htanhDen : 0 < 1 - Real.tanh t := by linarith
  have hratio :
      (1 + qubitMean b t) / (1 - qubitMean b t) ≤
        (1 + Real.tanh t) / (1 - Real.tanh t) := by
    rw [div_le_div_iff₀ hmDen htanhDen]
    nlinarith
  have hargMean :
      (1 + qubitMean b t) / (1 - qubitMean b t) ∈ Ioi (0 : ℝ) := by
    exact div_pos (by linarith) hmDen
  have hargTanh :
      (1 + Real.tanh t) / (1 - Real.tanh t) ∈ Ioi (0 : ℝ) := by
    exact div_pos (by linarith) htanhDen
  have hlog :
      Real.log ((1 + qubitMean b t) / (1 - qubitMean b t)) ≤ 2 * t := by
    rw [← log_tanh_odds_eq_two_mul t]
    exact Real.strictMonoOn_log.monotoneOn hargMean hargTanh hratio
  rw [qubitObservedWork, qubitReflectedQuantumWork_eq hb]
  rw [qubitMean]
  calc
    2 * (t / qubitRadius b t * Real.tanh (qubitRadius b t)) *
        Real.log ((1 + t / qubitRadius b t * Real.tanh (qubitRadius b t)) /
          (1 - t / qubitRadius b t * Real.tanh (qubitRadius b t))) ≤
        2 * (t / qubitRadius b t * Real.tanh (qubitRadius b t)) * (2 * t) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hm0)
    _ = 4 * t ^ 2 / qubitRadius b t * Real.tanh (qubitRadius b t) := by ring

@[simp] theorem qubitReflectedQuantumWork_neg (b t : ℝ) :
    qubitReflectedQuantumWork b (-t) = qubitReflectedQuantumWork b t := by
  rw [qubitReflectedQuantumWork, qubitReflectedQuantumWork]
  simp only [neg_neg]
  rw [qubitQuantumJeffreys, qubitQuantumJeffreys]
  ring

@[simp] theorem qubitObservedWork_neg {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitObservedWork b (-t) = qubitObservedWork b t := by
  have hm := abs_lt.mp (abs_qubitMean_lt_one hb t)
  have hplus : 1 + qubitMean b t ≠ 0 := by linarith
  have hminus : 1 - qubitMean b t ≠ 0 := by linarith
  have hratio :
      (1 - qubitMean b t) / (1 + qubitMean b t) =
        ((1 + qubitMean b t) / (1 - qubitMean b t))⁻¹ := by
    field_simp
  rw [qubitObservedWork, qubitObservedWork, qubitMean_neg]
  rw [show 1 + -qubitMean b t = 1 - qubitMean b t by ring,
    show 1 - -qubitMean b t = 1 + qubitMean b t by ring,
    hratio, Real.log_inv]
  ring

@[simp] theorem qubitMeasurementDeficit_neg {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitMeasurementDeficit b (-t) = qubitMeasurementDeficit b t := by
  simp [qubitMeasurementDeficit, qubitObservedWork_neg hb]

theorem qubitMeasurementDeficit_nonneg {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 ≤ qubitMeasurementDeficit b t := by
  rcases le_total 0 t with ht | ht
  · rw [qubitMeasurementDeficit]
    exact sub_nonneg.mpr
      (qubitObservedWork_le_qubitReflectedQuantumWork hb ht)
  · have hneg : 0 ≤ -t := neg_nonneg.mpr ht
    have h : 0 ≤ qubitMeasurementDeficit b (-t) := by
      rw [qubitMeasurementDeficit]
      exact sub_nonneg.mpr
        (qubitObservedWork_le_qubitReflectedQuantumWork hb hneg)
    simpa only [qubitMeasurementDeficit_neg hb] using h

/-- Explicit cubic-plus-exponential upper tail for the full BKM response. -/
theorem qubitResponse_le_cubic_exponential_tail {b t : ℝ} (hb : 0 < b)
    (ht : 1 ≤ t) :
    qubitResponse b t ≤
      b ^ 2 / t ^ 3 + 4 * Real.exp (-(2 * t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  have htr : t ≤ qubitRadius b t :=
    (le_abs_self t).trans (abs_lt_qubitRadius hb t).le
  have hr2 : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  have hfirst :
      b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t) ≤
        b ^ 2 / t ^ 3 := by
    calc
      b ^ 2 / qubitRadius b t ^ 3 * Real.tanh (qubitRadius b t)
          ≤ b ^ 2 / qubitRadius b t ^ 3 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (Real.tanh_lt_one (qubitRadius b t)).le
              (by positivity : 0 ≤ b ^ 2 / qubitRadius b t ^ 3)
      _ ≤ b ^ 2 / t ^ 3 := by
            rw [div_le_div_iff₀ (pow_pos hr 3) (pow_pos ht0 3)]
            gcongr
  have hratio : t ^ 2 / qubitRadius b t ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hr)]
    nlinarith [sq_nonneg b]
  have hsecond :
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2 ≤
        4 * Real.exp (-(2 * t)) := by
    calc
      t ^ 2 / qubitRadius b t ^ 2 / Real.cosh (qubitRadius b t) ^ 2
          ≤ 1 / Real.cosh (qubitRadius b t) ^ 2 := by
            gcongr
      _ ≤ 4 * Real.exp (-(2 * qubitRadius b t)) :=
        inv_cosh_sq_le_four_exp_neg_two hr.le
      _ ≤ 4 * Real.exp (-(2 * t)) := by
            gcongr
  rw [qubitResponse]
  exact add_le_add hfirst hsecond

private theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy' : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

private theorem sqrt_sq_div_cube_eq_rpow_neg_three_halves {b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) :
    Real.sqrt (b ^ 2 / t ^ 3) = b * t ^ (-(3 : ℝ) / 2) := by
  have hpow : (t ^ (-(3 : ℝ) / 2)) ^ 2 = 1 / t ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul ht.le]
    norm_num
    rfl
  have hsq : (b * t ^ (-(3 : ℝ) / 2)) ^ 2 = b ^ 2 / t ^ 3 := by
    rw [mul_pow, hpow]
    ring
  rw [← hsq, Real.sqrt_sq]
  positivity

private theorem sqrt_four_mul_exp_neg_two (t : ℝ) :
    Real.sqrt (4 * Real.exp (-(2 * t))) = 2 * Real.exp (-t) := by
  have hsq : (2 * Real.exp (-t)) ^ 2 = 4 * Real.exp (-(2 * t)) := by
    calc
      (2 * Real.exp (-t)) ^ 2 =
          4 * (Real.exp (-t) * Real.exp (-t)) := by ring
      _ = 4 * Real.exp (-t + -t) := by rw [Real.exp_add]
      _ = 4 * Real.exp (-(2 * t)) := by
        congr 1
        ring
  rw [← hsq, Real.sqrt_sq]
  positivity

/-- Exact square-root Fisher majorant on the positive tail. -/
theorem sqrt_qubitResponse_le_cubic_exponential_tail {b t : ℝ}
    (hb : 0 < b) (ht : 1 ≤ t) :
    Real.sqrt (qubitResponse b t) ≤
      b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  calc
    Real.sqrt (qubitResponse b t) ≤
        Real.sqrt (b ^ 2 / t ^ 3 + 4 * Real.exp (-(2 * t))) :=
      Real.sqrt_le_sqrt (qubitResponse_le_cubic_exponential_tail hb ht)
    _ ≤ Real.sqrt (b ^ 2 / t ^ 3) +
        Real.sqrt (4 * Real.exp (-(2 * t))) :=
      sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
    _ = b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t) := by
      rw [sqrt_sq_div_cube_eq_rpow_neg_three_halves hb ht0,
        sqrt_four_mul_exp_neg_two]

/-- The positive BKM--Fisher tail has finite length. -/
theorem integrableOn_Ioi_sqrt_qubitResponse {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.sqrt (qubitResponse b t)) (Ioi 1) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).2 (by norm_num)
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
    have h := integrableOn_exp_neg_mul_Ioi (b := (1 : ℝ)) (by norm_num) 1
    simpa only [one_mul] using h
  have hdom : IntegrableOn (fun t : ℝ =>
      b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t)) (Ioi 1) :=
    (hpow.const_mul b).add (hexp.const_mul 2)
  change Integrable (fun t : ℝ => Real.sqrt (qubitResponse b t))
    (volume.restrict (Ioi 1))
  change Integrable (fun t : ℝ =>
    b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t))
      (volume.restrict (Ioi 1)) at hdom
  apply hdom.mono
    (Real.continuous_sqrt.comp (continuous_qubitResponse hb)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change |Real.sqrt (qubitResponse b t)| ≤
    |b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t)|
  rw [abs_of_nonneg (Real.sqrt_nonneg (qubitResponse b t))]
  have hdom0 :
      0 ≤ b * t ^ (-(3 : ℝ) / 2) + 2 * Real.exp (-t) := by
    exact add_nonneg
      (mul_nonneg hb.le (Real.rpow_nonneg (le_trans zero_le_one ht.le) _))
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
  rw [abs_of_nonneg hdom0]
  exact sqrt_qubitResponse_le_cubic_exponential_tail hb ht.le

private theorem integrableOn_Iio_neg_of_even {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, f (-x) = f x) {R : ℝ}
    (h : IntegrableOn f (Ioi R) volume) :
    IntegrableOn f (Iio (-R)) volume := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' Iio (-R) = Ioi R := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi, neg_lt_neg_iff]
  have hmap : (volume : Measure ℝ).restrict (Iio (-R)) =
      ((volume : Measure ℝ).restrict (Ioi R)).map (fun x : ℝ => -x) := by
    rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Iio,
      Measure.map_neg_eq_self]
  rw [IntegrableOn, hmap, hemb.integrable_map_iff]
  exact h.congr (Filter.Eventually.of_forall fun x => (hf x).symm)

/-- The entire real qubit orbit has finite BKM--Fisher length. -/
theorem integrable_sqrt_qubitResponse {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.sqrt (qubitResponse b t)) := by
  let f : ℝ → ℝ := fun t => Real.sqrt (qubitResponse b t)
  have hfC : Continuous f :=
    Real.continuous_sqrt.comp (continuous_qubitResponse hb)
  have hpos : IntegrableOn f (Ioi 1) := integrableOn_Ioi_sqrt_qubitResponse hb
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    simp only [f, qubitResponse_neg]
  have hneg : IntegrableOn f (Iio (-1)) :=
    integrableOn_Iio_neg_of_even heven hpos
  have hmid : IntegrableOn f (Icc (-1) 1) := hfC.integrableOn_Icc
  have hall := (hneg.union hmid).union hpos
  have hcover : (Iio (-1) ∪ Icc (-1) 1) ∪ Ioi 1 = (Set.univ : Set ℝ) := by
    ext t
    change (((t < -1 ∨ (-1 ≤ t ∧ t ≤ 1)) ∨ 1 < t) ↔ True)
    constructor
    · intro _
      trivial
    · intro _
      rcases lt_or_ge t (-1) with ht | ht
      · exact Or.inl (Or.inl ht)
      · rcases le_or_gt t 1 with ht' | ht'
        · exact Or.inl (Or.inr ⟨ht, ht'⟩)
        · exact Or.inr ht'
  rw [hcover] at hall
  simpa only [IntegrableOn, Measure.restrict_univ, f] using hall

/-- The entire observed orbit also has finite Fisher length. -/
theorem integrable_sqrt_qubitObservedResponse {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.sqrt (qubitObservedResponse b t)) := by
  obtain ⟨T, hT, hpos⟩ :=
    exists_integrableOn_Ioi_sqrt_qubitObservedResponse hb
  let f : ℝ → ℝ := fun t => Real.sqrt (qubitObservedResponse b t)
  have hfC : Continuous f :=
    Real.continuous_sqrt.comp (continuous_qubitObservedResponse hb)
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    simp only [f, qubitObservedResponse_neg]
  have hneg : IntegrableOn f (Iio (-T)) :=
    integrableOn_Iio_neg_of_even heven hpos
  have hmid : IntegrableOn f (Icc (-T) T) := hfC.integrableOn_Icc
  have hall := (hneg.union hmid).union hpos
  have hcover : (Iio (-T) ∪ Icc (-T) T) ∪ Ioi T = (Set.univ : Set ℝ) := by
    ext t
    change (((t < -T ∨ (-T ≤ t ∧ t ≤ T)) ∨ T < t) ↔ True)
    constructor
    · intro _
      trivial
    · intro _
      rcases lt_or_ge t (-T) with ht | ht
      · exact Or.inl (Or.inl ht)
      · rcases le_or_gt t T with ht' | ht'
        · exact Or.inl (Or.inr ⟨ht, ht'⟩)
        · exact Or.inr ht'
  rw [hcover] at hall
  simpa only [IntegrableOn, Measure.restrict_univ, f] using hall

/-- Every positive BKM--Fisher tail collapses uniformly in response length. -/
theorem qubitResponseLengthTailCollapses {b : ℝ} (hb : 0 < b) :
    ResponseLengthTailCollapses (qubitResponse b) := by
  exact responseLengthTailCollapses_of_integrableOn_Ici
    (continuous_qubitResponse hb)
    (fun t => (qubitResponse_pos hb t).le)
    (T₀ := 0)
    (integrable_sqrt_qubitResponse hb).integrableOn

theorem qubitObservedResponseLengthTailCollapses {b : ℝ} (hb : 0 < b) :
    ResponseLengthTailCollapses (qubitObservedResponse b) := by
  exact responseLengthTailCollapses_of_integrableOn_Ici
    (continuous_qubitObservedResponse hb)
    (fun t => (qubitObservedResponse_pos hb t).le)
    (T₀ := 0)
    (integrable_sqrt_qubitObservedResponse hb).integrableOn

theorem qubitResponseWorkTailUnbounded {b : ℝ} (hb : 0 < b) :
    ResponseWorkTailUnbounded (qubitResponse b) := by
  apply responseWorkTailUnbounded_of_positive_tail
    (continuous_qubitResponse hb) (fun t => (qubitResponse_pos hb t).le)
  intro T
  refine ⟨T + 1, by linarith, ?_⟩
  apply intervalIntegral.integral_pos (by linarith)
    (continuous_qubitResponse hb).continuousOn
    (fun t _ => (qubitResponse_pos hb t).le)
  refine ⟨T + 1 / 2, ⟨by linarith, by linarith⟩, qubitResponse_pos hb _⟩

theorem qubitObservedResponseWorkTailUnbounded {b : ℝ} (hb : 0 < b) :
    ResponseWorkTailUnbounded (qubitObservedResponse b) := by
  apply responseWorkTailUnbounded_of_positive_tail
    (continuous_qubitObservedResponse hb)
    (fun t => (qubitObservedResponse_pos hb t).le)
  intro T
  refine ⟨T + 1, by linarith, ?_⟩
  apply intervalIntegral.integral_pos (by linarith)
    (continuous_qubitObservedResponse hb).continuousOn
    (fun t _ => (qubitObservedResponse_pos hb t).le)
  refine ⟨T + 1 / 2, ⟨by linarith, by linarith⟩,
    qubitObservedResponse_pos hb _⟩

/-- The complete positive Fisher-length tail is asymptotic to `2b T⁻¹ᐟ²`. -/
theorem tendsto_qubitResponseFisherTail_div_rpow_neg_half
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ =>
      (∫ t in Ioi T, Real.sqrt (qubitResponse b t)) /
        T ^ (-(1 : ℝ) / 2)) atTop (𝓝 (2 * b)) := by
  have h := tendsto_tailIntegral_div_rpow_of_tendsto_rpow_mul
    (p := (3 : ℝ) / 2) (c := b) (by norm_num)
    (Real.continuous_sqrt.comp (continuous_qubitResponse hb))
    (integrable_sqrt_qubitResponse hb)
    (tendsto_rpow_three_halves_mul_sqrt_qubitResponse hb)
  change Tendsto (fun T : ℝ =>
    (∫ t in Ioi T, Real.sqrt (qubitResponse b t)) /
      T ^ (1 - (3 : ℝ) / 2)) atTop
        (𝓝 (b / ((3 : ℝ) / 2 - 1))) at h
  simpa only [show (1 : ℝ) - 3 / 2 = -(1 : ℝ) / 2 by ring,
    show b / ((3 : ℝ) / 2 - 1) = 2 * b by ring] using h

/-- The observed positive Fisher-length tail is asymptotic to `b T⁻¹`. -/
theorem tendsto_qubitObservedResponseFisherTail_div_rpow_neg_one
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ =>
      (∫ t in Ioi T, Real.sqrt (qubitObservedResponse b t)) /
        T ^ (-(1 : ℝ))) atTop (𝓝 b) := by
  have hasymp : Tendsto (fun t : ℝ =>
      t ^ (2 : ℝ) * Real.sqrt (qubitObservedResponse b t))
      atTop (𝓝 b) := by
    refine (tendsto_sq_mul_sqrt_qubitObservedResponse hb).congr' ?_
    filter_upwards with t
    congr 1
    exact (Real.rpow_natCast t 2).symm
  have h := tendsto_tailIntegral_div_rpow_of_tendsto_rpow_mul
    (p := (2 : ℝ)) (c := b) (by norm_num)
    (Real.continuous_sqrt.comp (continuous_qubitObservedResponse hb))
    (integrable_sqrt_qubitObservedResponse hb) hasymp
  change Tendsto (fun T : ℝ =>
    (∫ t in Ioi T, Real.sqrt (qubitObservedResponse b t)) /
      T ^ (1 - (2 : ℝ))) atTop (𝓝 (b / ((2 : ℝ) - 1))) at h
  simpa only [show (1 : ℝ) - 2 = -(1 : ℝ) by ring,
    show b / ((2 : ℝ) - 1) = b by ring] using h

end

end GaloisForLFunctions.HTGeometry
