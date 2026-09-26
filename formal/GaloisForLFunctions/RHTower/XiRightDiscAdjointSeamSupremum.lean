import GaloisForLFunctions.RHTower.CircleLinearPhaseSeamMargin
import GaloisForLFunctions.RHTower.XiRightDiscPhaseIndexRiemannHypothesis
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# The adjoint seam of `xi` has supremum one over zero-free right discs

On a closed disc strictly right of the critical line on which `xi` has no zero, the adjoint Hankel
seam `(1 − P) U† P` of the boundary phase of `xi` is a strict contraction
(`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one`).  No margin is uniform:
`exists_zeroFree_xiRightDisc_adjointSeam_gt` gives, for every `ε > 0`, a zero-free right disc with
seam norm `> 1 − ε`.  The proof is unconditional.

The discs approach a zero `ρ₀` of `xi` on the critical line (Hardy's theorem, `exists_Xi_zero_gt`).
Near `ρ₀`, `xi(z) = (z − ρ₀)^m g(z)` with `g(ρ₀) ≠ 0`.  In the coordinates of the disc of radius
`t` centred at `ρ₀ + t/r`, the boundary values are `κ · exp Ψ` with `κ > 0` and
`exp Ψ = (1 + r z)^m G(z)`, `G` zero-free.  With `h = exp(Ψ/2)`, the Hardy test vector
`h/(1 + r z)` satisfies `U†(h/(1 + r z)) = conj(h)/(1 + r z)`.  The Hardy part of the latter is
`conj(h(−r))` times the Szegő kernel at `−r` (Cauchy's formula), which gives
`(1 − ‖seam‖²) ∫|h/(1 + r z)|² ≤ |h(−r)|²/(1 − r²)` (`one_sub_seam_sq_mul_le`).
* A simple zero: use the lower bound `∫|1 + r z|⁻¹ ≥ (1/2π) log(1 + π/(1 − r))`.
* A multiple zero: the factor `(1 − r²)^{m−1}` decays, compared against the mean value `|h(0)|²`.

Both cases give `1 − ‖seam‖² ≤ 3(1 − r²) + 6π / log(1 + π/(1 − r))`
(`OnLineZeroData.one_sub_seam_sq_le`).

Consequence (`not_exists_uniform_xiRightDisc_seam_margin`): no bound `‖(1 − P) U† P‖ ≤ 1 − δ`
with `δ > 0` holds on all zero-free right discs.  Any proof of the seam criterion must let the
margin degenerate as right discs approach the zeros of `xi` on the critical line.  The defect
`1 − ‖seam‖²` is at most of order `1/log(1/dist)` at a simple on-line zero and at most of order
`dist` at a multiple one.
-/

noncomputable section

open Complex MeasureTheory Metric intervalIntegral ContinuousLinearMap Filter Topology
open scoped Real InnerProductSpace

namespace RHTower

namespace XiSeamSupremum

open LinearPhaseSeam hiding e

local notation "𝕖" => LinearPhaseSeam.e

variable {r : ℝ}

/-! ## Cauchy's formula on the unit circle -/

/-- Cauchy's formula on the unit circle, in the parametrization `e`, for a function holomorphic on
a disc of radius `R > 1`. -/
theorem integral_e_cauchy_of_differentiable {R : ℝ} (hR : 1 < R) {G : ℂ → ℂ}
    (hG : ∀ z : ℂ, ‖z‖ < R → DifferentiableAt ℂ G z) {w : ℂ} (hw : ‖w‖ < 1) (j : ℕ) :
    ∫ x in (0 : ℝ)..1, 𝕖 x ^ (j + 1) * G (𝕖 x) * (𝕖 x - w)⁻¹ = w ^ j * G w := by
  set G' : ℂ → ℂ := fun z => z ^ j * G z with hG'
  have hdiff : ∀ z : ℂ, ‖z‖ < R → DifferentiableAt ℂ G' z := fun z hz =>
    (differentiableAt_id.pow j).mul (hG z hz)
  have hw' : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; exact hw
  have hC := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (R := 1) (c := 0) (w := w) (f := G') Set.countable_empty hw'
    (fun z hz => (hdiff z (by
      rw [mem_closedBall, dist_zero_right] at hz; linarith)).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (by
      have := hz.1; rw [mem_ball, dist_zero_right] at this; linarith))
  rw [circleIntegral] at hC
  set φ : ℝ → ℂ := fun θ => deriv (circleMap 0 1) θ •
    ((circleMap 0 1 θ - w)⁻¹ • G' (circleMap 0 1 θ)) with hφ
  have hsub : ∫ x in (0 : ℝ)..1, φ (2 * π * x) =
      (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, φ θ := by
    rw [intervalIntegral.integral_comp_mul_left φ (by positivity : (2 * π : ℝ) ≠ 0), mul_zero,
      mul_one]
  have hpt : ∀ x : ℝ, φ (2 * π * x) =
      I * (𝕖 x ^ (j + 1) * G (𝕖 x) * (𝕖 x - w)⁻¹) := by
    intro x
    simp only [hφ, hG', deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 1 (2 * π * x) = 𝕖 x from rfl]
    ring
  simp_rw [hpt] at hsub
  rw [intervalIntegral.integral_const_mul, hC] at hsub
  have hI : I ≠ 0 := I_ne_zero
  simp only [smul_eq_mul, real_smul, hG'] at hsub
  have hpi' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hI
  rw [hsub]
  push_cast
  field_simp

/-! ## The factor `1 + r z` -/

/-- The linear factor `1 + r z`, vanishing only at `−1/r`. -/
def qp (r : ℝ) (z : ℂ) : ℂ := 1 + (r : ℂ) * z

theorem qp_eq_q (z : ℂ) : qp r z = q r (-z) := by
  simp only [qp, q]; ring

theorem qp_ne_zero (hr0 : 0 < r) {z : ℂ} (hz : ‖z‖ < 1 / r) : qp r z ≠ 0 := by
  rw [qp_eq_q]; exact q_ne_zero hr0 (by rwa [norm_neg])

theorem qp_mem_slitPlane (hr0 : 0 < r) {z : ℂ} (hz : ‖z‖ < 1 / r) : qp r z ∈ slitPlane := by
  rw [qp_eq_q]; exact q_mem_slitPlane hr0 (by rwa [norm_neg])

theorem differentiableAt_qp (z : ℂ) : DifferentiableAt ℂ (qp r) z :=
  (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)

/-! ## The boundary function and its Fourier coefficients -/

/-- `h = exp(Ψ/2)`, a holomorphic square root of `exp Ψ`. -/
def hh (Ψ : ℂ → ℂ) (z : ℂ) : ℂ := Complex.exp (Ψ z / 2)

/-- The holomorphic test function `h / (1 + r z)`. -/
def testFn (r : ℝ) (Ψ : ℂ → ℂ) (z : ℂ) : ℂ := hh Ψ z * (qp r z)⁻¹

/-- The boundary function `conj(h)/(1 + r z)` on the unit circle. -/
def bdry (r : ℝ) (Ψ : ℂ → ℂ) (x : ℝ) : ℂ := starRingEnd ℂ (hh Ψ (𝕖 x)) * (qp r (𝕖 x))⁻¹

variable {Ψ : ℂ → ℂ}

theorem hh_ne_zero (z : ℂ) : hh Ψ z ≠ 0 := Complex.exp_ne_zero _

theorem hh_mul_self (z : ℂ) : hh Ψ z * hh Ψ z = Complex.exp (Ψ z) := by
  rw [hh, ← Complex.exp_add]; congr 1; ring

theorem norm_hh_sq (z : ℂ) : ‖hh Ψ z‖ ^ 2 = ‖Complex.exp (Ψ z)‖ := by
  rw [← hh_mul_self, norm_mul, pow_two]

theorem differentiableAt_hh {z : ℂ} (hΨ : DifferentiableAt ℂ Ψ z) :
    DifferentiableAt ℂ (hh Ψ) z :=
  (hΨ.div_const 2).cexp

theorem e_add_ne_zero (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) : 𝕖 x + (r : ℂ) ≠ 0 := by
  intro h
  have h1 : 𝕖 x = -(r : ℂ) := eq_neg_of_add_eq_zero_left h
  have := norm_e x
  rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at this
  linarith

theorem norm_neg_r_lt (hr0 : 0 < r) (hr1 : r < 1) : ‖(-(r : ℂ))‖ < 1 := by
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1

/-- Fourier coefficients of `conj(h)/(1 + r z)` at nonnegative frequencies:
`(−r)^j · conj(h(−r))`. -/
theorem fourierCoeff_bdry (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) (j : ℕ) :
    fourierCoeff (circleLift (bdry r Ψ)) (j : ℤ) =
      (-(r : ℂ)) ^ j * starRingEnd ℂ (hh Ψ (-(r : ℂ))) := by
  rw [fourierCoeff_circleLift]
  have hpt : ∀ x : ℝ,
      starRingEnd ℂ (fourier (-(j : ℤ)) (x : AddCircle (1 : ℝ)) * bdry r Ψ x) =
        𝕖 x ^ (j + 1) * hh Ψ (𝕖 x) * (𝕖 x - -(r : ℂ))⁻¹ := by
    intro x
    have hex := e_ne_zero x
    have hexr := e_add_ne_zero hr0 hr1 x
    have hexr' : 𝕖 x - -(r : ℂ) ≠ 0 := by rwa [sub_neg_eq_add]
    rw [map_mul, fourier_neg, Complex.conj_conj, ← e_pow, bdry, map_mul, Complex.conj_conj,
      map_inv₀, qp, map_add, map_one, map_mul, Complex.conj_ofReal, conj_e, sub_neg_eq_add]
    field_simp
    ring
  have h := interval_integral_conj
    (f := fun x => fourier (-(j : ℤ)) (x : AddCircle (1 : ℝ)) * bdry r Ψ x)
  simp_rw [hpt] at h
  rw [integral_e_cauchy_of_differentiable (one_lt_inv hr0 hr1)
    (fun z hz => differentiableAt_hh (hΨ z hz)) (norm_neg_r_lt hr0 hr1) j] at h
  have h2 := congrArg (starRingEnd ℂ) h
  rw [Complex.conj_conj] at h2
  rw [← h2, map_mul, map_pow, map_neg, Complex.conj_ofReal]

theorem periodic_bdry : Function.Periodic (bdry r Ψ) 1 := fun x => by
  simp only [bdry, periodic_e x]

/-! ## The phase identity -/

/-- If the boundary values of a disc datum are `κ · exp Ψ` with `κ > 0`, then
`conj(u) · h/(1 + r z) = conj(h)/(1 + r z)` on the circle. -/
theorem conj_phase_mul_testFn (D : DiscArgumentDatum) {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x))) (x : ℝ) :
    starRingEnd ℂ (D.phase x) * testFn r Ψ (𝕖 x) = bdry r Ψ x := by
  set H := hh Ψ (𝕖 x) with hH
  have hHne : H ≠ 0 := hh_ne_zero _
  have hcH : starRingEnd ℂ H ≠ 0 := (map_ne_zero _).mpr hHne
  have hv : D.value x = (κ : ℂ) * (H * H) := by rw [hval, hH, hh_mul_self]
  have hmod : ((D.modulus x : ℝ) : ℂ) = (κ : ℂ) * (H * starRingEnd ℂ H) := by
    rw [DiscArgumentDatum.modulus, hv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ.ne'
  rw [DiscArgumentDatum.phase, hmod, hv, testFn, bdry, ← hH]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
  field_simp

/-! ## The test vector and the seam estimate -/

theorem differentiableAt_testFn (hr0 : 0 < r)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) {z : ℂ} (hz : ‖z‖ < 1 / r) :
    DifferentiableAt ℂ (testFn r Ψ) z :=
  (differentiableAt_hh (hΨ z hz)).mul ((differentiableAt_qp z).inv (qp_ne_zero hr0 hz))

theorem testFn_ne_zero (hr0 : 0 < r) {z : ℂ} (hz : ‖z‖ < 1 / r) : testFn r Ψ z ≠ 0 :=
  mul_ne_zero (hh_ne_zero z) (inv_ne_zero (qp_ne_zero hr0 hz))

/-- The disc datum of the test function over the unit circle. -/
def testDatum (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) : DiscArgumentDatum :=
  datum hr0 hr1 (testFn r Ψ) (fun _ hz => differentiableAt_testFn hr0 hΨ hz)
    (fun _ hz => testFn_ne_zero hr0 hz)

theorem testDatum_value (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) (x : ℝ) :
    (testDatum hr0 hr1 hΨ).value x = testFn r Ψ (𝕖 x) := by
  simp [testDatum, datum, DiscArgumentDatum.value, DiscArgumentDatum.boundary, LinearPhaseSeam.e]

/-- The Hardy test vector: boundary values of `h/(1 + r z)`. -/
def testVec (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) : CCMCircleL2 :=
  circleLiftLp (testDatum hr0 hr1 hΨ).periodic_value
    (testDatum hr0 hr1 hΨ).contDiff_value.continuous

theorem hardy_testVec (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) :
    ccmCircleHardyProjection (testVec hr0 hr1 hΨ) = testVec hr0 hr1 hΨ := by
  apply hardy_eq_self_of_fourierCoeff_neg
  intro n hn
  rw [testVec, fourierCoeff_circleLiftLp]
  exact (testDatum hr0 hr1 hΨ).fourierCoeff_circleLift_value_of_neg hn

theorem norm_sq_testVec (hr0 : 0 < r) (hr1 : r < 1)
    (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) :
    ‖testVec hr0 hr1 hΨ‖ ^ 2 = ∫ x in (0 : ℝ)..1, ‖testFn r Ψ (𝕖 x)‖ ^ 2 := by
  rw [testVec, norm_sq_circleLiftLp]
  simp_rw [testDatum_value]

theorem conj_phase_mul_testFn_eq_bdry (D : DiscArgumentDatum) {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x)))
    (hr0 : 0 < r) (hr1 : r < 1) (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z)
    (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (D.circlePhase.toFun z) *
        circleLift (testDatum hr0 hr1 hΨ).value z = circleLift (bdry r Ψ) z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [DiscArgumentDatum.circlePhase_toFun, circleLift_coe D.periodic_phase,
    circleLift_coe (testDatum hr0 hr1 hΨ).periodic_value, circleLift_coe periodic_bdry,
    testDatum_value]
  exact conj_phase_mul_testFn D hκ hval x

theorem fourierCoeff_conjMultiplier_testVec (D : DiscArgumentDatum) {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x)))
    (hr0 : 0 < r) (hr1 : r < 1) (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) :
    fourierCoeff ((D.circlePhase.conjMultiplier (testVec hr0 hr1 hΨ) : CCMCircleL2) :
      AddCircle (1 : ℝ) → ℂ) = fourierCoeff (circleLift (bdry r Ψ)) := by
  apply fourierCoeff_congr_ae
  filter_upwards [D.circlePhase.conjMultiplier_coeFn (testVec hr0 hr1 hΨ),
    circleLiftLp_coeFn (testDatum hr0 hr1 hΨ).periodic_value
      (testDatum hr0 hr1 hΨ).contDiff_value.continuous] with z h1 h2
  rw [h1, show ((testVec hr0 hr1 hΨ : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) z =
      circleLift (testDatum hr0 hr1 hΨ).value z from h2]
  exact conj_phase_mul_testFn_eq_bdry D hκ hval hr0 hr1 hΨ z

/-- `‖P(U† f)‖² = |h(−r)|² / (1 − r²)`. -/
theorem norm_sq_hardy_adjoint_testVec (D : DiscArgumentDatum) {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x)))
    (hr0 : 0 < r) (hr1 : r < 1) (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) :
    ‖ccmCircleHardyProjection (D.circlePhase.conjMultiplier (testVec hr0 hr1 hΨ))‖ ^ 2 =
      ‖hh Ψ (-(r : ℂ))‖ ^ 2 / (1 - r ^ 2) := by
  rw [norm_sq_hardy_eq_tsum, fourierCoeff_conjMultiplier_testVec D hκ hval hr0 hr1 hΨ]
  have hterm : ∀ n : ℕ, ‖fourierCoeff (circleLift (bdry r Ψ)) (n : ℤ)‖ ^ 2 =
      ‖hh Ψ (-(r : ℂ))‖ ^ 2 * (r ^ 2) ^ n := by
    intro n
    rw [fourierCoeff_bdry hr0 hr1 hΨ n, norm_mul, norm_pow, Complex.norm_conj, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, mul_pow, ← pow_mul, ← pow_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by nlinarith)]
  rw [div_eq_mul_inv]

/-- **Seam estimate.**  `(1 − ‖(1 − P) U† P‖²) · ∫|h/(1 + r z)|² ≤ |h(−r)|² / (1 − r²)`. -/
theorem one_sub_seam_sq_mul_le (D : DiscArgumentDatum) {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x)))
    (hr0 : 0 < r) (hr1 : r < 1) (hΨ : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ Ψ z) :
    (1 - ‖D.circlePhase.datum.adjointHankelSeam‖ ^ 2) *
        ∫ x in (0 : ℝ)..1, ‖testFn r Ψ (𝕖 x)‖ ^ 2 ≤
      ‖hh Ψ (-(r : ℂ))‖ ^ 2 / (1 - r ^ 2) := by
  set f := testVec hr0 hr1 hΨ
  have hP : D.circlePhase.datum.projection f = f := hardy_testVec hr0 hr1 hΨ
  have hU : ContinuousLinearMap.adjoint D.circlePhase.datum.unitary =
      D.circlePhase.conjMultiplier := D.circlePhase.adjoint_multiplier
  have hineq := seam_sq_mul_ge D.circlePhase.datum f hP
  rw [hU] at hineq
  change ‖f‖ ^ 2 - ‖ccmCircleHardyProjection (D.circlePhase.conjMultiplier f)‖ ^ 2 ≤ _ at hineq
  rw [norm_sq_hardy_adjoint_testVec D hκ hval hr0 hr1 hΨ, norm_sq_testVec hr0 hr1 hΨ] at hineq
  linarith


/-! ## The one-log lower bound for a simple boundary zero -/

theorem e_add_half (x : ℝ) : 𝕖 (x + 1 / 2) = -𝕖 x := by
  simp only [LinearPhaseSeam.e, circleMap_zero, Complex.ofReal_one, one_mul]
  rw [show (2 * π * (x + 1 / 2) : ℝ) = 2 * π * x + π by ring]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem qp_e_eq (x : ℝ) : qp r (𝕖 x) = q r (𝕖 (x + 1 / 2)) := by
  rw [e_add_half, qp_eq_q]

theorem continuous_e : Continuous (fun x : ℝ => 𝕖 x) :=
  (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)

theorem continuous_norm_qp_e_inv (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun x => ‖qp r (𝕖 x)‖⁻¹) :=
  ((continuous_const.add (continuous_const.mul continuous_e)).norm).inv₀ fun x =>
    norm_ne_zero_iff.mpr (qp_ne_zero hr0 (norm_e_lt hr0 hr1 x))

/-- `∫ |1 + r e|⁻¹ ≥ (1/2π) log(1 + π/(1 − r))`. -/
theorem log_le_integral_norm_qp_inv (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log (1 + π / (1 - r)) / (2 * π) ≤ ∫ x in (0 : ℝ)..1, ‖qp r (𝕖 x)‖⁻¹ := by
  have hmodel := log_le_norm_sq_testVector hr0 hr1
  rw [testVector, norm_sq_circleLiftLp] at hmodel
  simp_rw [gDatum_value, norm_sq_g_e hr0 hr1] at hmodel
  have hper : Function.Periodic (fun x => ‖q r (𝕖 x)‖⁻¹) 1 := fun x => by
    simp only [periodic_e x]
  have hshift : ∫ x in (0 : ℝ)..1, ‖qp r (𝕖 x)‖⁻¹ = ∫ x in (0 : ℝ)..1, ‖q r (𝕖 x)‖⁻¹ := by
    simp_rw [qp_e_eq]
    rw [intervalIntegral.integral_comp_add_right (fun x => ‖q r (𝕖 x)‖⁻¹) (1 / 2)]
    have := hper.intervalIntegral_add_eq (1 / 2) 0
    rw [zero_add] at this
    rw [zero_add, show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 by ring, this]
  rw [hshift]
  exact hmodel

/-! ## An on-line zero of `xi` and its local factorization -/

/-- `xi` has a zero on the critical line (Hardy's theorem). -/
theorem exists_xi_zero_on_line : ∃ ρ₀ : ℂ, ρ₀.re = 1 / 2 ∧ xi ρ₀ = 0 := by
  obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
  have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  refine ⟨1 / 2 + (t : ℂ) * I, hre, ?_⟩
  apply Complex.ext
  · rw [Complex.zero_re]; unfold Xi at ht; exact ht
  · rw [xi_im_eq_zero_on_line hre, Complex.zero_im]

/-- A zero of `xi` of multiplicity `m ≥ 1` factors locally as `(z − ρ₀)^m g(z)`, `g(ρ₀) ≠ 0`. -/
theorem xi_local_factor {ρ₀ : ℂ} (hρ : xi ρ₀ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ₀ ∧ g ρ₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ₀, xi z = (z - ρ₀) ^ m * g z := by
  have han : AnalyticAt ℂ xi ρ₀ := xi_differentiable.analyticAt ρ₀
  have hne0 : analyticOrderAt xi ρ₀ ≠ 0 := by
    rw [ne_eq, han.analyticOrderAt_eq_zero]; exact fun h => h hρ
  have hnetop : analyticOrderAt xi ρ₀ ≠ ⊤ := by
    intro htop
    have hev : xi =ᶠ[𝓝 ρ₀] 0 := analyticOrderAt_eq_top.mp htop
    have hall : Set.EqOn xi 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => xi_differentiable.analyticAt z) isPreconnected_univ (Set.mem_univ ρ₀) hev
    exact xi_ne_zero_of_one_le_re (ρ := 2) (by norm_num) (hall (Set.mem_univ 2))
  set m := (analyticOrderAt xi ρ₀).toNat with hm
  have hcast : analyticOrderAt xi ρ₀ = (m : ℕ∞) := (ENat.coe_toNat hnetop).symm
  obtain ⟨g, hg, hg0, hev⟩ := (han.analyticOrderAt_eq_natCast).mp hcast
  refine ⟨m, ?_, g, hg, hg0, ?_⟩
  · rw [hm, Nat.one_le_iff_ne_zero, ne_eq, ENat.toNat_eq_zero]
    push Not
    exact ⟨hne0, hnetop⟩
  · filter_upwards [hev] with z hz
    rw [hz, smul_eq_mul]

/-- Local data at a zero of `xi` on the critical line. -/
structure OnLineZeroData where
  ρ₀ : ℂ
  re_eq : ρ₀.re = 1 / 2
  m : ℕ
  one_le_m : 1 ≤ m
  g : ℂ → ℂ
  δ : ℝ
  δ_pos : 0 < δ
  norm_pos : 0 < ‖g ρ₀‖
  factor : ∀ z ∈ ball ρ₀ δ, xi z = (z - ρ₀) ^ m * g z
  diff : ∀ z ∈ ball ρ₀ δ, DifferentiableAt ℂ g z
  lower : ∀ z ∈ ball ρ₀ δ, ‖g ρ₀‖ / 2 ≤ ‖g z‖
  upper : ∀ z ∈ ball ρ₀ δ, ‖g z‖ ≤ 3 * ‖g ρ₀‖ / 2

theorem nonempty_onLineZeroData : Nonempty OnLineZeroData := by
  obtain ⟨ρ₀, hre, hρ⟩ := exists_xi_zero_on_line
  obtain ⟨m, hm, g, hg, hg0, hev⟩ := xi_local_factor hρ
  have hA : 0 < ‖g ρ₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 ρ₀, ‖g z - g ρ₀‖ < ‖g ρ₀‖ / 2 := by
    have h := (Metric.tendsto_nhds.mp hg.continuousAt.tendsto) (‖g ρ₀‖ / 2) (by positivity)
    filter_upwards [h] with z hz
    rwa [dist_eq_norm] at hz
  have hdiff : ∀ᶠ z in 𝓝 ρ₀, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and (hcont.and hdiff))
  refine ⟨⟨ρ₀, hre, m, hm, g, δ, hδ, hA, fun z hz => (hball hz).1, fun z hz => (hball hz).2.2,
    fun z hz => ?_, fun z hz => ?_⟩⟩
  · have h1 := (hball hz).2.1
    have h2 := norm_sub_norm_le (g ρ₀) (g z)
    rw [norm_sub_rev] at h2
    linarith
  · have h1 := (hball hz).2.1
    have h2 := norm_sub_norm_le (g z) (g ρ₀)
    linarith

namespace OnLineZeroData

variable (Z : OnLineZeroData)

/-- The radius of the comparison discs. -/
def t : ℝ := Z.δ / 4

theorem t_pos : 0 < Z.t := by unfold t; linarith [Z.δ_pos]

/-- The disc centre `ρ₀ + t/r`, at distance `t/r > t` right of the on-line zero. -/
def center (r : ℝ) : ℂ := Z.ρ₀ + ((Z.t / r : ℝ) : ℂ)

theorem mem_ball_of_norm_lt (hr : 1 / 2 < r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ < 1 / r) :
    Z.center r + (Z.t : ℂ) * w ∈ ball Z.ρ₀ Z.δ := by
  have hr0 : 0 < r := by linarith
  have ht := Z.t_pos
  rw [mem_ball, dist_eq_norm, center,
    show Z.ρ₀ + ((Z.t / r : ℝ) : ℂ) + (Z.t : ℂ) * w - Z.ρ₀ = ((Z.t / r : ℝ) : ℂ) + (Z.t : ℂ) * w
      by ring]
  calc ‖((Z.t / r : ℝ) : ℂ) + (Z.t : ℂ) * w‖
      ≤ ‖((Z.t / r : ℝ) : ℂ)‖ + ‖(Z.t : ℂ) * w‖ := norm_add_le _ _
    _ = Z.t / r + Z.t * ‖w‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    _ < Z.t / r + Z.t * (1 / r) := by gcongr
    _ = 2 * Z.t / r := by ring
    _ < Z.δ := by
        rw [div_lt_iff₀ hr0]
        unfold t
        nlinarith [Z.δ_pos]

theorem sub_eq (hr0 : 0 < r) (w : ℂ) :
    Z.center r + (Z.t : ℂ) * w - Z.ρ₀ = ((Z.t / r : ℝ) : ℂ) * qp r w := by
  have hr : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  simp only [center, qp]
  push_cast
  field_simp
  ring

theorem xi_ne_zero (hr : 1 / 2 < r) (hr1 : r < 1) :
    ∀ z ∈ closedBall (Z.center r) Z.t, xi z ≠ 0 := by
  intro z hz
  have hr0 : 0 < r := by linarith
  have ht := Z.t_pos
  rw [mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := (z - Z.center r) / (Z.t : ℂ) with hw
  have htc : (Z.t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hz' : z = Z.center r + (Z.t : ℂ) * w := by rw [hw]; field_simp; ring
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_le_one ht]
    exact hz
  have hwlt : ‖w‖ < 1 / r := lt_of_le_of_lt hwn (one_lt_inv hr0 hr1)
  have hmem := Z.mem_ball_of_norm_lt hr hr1 hwlt
  rw [← hz'] at hmem
  rw [Z.factor z hmem, hz', Z.sub_eq hr0]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ (qp_ne_zero hr0 hwlt))) ?_
  · exact ofReal_ne_zero.mpr (by positivity)
  · rw [← hz']
    have := Z.lower z hmem
    have hA := Z.norm_pos
    exact norm_pos_iff.mp (by linarith)

theorem right_of_line (hr : 1 / 2 < r) (hr1 : r < 1) :
    ∀ z ∈ closedBall (Z.center r) Z.t, 1 / 2 < z.re := by
  intro z hz
  have hr0 : 0 < r := by linarith
  have ht := Z.t_pos
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - Z.center r).re| ≤ ‖z - Z.center r‖ := Complex.abs_re_le_norm _
  have h2 := neg_abs_le (z - Z.center r).re
  have hc : (Z.center r).re = 1 / 2 + Z.t / r := by
    simp [center, Z.re_eq]
  have htr : Z.t < Z.t / r := by rw [lt_div_iff₀ hr0]; nlinarith
  rw [Complex.sub_re, hc] at h1 h2
  linarith

theorem sphere_ne_zero (hr : 1 / 2 < r) (hr1 : r < 1) :
    ∀ ζ ∈ sphere (Z.center r) Z.t, xi ζ ≠ 0 := fun ζ hζ =>
  Z.xi_ne_zero hr hr1 ζ (sphere_subset_closedBall hζ)

/-- **Seam defect bound near an on-line zero.**  For the disc of radius `t` centred at
`ρ₀ + t/r`, `1 − ‖(1 − P) U† P‖² ≤ 3(1 − r²) + 6π / log(1 + π/(1 − r))`, uniformly in the local
data of the zero. -/
theorem one_sub_seam_sq_le (hr : 1 / 2 < r) (hr1 : r < 1) :
    1 - ‖(xiDiscDatum (Z.center r) Z.t Z.t_pos
        (Z.sphere_ne_zero hr hr1)).circlePhase.datum.adjointHankelSeam‖ ^ 2 ≤
      3 * (1 - r ^ 2) + 6 * π / Real.log (1 + π / (1 - r)) := by
  have hr0 : 0 < r := by linarith
  have ht := Z.t_pos
  set A := ‖Z.g Z.ρ₀‖ with hA
  have hApos : 0 < A := Z.norm_pos
  set Gt : ℂ → ℂ := fun w => Z.g (Z.center r + (Z.t : ℂ) * w) with hGt
  have hmemw : ∀ w ∈ ball (0 : ℂ) (1 / r), Z.center r + (Z.t : ℂ) * w ∈ ball Z.ρ₀ Z.δ :=
    fun w hw => Z.mem_ball_of_norm_lt hr hr1 (by rwa [mem_ball, dist_zero_right] at hw)
  have hGdiff : DifferentiableOn ℂ Gt (ball (0 : ℂ) (1 / r)) := fun w hw =>
    ((Z.diff _ (hmemw w hw)).comp w
      ((differentiableAt_const _).add ((differentiableAt_const _).mul
        differentiableAt_id))).differentiableWithinAt
  have hGne : ∀ w ∈ ball (0 : ℂ) (1 / r), Gt w ≠ 0 := fun w hw => by
    have := Z.lower _ (hmemw w hw)
    exact norm_pos_iff.mp (by simp only [hGt]; linarith)
  obtain ⟨L, hLd, -, hLeq⟩ :=
    GaloisForLFunctions.HTGeometry.exists_log_on_ball (by positivity : (0 : ℝ) < 1 / r) hGdiff hGne
  have hG0 : Gt 0 ≠ 0 := hGne 0 (mem_ball_self (by positivity))
  set Ψ : ℂ → ℂ := fun w => (Z.m : ℂ) * Complex.log (qp r w) + Complex.log (Gt 0) + L w with hΨdef
  have hΨ : ∀ w : ℂ, ‖w‖ < 1 / r → DifferentiableAt ℂ Ψ w := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) (1 / r) := by rwa [mem_ball, dist_zero_right]
    exact (((differentiableAt_qp w).clog (qp_mem_slitPlane hr0 hw)).const_mul _).add_const _ |>.add
      (hLd.differentiableAt (isOpen_ball.mem_nhds hwb))
  have hexpΨ : ∀ w : ℂ, ‖w‖ < 1 / r → Complex.exp (Ψ w) = qp r w ^ Z.m * Gt w := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) (1 / r) := by rwa [mem_ball, dist_zero_right]
    rw [hΨdef]
    simp only
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
      Complex.exp_log (qp_ne_zero hr0 hw), Complex.exp_log hG0, hLeq w hwb]
    ring
  set κ : ℝ := (Z.t / r) ^ Z.m with hκdef
  have hκ : 0 < κ := by positivity
  set D := xiDiscDatum (Z.center r) Z.t Z.t_pos (Z.sphere_ne_zero hr hr1) with hD
  have hval : ∀ x, D.value x = (κ : ℂ) * Complex.exp (Ψ (𝕖 x)) := by
    intro x
    have hex := norm_e_lt hr0 hr1 x
    have hbd : D.boundary x = Z.center r + (Z.t : ℂ) * 𝕖 x := by
      simp [hD, DiscArgumentDatum.boundary, xiDiscDatum, LinearPhaseSeam.e, circleMap]
    have hmem := Z.mem_ball_of_norm_lt hr hr1 hex
    rw [DiscArgumentDatum.value, hbd, show D.F = xi from rfl, Z.factor _ hmem, Z.sub_eq hr0,
      hexpΨ _ hex, hκdef]
    push_cast
    ring
  have hmain := one_sub_seam_sq_mul_le D hκ hval hr0 hr1 hΨ
  set σ := ‖D.circlePhase.datum.adjointHankelSeam‖ with hσ
  set I₀ := ∫ x in (0 : ℝ)..1, ‖testFn r Ψ (𝕖 x)‖ ^ 2 with hI₀
  -- the numerator
  have hnegr : ‖(-(r : ℂ))‖ < 1 / r := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact lt_trans hr1 (one_lt_inv hr0 hr1)
  have hqr : qp r (-(r : ℂ)) = ((1 - r ^ 2 : ℝ) : ℂ) := by simp only [qp]; push_cast; ring
  have h1r : 0 < 1 - r ^ 2 := by nlinarith
  have hnum : ‖hh Ψ (-(r : ℂ))‖ ^ 2 / (1 - r ^ 2) ≤
      (1 - r ^ 2) ^ (Z.m - 1) * (3 * A / 2) := by
    rw [norm_hh_sq, hexpΨ _ hnegr, norm_mul, norm_pow, hqr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h1r]
    have hGup : ‖Gt (-(r : ℂ))‖ ≤ 3 * A / 2 :=
      Z.upper _ (hmemw _ (by rwa [mem_ball, dist_zero_right]))
    have hm1 : (1 - r ^ 2) ^ Z.m = (1 - r ^ 2) ^ (Z.m - 1) * (1 - r ^ 2) := by
      rw [← pow_succ, Nat.sub_add_cancel Z.one_le_m]
    rw [hm1, div_le_iff₀ h1r]
    have hp : 0 ≤ (1 - r ^ 2) ^ (Z.m - 1) := by positivity
    calc (1 - r ^ 2) ^ (Z.m - 1) * (1 - r ^ 2) * ‖Gt (-(r : ℂ))‖
        ≤ (1 - r ^ 2) ^ (Z.m - 1) * (1 - r ^ 2) * (3 * A / 2) := by gcongr
      _ = (1 - r ^ 2) ^ (Z.m - 1) * (3 * A / 2) * (1 - r ^ 2) := by ring
  have hlogpos : 0 < Real.log (1 + π / (1 - r)) := by
    apply Real.log_pos
    have : 0 < π / (1 - r) := div_pos Real.pi_pos (by linarith)
    linarith
  have hB : 0 ≤ 3 * (1 - r ^ 2) + 6 * π / Real.log (1 + π / (1 - r)) := by positivity
  by_cases hσ1 : 1 < σ ^ 2
  · linarith
  push Not at hσ1
  have hdef : 0 ≤ 1 - σ ^ 2 := by linarith
  -- the pointwise size of the test function
  have htest : ∀ x, ‖testFn r Ψ (𝕖 x)‖ ^ 2 =
      ‖qp r (𝕖 x)‖ ^ Z.m * ‖Gt (𝕖 x)‖ * (‖qp r (𝕖 x)‖ ^ 2)⁻¹ := by
    intro x
    rw [testFn, norm_mul, mul_pow, norm_hh_sq, hexpΨ _ (norm_e_lt hr0 hr1 x), norm_mul, norm_pow,
      norm_inv, inv_pow]
  rcases Nat.lt_or_ge Z.m 2 with hm2 | hm2
  · -- simple zero: the one-log lower bound
    have hm : Z.m = 1 := by have := Z.one_le_m; omega
    have hlow : A / 2 * (Real.log (1 + π / (1 - r)) / (2 * π)) ≤ I₀ := by
      have hint := log_le_integral_norm_qp_inv hr0 hr1
      have hmono : ∫ x in (0 : ℝ)..1, A / 2 * ‖qp r (𝕖 x)‖⁻¹ ≤ I₀ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact ((continuous_const.mul (continuous_norm_qp_e_inv hr0 hr1)).intervalIntegrable _ _)
        · have hc : Continuous (fun x => ‖testFn r Ψ (𝕖 x)‖ ^ 2) := by
            have := (testDatum hr0 hr1 hΨ).contDiff_value.continuous
            simp_rw [funext (testDatum_value hr0 hr1 hΨ)] at this
            exact this.norm.pow 2
          exact hc.intervalIntegrable _ _
        · intro x _
          rw [htest x, hm, pow_one]
          have hqpos : 0 < ‖qp r (𝕖 x)‖ :=
            norm_pos_iff.mpr (qp_ne_zero hr0 (norm_e_lt hr0 hr1 x))
          have hGl : A / 2 ≤ ‖Gt (𝕖 x)‖ :=
            Z.lower _ (hmemw _ (by rw [mem_ball, dist_zero_right]; exact norm_e_lt hr0 hr1 x))
          rw [show ‖qp r (𝕖 x)‖ * ‖Gt (𝕖 x)‖ * (‖qp r (𝕖 x)‖ ^ 2)⁻¹ =
              ‖Gt (𝕖 x)‖ * ‖qp r (𝕖 x)‖⁻¹ by field_simp]
          exact mul_le_mul_of_nonneg_right hGl (inv_nonneg.mpr hqpos.le)
      rw [intervalIntegral.integral_const_mul] at hmono
      calc A / 2 * (Real.log (1 + π / (1 - r)) / (2 * π))
          ≤ A / 2 * ∫ x in (0 : ℝ)..1, ‖qp r (𝕖 x)‖⁻¹ := by gcongr
        _ ≤ I₀ := hmono
    rw [hm, Nat.sub_self, pow_zero, one_mul] at hnum
    have hkey : (1 - σ ^ 2) * (A / 2 * (Real.log (1 + π / (1 - r)) / (2 * π))) ≤ 3 * A / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hlow hdef) (le_trans hmain hnum)
    have hbound : 1 - σ ^ 2 ≤ 6 * π / Real.log (1 + π / (1 - r)) := by
      rw [le_div_iff₀ hlogpos]
      have hpi := Real.pi_pos
      have : (1 - σ ^ 2) * Real.log (1 + π / (1 - r)) * A = 6 * π *
          ((1 - σ ^ 2) * (A / 2 * (Real.log (1 + π / (1 - r)) / (2 * π)))) / 3 * 2 := by
        field_simp; ring
      nlinarith
    have : 0 ≤ 3 * (1 - r ^ 2) := by positivity
    linarith
  · -- multiple zero: the mean value lower bound
    have hlow : A / 2 ≤ I₀ := by
      set f := testVec hr0 hr1 hΨ with hf
      have hcoef : fourierCoeff ((f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) 0 = testFn r Ψ 0 := by
        rw [hf, testVec, fourierCoeff_circleLiftLp, fourierCoeff_circleLift]
        have hc := integral_e_cauchy_of_differentiable (one_lt_inv hr0 hr1)
          (fun z hz => differentiableAt_testFn hr0 hΨ hz) (w := 0) (by simp) 0
        simp only [pow_zero, one_mul, zero_add, pow_one, sub_zero] at hc
        rw [← hc]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [neg_zero, fourier_zero, one_mul, testDatum_value]
        field_simp [e_ne_zero x]
      have hin : ‖fourierCoeff ((f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) 0‖ ≤ ‖f‖ := by
        rw [← GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff]
        calc ‖inner ℂ (fourierLp 2 (0 : ℤ)) f‖ ≤ ‖fourierLp (T := 1) 2 (0 : ℤ)‖ * ‖f‖ :=
              norm_inner_le_norm _ _
          _ = ‖f‖ := by rw [(orthonormal_fourier (T := 1)).1 0, one_mul]
      rw [hcoef] at hin
      have h0 : ‖testFn r Ψ 0‖ ^ 2 = ‖Gt 0‖ := by
        rw [testFn, norm_mul, mul_pow, norm_hh_sq, hexpΨ 0 (by simp; positivity)]
        simp [qp]
      have hG0l : A / 2 ≤ ‖Gt 0‖ := Z.lower _ (hmemw 0 (mem_ball_self (by positivity)))
      have hsq : ‖testFn r Ψ 0‖ ^ 2 ≤ ‖f‖ ^ 2 := by
        have := norm_nonneg (testFn r Ψ 0)
        nlinarith
      rw [hI₀, ← norm_sq_testVec hr0 hr1 hΨ]
      linarith
    have hpow : (1 - r ^ 2) ^ (Z.m - 1) ≤ 1 - r ^ 2 :=
      pow_le_of_le_one h1r.le (by nlinarith) (by omega)
    have hkey : (1 - σ ^ 2) * (A / 2) ≤ (1 - r ^ 2) * (3 * A / 2) := by
      calc (1 - σ ^ 2) * (A / 2) ≤ (1 - σ ^ 2) * I₀ := mul_le_mul_of_nonneg_left hlow hdef
        _ ≤ _ := hmain
        _ ≤ (1 - r ^ 2) ^ (Z.m - 1) * (3 * A / 2) := hnum
        _ ≤ (1 - r ^ 2) * (3 * A / 2) := by gcongr
    have hbound : 1 - σ ^ 2 ≤ 3 * (1 - r ^ 2) := by nlinarith
    have : 0 ≤ 6 * π / Real.log (1 + π / (1 - r)) := by positivity
    linarith

end OnLineZeroData

/-- **No uniform seam margin for `xi`.**  For every `ε > 0` there is a closed disc strictly right
of the critical line on which `xi` has no zero, yet the adjoint Hankel seam `(1 − P) U† P` of its
boundary phase has norm `> 1 − ε`.  The discs approach a zero of `xi` on the critical line. -/
theorem exists_zeroFree_xiRightDisc_adjointSeam_gt (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0),
      (∀ z ∈ closedBall c t, 1 / 2 < z.re) ∧ (∀ z ∈ closedBall c t, xi z ≠ 0) ∧
        1 - ε < ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ := by
  obtain ⟨Z⟩ := nonempty_onLineZeroData
  have hpi := Real.pi_pos
  set M := Real.exp (12 * π / ε) + 4 with hM
  have hexp : 12 * π / ε < Real.exp (12 * π / ε) := by
    have := Real.add_one_le_exp (12 * π / ε); linarith
  have hM4 : 4 < M := by have := Real.exp_pos (12 * π / ε); linarith
  have hpi4 := Real.pi_le_four
  set r := 1 - π / (M + π) with hrdef
  have hMπ : 0 < M + π := by linarith
  have hpiM : 0 < π / (M + π) := div_pos hpi hMπ
  have hpiM1 : π / (M + π) < 1 / 2 := by
    rw [div_lt_iff₀ hMπ]; linarith
  have hr : 1 / 2 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  refine ⟨Z.center r, Z.t, Z.t_pos, Z.sphere_ne_zero hr hr1, Z.right_of_line hr hr1,
    Z.xi_ne_zero hr hr1, ?_⟩
  have hbound := Z.one_sub_seam_sq_le hr hr1
  have h1r : 1 - r = π / (M + π) := by rw [hrdef]; ring
  have h2 : π / (1 - r) = M + π := by
    rw [h1r]; field_simp
  have hlog : 12 * π / ε < Real.log (1 + π / (1 - r)) := by
    rw [h2]
    calc 12 * π / ε = Real.log (Real.exp (12 * π / ε)) := (Real.log_exp _).symm
      _ < Real.log (1 + (M + π)) :=
          Real.log_lt_log (Real.exp_pos _) (by linarith)
  have hlogpos : 0 < Real.log (1 + π / (1 - r)) := lt_trans (by positivity) hlog
  have hsmall1 : 6 * π / Real.log (1 + π / (1 - r)) < ε / 2 := by
    rw [div_lt_iff₀ hlogpos]
    have := (div_lt_iff₀ hε).mp hlog
    nlinarith
  have hsmall2 : 3 * (1 - r ^ 2) < ε / 2 := by
    have hfac : 1 - r ^ 2 ≤ 2 * (1 - r) := by nlinarith
    have hMε : 12 * π / ε < M := by linarith
    have h3 : 6 * (1 - r) < ε / 2 := by
      rw [h1r]
      rw [div_lt_iff₀ hε] at hMε
      rw [show 6 * (π / (M + π)) = 6 * π / (M + π) by ring, div_lt_iff₀ hMπ]
      nlinarith
    linarith
  set x := ‖(xiDiscDatum (Z.center r) Z.t Z.t_pos
    (Z.sphere_ne_zero hr hr1)).circlePhase.datum.adjointHankelSeam‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hsq : 1 - ε < x ^ 2 := by linarith
  by_cases hx1 : 1 ≤ x
  · linarith
  · push Not at hx1
    nlinarith

/-- No seam bound bounded away from one holds on all zero-free right discs of `xi`. -/
theorem not_exists_uniform_xiRightDisc_seam_margin :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0),
      (∀ z ∈ closedBall c t, 1 / 2 < z.re) → (∀ z ∈ closedBall c t, xi z ≠ 0) →
        ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ ≤ 1 - δ := by
  rintro ⟨δ, hδ, h⟩
  obtain ⟨c, t, ht, hne, hright, hzero, hgt⟩ := exists_zeroFree_xiRightDisc_adjointSeam_gt δ hδ
  have := h c t ht hne hright hzero
  linarith

end XiSeamSupremum

end RHTower
