import GaloisForLFunctions.RHTower.RoutePComplexPointedFourUnitPolarization
import GaloisForLFunctions.RHTower.RoutePCubicHardyMixedJetLanding

/-!
# Route P: full Hardy-half-plane polarization

The literal complex full-Euler column is square summable on its sharp source domain
`Re u > -1/2`, not merely on the sufficient inward chart `Re u >= 0`.  On this full domain the
projective nodes `R * a - 1/2` are admitted for every positive scale and depth.  Their finite-sigma
Euler overlaps converge, after the fixed projective scaling, to the universal Route-P Hardy
kernel.  Thus projective scale blow-up was a chart artifact rather than a source obstruction.
-/

open Complex Filter Set
open scoped BigOperators Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Real exponent controlling the squared norm of a complex-damped full-Euler column. -/
def eulerPositiveComplexHardySquareExponent (sigma : ℝ) (u : ℂ) : ℝ :=
  sigma + 2 * u.re * (sigma - 1)

theorem one_lt_eulerPositiveComplexHardySquareExponent
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    1 < eulerPositiveComplexHardySquareExponent sigma u := by
  unfold eulerPositiveComplexHardySquareExponent
  nlinarith [mul_pos (by nlinarith : 0 < 1 + 2 * u.re) (sub_pos.mpr hsigma)]

theorem one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    1 < (eulerPositiveComplexBoundaryParameter sigma u).re := by
  simp only [eulerPositiveComplexBoundaryParameter, add_re, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith [mul_pos (by nlinarith : 0 < 1 + u.re) (sub_pos.mpr hsigma)]

theorem norm_sq_eulerPositiveCriticalComplexDampedStateWeight_eq_mass
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (n : ℕ+) :
    ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ ^ 2 =
      eulerPositiveMass (eulerPositiveComplexHardySquareExponent sigma u) n /
        eulerPositiveTotal sigma := by
  rw [norm_eulerPositiveCriticalComplexDampedStateWeight,
    eulerPositiveCriticalDampedStateWeight, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    eulerPositiveCriticalDamping,
    abs_of_pos (Real.exp_pos _), mul_pow,
    norm_eulerPositiveStateWeight_sq hsigma,
    eulerPositiveProbability,
    eulerPositiveMass, eulerPositiveMass]
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hpow :
      Real.exp (-(u.re * (sigma - 1) * Real.log (n : ℕ))) =
        ((n : ℕ) : ℝ) ^ (-(u.re * (sigma - 1))) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  rw [hpow]
  rw [← Real.rpow_natCast (((n : ℕ) : ℝ) ^ (-(u.re * (sigma - 1)))) 2,
    ← Real.rpow_mul hnpos.le]
  simp only [div_eq_mul_inv]
  rw [← mul_assoc, ← Real.rpow_add hnpos]
  have hexponent :
      -(u.re * (sigma - 1)) * ((2 : ℕ) : ℝ) + -sigma =
        -eulerPositiveComplexHardySquareExponent sigma u := by
    unfold eulerPositiveComplexHardySquareExponent
    ring
  rw [hexponent]

private theorem summable_norm_sq_eulerPositiveCriticalComplexHardyStateWeight
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ ^ 2) := by
  have hmass := summable_eulerPositiveMass
    (one_lt_eulerPositiveComplexHardySquareExponent hsigma hu)
  exact (hmass.div_const (eulerPositiveTotal sigma)).congr fun n =>
    (norm_sq_eulerPositiveCriticalComplexDampedStateWeight_eq_mass hsigma n).symm

/-- Actual full-Euler column on the sharp Hardy source half-plane `Re u > -1/2`. -/
def eulerPositiveCriticalComplexHardyStateLp
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    EulerPositiveL2 :=
  ⟨eulerPositiveCriticalComplexDampedStateWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveCriticalComplexHardyStateWeight hsigma hu)⟩

/-- The base column paired with any full-Hardy-half-plane column is the exact Euler overlap. -/
theorem inner_eulerPositiveState_complexHardy_eq_affineOverlap
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    inner ℂ (eulerPositiveStateLp sigma hsigma)
        (eulerPositiveCriticalComplexHardyStateLp sigma u hsigma hu) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) u := by
  have hshift :=
    one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt hsigma hu
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveStateLp,
    eulerPositiveCriticalComplexHardyStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalComplexDampedStateWeight sigma u n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
      ∑' n : ℕ+,
        (Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveMass sigma n : ℂ)) /
            (eulerPositiveTotal sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
    have hnorm : eulerPositiveStateWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
      hnorm, eulerPositiveProbability, Complex.ofReal_div]
    rw [← mul_div_assoc]]
  rw [tsum_div_const, tsum_complexDamping_eulerPositiveMass hshift,
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
  rfl

/-- Exact non-diagonal Gram on the complete natural source domain `Re u, Re v > -1/2`. -/
theorem inner_eulerPositiveComplexHardy_complexHardy_eq_affineOverlap
    {sigma : ℝ} {u v : ℂ} (hsigma : 1 < sigma)
    (hu : -1 / 2 < u.re) (hv : -1 / 2 < v.re) :
    inner ℂ
        (eulerPositiveCriticalComplexHardyStateLp sigma u hsigma hu)
        (eulerPositiveCriticalComplexHardyStateLp sigma v hsigma hv) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) (v + (starRingEnd ℂ) u) := by
  have hsum : -1 < (v + (starRingEnd ℂ) u).re := by
    simp only [add_re, Complex.conj_re]
    linarith
  have hshift :
      1 < (eulerPositiveComplexBoundaryParameter sigma
        (v + (starRingEnd ℂ) u)).re := by
    simp only [eulerPositiveComplexBoundaryParameter, add_re, mul_re,
      ofReal_re, ofReal_im, mul_zero, sub_zero, Complex.conj_re]
    nlinarith [mul_pos (by linarith : 0 < 1 + v.re + u.re)
      (sub_pos.mpr hsigma)]
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveCriticalComplexHardyStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalComplexDampedStateWeight sigma v n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalComplexDampedStateWeight sigma u n)) =
      ∑' n : ℕ+,
        (Complex.exp
            (-(v + (starRingEnd ℂ) u) * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveMass sigma n : ℂ)) /
            (eulerPositiveTotal sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [complexDamped_pair_apply]
    rw [eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
    have hnorm : eulerPositiveStateWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      Complex.exp
            (-(v + (starRingEnd ℂ) u) * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        Complex.exp
            (-(v + (starRingEnd ℂ) u) * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
      hnorm, eulerPositiveProbability, Complex.ofReal_div]
    rw [← mul_div_assoc]]
  rw [tsum_div_const, tsum_complexDamping_eulerPositiveMass hshift,
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
  rfl

/-- Every positive projective node lies strictly inside the sharp source half-plane. -/
theorem neg_half_lt_routePProjectiveHardyNode_re
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    -1 / 2 < (routePProjectiveHardyNode R a).re := by
  rw [routePProjectiveHardyNode_re]
  nlinarith [mul_pos hR ha]

/-- Finite-sigma projective full-Euler overlap, before taking the critical source boundary. -/
theorem inner_eulerPositiveComplexHardy_projective_eq_zetaRatio
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (eulerPositiveCriticalComplexHardyStateLp sigma
          (routePProjectiveHardyNode R a) hsigma
          (neg_half_lt_routePProjectiveHardyNode_re hR ha))
        (eulerPositiveCriticalComplexHardyStateLp sigma
          (routePProjectiveHardyNode R b) hsigma
          (neg_half_lt_routePProjectiveHardyNode_re hR hb)) =
      riemannZeta (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) /
        riemannZeta (sigma : ℂ) := by
  rw [inner_eulerPositiveComplexHardy_complexHardy_eq_affineOverlap]
  unfold eulerAffineBoundaryOverlap
  congr 2
  simp only [routePProjectiveHardyNode, Complex.conj_ofReal]
  push_cast
  ring

/-- Projectively rescaled finite-`sigma` zeta overlap of two full-Hardy Euler columns. -/
def routePProjectiveFullEulerZetaOverlap (R a b sigma : ℝ) : ℂ :=
  (R : ℂ) *
    (riemannZeta (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) /
      riemannZeta (sigma : ℂ))

/-- The rescaled zeta overlap is not a fitted kernel: it is exactly the inner product of the
genuine square-summable full-Euler columns at every `sigma > 1`. -/
theorem routePProjectiveFullEulerZetaOverlap_eq_scaled_inner
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    routePProjectiveFullEulerZetaOverlap R a b sigma =
      (R : ℂ) *
        inner ℂ
          (eulerPositiveCriticalComplexHardyStateLp sigma
            (routePProjectiveHardyNode R a) hsigma
            (neg_half_lt_routePProjectiveHardyNode_re hR ha))
          (eulerPositiveCriticalComplexHardyStateLp sigma
            (routePProjectiveHardyNode R b) hsigma
            (neg_half_lt_routePProjectiveHardyNode_re hR hb)) := by
  rw [inner_eulerPositiveComplexHardy_projective_eq_zetaRatio hsigma hR ha hb]
  rfl

/-- Pole cancellation turns every fixed positive projective scale of the genuine Euler source into
the universal Hardy kernel.  The scale `R` disappears exactly, rather than being sent to infinity. -/
theorem tendsto_routePProjectiveFullEulerZetaOverlap
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (routePProjectiveFullEulerZetaOverlap R a b)
      (nhdsWithin 1 (Ioi 1))
      (nhds (((1 / (a + b) : ℝ) : ℂ))) := by
  let q : ℂ := ((a + b : ℝ) : ℂ)
  have hab : 0 < a + b := add_pos ha hb
  have hq : q ≠ 0 := by
    exact ofReal_ne_zero.mpr (ne_of_gt hab)
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hparam : Tendsto
      (fun sigma : ℝ =>
        ((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          ((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hunitSigma : Tendsto
      (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
    simpa only [Function.comp_def, zetaResidueUnit_one] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hunitParam : Tendsto
      (fun sigma : ℝ =>
        zetaResidueUnit
          (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
    simpa only [Function.comp_def, zetaResidueUnit_one] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hparam
  have hregularized : Tendsto
      (fun sigma : ℝ =>
        zetaResidueUnit
              (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) /
          (zetaResidueUnit (sigma : ℂ) * q))
      (nhdsWithin 1 (Ioi 1)) (nhds q⁻¹) := by
    have h := hunitParam.div (hunitSigma.mul_const q)
      (mul_ne_zero one_ne_zero hq)
    have hfun :
        ((fun sigma : ℝ =>
            zetaResidueUnit
              (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ))) /
          (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ) * q)) =
        (fun sigma : ℝ =>
          zetaResidueUnit
                (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) /
            (zetaResidueUnit (sigma : ℂ) * q)) := by
      funext sigma
      rfl
    rw [hfun] at h
    simpa only [one_mul, one_div] using h
  have htarget : q⁻¹ = (((1 / (a + b) : ℝ) : ℂ)) := by
    rw [show ((1 / (a + b) : ℝ) : ℂ) = (1 : ℂ) / q by
      simp only [q, Complex.ofReal_div, Complex.ofReal_one]]
    exact (one_div q).symm
  rw [htarget] at hregularized
  apply hregularized.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigmaGt
  have hscale : 0 < R * (a + b) := mul_pos hR hab
  have hparamGt : 1 < 1 + R * (a + b) * (sigma - 1) := by
    nlinarith [mul_pos hscale (sub_pos.mpr hsigmaGt)]
  have hparamOne : 1 + R * (a + b) * (sigma - 1) ≠ 1 :=
    ne_of_gt hparamGt
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
  have hparamZeta :
      1 < (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)).re := by
    simpa using hparamGt
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  have hunitPar :
      zetaResidueUnit
          (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) =
        ((((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) - 1) *
          riemannZeta
            (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) := by
    rw [zetaResidueUnit,
      Function.update_of_ne (by exact_mod_cast hparamOne)]
  rw [routePProjectiveFullEulerZetaOverlap, hunitSig, hunitPar]
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  have hparamOneC :
      (((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hparamOne)
  field_simp [hq, hsigOneC, hparamOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta]
  unfold q
  push_cast
  ring

/-- The transverse Fisher source reports its exact holomorphic score on the full source domain. -/
theorem inner_eulerPositiveFisherTangent_complexHardy_eq_affineScore
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    inner ℂ (eulerPositiveCriticalFisherTangentLp sigma hsigma)
        (eulerPositiveCriticalComplexHardyStateLp sigma u hsigma hu) =
      eulerAffineFisherScore (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) u := by
  have hshift :=
    one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt hsigma hu
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveCriticalFisherTangentLp,
    eulerPositiveCriticalComplexHardyStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalComplexDampedStateWeight sigma u n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalFisherTangentWeight sigma n)) =
      ((-2 * (sigma - 1 : ℝ) : ℝ) : ℂ) /
          (eulerPositiveTotal sigma : ℂ) *
        ∑' n : ℕ+,
          (Complex.exp
                (-u * ((sigma - 1 : ℝ) : ℂ) *
                  ((Real.log (n : ℕ) : ℝ) : ℂ)) *
              (eulerPositiveMass sigma n : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ) -
            ((eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) *
              (Complex.exp
                  (-u * ((sigma - 1 : ℝ) : ℂ) *
                    ((Real.log (n : ℕ) : ℝ) : ℂ)) *
                (eulerPositiveMass sigma n : ℂ))) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalComplexDampedStateWeight_eq_exp,
      eulerPositiveCriticalFisherTangentWeight]
    simp only [map_mul, conj_ofReal]
    have hnorm : eulerPositiveStateWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
          (((-2 * (sigma - 1) *
              (Real.log (n : ℕ) -
                eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
        ((-2 * (sigma - 1) : ℝ) : ℂ) *
          (Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (eulerPositiveStateWeight sigma n *
              (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) *
            (((Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma : ℝ) : ℂ))) by
        push_cast
        ring,
      hnorm, eulerPositiveProbability, Complex.ofReal_div]
    push_cast
    ring]
  have hlogSum : Summable (fun n : ℕ+ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ) *
          ((Real.log (n : ℕ) : ℝ) : ℂ)) := by
    have hnat := summable_complexEulerLogDirichlet hshift
    have hpnat : Summable (fun n : ℕ+ =>
        (Real.log (n : ℕ) : ℂ) /
          ((n : ℕ) : ℂ) ^ eulerPositiveComplexBoundaryParameter sigma u) := by
      simpa only [Function.comp_apply] using!
        hnat.subtype (fun n : ℕ => 0 < n)
    exact hpnat.congr fun n => by
      rw [show
        Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (eulerPositiveMass sigma n : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ) =
          ((Real.log (n : ℕ) : ℝ) : ℂ) *
            (Complex.exp
                (-u * ((sigma - 1 : ℝ) : ℂ) *
                  ((Real.log (n : ℕ) : ℝ) : ℂ)) *
              (eulerPositiveMass sigma n : ℂ)) by ring,
        complexDamping_mul_eulerPositiveMass]
      simp only [div_eq_mul_inv, one_mul]
  have hmass : Summable (fun n : ℕ+ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ)) := by
    have hs : Summable (fun n : ℕ+ =>
        1 / ((n : ℕ) : ℂ) ^
          eulerPositiveComplexBoundaryParameter sigma u) := by
      have hnat := Complex.summable_one_div_nat_cpow.mpr hshift
      simpa only [Function.comp_apply] using!
        hnat.subtype (fun n : ℕ => 0 < n)
    exact hs.congr fun n =>
      (complexDamping_mul_eulerPositiveMass sigma u n).symm
  have htotal : (eulerPositiveTotal sigma : ℂ) =
      riemannZeta (sigma : ℂ) :=
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma
  have hbase : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  rw [hlogSum.tsum_sub (hmass.mul_left
      ((eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)),
    tsum_mul_left,
    tsum_complexDamping_eulerPositiveMass_mul_log hshift,
    tsum_complexDamping_eulerPositiveMass hshift,
    htotal,
    ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hsigma,
    eulerAffineFisherScore_eq_current_difference
      (by simpa using hsigma) hshift]
  simp only [eulerAffineBoundaryOverlap,
    eulerPositiveComplexBoundaryParameter]
  field_simp [hbase]
  push_cast
  ring

theorem eulerPositivePreScalarComplexGraphDenominator_ne_zero_of_neg_half_lt
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    eulerPositivePreScalarComplexGraphDenominator sigma u ≠ 0 := by
  have hshift :=
    one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt hsigma hu
  unfold eulerPositivePreScalarComplexGraphDenominator
  apply mul_ne_zero
  · exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  · unfold eulerAffineBoundaryOverlap
    apply div_ne_zero
    · exact riemannZeta_ne_zero_of_one_lt_re hshift
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)

/-- Graph-normal coefficient on the complete Hardy source half-plane. -/
def eulerPositivePreScalarHardyGraphNormalizedCoefficient
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : -1 / 2 < u.re)
    (source : EulerPositiveL2) : ℂ :=
  inner ℂ source
      (eulerPositiveCriticalComplexHardyStateLp sigma u hsigma hu) /
    eulerPositivePreScalarComplexGraphDenominator sigma u

theorem eulerPositivePreScalarHardyGraphNormalizedCoefficient_transverse
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    eulerPositivePreScalarHardyGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) =
      2 * (infinitePrimeFlux (eulerPositiveComplexBoundaryParameter sigma u) -
        infinitePrimeFlux (sigma : ℂ)) := by
  rw [eulerPositivePreScalarHardyGraphNormalizedCoefficient,
    eulerPositivePreScalarGammaTransverseSource, inner_neg_left,
    inner_eulerPositiveFisherTangent_complexHardy_eq_affineScore hsigma hu]
  have hden :=
    eulerPositivePreScalarComplexGraphDenominator_ne_zero_of_neg_half_lt hsigma hu
  apply (div_eq_iff hden).2
  rw [eulerAffineFisherScore_eq_current_difference
      (by simpa using hsigma)
      (one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt hsigma hu)]
  unfold eulerPositivePreScalarComplexGraphDenominator
  simp only [eulerPositiveComplexBoundaryParameter]
  ring

/-- Exact pointed continued-Xi reporter throughout the full Hardy source half-plane. -/
def eulerPositiveTransverseGammaXiHardyPointedReporter
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) : ℂ :=
  (-I / 2) *
    (eulerPositivePreScalarHardyGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) -
      2 * (logDeriv archFactor
              (eulerPositiveComplexBoundaryParameter sigma u) -
            logDeriv archFactor (sigma : ℂ)))

theorem eulerPositiveTransverseGammaXiHardyPointedReporter_eq_continued_sub_base
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    eulerPositiveTransverseGammaXiHardyPointedReporter sigma u hsigma hu =
      continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (eulerPositiveComplexBoundaryParameter sigma u)) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (sigma : ℂ)) := by
  rw [eulerPositiveTransverseGammaXiHardyPointedReporter,
    eulerPositivePreScalarHardyGraphNormalizedCoefficient_transverse hsigma hu]
  simp only [continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]
  ring

/-- Actual augmented source packet on the complete natural source domain. -/
def eulerPositiveComplexHardyPointedTransverseVector
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) :
    Fin n ⊕ Unit → EulerPositiveL2
  | Sum.inl i =>
      eulerPositiveCriticalComplexHardyStateLp sigma (u i) hsigma (hu i)
  | Sum.inr _ => eulerPositivePreScalarGammaTransverseSource sigma hsigma

def eulerPositiveComplexHardyPointedTransverseGram
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.gram ℂ (eulerPositiveComplexHardyPointedTransverseVector sigma hsigma u hu)

theorem eulerPositiveComplexHardyPointedTransverseGram_posSemidef
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) :
    (eulerPositiveComplexHardyPointedTransverseGram sigma hsigma u hu).PosSemidef :=
  Matrix.posSemidef_gram ℂ
    (eulerPositiveComplexHardyPointedTransverseVector sigma hsigma u hu)

theorem eulerPositiveComplexHardyPointedTransverseGram_topLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) (i j : Fin n) :
    eulerPositiveComplexHardyPointedTransverseGram sigma hsigma u hu
        (Sum.inl i) (Sum.inl j) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ)
        (u j + (starRingEnd ℂ) (u i)) := by
  exact inner_eulerPositiveComplexHardy_complexHardy_eq_affineOverlap
    hsigma (hu i) (hu j)

theorem eulerPositiveComplexHardyPointedTransverseGram_bottomLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) (i : Fin n) :
    eulerPositiveComplexHardyPointedTransverseGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inl i) =
      -eulerAffineFisherScore (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) (u i) := by
  change inner ℂ (eulerPositivePreScalarGammaTransverseSource sigma hsigma)
      (eulerPositiveCriticalComplexHardyStateLp sigma (u i) hsigma (hu i)) = _
  rw [eulerPositivePreScalarGammaTransverseSource, inner_neg_left,
    inner_eulerPositiveFisherTangent_complexHardy_eq_affineScore hsigma (hu i)]

theorem eulerPositiveComplexHardyPointedTransverseGram_bottomRight
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, -1 / 2 < (u i).re) :
    eulerPositiveComplexHardyPointedTransverseGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inr ()) =
      (eulerPositiveCriticalProjectiveFisherEnergy sigma : ℂ) := by
  change inner ℂ (eulerPositivePreScalarGammaTransverseSource sigma hsigma)
      (eulerPositivePreScalarGammaTransverseSource sigma hsigma) = _
  rw [inner_self_eq_norm_sq_to_K]
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (norm_eulerPositivePreScalarGammaTransverseSource_sq hsigma)
  push_cast at h
  exact h

end

end RHTower
