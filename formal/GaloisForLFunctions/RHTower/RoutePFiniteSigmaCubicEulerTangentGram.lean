import GaloisForLFunctions.RHTower.RoutePFullHardyHalfPlanePolarization
import GaloisForLFunctions.RHTower.EulerPositiveGammaPoleCancellation

/-!
# Route P: finite-sigma cubic Euler tangent Gram

The cubic horizontal separator is already present before the critical limit.  At a projective
Hardy node, differentiation in divisor depth inserts the literal Euler logarithm.  The derivative
of the forced half-weighted two-scale packet is therefore a square-summable log-weighted Euler
vector.  Its exact finite-`sigma` Hilbert Gram converges to the cubic Hellinger kernel by combining
the first-order zeta residue with the second-order Euler log-moment residue.
-/

open Complex Filter Set
open scoped BigOperators Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Real Dirichlet exponent of the product of two projective full-Euler columns. -/
def routePProjectiveFullEulerPairExponent
    (sigma R a b : ℝ) : ℝ :=
  1 + R * (a + b) * (sigma - 1)

theorem one_lt_routePProjectiveFullEulerPairExponent
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    1 < routePProjectiveFullEulerPairExponent sigma R a b := by
  unfold routePProjectiveFullEulerPairExponent
  nlinarith [mul_pos (mul_pos hR (add_pos ha hb)) (sub_pos.mpr hsigma)]

theorem eulerPositiveComplexHardySquareExponent_projective
    (sigma R a : ℝ) :
    eulerPositiveComplexHardySquareExponent sigma
        (routePProjectiveHardyNode R a) =
      routePProjectiveFullEulerPairExponent sigma R a a := by
  simp only [eulerPositiveComplexHardySquareExponent,
    routePProjectiveFullEulerPairExponent, routePProjectiveHardyNode_re]
  ring

private theorem one_div_nat_cpow_eq_ofReal_eulerPositiveMass
    (tau : ℝ) (n : ℕ+) :
    1 / ((n : ℕ) : ℂ) ^ (tau : ℂ) =
      (eulerPositiveMass tau n : ℂ) := by
  rw [eulerPositiveMass, Complex.ofReal_cpow (by positivity)]
  rw [show ((-tau : ℝ) : ℂ) = -(tau : ℂ) by norm_cast,
    Complex.cpow_neg]
  rw [one_div]
  congr 1

/-- Coordinate product of two projective columns is the exact positive Dirichlet mass at their
pair exponent, divided by the original source partition function. -/
theorem routePProjectiveFullEulerPairWeight_eq_mass
    (sigma R a b : ℝ) (hsigma : 1 < sigma) (n : ℕ+) :
    eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveHardyNode R b) n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalComplexDampedStateWeight sigma
            (routePProjectiveHardyNode R a) n) =
      (eulerPositiveMass
          (routePProjectiveFullEulerPairExponent sigma R a b) n : ℂ) /
        (eulerPositiveTotal sigma : ℂ) := by
  rw [complexDamped_pair_apply,
    eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
  have hnorm : eulerPositiveStateWeight sigma n *
      (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
      (eulerPositiveProbability sigma n : ℂ) := by
    calc
      _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
        RCLike.mul_conj (eulerPositiveStateWeight sigma n)
      _ = _ := by
        rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
  rw [show
      Complex.exp
            (-(routePProjectiveHardyNode R b +
                (starRingEnd ℂ) (routePProjectiveHardyNode R a)) *
              ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        Complex.exp
            (-(routePProjectiveHardyNode R b +
                (starRingEnd ℂ) (routePProjectiveHardyNode R a)) *
              ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
    hnorm, eulerPositiveProbability, Complex.ofReal_div]
  rw [← mul_div_assoc, complexDamping_mul_eulerPositiveMass]
  have hparam :
      eulerPositiveComplexBoundaryParameter sigma
          (routePProjectiveHardyNode R b +
            (starRingEnd ℂ) (routePProjectiveHardyNode R a)) =
        (routePProjectiveFullEulerPairExponent sigma R a b : ℂ) := by
    simp only [eulerPositiveComplexBoundaryParameter,
      routePProjectiveHardyNode, Complex.conj_ofReal,
      routePProjectiveFullEulerPairExponent]
    push_cast
    ring
  rw [hparam, one_div_nat_cpow_eq_ofReal_eulerPositiveMass]

/-- Log-weighted projective Euler column, the coordinate derivative carrier. -/
def routePProjectiveFullEulerLogStateWeight
    (sigma R a : ℝ) (n : ℕ+) : ℂ :=
  (Real.log (n : ℕ) : ℂ) *
    eulerPositiveCriticalComplexDampedStateWeight sigma
      (routePProjectiveHardyNode R a) n

private theorem summable_norm_sq_routePProjectiveFullEulerLogStateWeight
    {sigma R a : ℝ} (hsigma : 1 < sigma) (hR : 0 < R) (ha : 0 < a) :
    Summable (fun n : ℕ+ =>
      ‖routePProjectiveFullEulerLogStateWeight sigma R a n‖ ^ 2) := by
  let tau := routePProjectiveFullEulerPairExponent sigma R a a
  have htau : 1 < tau :=
    one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha ha
  have hm := (summable_eulerPositiveLogMoment 2 htau).mul_left
    (eulerPositiveTotal tau / eulerPositiveTotal sigma)
  exact hm.congr fun n => by
    rw [routePProjectiveFullEulerLogStateWeight, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs,
      norm_sq_eulerPositiveCriticalComplexDampedStateWeight_eq_mass hsigma,
      eulerPositiveComplexHardySquareExponent_projective]
    rw [abs_of_nonneg (Real.log_natCast_nonneg (n : ℕ)),
      eulerPositiveProbability]
    dsimp only [tau]
    have htotalSigma := (eulerPositiveTotal_pos hsigma).ne'
    have htotalTau := (eulerPositiveTotal_pos htau).ne'
    dsimp only [tau] at htotalTau
    field_simp [htotalSigma, htotalTau]

/-- Actual square-summable log-weighted projective Euler column. -/
def routePProjectiveFullEulerLogStateLp
    (sigma R a : ℝ) (hsigma : 1 < sigma) (hR : 0 < R) (ha : 0 < a) :
    EulerPositiveL2 :=
  ⟨routePProjectiveFullEulerLogStateWeight sigma R a,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_routePProjectiveFullEulerLogStateWeight hsigma hR ha)⟩

/-- Exact second-log-moment inner product of two finite-`sigma` projective Euler columns. -/
theorem inner_routePProjectiveFullEulerLogStateLp_eq_moment
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (routePProjectiveFullEulerLogStateLp sigma R a hsigma hR ha)
        (routePProjectiveFullEulerLogStateLp sigma R b hsigma hR hb) =
      ((eulerPositiveTotal
              (routePProjectiveFullEulerPairExponent sigma R a b) /
            eulerPositiveTotal sigma : ℝ) : ℂ) *
        (eulerPositiveLogMoment 2
          (routePProjectiveFullEulerPairExponent sigma R a b) : ℂ) := by
  let tau := routePProjectiveFullEulerPairExponent sigma R a b
  have htau : 1 < tau :=
    one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha hb
  rw [lp.inner_eq_tsum]
  simp only [routePProjectiveFullEulerLogStateLp, RCLike.inner_apply]
  rw [show
      (∑' n : ℕ+,
        routePProjectiveFullEulerLogStateWeight sigma R b n *
          (starRingEnd ℂ)
            (routePProjectiveFullEulerLogStateWeight sigma R a n)) =
      ∑' n : ℕ+,
        ((eulerPositiveTotal tau / eulerPositiveTotal sigma : ℝ) : ℂ) *
          ((eulerPositiveProbability tau n *
            Real.log (n : ℕ) ^ 2 : ℝ) : ℂ) by
    apply tsum_congr
    intro n
    rw [routePProjectiveFullEulerLogStateWeight,
      routePProjectiveFullEulerLogStateWeight, map_mul,
      Complex.conj_ofReal]
    rw [show
        (Real.log (n : ℕ) : ℂ) *
              eulerPositiveCriticalComplexDampedStateWeight sigma
                (routePProjectiveHardyNode R b) n *
            ((Real.log (n : ℕ) : ℂ) *
              (starRingEnd ℂ)
                (eulerPositiveCriticalComplexDampedStateWeight sigma
                  (routePProjectiveHardyNode R a) n)) =
          ((Real.log (n : ℕ) : ℂ) * (Real.log (n : ℕ) : ℂ)) *
            (eulerPositiveCriticalComplexDampedStateWeight sigma
                (routePProjectiveHardyNode R b) n *
              (starRingEnd ℂ)
                (eulerPositiveCriticalComplexDampedStateWeight sigma
                  (routePProjectiveHardyNode R a) n)) by ring,
      routePProjectiveFullEulerPairWeight_eq_mass sigma R a b hsigma n]
    rw [eulerPositiveProbability]
    dsimp only [tau]
    have htotalSigma := (eulerPositiveTotal_pos hsigma).ne'
    have htotalTau := (eulerPositiveTotal_pos htau).ne'
    dsimp only [tau] at htotalTau
    have htotalSigmaC : (eulerPositiveTotal sigma : ℂ) ≠ 0 := by
      exact_mod_cast htotalSigma
    have htotalTauC :
        (eulerPositiveTotal
          (routePProjectiveFullEulerPairExponent sigma R a b) : ℂ) ≠ 0 := by
      exact_mod_cast htotalTau
    push_cast
    field_simp [htotalSigma, htotalTau, htotalSigmaC, htotalTauC]]
  rw [tsum_mul_left, eulerPositiveLogMoment, Complex.ofReal_tsum]

end

end RHTower
