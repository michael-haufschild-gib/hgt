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

/-- Coordinate derivative of a literal projective full-Euler column. -/
theorem hasDerivAt_routePProjectiveFullEulerStateWeight
    (sigma R x : ℝ) (n : ℕ+) :
    HasDerivAt
      (fun a : ℝ =>
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveHardyNode R a) n)
      (-((R * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) *
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveHardyNode R x) n)
      x := by
  have hnodeReal : HasDerivAt
      (fun a : ℝ => R * a - 1 / 2) R x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul R).sub_const (1 / 2)
  have hnode : HasDerivAt
      (fun a : ℝ => routePProjectiveHardyNode R a) (R : ℂ) x := by
    simpa only [routePProjectiveHardyNode] using hnodeReal.ofReal_comp
  have harg := ((hnode.neg.mul_const (((sigma - 1 : ℝ) : ℂ))).mul_const
    ((Real.log (n : ℕ) : ℝ) : ℂ))
  have hexp := harg.cexp.mul_const (eulerPositiveStateWeight sigma n)
  have hder :
      Complex.exp
            (-routePProjectiveHardyNode R x * (((sigma - 1 : ℝ) : ℂ)) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (-((R : ℂ)) * (((sigma - 1 : ℝ) : ℂ)) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n =
        -((R * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) *
          (Complex.exp
              (-routePProjectiveHardyNode R x * (((sigma - 1 : ℝ) : ℂ)) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            eulerPositiveStateWeight sigma n) := by
    push_cast
    ring
  simpa only [eulerPositiveCriticalComplexDampedStateWeight_eq_exp,
    Pi.neg_apply] using hexp.congr_deriv hder

/-- Coordinate form of P-G168's forced half-weighted projective source packet. -/
def routePProjectiveFullEulerHalfWeightedStateWeight
    (sigma R a : ℝ) (n : ℕ+) : ℂ :=
  (Real.sqrt R : ℂ) *
    (eulerPositiveCriticalComplexDampedStateWeight sigma
        (routePProjectiveHardyNode R a) n -
      (1 / 2 : ℂ) *
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveHardyNode R (2 * a)) n)

/-- Direct coordinate formula for the finite-`sigma` Hellinger source tangent. -/
def routePProjectiveFullEulerHellingerTangentWeight
    (sigma R a : ℝ) (n : ℕ+) : ℂ :=
  ((Real.sqrt R * (R * (sigma - 1)) : ℝ) : ℂ) *
    (routePProjectiveFullEulerLogStateWeight sigma R (2 * a) n -
      routePProjectiveFullEulerLogStateWeight sigma R a n)

/-- The half weight cancels the doubled-node chain rule exactly: the constructed log-weighted
Euler vector is the coordinate derivative of the actual half-weighted source packet. -/
theorem hasDerivAt_routePProjectiveFullEulerHalfWeightedStateWeight
    (sigma R a : ℝ) (n : ℕ+) :
    HasDerivAt
      (fun x : ℝ =>
        routePProjectiveFullEulerHalfWeightedStateWeight sigma R x n)
      (routePProjectiveFullEulerHellingerTangentWeight sigma R a n)
      a := by
  have h1 := hasDerivAt_routePProjectiveFullEulerStateWeight sigma R a n
  have h2base := hasDerivAt_routePProjectiveFullEulerStateWeight sigma R (2 * a) n
  have hdouble : HasDerivAt (fun x : ℝ => 2 * x) 2 a := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id a).const_mul 2
  have h2 := h2base.scomp a hdouble
  have hpacket :=
    (h1.sub (h2.const_mul (1 / 2 : ℂ))).const_mul (Real.sqrt R : ℂ)
  have hpacket' := hpacket.congr_deriv
    (g' := routePProjectiveFullEulerHellingerTangentWeight sigma R a n) (by
    unfold routePProjectiveFullEulerHellingerTangentWeight
      routePProjectiveFullEulerLogStateWeight
    simp only [two_smul]
    push_cast
    ring)
  apply hpacket'.congr_of_eventuallyEq
  filter_upwards with x
  simp only [routePProjectiveFullEulerHalfWeightedStateWeight,
    Function.comp_apply, Pi.sub_apply]

/-- One finite-`sigma` log-moment Gram term, already normalized by the projective source scale. -/
def routePProjectiveFullEulerLogMomentGramTerm
    (R a b sigma : ℝ) : ℂ :=
  routePProjectiveFullEulerZetaOverlap R a b sigma *
    (((R * (sigma - 1)) ^ 2 *
      eulerPositiveLogMoment 2
        (routePProjectiveFullEulerPairExponent sigma R a b) : ℝ) : ℂ)

/-- The scalar Gram term is exactly the scaled inner product of two actual log-weighted Euler
columns. -/
theorem routePProjectiveFullEulerLogMomentGramTerm_eq_scaled_inner
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    ((((Real.sqrt R * (R * (sigma - 1))) ^ 2 : ℝ) : ℂ) *
      inner ℂ
        (routePProjectiveFullEulerLogStateLp sigma R a hsigma hR ha)
        (routePProjectiveFullEulerLogStateLp sigma R b hsigma hR hb)) =
      routePProjectiveFullEulerLogMomentGramTerm R a b sigma := by
  let tau := routePProjectiveFullEulerPairExponent sigma R a b
  have htau : 1 < tau :=
    one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha hb
  rw [inner_routePProjectiveFullEulerLogStateLp_eq_moment hsigma hR ha hb,
    routePProjectiveFullEulerLogMomentGramTerm,
    routePProjectiveFullEulerZetaOverlap]
  have htotalSigma := ofReal_eulerPositiveTotal_eq_riemannZeta hsigma
  have htotalTau := ofReal_eulerPositiveTotal_eq_riemannZeta htau
  dsimp only [tau] at htotalTau
  rw [show
    (1 + R * (a + b) * (sigma - 1) : ℝ) =
      routePProjectiveFullEulerPairExponent sigma R a b by rfl]
  rw [← htotalSigma, ← htotalTau]
  rw [mul_pow, Real.sq_sqrt hR.le]
  push_cast
  ring

/-- Actual finite-`sigma` source tangent of the half-weighted two-scale projective packet. -/
def routePProjectiveFullEulerHellingerTangentLp
    (sigma R a : ℝ) (hsigma : 1 < sigma) (hR : 0 < R) (ha : 0 < a) :
    EulerPositiveL2 :=
  (((Real.sqrt R * (R * (sigma - 1)) : ℝ) : ℂ) •
    (routePProjectiveFullEulerLogStateLp sigma R (2 * a) hsigma hR
        (mul_pos two_pos ha) -
      routePProjectiveFullEulerLogStateLp sigma R a hsigma hR ha))

/-- The Hilbert tangent has exactly the coordinate derivative weight constructed above. -/
@[simp] theorem routePProjectiveFullEulerHellingerTangentLp_apply
    {sigma R a : ℝ} (hsigma : 1 < sigma) (hR : 0 < R) (ha : 0 < a)
    (n : ℕ+) :
    routePProjectiveFullEulerHellingerTangentLp sigma R a hsigma hR ha n =
      routePProjectiveFullEulerHellingerTangentWeight sigma R a n := by
  rfl

/-- Four-term finite-`sigma` arithmetic Gram of the half-weighted source tangents. -/
def routePProjectiveFullEulerCubicTangentGram
    (R a b sigma : ℝ) : ℂ :=
  routePProjectiveFullEulerLogMomentGramTerm R a b sigma -
    routePProjectiveFullEulerLogMomentGramTerm R a (2 * b) sigma -
    routePProjectiveFullEulerLogMomentGramTerm R (2 * a) b sigma +
    routePProjectiveFullEulerLogMomentGramTerm R (2 * a) (2 * b) sigma

/-- The four arithmetic terms are exactly the Hilbert Gram of the genuine finite-`sigma` tangent
vectors, before any critical limit. -/
theorem inner_routePProjectiveFullEulerHellingerTangentLp_eq_cubicTangentGram
    {sigma R a b : ℝ} (hsigma : 1 < sigma) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (routePProjectiveFullEulerHellingerTangentLp
          sigma R a hsigma hR ha)
        (routePProjectiveFullEulerHellingerTangentLp
          sigma R b hsigma hR hb) =
      routePProjectiveFullEulerCubicTangentGram R a b sigma := by
  have h2a : 0 < 2 * a := mul_pos two_pos ha
  have h2b : 0 < 2 * b := mul_pos two_pos hb
  have hab := routePProjectiveFullEulerLogMomentGramTerm_eq_scaled_inner
    hsigma hR ha hb
  have ha2b := routePProjectiveFullEulerLogMomentGramTerm_eq_scaled_inner
    hsigma hR ha h2b
  have h2ab := routePProjectiveFullEulerLogMomentGramTerm_eq_scaled_inner
    hsigma hR h2a hb
  have h2a2b := routePProjectiveFullEulerLogMomentGramTerm_eq_scaled_inner
    hsigma hR h2a h2b
  rw [routePProjectiveFullEulerHellingerTangentLp,
    routePProjectiveFullEulerHellingerTangentLp,
    routePProjectiveFullEulerCubicTangentGram,
    ← hab, ← ha2b, ← h2ab, ← h2a2b]
  simp only [inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, Complex.conj_ofReal]
  push_cast
  ring

/-- The projective second log moment has the forced inverse-square critical profile. -/
theorem tendsto_routePProjectiveFullEuler_scaledSecondLogMoment
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun sigma : ℝ =>
        (R * (sigma - 1)) ^ 2 *
          eulerPositiveLogMoment 2
            (routePProjectiveFullEulerPairExponent sigma R a b))
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 / (a + b) ^ 2)) := by
  let param : ℝ → ℝ := fun sigma =>
    routePProjectiveFullEulerPairExponent sigma R a b
  have hab : 0 < a + b := add_pos ha hb
  have hparamNhds : Tendsto param
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have hcont : ContinuousAt param 1 := by
      unfold param routePProjectiveFullEulerPairExponent
      fun_prop
    simpa [param, routePProjectiveFullEulerPairExponent] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hparamMem : ∀ᶠ sigma in nhdsWithin 1 (Ioi 1), param sigma ∈ Ioi 1 := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    exact one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha hb
  have hparamWithin : Tendsto param
      (nhdsWithin 1 (Ioi 1)) (nhdsWithin 1 (Ioi 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hparamNhds, hparamMem⟩
  have hbase := tendsto_sub_one_sq_mul_eulerPositiveLogMoment_two.comp
    hparamWithin
  have hscaled := hbase.div_const ((a + b) ^ 2)
  apply hscaled.congr'
  filter_upwards with sigma
  have hparamEq : param sigma - 1 =
      R * (a + b) * (sigma - 1) := by
    unfold param routePProjectiveFullEulerPairExponent
    ring
  change
    ((param sigma - 1) ^ 2 * eulerPositiveLogMoment 2 (param sigma)) /
        (a + b) ^ 2 =
      (R * (sigma - 1)) ^ 2 * eulerPositiveLogMoment 2 (param sigma)
  rw [hparamEq]
  field_simp [hab.ne']

/-- Each normalized finite-`sigma` source Gram term converges to one cubic Laplace term. -/
theorem tendsto_routePProjectiveFullEulerLogMomentGramTerm
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (routePProjectiveFullEulerLogMomentGramTerm R a b)
      (nhdsWithin 1 (Ioi 1))
      (nhds (((2 / (a + b) ^ 3 : ℝ) : ℂ))) := by
  have hoverlap := tendsto_routePProjectiveFullEulerZetaOverlap hR ha hb
  have hmomentReal :=
    tendsto_routePProjectiveFullEuler_scaledSecondLogMoment hR ha hb
  have hmoment : Tendsto
      (fun sigma : ℝ =>
        (((R * (sigma - 1)) ^ 2 *
          eulerPositiveLogMoment 2
            (routePProjectiveFullEulerPairExponent sigma R a b) : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1))
      (nhds (((2 / (a + b) ^ 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmomentReal
  have hprod := hoverlap.mul hmoment
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  convert hprod using 1
  · rfl
  · push_cast
    field_simp [hab]

/-- **Finite-sigma cubic source landing.** The exact arithmetic Hilbert Gram of the projective
Euler tangents converges to the Route-P cubic horizontal separator. -/
theorem tendsto_routePProjectiveFullEulerCubicTangentGram
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (routePProjectiveFullEulerCubicTangentGram R a b)
      (nhdsWithin 1 (Ioi 1))
      (nhds (cubicLogMomentHellingerHorizontalKernel a b : ℂ)) := by
  have h1 := tendsto_routePProjectiveFullEulerLogMomentGramTerm hR ha hb
  have h2 := tendsto_routePProjectiveFullEulerLogMomentGramTerm hR ha
    (mul_pos two_pos hb)
  have h3 := tendsto_routePProjectiveFullEulerLogMomentGramTerm hR
    (mul_pos two_pos ha) hb
  have h4 := tendsto_routePProjectiveFullEulerLogMomentGramTerm hR
    (mul_pos two_pos ha) (mul_pos two_pos hb)
  have h := ((h1.sub h2).sub h3).add h4
  rw [cubicLogMomentHellingerHorizontalKernel_eq_laplace ha hb]
  have hlimit :
      ((2 / (a + b) ^ 3 : ℝ) : ℂ) -
          ((2 / (a + 2 * b) ^ 3 : ℝ) : ℂ) -
          ((2 / (2 * a + b) ^ 3 : ℝ) : ℂ) +
          ((2 / (2 * a + 2 * b) ^ 3 : ℝ) : ℂ) =
        ((2 / (a + b) ^ 3 - 2 / (a + 2 * b) ^ 3 -
          2 / (2 * a + b) ^ 3 + 2 / (2 * a + 2 * b) ^ 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hlimit] at h
  apply h.congr'
  filter_upwards with sigma
  rfl

end

end RHTower
