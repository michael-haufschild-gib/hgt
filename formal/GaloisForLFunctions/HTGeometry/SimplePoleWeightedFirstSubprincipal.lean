import GaloisForLFunctions.HTGeometry.GammaPoleBinomialSubprincipalDescent
import GaloisForLFunctions.HTGeometry.GammaPoleWeightedCovariantAsymptotic
import GaloisForLFunctions.HTGeometry.MvPolynomialSmoothEvaluation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# First subprincipal reflection for weighted simple-pole jet packets

The maximal weighted boundary of a simple-pole jet polynomial is its evaluation on the principal
coefficient frame.  When that value cancels, this module identifies the entire next boundary:
only replacement of the unique weight-one coordinate can lose exactly one pole grade.  The
survivor is the `X₀` partial derivative of the packet at the principal frame, multiplied by the
finite part of the base jet.

Thus an arbitrary weighted-homogeneous cancellation is reflected one grade lower by a canonical
algebraic directional derivative.  A nonzero reflected derivative and finite part give an exact
meromorphic order.  This general law contains the binomial quadratic descent family as its basic
divided-power instance.
-/

open Complex Filter Topology Finset MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- A polynomial curve vanishing at the origin has first quotient limit equal to its algebraic
directional derivative. -/
theorem tendsto_inv_mul_mvPolynomial_eval_curve_of_eval_zero
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (g : Fin n → ℂ → ℂ) (g' : Fin n → ℂ)
    (hg : ∀ i, HasDerivAt (g i) (g' i) 0)
    (hzero : MvPolynomial.eval (fun i => g i 0) P = 0) :
    Tendsto
      (fun z : ℂ => z⁻¹ * MvPolynomial.eval (fun i => g i z) P)
      (𝓝[≠] 0)
      (𝓝 (∑ i, MvPolynomial.eval (fun q => g q 0) (MvPolynomial.pderiv i P) * g' i)) := by
  have hd := HTGeometry.hasDerivAt_mvPolynomial_eval_curve_complex P g g' 0 hg
  have hs := hd.tendsto_slope_zero
  simpa [hzero] using hs

/-- Analytic extension of the pole-normalized `q`th simple-pole jet. -/
def simplePoleJetNormalizedExtension (U : ℂ → ℂ) (q : ℕ) (x : ℂ) : ℂ :=
  simplePoleJetPrincipalCoefficient U q +
    x ^ (q + 1) * simplePoleJetRegularRemainder U q x

theorem analyticAt_simplePoleJetNormalizedExtension
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (q : ℕ) :
    AnalyticAt ℂ (simplePoleJetNormalizedExtension U q) 0 := by
  exact analyticAt_const.add ((analyticAt_id.pow (q + 1)).mul
    (analyticAt_simplePoleJetRegularRemainder hU q))

theorem simplePoleJetNormalizedExtension_zero (U : ℂ → ℂ) (q : ℕ) :
    simplePoleJetNormalizedExtension U q 0 = simplePoleJetPrincipalCoefficient U q := by
  simp [simplePoleJetNormalizedExtension]

/-- The normalized jet curve has a nonzero first tangent only in the weight-one coordinate. -/
theorem hasDerivAt_simplePoleJetNormalizedExtension
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (q : ℕ) :
    HasDerivAt (simplePoleJetNormalizedExtension U q)
      (if q = 0 then simplePoleJetRegularRemainder U 0 0 else 0) 0 := by
  have hpow := (hasDerivAt_id (x := (0 : ℂ))).pow (q + 1)
  have hR :=
    (analyticAt_simplePoleJetRegularRemainder hU q).differentiableAt.hasDerivAt
  have h := (hasDerivAt_const (x := (0 : ℂ))
    (simplePoleJetPrincipalCoefficient U q)).add (hpow.mul hR)
  convert h using 1
  by_cases hq : q = 0
  · subst q
    simp
  · simp [hq, zero_pow hq]

/-- On the punctured chart, pole normalization agrees with the explicit analytic extension. -/
theorem pow_mul_simplePoleCovariantJetValue_eventuallyEq_normalizedExtension
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (q : ℕ) :
    (fun x : ℂ => x ^ (q + 1) * simplePoleCovariantJetValue U q x) =ᶠ[𝓝[≠] 0]
      simplePoleJetNormalizedExtension U q := by
  filter_upwards [simplePoleCovariantJetValue_sub_principal_eventuallyEq hU q,
    self_mem_nhdsWithin] with x hx hxp
  have hx0 : x ≠ 0 := by simpa using hxp
  change simplePoleCovariantJetValue U q x -
      simplePoleJetPrincipalCoefficient U q * x⁻¹ ^ (q + 1) =
    simplePoleJetRegularRemainder U q x at hx
  rw [show simplePoleCovariantJetValue U q x =
      simplePoleJetPrincipalCoefficient U q * x⁻¹ ^ (q + 1) +
        simplePoleJetRegularRemainder U q x by linear_combination hx]
  simp only [simplePoleJetNormalizedExtension]
  have hcancel : x ^ (q + 1) * x⁻¹ ^ (q + 1) = 1 := by
    rw [inv_pow, ← pow_sub₀ x hx0 le_rfl]
    simp
  rw [mul_add]
  linear_combination simplePoleJetPrincipalCoefficient U q * hcancel

/-- **Universal first-subprincipal reflection.**  Let `P` be Bell-weight homogeneous of weight
`W > 0`.  If its principal-frame value vanishes, then multiplying the corresponding simple-pole
jet packet by `x^(W-1)` selects exactly the `X₀` partial derivative of `P` at that frame times the
finite part of the base jet. -/
theorem tendsto_pow_pred_mul_simplePoleWeightedJetEval
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ)) P = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 1) * MvPolynomial.eval
        (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval
          (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ))
          (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        simplePoleJetRegularRemainder U 0 0)) := by
  let g : Fin (n + 1) → ℂ → ℂ := fun q =>
    simplePoleJetNormalizedExtension U (q : ℕ)
  let g' : Fin (n + 1) → ℂ := fun q =>
    if (q : ℕ) = 0 then simplePoleJetRegularRemainder U 0 0 else 0
  have hg : ∀ q, HasDerivAt (g q) (g' q) 0 := by
    intro q
    exact hasDerivAt_simplePoleJetNormalizedExtension hU (q : ℕ)
  have hg0 : (fun q : Fin (n + 1) => g q 0) =
      (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ)) := by
    funext q
    exact simplePoleJetNormalizedExtension_zero U (q : ℕ)
  have hcurve := tendsto_inv_mul_mvPolynomial_eval_curve_of_eval_zero
    P g g' hg (by rw [hg0]; exact hcancel)
  have hderivative :
      (∑ q, MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) * g' q) =
        MvPolynomial.eval
            (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ))
            (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
          simplePoleJetRegularRemainder U 0 0 := by
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · rw [show g' (0 : Fin (n + 1)) = simplePoleJetRegularRemainder U 0 0 by
        simp [g']]
      rw [hg0]
    · intro q _ hq
      rw [show g' q = 0 by simp [g', hq], mul_zero]
    · simp
  rw [hderivative] at hcurve
  have hev :
      (fun x : ℂ => x ^ (W - 1) * MvPolynomial.eval
        (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) P) =ᶠ[𝓝[≠] 0]
      (fun x => x⁻¹ * MvPolynomial.eval (fun q => g q x) P) := by
    have hcoord : ∀ q : Fin (n + 1),
        (fun x : ℂ => x ^ bellJetWeight (n + 1) q *
          simplePoleCovariantJetValue U (q : ℕ) x) =ᶠ[𝓝[≠] 0] g q := by
      intro q
      simpa [bellJetWeight, g] using
        pow_mul_simplePoleCovariantJetValue_eventuallyEq_normalizedExtension
          hU (q : ℕ)
    filter_upwards [Filter.eventually_all.2 hcoord, self_mem_nhdsWithin]
      with x hx hxp
    have hx0 : x ≠ 0 := by simpa using hxp
    have hframe :
        (fun q : Fin (n + 1) =>
          x ^ bellJetWeight (n + 1) q *
            simplePoleCovariantJetValue U (q : ℕ) x) =
        fun q => g q x := by
      funext q
      exact hx q
    have hscale := isWeightedHomogeneous_eval₂_scale hP (RingHom.id ℂ)
      (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) x
    have hxpow : x⁻¹ * x ^ W = x ^ (W - 1) := by
      rw [show W = (W - 1) + 1 by omega, pow_succ]
      calc
        x⁻¹ * (x ^ (W - 1) * x) = x ^ (W - 1) * (x⁻¹ * x) := by ring
        _ = x ^ (W - 1) := by rw [inv_mul_cancel₀ hx0, mul_one]
    rw [← hxpow]
    calc
      x⁻¹ * x ^ W * MvPolynomial.eval
          (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) P =
          x⁻¹ * (x ^ W * MvPolynomial.eval
            (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) P) := by ring
      _ = x⁻¹ * MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun q : Fin (n + 1) => x ^ bellJetWeight (n + 1) q *
            simplePoleCovariantJetValue U (q : ℕ) x) P :=
        congrArg (fun y => x⁻¹ * y) hscale.symm
      _ = x⁻¹ * MvPolynomial.eval (fun q => g q x) P := by
        rw [hframe, MvPolynomial.eval₂_id]
  exact hcurve.congr' (hev.mono fun _ hx => hx.symm)

/-- Constant-coefficient simple-pole jet evaluation. -/
def simplePoleWeightedJetEval (U : ℂ → ℂ) (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun q : Fin (n + 1) => simplePoleCovariantJetValue U (q : ℕ) x) P

theorem meromorphicAt_simplePoleWeightedJetEval
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MeromorphicAt (simplePoleWeightedJetEval U n P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have heq : simplePoleWeightedJetEval U n (MvPolynomial.C c) =
          fun _ : ℂ => c := by
        funext x
        simp [simplePoleWeightedJetEval]
      rw [heq]
      exact analyticAt_const.meromorphicAt
  | add P Q hP hQ =>
      have heq : simplePoleWeightedJetEval U n (P + Q) =
          simplePoleWeightedJetEval U n P + simplePoleWeightedJetEval U n Q := by
        funext x
        simp [simplePoleWeightedJetEval]
      rw [heq]
      exact hP.add hQ
  | mul_X P q hP =>
      have heq : simplePoleWeightedJetEval U n (P * MvPolynomial.X q) =
          simplePoleWeightedJetEval U n P *
            simplePoleCovariantJetValue U (q : ℕ) := by
        funext x
        simp [simplePoleWeightedJetEval]
      rw [heq]
      exact hP.mul (meromorphicAt_simplePoleCovariantJetValue hU (q : ℕ))

/-- A nonzero first-subprincipal reflection fixes the exact improved pole order. -/
theorem meromorphicOrderAt_simplePoleWeightedJetEval_of_firstSubprincipal
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ)) P = 0)
    (hpartial : MvPolynomial.eval
      (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0)
    (hfinite : simplePoleJetRegularRemainder U 0 0 ≠ 0) :
    meromorphicOrderAt (simplePoleWeightedJetEval U n P) 0 =
      ((-((W - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  refine meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (W - 1)
    (meromorphicAt_simplePoleWeightedJetEval hU n P)
    (c := MvPolynomial.eval
      (fun q : Fin (n + 1) => simplePoleJetPrincipalCoefficient U (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        simplePoleJetRegularRemainder U 0 0) (mul_ne_zero hpartial hfinite) ?_
  simpa only [sub_zero, simplePoleWeightedJetEval] using
    tendsto_pow_pred_mul_simplePoleWeightedJetEval hU n P hP hW hcancel

/-- Abstract weighted first-boundary law for any meromorphic coordinates admitting analytic
pole-normalized extensions.  This is the common mechanism behind both simple-pole and Gamma
reflections. -/
theorem tendsto_pow_pred_mul_weightedJetEval_of_normalizedExtension
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (a : Fin (n + 1) → ℂ → ℂ)
    (g : Fin (n + 1) → ℂ → ℂ) (g' : Fin (n + 1) → ℂ)
    (hg : ∀ q, HasDerivAt (g q) (g' q) 0)
    (hcoord : ∀ q : Fin (n + 1),
      (fun x : ℂ => x ^ bellJetWeight (n + 1) q * a q x) =ᶠ[𝓝[≠] 0] g q)
    (hcancel : MvPolynomial.eval (fun q => g q 0) P = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 1) * MvPolynomial.eval (fun q => a q x) P)
      (𝓝[≠] 0)
      (𝓝 (∑ q, MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) * g' q)) := by
  have hcurve := tendsto_inv_mul_mvPolynomial_eval_curve_of_eval_zero
    P g g' hg hcancel
  have hev :
      (fun x : ℂ => x ^ (W - 1) * MvPolynomial.eval (fun q => a q x) P) =ᶠ[𝓝[≠] 0]
      (fun x => x⁻¹ * MvPolynomial.eval (fun q => g q x) P) := by
    filter_upwards [Filter.eventually_all.2 hcoord, self_mem_nhdsWithin]
      with x hx hxp
    have hx0 : x ≠ 0 := by simpa using hxp
    have hframe :
        (fun q : Fin (n + 1) => x ^ bellJetWeight (n + 1) q * a q x) =
          fun q => g q x := by
      funext q
      exact hx q
    have hscale := isWeightedHomogeneous_eval₂_scale hP (RingHom.id ℂ)
      (fun q : Fin (n + 1) => a q x) x
    have hxpow : x⁻¹ * x ^ W = x ^ (W - 1) := by
      rw [show W = (W - 1) + 1 by omega, pow_succ]
      calc
        x⁻¹ * (x ^ (W - 1) * x) = x ^ (W - 1) * (x⁻¹ * x) := by ring
        _ = x ^ (W - 1) := by rw [inv_mul_cancel₀ hx0, mul_one]
    rw [← hxpow]
    calc
      x⁻¹ * x ^ W * MvPolynomial.eval (fun q => a q x) P =
          x⁻¹ * (x ^ W * MvPolynomial.eval (fun q => a q x) P) := by ring
      _ = x⁻¹ * MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun q : Fin (n + 1) => x ^ bellJetWeight (n + 1) q * a q x) P :=
        congrArg (fun y => x⁻¹ * y) hscale.symm
      _ = x⁻¹ * MvPolynomial.eval (fun q => g q x) P := by
        rw [hframe, MvPolynomial.eval₂_id]
  exact hcurve.congr' (hev.mono fun _ hx => hx.symm)

/-- Analytic extension of a pole-normalized Gamma covariant jet. -/
def gammaPoleJetNormalizedExtension (branch q : ℕ) (x : ℂ) : ℂ :=
  gammaPoleJetPrincipalCoefficient branch q +
    x ^ (q + 1) * gammaPoleJetRegularRemainder branch q x

theorem analyticAt_gammaPoleJetNormalizedExtension (branch q : ℕ) :
    AnalyticAt ℂ (gammaPoleJetNormalizedExtension branch q) 0 := by
  exact analyticAt_const.add ((analyticAt_id.pow (q + 1)).mul
    (analyticAt_gammaPoleJetRegularRemainder branch q))

theorem gammaPoleJetNormalizedExtension_zero (branch q : ℕ) :
    gammaPoleJetNormalizedExtension branch q 0 =
      gammaPoleJetPrincipalCoefficient branch q := by
  simp [gammaPoleJetNormalizedExtension]

/-- As for a general simple pole, only the base Gamma jet has a first-order tangent after each
coordinate is normalized by its pole weight. -/
theorem hasDerivAt_gammaPoleJetNormalizedExtension (branch q : ℕ) :
    HasDerivAt (gammaPoleJetNormalizedExtension branch q)
      (if q = 0 then gammaPoleJetRegularRemainder branch 0 0 else 0) 0 := by
  have hpow := (hasDerivAt_id (x := (0 : ℂ))).pow (q + 1)
  have hR := (analyticAt_gammaPoleJetRegularRemainder branch q).differentiableAt.hasDerivAt
  have h := (hasDerivAt_const (x := (0 : ℂ))
    (gammaPoleJetPrincipalCoefficient branch q)).add (hpow.mul hR)
  convert h using 1
  by_cases hq : q = 0
  · subst q
    simp
  · simp [hq, zero_pow hq]

theorem pow_mul_gammaPoleCovariantJetValue_eventuallyEq_normalizedExtension
    (branch q : ℕ) :
    (fun x : ℂ => x ^ (q + 1) * gammaPoleCovariantJetValue branch q x) =ᶠ[𝓝[≠] 0]
      gammaPoleJetNormalizedExtension branch q := by
  filter_upwards [gammaPoleCovariantJetValue_sub_principal_eventuallyEq branch q,
    self_mem_nhdsWithin] with x hx hxp
  have hx0 : x ≠ 0 := by simpa using hxp
  change gammaPoleCovariantJetValue branch q x -
      gammaPoleJetPrincipalCoefficient branch q * x⁻¹ ^ (q + 1) =
    gammaPoleJetRegularRemainder branch q x at hx
  rw [show gammaPoleCovariantJetValue branch q x =
      gammaPoleJetPrincipalCoefficient branch q * x⁻¹ ^ (q + 1) +
        gammaPoleJetRegularRemainder branch q x by linear_combination hx]
  simp only [gammaPoleJetNormalizedExtension]
  have hcancel : x ^ (q + 1) * x⁻¹ ^ (q + 1) = 1 := by
    rw [inv_pow, ← pow_sub₀ x hx0 le_rfl]
    simp
  rw [mul_add]
  linear_combination gammaPoleJetPrincipalCoefficient branch q * hcancel

/-- **Gamma weighted first-subprincipal reflection.**  Any Bell-weight homogeneous Gamma jet
packet whose principal-frame value cancels has next boundary equal to its `X₀` partial at that
frame times the canonical Gamma finite part. -/
theorem tendsto_pow_pred_mul_gammaPoleWeightedJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 1) * MvPolynomial.eval
        (fun q : Fin (n + 1) => gammaPoleCovariantJetValue branch (q : ℕ) x) P)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval
          (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
          (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        gammaPoleJetRegularRemainder branch 0 0)) := by
  let g : Fin (n + 1) → ℂ → ℂ := fun q =>
    gammaPoleJetNormalizedExtension branch (q : ℕ)
  let g' : Fin (n + 1) → ℂ := fun q =>
    if (q : ℕ) = 0 then gammaPoleJetRegularRemainder branch 0 0 else 0
  have hg : ∀ q, HasDerivAt (g q) (g' q) 0 := by
    intro q
    exact hasDerivAt_gammaPoleJetNormalizedExtension branch (q : ℕ)
  have hcoord : ∀ q : Fin (n + 1),
      (fun x : ℂ => x ^ bellJetWeight (n + 1) q *
        gammaPoleCovariantJetValue branch (q : ℕ) x) =ᶠ[𝓝[≠] 0] g q := by
    intro q
    simpa [bellJetWeight, g] using
      pow_mul_gammaPoleCovariantJetValue_eventuallyEq_normalizedExtension
        branch (q : ℕ)
  have hlim := tendsto_pow_pred_mul_weightedJetEval_of_normalizedExtension
    P hP hW
    (fun q x => gammaPoleCovariantJetValue branch (q : ℕ) x) g g' hg hcoord
    (by
      have hg0 : (fun q : Fin (n + 1) => g q 0) =
          (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) := by
        funext q
        exact gammaPoleJetNormalizedExtension_zero branch (q : ℕ)
      rw [hg0]
      exact hcancel)
  have hderivative :
      (∑ q, MvPolynomial.eval (fun i => g i 0) (MvPolynomial.pderiv q P) * g' q) =
        MvPolynomial.eval
            (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
            (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
          gammaPoleJetRegularRemainder branch 0 0 := by
    have hg0 : (fun q : Fin (n + 1) => g q 0) =
        (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) := by
      funext q
      exact gammaPoleJetNormalizedExtension_zero branch (q : ℕ)
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · rw [show g' (0 : Fin (n + 1)) = gammaPoleJetRegularRemainder branch 0 0 by
        simp [g']]
      rw [hg0]
    · intro q _ hq
      rw [show g' q = 0 by simp [g', hq], mul_zero]
    · simp
  rwa [hderivative] at hlim

/-- Constant-coefficient weighted Gamma covariant jet evaluation. -/
def gammaPoleWeightedJetEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun q : Fin (n + 1) => gammaPoleCovariantJetValue branch (q : ℕ) x) P

theorem meromorphicAt_gammaPoleWeightedJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MeromorphicAt (gammaPoleWeightedJetEval branch n P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have heq : gammaPoleWeightedJetEval branch n (MvPolynomial.C c) =
          fun _ : ℂ => c := by
        funext x
        simp [gammaPoleWeightedJetEval]
      rw [heq]
      exact analyticAt_const.meromorphicAt
  | add P Q hP hQ =>
      have heq : gammaPoleWeightedJetEval branch n (P + Q) =
          gammaPoleWeightedJetEval branch n P + gammaPoleWeightedJetEval branch n Q := by
        funext x
        simp [gammaPoleWeightedJetEval]
      rw [heq]
      exact hP.add hQ
  | mul_X P q hP =>
      have heq : gammaPoleWeightedJetEval branch n (P * MvPolynomial.X q) =
          gammaPoleWeightedJetEval branch n P * gammaPoleCovariantJetValue branch (q : ℕ) := by
        funext x
        simp [gammaPoleWeightedJetEval]
      rw [heq]
      exact hP.mul (meromorphicAt_gammaPoleCovariantJetValue branch (q : ℕ))

/-- A nonzero Gamma first-subprincipal reflection gives exact order `-(W-1)`. -/
theorem meromorphicOrderAt_gammaPoleWeightedJetEval_of_firstSubprincipal
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hpartial : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0)
    (hfinite : gammaPoleJetRegularRemainder branch 0 0 ≠ 0) :
    meromorphicOrderAt (gammaPoleWeightedJetEval branch n P) 0 =
      ((-((W - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  refine meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (W - 1)
    (meromorphicAt_gammaPoleWeightedJetEval branch n P)
    (c := MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        gammaPoleJetRegularRemainder branch 0 0) (mul_ne_zero hpartial hfinite) ?_
  simpa only [sub_zero, gammaPoleWeightedJetEval] using
    tendsto_pow_pred_mul_gammaPoleWeightedJetEval branch n P hP hW hcancel

/-- The same constant-coefficient packet in native affine Gamma derivatives. -/
def gammaAffineWeightedJetEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun q : Fin (n + 1) => iteratedDeriv (q : ℕ) Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) P

theorem gammaAffineWeightedJetEval_eventuallyEq_covariant
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaAffineWeightedJetEval branch n P =ᶠ[𝓝[≠] 0]
      gammaPoleWeightedJetEval branch n P := by
  have hcoord : ∀ q : Fin (n + 1),
      (fun x : ℂ => iteratedDeriv (q : ℕ) Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) =ᶠ[𝓝[≠] 0]
        gammaPoleCovariantJetValue branch (q : ℕ) := by
    intro q
    exact gammaPoleJet_eventuallyEq_covariant branch (q : ℕ)
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  simp only [gammaAffineWeightedJetEval, gammaPoleWeightedJetEval]
  apply congrArg (fun v : Fin (n + 1) → ℂ => MvPolynomial.eval v P)
  funext q
  exact hx q

/-- The general first-subprincipal value reflection transfers to actual affine Gamma jets. -/
theorem tendsto_pow_pred_mul_gammaAffineWeightedJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0) :
    Tendsto
      (fun x : ℂ => x ^ (W - 1) * gammaAffineWeightedJetEval branch n P x)
      (𝓝[≠] 0)
      (𝓝 (MvPolynomial.eval
          (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
          (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        gammaPoleJetRegularRemainder branch 0 0)) := by
  have hev :
      (fun x : ℂ => x ^ (W - 1) * gammaAffineWeightedJetEval branch n P x) =ᶠ[𝓝[≠] 0]
      (fun x => x ^ (W - 1) * gammaPoleWeightedJetEval branch n P x) :=
    (gammaAffineWeightedJetEval_eventuallyEq_covariant branch n P).mono fun x hx =>
      congrArg (fun y => x ^ (W - 1) * y) hx
  exact (tendsto_pow_pred_mul_gammaPoleWeightedJetEval branch n P hP hW hcancel).congr'
    (hev.mono fun _ hx => hx.symm)

/-- Nonzero first-subprincipal reflection fixes the same exact order for the native packet. -/
theorem meromorphicOrderAt_gammaAffineWeightedJetEval_of_firstSubprincipal
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ)) P = 0)
    (hpartial : MvPolynomial.eval
      (fun q : Fin (n + 1) => gammaPoleJetPrincipalCoefficient branch (q : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0)
    (hfinite : gammaPoleJetRegularRemainder branch 0 0 ≠ 0) :
    meromorphicOrderAt (gammaAffineWeightedJetEval branch n P) 0 =
      ((-((W - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr
    (gammaAffineWeightedJetEval_eventuallyEq_covariant branch n P)]
  exact meromorphicOrderAt_gammaPoleWeightedJetEval_of_firstSubprincipal
    branch n P hP hW hcancel hpartial hfinite

end

end GaloisForLFunctions
