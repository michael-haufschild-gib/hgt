import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventOperatorLift
import GaloisForLFunctions.RHTower.SuzukiNegativeProjectorCoherentCompletion
import GaloisForLFunctions.HTGeometry.CfcEigenvector

/-!
# The finite-Morse block identity on a negative eigenspace

Statement `(3)` of the finite-Morse resolvent completion says that at a negative spectral level the
jet square is exactly the negative of the affine Krein defect.  In the resolvent coordinate the
scalar form of this is the vanishing of the completed weight.

This module raises that scalar identity to an operator identity on the eigenspace itself: on every
eigenvector of the below-spectrum resolvent sitting at a negative spectral level,

`q(R)^(2 : ℕ) v = - d(A) v`,

so the completed operator annihilates the whole negative eigenspace.  The lift is the eigenvector
law for the continuous functional calculus: `cfc f R` scales an eigenvector of `R` by the value of
`f` at the eigenvalue, so both blocks act by their scalar symbols and the scalar cancellation
transports verbatim.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The affine Krein defect operator acts on an eigenvector of the resolvent by the scalar weight
at the eigenvalue. -/
theorem suzukiOperatorKreinDefect_apply_of_eigenvector
    {alpha beta rho : ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R))
    {x : ℝ} {v : H} (hx : x ∈ spectrum ℝ R) (hv : R v = ((x : ℝ) : ℂ) • v) :
    suzukiOperatorKreinDefect alpha beta rho R v
      = ((suzukiKreinResolventWeight alpha beta rho x : ℝ) : ℂ) • v := by
  rw [suzukiOperatorKreinDefect]
  exact cfc_apply_eigenvector hR hv hx _ hcont

/-- **`(3)` at operator level, negative block.**  The completed operator annihilates every
eigenvector of the below-spectrum resolvent sitting at a negative spectral level. -/
theorem suzukiFiniteMorse_completion_apply_negativeEigenvector_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel)
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R))
    (i : ι) {v : H}
    (hx : suzukiFiniteMorseResolventNode rho (negativeLevel i) ∈ spectrum ℝ R)
    (hv : R v = ((suzukiFiniteMorseResolventNode rho (negativeLevel i) : ℝ) : ℂ) • v) :
    (suzukiOperatorKreinDefect alpha beta rho R
        + suzukiResolventJetSquare
            (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R) v = 0 := by
  have hzero := suzukiFiniteMorse_completedWeight_eq_zero hab hb0 hbt hnegative hrho hinjective i
  have hadd : (suzukiOperatorKreinDefect alpha beta rho R
      + suzukiResolventJetSquare
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R) v
      = suzukiOperatorKreinDefect alpha beta rho R v
        + suzukiResolventJetSquare
            (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R v := rfl
  rw [hadd, suzukiOperatorKreinDefect_apply_of_eigenvector hR hcont hx hv,
    suzukiResolventJetSquare_apply_of_eigenvector hv, ← add_smul]
  have hcast : ((suzukiKreinResolventWeight alpha beta rho
        (suzukiFiniteMorseResolventNode rho (negativeLevel i)) : ℝ) : ℂ)
      + (((suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
          (suzukiFiniteMorseResolventNode rho (negativeLevel i)) ^ (2 : ℕ) : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_add, hzero, Complex.ofReal_zero]
  rw [hcast, zero_smul]

/-- **`(3)` at operator level, block form.**  On every negative eigenspace the finite jet square is
exactly the negative of the affine Krein defect. -/
theorem suzukiFiniteMorse_jetSquare_eq_neg_kreinDefect_on_negativeEigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel)
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R))
    (i : ι) {v : H}
    (hx : suzukiFiniteMorseResolventNode rho (negativeLevel i) ∈ spectrum ℝ R)
    (hv : R v = ((suzukiFiniteMorseResolventNode rho (negativeLevel i) : ℝ) : ℂ) • v) :
    suzukiResolventJetSquare
        (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R v
      = - (suzukiOperatorKreinDefect alpha beta rho R v) := by
  have h := suzukiFiniteMorse_completion_apply_negativeEigenvector_eq_zero hR hab hb0 hbt
    hnegative hrho hinjective hcont i hx hv
  have hadd : (suzukiOperatorKreinDefect alpha beta rho R
      + suzukiResolventJetSquare
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R) v
      = suzukiOperatorKreinDefect alpha beta rho R v
        + suzukiResolventJetSquare
            (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R v := rfl
  rw [hadd] at h
  linear_combination (norm := module) h

/-- **`(3)` at operator level, positive block.**  On an eigenvector of the below-spectrum resolvent
sitting at a positive spectral level the affine Krein defect already acts by a strictly positive
scalar, so any added jet square only overpays. -/
theorem suzukiFiniteMorse_kreinDefect_apply_positiveEigenvector
    {alpha beta rho t : ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R))
    (hab : alpha < beta) (hb0 : beta < 0) (hrho0 : rho < 0) (htpos : 0 < t) {v : H}
    (hx : suzukiFiniteMorseResolventNode rho t ∈ spectrum ℝ R)
    (hv : R v = ((suzukiFiniteMorseResolventNode rho t : ℝ) : ℂ) • v) :
    suzukiOperatorKreinDefect alpha beta rho R v
        = ((suzukiKreinResolventWeight alpha beta rho
            (suzukiFiniteMorseResolventNode rho t) : ℝ) : ℂ) • v
      ∧ 0 < suzukiKreinResolventWeight alpha beta rho
            (suzukiFiniteMorseResolventNode rho t) :=
  ⟨suzukiOperatorKreinDefect_apply_of_eigenvector hR hcont hx hv,
    suzukiFiniteMorse_kreinResolventWeight_pos hab hb0 hrho0 htpos⟩

omit [CompleteSpace H] in
/-- The jet square acts on any eigenvector by a nonnegative scalar. -/
theorem suzukiResolventJetSquare_apply_eigenvector_nonneg
    {q : Polynomial ℝ} {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) :
    suzukiResolventJetSquare q R v = (((q.eval x ^ (2 : ℕ) : ℝ)) : ℂ) • v ∧ 0 ≤ q.eval x ^ (2 : ℕ) :=
  ⟨suzukiResolventJetSquare_apply_of_eigenvector hv, sq_nonneg _⟩

/-! ## The minimal-completion decomposition -/

/-- The negative part of a functional calculus acts on an eigenvector by the negative part of the
symbol at the eigenvalue. -/
theorem negPart_cfc_apply_of_eigenvector {f : ℝ → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hf : ContinuousOn f (spectrum ℝ R)) {x : ℝ} {v : H}
    (hx : x ∈ spectrum ℝ R) (hv : R v = ((x : ℝ) : ℂ) • v) :
    ((cfc f R)⁻) v = (((f x)⁻ : ℝ) : ℂ) • v := by
  rw [negPart_cfc hR hf]
  exact cfc_apply_eigenvector hR hv hx _ (hf.neg.sup continuousOn_const)

/-- **`(T1)`, the decomposition equation.**  On every negative eigenspace the finite jet square
already equals the minimal completion `D⁻`.  Hence the excess `C - D⁻` of the jet square over the
Loewner-minimal correction annihilates the whole negative spectral part and is carried entirely by
the positive spectral part — which is the content of `C = D⁻ + P₊C`, stated without needing the
discontinuous spectral projector `P₊` to exist as an operator. -/
theorem suzukiFiniteMorse_jetSquare_eq_negPart_on_negativeEigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel)
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R))
    (i : ι) {v : H}
    (hx : suzukiFiniteMorseResolventNode rho (negativeLevel i) ∈ spectrum ℝ R)
    (hv : R v = ((suzukiFiniteMorseResolventNode rho (negativeLevel i) : ℝ) : ℂ) • v) :
    suzukiResolventJetSquare
        (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R v
      = ((suzukiOperatorKreinDefect alpha beta rho R)⁻) v := by
  have hzero := suzukiFiniteMorse_completedWeight_eq_zero hab hb0 hbt hnegative hrho hinjective i
  have hnp : (suzukiKreinResolventWeight alpha beta rho
        (suzukiFiniteMorseResolventNode rho (negativeLevel i)))⁻
      = ((suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
          (suzukiFiniteMorseResolventNode rho (negativeLevel i))) ^ (2 : ℕ) := by
    have hle : suzukiKreinResolventWeight alpha beta rho
        (suzukiFiniteMorseResolventNode rho (negativeLevel i)) ≤ 0 := by
      nlinarith [sq_nonneg ((suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
        (suzukiFiniteMorseResolventNode rho (negativeLevel i)))]
    rw [negPart_of_nonpos hle]
    linarith
  rw [suzukiResolventJetSquare_apply_of_eigenvector hv, suzukiOperatorKreinDefect,
    negPart_cfc_apply_of_eigenvector hR hcont hx hv, hnp]

/-! ## The completion Gram kernel -/

/-- **The completion Gram kernel factorizes:** `K_C(z, w) = ⟪p(R)Γ(w), p(R)Γ(z)⟫`.  The jet square
is `B²` with `B = p(R)` self-adjoint, so one application of self-adjointness moves a factor across
the inner product. -/
theorem suzukiResolventJetSquare_inner_eq {q : Polynomial ℝ} {R : H →L[ℂ] H}
    (hR : IsSelfAdjoint R) (v w : H) :
    inner ℂ (suzukiResolventJetSquare q R w) v
      = inner ℂ ((Polynomial.aeval R q) w) ((Polynomial.aeval R q) v) := by
  have hsa : IsSelfAdjoint (Polynomial.aeval R q) := suzukiResolventJet_isSelfAdjoint q hR
  have hadj : ContinuousLinearMap.adjoint (Polynomial.aeval R q) = Polynomial.aeval R q := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hsa
  have hstep : suzukiResolventJetSquare q R w
      = (Polynomial.aeval R q) ((Polynomial.aeval R q) w) := by
    rw [suzukiResolventJetSquare, pow_two]
    rfl
  have key := ContinuousLinearMap.adjoint_inner_left (Polynomial.aeval R q) v
    ((Polynomial.aeval R q) w)
  rw [hadj] at key
  rw [hstep]
  exact key

/-- **The completion Gram kernel is positive semidefinite.**  This is the Gram form promised by
`(T1)`: the jet square is a positive operator, so its kernel `K_C` is a positive kernel on every
finite family of evaluation vectors, with no Xi zero or divisor entering. -/
theorem suzukiResolventJetSquare_gram_nonneg {q : Polynomial ℝ} {R : H →L[ℂ] H}
    (hR : IsSelfAdjoint R) {ι : Type*} (s : Finset ι) (Gamma : ι → H) (c : ι → ℂ) :
    0 ≤ RCLike.re (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
      * inner ℂ (suzukiResolventJetSquare q R (Gamma i)) (Gamma j)) :=
  gram_re_nonneg_of_nonneg (suzukiResolventJetSquare_nonneg q hR) s Gamma c

end RHTower
