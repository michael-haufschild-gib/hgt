import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.AnalyticConjReflection
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicAdditiveCrossPrimeUniversality
import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux

/-!
# Skew-adjoint additive SC two-port no-go

Unrestricted additive SC two-port determinants are compact-open universal because their two odd
legs are independent. The Stokes-natural skew-adjoint reality condition ties the lower leg to the
negative Schwarz reflection of the upper leg. That tie forces the determinant's central quadratic
jet to be `2 * |A'(0)|^2`, hence nonnegative. Normalized centered Xi has strictly negative central
quadratic jet. Cauchy jet convergence therefore excludes every compact-open Xi landing through
these stages.

This closes the chain
`skew-adjoint additive SC stages -> Xi determinant landing -> SC divisor/orientation endpoint -> RH`
at its Xi-landing gate. It does not exclude the opposite Hermitian sign, nondeterminantal landings,
or singular/operator-valued limits.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Schwarz reflection of an entire scalar leg. -/
def additiveSCSchwarzSharp (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (A ((starRingEnd ℂ) z))

/-- Determinant carrier forced by the skew-adjoint two-port tie. -/
def skewAdjointAdditiveSCTwoPortDet (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 + A z * additiveSCSchwarzSharp A z

/-- Identity plus a real-axis skew-adjoint off-diagonal two-port stage. -/
def skewAdjointAdditiveSCTwoPortMatrix
    (A : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, A z; -additiveSCSchwarzSharp A z, 1]

theorem det_skewAdjointAdditiveSCTwoPortMatrix (A : ℂ → ℂ) (z : ℂ) :
    (skewAdjointAdditiveSCTwoPortMatrix A z).det =
      skewAdjointAdditiveSCTwoPortDet A z := by
  rw [Matrix.det_fin_two]
  simp [skewAdjointAdditiveSCTwoPortMatrix, skewAdjointAdditiveSCTwoPortDet]

theorem differentiable_additiveSCSchwarzSharp
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) :
    Differentiable ℂ (additiveSCSchwarzSharp A) := by
  intro z
  have hAn : AnalyticOnNhd ℂ A Set.univ :=
    hA.differentiableOn.analyticOnNhd isOpen_univ
  exact ((hAn ((starRingEnd ℂ) z) (Set.mem_univ _)).conj_comp_conj).differentiableAt

theorem deriv_additiveSCSchwarzSharp (A : ℂ → ℂ) :
    deriv (additiveSCSchwarzSharp A) =
      (starRingEnd ℂ) ∘ deriv A ∘ (starRingEnd ℂ) := by
  exact deriv_conj_conj

/-- Exact central curvature law for a centered skew-adjoint additive two-port stage. -/
theorem iteratedDeriv_two_skewAdjointAdditiveSCTwoPortDet_zero
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hA0 : A 0 = 0) :
    iteratedDeriv 2 (skewAdjointAdditiveSCTwoPortDet A) 0 =
      2 * deriv A 0 * (starRingEnd ℂ) (deriv A 0) := by
  have hS : Differentiable ℂ (additiveSCSchwarzSharp A) :=
    differentiable_additiveSCSchwarzSharp hA
  have hderiv : deriv (skewAdjointAdditiveSCTwoPortDet A) = fun z =>
      deriv A z * additiveSCSchwarzSharp A z +
        A z * deriv (additiveSCSchwarzSharp A) z := by
    funext z
    change deriv (fun w => 1 + A w * additiveSCSchwarzSharp A w) z = _
    change deriv ((fun _ : ℂ => (1 : ℂ)) + A * additiveSCSchwarzSharp A) z = _
    simpa only [zero_add] using
      ((hasDerivAt_const (x := z) (1 : ℂ)).add
        ((hA z).hasDerivAt.mul (hS z).hasDerivAt)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, hderiv]
  have hAd : DifferentiableAt ℂ (deriv A) 0 := by
    simpa [iteratedDeriv_one] using
      (GaloisForLFunctions.differentiable_iteratedDeriv_of_entire hA 1) 0
  have hSd : DifferentiableAt ℂ (deriv (additiveSCSchwarzSharp A)) 0 := by
    simpa [iteratedDeriv_one] using
      (GaloisForLFunctions.differentiable_iteratedDeriv_of_entire hS 1) 0
  have hsecond : HasDerivAt
      (fun z => deriv A z * additiveSCSchwarzSharp A z +
        A z * deriv (additiveSCSchwarzSharp A) z)
      (deriv (deriv A) 0 * additiveSCSchwarzSharp A 0 +
          deriv A 0 * deriv (additiveSCSchwarzSharp A) 0 +
        (deriv A 0 * deriv (additiveSCSchwarzSharp A) 0 +
          A 0 * deriv (deriv (additiveSCSchwarzSharp A)) 0)) 0 := by
    change HasDerivAt
      (deriv A * additiveSCSchwarzSharp A + A * deriv (additiveSCSchwarzSharp A)) _ 0
    exact (hAd.hasDerivAt.mul (hS 0).hasDerivAt).add
      ((hA 0).hasDerivAt.mul hSd.hasDerivAt)
  rw [hsecond.deriv, hA0]
  have hS0 : additiveSCSchwarzSharp A 0 = 0 := by
    simp [additiveSCSchwarzSharp, hA0]
  have hSd0 : deriv (additiveSCSchwarzSharp A) 0 =
      (starRingEnd ℂ) (deriv A 0) := by
    rw [deriv_additiveSCSchwarzSharp]
    simp [Function.comp_apply]
  rw [hS0, hSd0]
  ring

theorem re_iteratedDeriv_two_skewAdjointAdditiveSCTwoPortDet_zero_nonneg
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hA0 : A 0 = 0) :
    0 ≤ (iteratedDeriv 2 (skewAdjointAdditiveSCTwoPortDet A) 0).re := by
  rw [iteratedDeriv_two_skewAdjointAdditiveSCTwoPortDet_zero hA hA0]
  rw [show 2 * deriv A 0 * (starRingEnd ℂ) (deriv A 0) =
      2 * (deriv A 0 * (starRingEnd ℂ) (deriv A 0)) by ring,
    Complex.mul_conj]
  simpa [Complex.mul_re] using
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Complex.normSq_nonneg (deriv A 0)))

theorem differentiable_skewAdjointAdditiveSCTwoPortDet
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) :
    Differentiable ℂ (skewAdjointAdditiveSCTwoPortDet A) := by
  exact differentiable_const (1 : ℂ) |>.add
    (hA.mul (differentiable_additiveSCSchwarzSharp hA))

theorem iteratedDeriv_two_normalizedXiC_zero :
    iteratedDeriv 2 (fun z => XiC z / XiC 0) 0 =
      deriv (deriv XiC) 0 / XiC 0 := by
  rw [show (fun z => XiC z / XiC 0) = fun z => (XiC 0)⁻¹ * XiC z by
        funext z
        simp [div_eq_mul_inv, mul_comm]]
  rw [GaloisForLFunctions.iteratedDeriv_const_mul_field]
  simp [iteratedDeriv_succ, iteratedDeriv_zero, div_eq_mul_inv, mul_comm]

/-- No centered entire skew-adjoint additive two-port determinants can approach normalized Xi. -/
theorem not_tendstoLocallyUniformly_skewAdjointAdditiveSCTwoPortDet_normalizedXiC
    (A : ℕ → ℂ → ℂ) (hA : ∀ n, Differentiable ℂ (A n))
    (hA0 : ∀ n, A n 0 = 0) :
    ¬ TendstoLocallyUniformly
      (fun n => skewAdjointAdditiveSCTwoPortDet (A n))
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hjet : Tendsto
      (fun n => iteratedDeriv 2 (skewAdjointAdditiveSCTwoPortDet (A n)) 0) atTop
      (𝓝 (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0)) := by
    exact GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
      hconv.tendstoLocallyUniformlyOn
      (Filter.Eventually.of_forall fun n =>
        (differentiable_skewAdjointAdditiveSCTwoPortDet (hA n)).differentiableOn)
      2 (Set.mem_univ 0)
  have hjetRe : Tendsto
      (fun n => (iteratedDeriv 2 (skewAdjointAdditiveSCTwoPortDet (A n)) 0).re) atTop
      (𝓝 (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hjet
  have hnonneg : 0 ≤ (iteratedDeriv 2 (fun z => XiC z / XiC 0) 0).re := by
    exact isClosed_Ici.mem_of_tendsto hjetRe
      (Filter.Eventually.of_forall fun n =>
        re_iteratedDeriv_two_skewAdjointAdditiveSCTwoPortDet_zero_nonneg
          (hA n) (hA0 n))
  rw [iteratedDeriv_two_normalizedXiC_zero] at hnonneg
  exact (not_lt_of_ge hnonneg) XiC_secondDeriv_div_center_re_neg

/-- Matrix-form SC landing no-go. -/
theorem not_tendstoLocallyUniformly_skewAdjointAdditiveSCTwoPortMatrix_normalizedXiC
    (A : ℕ → ℂ → ℂ) (hA : ∀ n, Differentiable ℂ (A n))
    (hA0 : ∀ n, A n 0 = 0) :
    ¬ TendstoLocallyUniformly
      (fun n z => (skewAdjointAdditiveSCTwoPortMatrix (A n) z).det)
      (fun z => XiC z / XiC 0) atTop := by
  simpa only [det_skewAdjointAdditiveSCTwoPortMatrix] using
    not_tendstoLocallyUniformly_skewAdjointAdditiveSCTwoPortDet_normalizedXiC A hA hA0

end

end RHTower
