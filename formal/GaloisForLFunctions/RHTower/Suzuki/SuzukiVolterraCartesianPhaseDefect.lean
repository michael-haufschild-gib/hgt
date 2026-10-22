import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveResolventPluckerLift
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanJumpEulerDefectWeld
import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveAffineSecantTensor
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Suzuki Volterra Cartesian phase defect

The physical right convolution triangle is the Fourier observation of a causal Volterra half
`V`.  Its Cartesian decomposition is

`V = (C + i H) / 2`,

where `C = V + V*` is the symmetric convolution pencil and
`H = -i(V - V*)` is its self-adjoint orientation/phase pencil.  In the canonical Xi-real
coordinate,

`-i V = (H - i C) / 2`.

For Suzuki's odd phase-one source, the `C` response is the already classified odd sine-clock
sector, whereas the unresolved even Carleman carrier is the `H` response.  This module formalizes
that exact algebra, the relative phase defect on a resolvent orbit, its homogeneous projective
chord, and the rank-one Neumann moment law.  It uses no RH premise, positivity assumption,
Xi-divisor data, or numerical computation.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## Cartesian decomposition of the physical right response -/

/-- Xi-real normalization of a shifted physical right-Volterra observation. -/
def suzukiXiRealRightVolterraResponse
    (rightEuler rightNeumann : V →ₗ[ℂ] ℂ) (lambda : ℂ) (u : V) : ℂ :=
  -I * (rightEuler u - lambda * rightNeumann u)

/-- **Cartesian phase decomposition.**  If each causal right observation is half of its
symmetric and `i` times its self-adjoint phase observation, Xi-real normalization separates the
phase response from the symmetric response with the forced relative quarter-turn. -/
theorem suzukiXiRealRightVolterraResponse_eq_cartesian
    (rightEuler rightNeumann symmetricEuler symmetricNeumann
      phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ)
    (lambda : ℂ) (u : V)
    (hEuler : 2 * rightEuler u = symmetricEuler u + I * phaseEuler u)
    (hNeumann : 2 * rightNeumann u = symmetricNeumann u + I * phaseNeumann u) :
    suzukiXiRealRightVolterraResponse rightEuler rightNeumann lambda u =
      ((phaseEuler u - lambda * phaseNeumann u) -
          I * (symmetricEuler u - lambda * symmetricNeumann u)) / 2 := by
  rw [suzukiXiRealRightVolterraResponse]
  linear_combination
    (-I / 2) * hEuler +
    (I * lambda / 2) * hNeumann +
    ((lambda * phaseNeumann u - phaseEuler u) / 2) * Complex.I_sq

/-- Keeping the symmetric Cartesian coordinate fixed leaves half of the phase difference in the
Xi-real right response.  Therefore positivity of the symmetric pencil alone cannot determine the
RH-bearing phase carrier. -/
theorem suzukiXiRealCartesianResponse_sub_eq_phaseHalf
    (s h₁ h₂ : ℂ) :
    -I * ((s + I * h₁) / 2) - (-I * ((s + I * h₂) / 2)) = (h₁ - h₂) / 2 := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Relative phase defect on a resolvent pencil -/

/-- Fixed relative phase observation left after the form shift is absorbed by the resolvent
equation.  Analytically this is the boundary observation of `H_g - H_r A`. -/
def suzukiRelativeVolterraPhaseObservation
    (A : V →ₗ[ℂ] V) (phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ) : V →ₗ[ℂ] ℂ :=
  phaseEuler - phaseNeumann.comp A

/-- The shifted Volterra phase pencil becomes one fixed linear observation plus the Neumann
homogeneous coordinate. -/
theorem suzukiShiftedVolterraPhase_eq_relative_homogeneous
    (A : V →ₗ[ℂ] V) (phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ)
    (e u : V) (lambda : ℂ)
    (hres : A u - lambda • u = e) :
    phaseEuler u - lambda * phaseNeumann u =
      suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann u +
        phaseNeumann e := by
  rw [suzukiRelativeVolterraPhaseObservation]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [← hres]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- Full Cartesian response on a state whose symmetric pencil has fixed forcing.  The symmetric
energy becomes a homogeneous coordinate; all state-dependent motion is carried by the relative
Volterra phase observation. -/
theorem suzukiXiRealRightVolterraResponse_eq_relativePhaseHomogeneous
    (A : V →ₗ[ℂ] V)
    (rightEuler rightNeumann symmetricEuler symmetricNeumann
      phaseEuler phaseNeumann : V →ₗ[ℂ] ℂ)
    (e u : V) (lambda forcing : ℂ)
    (hres : A u - lambda • u = e)
    (hEuler : 2 * rightEuler u = symmetricEuler u + I * phaseEuler u)
    (hNeumann : 2 * rightNeumann u = symmetricNeumann u + I * phaseNeumann u)
    (hforcing : symmetricEuler u - lambda * symmetricNeumann u = forcing) :
    suzukiXiRealRightVolterraResponse rightEuler rightNeumann lambda u =
      (suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann u +
          phaseNeumann e - I * forcing) / 2 := by
  rw [suzukiXiRealRightVolterraResponse_eq_cartesian
    rightEuler rightNeumann symmetricEuler symmetricNeumann
    phaseEuler phaseNeumann lambda u hEuler hNeumann]
  rw [hforcing,
    suzukiShiftedVolterraPhase_eq_relative_homogeneous
      A phaseEuler phaseNeumann e u lambda hres]

/-- **Volterra phase/Plucker capstone.**  On a two-resolvent orbit, the projective chord of the
actual Xi-real right responses is the boundary image of the relative phase blade plus the single
homogeneous Neumann/forcing coordinate. -/
theorem suzukiXiRealRightVolterraProjectiveChord_twoResolvents
    (A RAlpha RBeta : V →ₗ[ℂ] V)
    (rightEuler rightNeumann symmetricEuler symmetricNeumann
      phaseEuler phaseNeumann D : V →ₗ[ℂ] ℂ)
    (alpha beta forcing : ℂ) (e : V)
    (hAlphaInv : ∀ x, A (RAlpha x) - alpha • RAlpha x = x)
    (hBetaInv : ∀ x, A (RBeta x) - beta • RBeta x = x)
    (hcomm : RAlpha (RBeta e) = RBeta (RAlpha e))
    (hEuler : ∀ u, 2 * rightEuler u = symmetricEuler u + I * phaseEuler u)
    (hNeumann : ∀ u, 2 * rightNeumann u = symmetricNeumann u + I * phaseNeumann u)
    (hAlphaForcing :
      symmetricEuler (RAlpha e) - alpha * symmetricNeumann (RAlpha e) = forcing)
    (hBetaForcing :
      symmetricEuler (RBeta e) - beta * symmetricNeumann (RBeta e) = forcing) :
    suzukiXiRealRightVolterraResponse rightEuler rightNeumann beta (RBeta e) * D (RAlpha e) -
        suzukiXiRealRightVolterraResponse rightEuler rightNeumann alpha (RAlpha e) * D (RBeta e) =
      (beta - alpha) / 2 *
        (suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
              (RAlpha (RBeta e)) * D (A (RAlpha (RBeta e))) -
          suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
              (A (RAlpha (RBeta e))) * D (RAlpha (RBeta e)) -
          (phaseNeumann e - I * forcing) * D (RAlpha (RBeta e))) := by
  let B : V →ₗ[ℂ] ℂ := suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
  let c : ℂ := phaseNeumann e - I * forcing
  have hBetaState : RBeta e = A (RAlpha (RBeta e)) - alpha • RAlpha (RBeta e) :=
    (hAlphaInv (RBeta e)).symm
  have hAlphaState : RAlpha e = A (RAlpha (RBeta e)) - beta • RAlpha (RBeta e) := by
    rw [hcomm]
    exact (hBetaInv (RAlpha e)).symm
  have hBetaResponse :
      suzukiXiRealRightVolterraResponse rightEuler rightNeumann beta (RBeta e) =
        (B (RBeta e) + c) / 2 := by
    rw [suzukiXiRealRightVolterraResponse_eq_relativePhaseHomogeneous
      A rightEuler rightNeumann symmetricEuler symmetricNeumann phaseEuler phaseNeumann
      e (RBeta e) beta forcing (hBetaInv e) (hEuler _) (hNeumann _) hBetaForcing]
    dsimp only [B, c]
    ring
  have hAlphaResponse :
      suzukiXiRealRightVolterraResponse rightEuler rightNeumann alpha (RAlpha e) =
        (B (RAlpha e) + c) / 2 := by
    rw [suzukiXiRealRightVolterraResponse_eq_relativePhaseHomogeneous
      A rightEuler rightNeumann symmetricEuler symmetricNeumann phaseEuler phaseNeumann
      e (RAlpha e) alpha forcing (hAlphaInv e) (hEuler _) (hNeumann _) hAlphaForcing]
    dsimp only [B, c]
    ring
  rw [hBetaResponse, hAlphaResponse]
  have hChord := suzukiHomogeneousProjectiveResolventChord
    A B D alpha beta c (RAlpha e) (RBeta e) (RAlpha (RBeta e)) hBetaState hAlphaState
  dsimp only [B, c] at hChord ⊢
  linear_combination hChord / 2

/-! ## Rank-one Neumann phase law -/

/-- Spatial response of the antisymmetric half of the kernel `r₀(t)=-|t|/2`, expressed only in
terms of source mass and first moment. -/
def suzukiNeumannVolterraSkewMomentResponse
    (x mass firstMoment : ℂ) : ℂ :=
  -(x * mass) / 2 + firstMoment / 2

/-- On the odd/zero-mass source sector the Neumann skew response is constant and has rank one. -/
theorem suzukiNeumannVolterraSkewMomentResponse_of_zeroMass
    (x firstMoment : ℂ) :
    suzukiNeumannVolterraSkewMomentResponse x 0 firstMoment = firstMoment / 2 := by
  simp [suzukiNeumannVolterraSkewMomentResponse]

/-- After the self-adjoint quarter-turn and interval Fourier transform, the rank-one Neumann
phase is exactly the full-frequency projective holonomy numerator. -/
theorem suzukiNeumannXiRealEvenTriangle_eq_projectiveHolonomyNumerator
    (firstMoment centralJet sineOverFrequency : ℂ)
    (hjet : centralJet = I * firstMoment) :
    (-I * firstMoment / 2) * sineOverFrequency =
      -centralJet * sineOverFrequency / 2 := by
  rw [hjet]
  ring

/-! ## Complete marked affine-secant carrier -/

/-- Complex boundary-value extension of the real marked affine-secant tensor. -/
def suzukiComplexProjectiveAffineSecantTensor
    (alpha beta x X y Y c : ℂ) : ℂ :=
  (X + c) * Y - (alpha + beta) * x * Y + alpha * beta * x * y

/-- The complex marked tensor restricts exactly to the existing real source tensor. -/
theorem suzukiComplexProjectiveAffineSecantTensor_ofReal
    (alpha beta x X y Y c : ℝ) :
    suzukiComplexProjectiveAffineSecantTensor
        alpha beta x X y Y c =
      (suzukiProjectiveAffineSecantTensor alpha beta x X y Y c : ℂ) := by
  simp only [suzukiComplexProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantTensor]

/-- Division-free complex marked-secant identity.  Unlike the alternating Plucker chord, this is
the complete carrier of the weighted affine intercept used by Suzuki jump sewing. -/
theorem suzukiComplexProjectiveAffineSecant_cross_identity
    (alpha beta x X y Y c : ℂ) :
    beta * (X - beta * x + c) * (Y - alpha * y) -
        alpha * (X - alpha * x + c) * (Y - beta * y) =
      (beta - alpha) *
        suzukiComplexProjectiveAffineSecantTensor alpha beta x X y Y c := by
  simp only [suzukiComplexProjectiveAffineSecantTensor]
  ring

/-- **Actual Volterra marked-secant capstone.**  The weighted affine sewing of two shifted phase
responses is the marked secant tensor of the relative Volterra phase observation.  This retains
diagonal and symmetric-pair sectors which the Plucker chord provably forgets. -/
theorem suzukiShiftedVolterraPhase_affineSecant_twoResolvents
    (A RAlpha RBeta : V →ₗ[ℂ] V)
    (phaseEuler phaseNeumann D : V →ₗ[ℂ] ℂ)
    (alpha beta : ℂ) (e : V)
    (hAlphaInv : ∀ x, A (RAlpha x) - alpha • RAlpha x = x)
    (hBetaInv : ∀ x, A (RBeta x) - beta • RBeta x = x)
    (hcomm : RAlpha (RBeta e) = RBeta (RAlpha e)) :
    beta * ((phaseEuler (RAlpha e) - alpha * phaseNeumann (RAlpha e)) / 2) *
          D (RBeta e) -
        alpha * ((phaseEuler (RBeta e) - beta * phaseNeumann (RBeta e)) / 2) *
          D (RAlpha e) =
      (beta - alpha) *
        suzukiComplexProjectiveAffineSecantTensor alpha beta
          (suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
            (RAlpha (RBeta e)) / 2)
          (suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
            (A (RAlpha (RBeta e))) / 2)
          (D (RAlpha (RBeta e)))
          (D (A (RAlpha (RBeta e))))
          (phaseNeumann e / 2) := by
  let v : V := RAlpha (RBeta e)
  have hBetaState : RBeta e = A v - alpha • v :=
    (hAlphaInv (RBeta e)).symm
  have hAlphaState : RAlpha e = A v - beta • v := by
    change RAlpha e = A (RAlpha (RBeta e)) - beta • RAlpha (RBeta e)
    rw [hcomm]
    exact (hBetaInv (RAlpha e)).symm
  let B : V →ₗ[ℂ] ℂ :=
    suzukiRelativeVolterraPhaseObservation A phaseEuler phaseNeumann
  have hPhaseAlpha := suzukiShiftedVolterraPhase_eq_relative_homogeneous
    A phaseEuler phaseNeumann e (RAlpha e) alpha (hAlphaInv e)
  have hPhaseBeta := suzukiShiftedVolterraPhase_eq_relative_homogeneous
    A phaseEuler phaseNeumann e (RBeta e) beta (hBetaInv e)
  have hBAlpha : B (RAlpha e) = B (A v) - beta * B v := by
    rw [hAlphaState]
    simp only [map_sub, map_smul, smul_eq_mul]
  have hBBeta : B (RBeta e) = B (A v) - alpha * B v := by
    rw [hBetaState]
    simp only [map_sub, map_smul, smul_eq_mul]
  have hDAlpha : D (RAlpha e) = D (A v) - beta * D v := by
    rw [hAlphaState]
    simp only [map_sub, map_smul, smul_eq_mul]
  have hDBeta : D (RBeta e) = D (A v) - alpha * D v := by
    rw [hBetaState]
    simp only [map_sub, map_smul, smul_eq_mul]
  have hNAlpha :
      (phaseEuler (RAlpha e) - alpha * phaseNeumann (RAlpha e)) / 2 =
        B (A v) / 2 - beta * (B v / 2) + phaseNeumann e / 2 := by
    rw [hPhaseAlpha]
    change (B (RAlpha e) + phaseNeumann e) / 2 = _
    rw [hBAlpha]
    ring
  have hNBeta :
      (phaseEuler (RBeta e) - beta * phaseNeumann (RBeta e)) / 2 =
        B (A v) / 2 - alpha * (B v / 2) + phaseNeumann e / 2 := by
    rw [hPhaseBeta]
    change (B (RBeta e) + phaseNeumann e) / 2 = _
    rw [hBBeta]
    ring
  rw [hNAlpha, hNBeta, hDAlpha, hDBeta]
  change
    beta * (B (A v) / 2 - beta * (B v / 2) + phaseNeumann e / 2) *
          (D (A v) - alpha * D v) -
        alpha * (B (A v) / 2 - alpha * (B v / 2) + phaseNeumann e / 2) *
          (D (A v) - beta * D v) =
      (beta - alpha) *
        suzukiComplexProjectiveAffineSecantTensor alpha beta
          (B v / 2) (B (A v) / 2) (D v) (D (A v)) (phaseNeumann e / 2)
  exact suzukiComplexProjectiveAffineSecant_cross_identity
    alpha beta (B v / 2) (B (A v) / 2) (D v) (D (A v)) (phaseNeumann e / 2)

/-! ## Connector to the proved RH implication -/

/-- Boundary-family form of the actual Xi-real right-Volterra response. -/
def suzukiXiRealRightVolterraBoundaryResponse
    (rightEuler rightNeumann : ℂ → V →ₗ[ℂ] ℂ)
    (lambda : ℂ) (u : V) (z : ℂ) : ℂ :=
  suzukiXiRealRightVolterraResponse (rightEuler z) (rightNeumann z) lambda u

/-- **RH connector for the relative Volterra phase programme.**  Once the actual two shifted
Volterra boundary responses supply one analytic upper-half-plane Euler-defect source germ, the
existing exact pole-tomography weld proves RH.  The premise is the named open source Green/CD
identity; no divisor positivity or RH assumption is hidden in this implication. -/
theorem riemannHypothesis_of_suzukiVolterraPhaseEulerDefect_source_germ_weld
    {alpha beta : ℂ}
    {WAlpha WBeta DSource : ℂ → ℂ} {seed : ℂ}
    (rightEuler rightNeumann : ℂ → V →ₗ[ℂ] ℂ)
    (uAlpha uBeta : V)
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ z, AnalyticAt ℂ WAlpha z)
    (hWBeta : ∀ z, AnalyticAt ℂ WBeta z)
    (hRightAlpha : ∀ z, AnalyticAt ℂ
      (suzukiXiRealRightVolterraBoundaryResponse
        rightEuler rightNeumann alpha uAlpha) z)
    (hRightBeta : ∀ z, AnalyticAt ℂ
      (suzukiXiRealRightVolterraBoundaryResponse
        rightEuler rightNeumann beta uBeta) z)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    (hSource : AnalyticOnNhd ℂ DSource UpperHalfPlane.upperHalfPlaneSet)
    (hseedUpper : seed ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hseed :
      GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta
            (suzukiXiRealRightVolterraBoundaryResponse
              rightEuler rightNeumann alpha uAlpha)
            (suzukiXiRealRightVolterraBoundaryResponse
              rightEuler rightNeumann beta uBeta)) =ᶠ[𝓝[≠] seed] DSource) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
    hab hWAlpha hWBeta hRightAlpha hRightBeta hrealAlpha hrealBeta
    hSource hseedUpper hseed

end

/-! ## The Cartesian split is an identity

The response theorems above take the split `2V = C + i H` as a hypothesis.  It is not an
assumption: for any bounded operator the symmetric part `V + V*` and the phase `-i(V - V*)` are both
self-adjoint, and their combination reproduces `2V` exactly.  So the Cartesian coordinates exist for
every causal observation, and the phase is a genuine self-adjoint coordinate rather than a remainder
chosen after the fact. -/

section Cartesian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap

/-- The symmetric Cartesian coordinate of a bounded operator. -/
noncomputable def volterraSymmetric (T : H →L[ℂ] H) : H →L[ℂ] H := T + adjoint T

/-- **`(5)`, the Volterra phase coordinate.** -/
noncomputable def volterraPhase (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (-Complex.I) • (T - adjoint T)

/-- The symmetric coordinate is self-adjoint. -/
theorem isSelfAdjoint_volterraSymmetric (T : H →L[ℂ] H) :
    IsSelfAdjoint (volterraSymmetric T) := by
  rw [IsSelfAdjoint, volterraSymmetric, star_add, star_eq_adjoint, star_eq_adjoint,
    adjoint_adjoint]
  abel

/-- **`(5)`, the phase coordinate is self-adjoint.**  Adjoining conjugates the scalar and reverses
the difference, and the two sign changes cancel. -/
theorem isSelfAdjoint_volterraPhase (T : H →L[ℂ] H) :
    IsSelfAdjoint (volterraPhase T) := by
  rw [IsSelfAdjoint, volterraPhase, star_smul, star_sub, star_eq_adjoint, star_eq_adjoint,
    adjoint_adjoint]
  simp only [RCLike.star_def, Complex.conj_neg_I]
  module

/-- **`(6)`, the Cartesian split.**  Every bounded operator is half its symmetric coordinate plus
`i/2` times its phase coordinate — an identity, not a hypothesis. -/
theorem two_smul_eq_volterraSymmetric_add_I_smul_volterraPhase (T : H →L[ℂ] H) :
    (2 : ℂ) • T = volterraSymmetric T + Complex.I • volterraPhase T := by
  rw [volterraSymmetric, volterraPhase, smul_smul,
    show Complex.I * -Complex.I = 1 by simp [Complex.I_mul_I]]
  module

/-- **The response hypothesis is automatic.**  Reading the three responses as pairings of a fixed
observation vector against the operator's Cartesian coordinates, the hypothesis carried by the
response theorems above is exactly the operator identity `(6)` — so it need never be assumed. -/
theorem inner_volterra_cartesian (T : H →L[ℂ] H) (u w : H) :
    2 * inner ℂ w (T u)
      = inner ℂ w ((volterraSymmetric T) u)
        + Complex.I * inner ℂ w ((volterraPhase T) u) := by
  have hop := two_smul_eq_volterraSymmetric_add_I_smul_volterraPhase T
  have happ : ((2 : ℂ) • T) u = (volterraSymmetric T + Complex.I • volterraPhase T) u := by
    rw [hop]
  rw [smul_apply, add_apply, smul_apply] at happ
  have := congrArg (fun x => inner ℂ w x) happ
  simpa [inner_add_right, inner_smul_right] using this

/-! ## Reflection parity of the Cartesian coordinates

`(9)` says a reflection conjugates the causal operator to its adjoint.  That single relation forces
the two Cartesian coordinates to have opposite reflection parity: the symmetric coordinate is fixed
and the phase is negated.  This is why `(10)`--`(11)` separate — the admissible positive pencil
controls one parity and says nothing about the other. -/

/-- A reflection conjugating the operator to its adjoint also conjugates the adjoint back. -/
theorem reflection_adjoint_conj {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (h : R * T * R = adjoint T) : R * adjoint T * R = T := by
  have hstar := congrArg star h
  rw [star_mul, star_mul, hR.star_eq, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint] at hstar
  simpa [mul_assoc] using hstar

/-- **The symmetric coordinate is reflection-even.** -/
theorem volterraSymmetric_reflection {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (h : R * T * R = adjoint T) :
    R * volterraSymmetric T * R = volterraSymmetric T := by
  have hback := reflection_adjoint_conj hR h
  rw [volterraSymmetric, mul_add, add_mul, h, hback]
  exact add_comm _ _

/-- **The phase coordinate is reflection-odd.**  So the two coordinates cannot be controlled by the
same parity sector, which is the content of `(10)`--`(11)`. -/
theorem volterraPhase_reflection {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (h : R * T * R = adjoint T) :
    R * volterraPhase T * R = -volterraPhase T := by
  have hback := reflection_adjoint_conj hR h
  have hexp : R * volterraPhase T * R
      = (-Complex.I) • (R * T * R - R * adjoint T * R) := by
    rw [volterraPhase, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
  rw [hexp, h, hback, volterraPhase]
  module

/-- The reflection commutes with the symmetric coordinate. -/
theorem volterraSymmetric_comm_reflection {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinv : R * R = 1) (h : R * T * R = adjoint T) :
    R * volterraSymmetric T = volterraSymmetric T * R := by
  have hfix := volterraSymmetric_reflection hR h
  calc R * volterraSymmetric T = R * volterraSymmetric T * (R * R) := by rw [hinv, mul_one]
    _ = (R * volterraSymmetric T * R) * R := by noncomm_ring
    _ = volterraSymmetric T * R := by rw [hfix]

/-- The reflection anticommutes with the phase coordinate. -/
theorem volterraPhase_anticomm_reflection {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinv : R * R = 1) (h : R * T * R = adjoint T) :
    R * volterraPhase T = -(volterraPhase T * R) := by
  have hneg := volterraPhase_reflection hR h
  calc R * volterraPhase T = R * volterraPhase T * (R * R) := by rw [hinv, mul_one]
    _ = (R * volterraPhase T * R) * R := by noncomm_ring
    _ = (-volterraPhase T) * R := by rw [hneg]
    _ = -(volterraPhase T * R) := by noncomm_ring

/-- **`(10)`--`(11)`, the parity separation.**  On an odd vector the symmetric coordinate stays odd
while the phase becomes even, so the two responses occupy complementary reflection sectors and no
sign transfers between them. -/
theorem volterraSymmetric_apply_odd {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinv : R * R = 1) (h : R * T * R = adjoint T) {u : H} (hu : R u = -u) :
    R ((volterraSymmetric T) u) = -((volterraSymmetric T) u) := by
  have hcomm := volterraSymmetric_comm_reflection hR hinv h
  have := congrArg (fun A : H →L[ℂ] H => A u) hcomm
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at this
  rw [this, hu, map_neg]

theorem volterraPhase_apply_odd {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinv : R * R = 1) (h : R * T * R = adjoint T) {u : H} (hu : R u = -u) :
    R ((volterraPhase T) u) = (volterraPhase T) u := by
  have hanti := volterraPhase_anticomm_reflection hR hinv h
  have := congrArg (fun A : H →L[ℂ] H => A u) hanti
  rw [mul_apply_eq_comp, neg_apply, mul_apply_eq_comp] at this
  rw [this, hu, map_neg, neg_neg]

end Cartesian

section Triangles

open MeasureTheory

/-- **`(4)`, the complementary triangles.**  The causal and anticausal halves of a convolution
recombine into the full one.  Stated on interval integrals the shared endpoint contributes nothing
automatically, so the "diagonal has measure zero" step is not a separate argument. -/
theorem causal_add_anticausal (k u : ℝ → ℂ) (a x : ℝ)
    (h₁ : IntervalIntegrable (fun y => k (x - y) * u y) volume (-a) x)
    (h₂ : IntervalIntegrable (fun y => k (x - y) * u y) volume x a) :
    (∫ y in (-a)..x, k (x - y) * u y) + (∫ y in x..a, k (x - y) * u y)
      = ∫ y in (-a)..a, k (x - y) * u y :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

/-- The anticausal half is the full convolution minus the causal one. -/
theorem anticausal_eq_sub (k u : ℝ → ℂ) (a x : ℝ)
    (h₁ : IntervalIntegrable (fun y => k (x - y) * u y) volume (-a) x)
    (h₂ : IntervalIntegrable (fun y => k (x - y) * u y) volume x a) :
    (∫ y in x..a, k (x - y) * u y)
      = (∫ y in (-a)..a, k (x - y) * u y) - ∫ y in (-a)..x, k (x - y) * u y := by
  rw [← causal_add_anticausal k u a x h₁ h₂]
  ring

/-- **The causal restriction is an indicator factor.**  Writing the moving upper limit as an
indicator inside a fixed interval turns the triangle of `(3)` into an ordinary product region, so the
Fubini step there is a plain product-measure swap rather than a change of variables. -/
theorem causal_eq_indicator_integral (k u : ℝ → ℂ) (a x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
    (∫ y in (-a)..a, Set.indicator {y | y ≤ x} (fun y => k (x - y) * u y) y)
      = ∫ y in (-a)..x, k (x - y) * u y :=
  intervalIntegral.integral_indicator hx

/-- The anticausal restriction likewise, read from the complementary triangle. -/
theorem anticausal_eq_sub_indicator (k u : ℝ → ℂ) (a x : ℝ) (hx : x ∈ Set.Icc (-a) a)
    (h₁ : IntervalIntegrable (fun y => k (x - y) * u y) volume (-a) x)
    (h₂ : IntervalIntegrable (fun y => k (x - y) * u y) volume x a) :
    (∫ y in x..a, k (x - y) * u y)
      = (∫ y in (-a)..a, k (x - y) * u y)
        - ∫ y in (-a)..a, Set.indicator {y | y ≤ x} (fun y => k (x - y) * u y) y := by
  rw [causal_eq_indicator_integral k u a x hx]
  exact anticausal_eq_sub k u a x h₁ h₂

/-- **`(3)`'s reduction, completed.**  The interval transform of a causal convolution is the double
integral over the *fixed* square carrying the causal indicator.  Combined with a product-measure
swap this is `(3)`; no change of variables on a moving triangle is required. -/
theorem intervalFourier_causal_eq_indicator_double (k u : ℝ → ℂ) (a : ℝ) (ha : 0 ≤ a) (w : ℂ) :
    (∫ x in (-a)..a, Complex.exp (w * x) *
        ∫ y in (-a)..a, Set.indicator {y | y ≤ x} (fun y => k (x - y) * u y) y)
      = ∫ x in (-a)..a, Complex.exp (w * x) * ∫ y in (-a)..x, k (x - y) * u y := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
  rw [causal_eq_indicator_integral k u a x hx]

/-- **`(3)`'s Fubini step.**  On the fixed square the double integral may be taken in either order.
The indicator carries the causal restriction, so this is an ordinary product-measure swap and the
only hypothesis is integrability on the square. -/
theorem causal_double_swap (F : ℝ → ℝ → ℂ) (a : ℝ)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (-a) a)).prod (volume.restrict (Set.Ioc (-a) a)))) :
    (∫ x in Set.Ioc (-a) a, ∫ y in Set.Ioc (-a) a, F x y)
      = ∫ y in Set.Ioc (-a) a, ∫ x in Set.Ioc (-a) a, F x y :=
  MeasureTheory.integral_integral_swap hF

/-- The causal integrand of `(3)`, as a function on the square. -/
noncomputable def causalSquareIntegrand (k u : ℝ → ℂ) (w : ℂ) (x y : ℝ) : ℂ :=
  Complex.exp (w * x) * Set.indicator {y | y ≤ x} (fun y => k (x - y) * u y) y

/-- **`(3)` on the square.**  Swapping the order of the causal double integral exchanges the roles of
the two triangles, which is exactly the passage between the right-triangle response and the
transform of the causal convolution. -/
theorem causalSquareIntegrand_swap (k u : ℝ → ℂ) (w : ℂ) (a : ℝ)
    (hF : Integrable (Function.uncurry (causalSquareIntegrand k u w))
      ((volume.restrict (Set.Ioc (-a) a)).prod (volume.restrict (Set.Ioc (-a) a)))) :
    (∫ x in Set.Ioc (-a) a, ∫ y in Set.Ioc (-a) a, causalSquareIntegrand k u w x y)
      = ∫ y in Set.Ioc (-a) a, ∫ x in Set.Ioc (-a) a, causalSquareIntegrand k u w x y :=
  causal_double_swap _ a hF

end Triangles

end RHTower
