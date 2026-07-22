import GaloisForLFunctions.RHTower.SuzukiProjectiveResolventPluckerLift
import GaloisForLFunctions.RHTower.SuzukiCarlemanJumpEulerDefectWeld
import GaloisForLFunctions.RHTower.SuzukiProjectiveAffineSecantTensor

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

end RHTower
