import GaloisForLFunctions.RHTower.EulerSquarefreeWickQuadraticCommonRefinementDescent
import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimeResidueHT
import GaloisForLFunctions.HTGeometry.FormalInvolutionJetRigidity

open PowerSeries

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Scalar renormalization of the first literal EWQ gauge. -/
def eulerWickQuadraticScalarRowFlip (c : ℂ) :
    EulerWickQuadraticCommonRefinement →ₗ[ℂ]
      EulerWickQuadraticCommonRefinement :=
  c • eulerWickQuadraticRowFlip

/-- Scalar renormalization of the second literal EWQ gauge. -/
def eulerWickQuadraticScalarColumnFlip (c : ℂ) :
    EulerWickQuadraticCommonRefinement →ₗ[ℂ]
      EulerWickQuadraticCommonRefinement :=
  c • eulerWickQuadraticColumnFlip

/-- Central scalar renormalizations cannot turn the commuting EWQ gauge square into a
projective one: the two scaled operators still commute exactly. -/
theorem eulerWickQuadraticScalarRowFlip_columnFlip_commute (a b : ℂ) :
    (eulerWickQuadraticScalarRowFlip a).comp
        (eulerWickQuadraticScalarColumnFlip b) =
      (eulerWickQuadraticScalarColumnFlip b).comp
        (eulerWickQuadraticScalarRowFlip a) := by
  apply LinearMap.ext
  intro v
  funext x
  change a * (b * eulerWickQuadraticRowFlip
      (eulerWickQuadraticColumnFlip v) x) =
    b * (a * eulerWickQuadraticColumnFlip
      (eulerWickQuadraticRowFlip v) x)
  rw [eulerWickQuadraticRowFlip_columnFlip_commute v]
  ring

/-- Any Weyl phase assigned to nonzero scalar twists of the two literal EWQ gauges is trivial. -/
theorem eulerWickQuadraticScalarGauge_weyl_phase_eq_one
    {a b zeta : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hweyl :
      (eulerWickQuadraticScalarRowFlip a).comp
          (eulerWickQuadraticScalarColumnFlip b) =
        zeta •
          ((eulerWickQuadraticScalarColumnFlip b).comp
            (eulerWickQuadraticScalarRowFlip a))) :
    zeta = 1 := by
  let v : EulerWickQuadraticCommonRefinement := fun _ => 1
  have hpoint := LinearMap.congr_fun hweyl v
  have hcoord := congrFun hpoint ((0 : Fin 2), (0 : Fin 2))
  change a * (b * 1) = zeta * (b * (a * 1)) at hcoord
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have heq : a * b = zeta * (a * b) := by
    simpa [mul_comm] using hcoord
  apply mul_right_cancel₀ hab
  simpa using heq.symm

/-- In particular the literal EWQ gauge pair cannot be made anticommuting by nonzero scalar
counterterms. -/
theorem eulerWickQuadraticScalarGauge_not_anticommute
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (eulerWickQuadraticScalarRowFlip a).comp
          (eulerWickQuadraticScalarColumnFlip b) ≠
      -((eulerWickQuadraticScalarColumnFlip b).comp
          (eulerWickQuadraticScalarRowFlip a)) := by
  intro hanti
  have hphase : (-1 : ℂ) = 1 :=
    eulerWickQuadraticScalarGauge_weyl_phase_eq_one ha hb (by
      apply LinearMap.ext
      intro v
      have hv := LinearMap.congr_fun hanti v
      simpa using hv)
  norm_num at hphase

/-- The nonzero EWQ marginal-quotient class therefore does not itself define a nontrivial
projective commutator.  Interaction cohomology and group `H²` are distinct invariants here. -/
theorem eulerWickNormalizedInteraction_nonzero_and_scalarProjectivePhase_trivial :
    eulerSquarefreeWickInteractionClass eulerSquarefreeWickNormalizedPacket ≠ 0 ∧
      ∀ {a b zeta : ℂ}, a ≠ 0 → b ≠ 0 →
        (eulerWickQuadraticScalarRowFlip a).comp
            (eulerWickQuadraticScalarColumnFlip b) =
          zeta •
            ((eulerWickQuadraticScalarColumnFlip b).comp
              (eulerWickQuadraticScalarRowFlip a)) →
        zeta = 1 := by
  constructor
  · intro hzero
    have hdefect :=
      (eulerSquarefreeWickInteractionClass_eq_zero_iff _).mp hzero
    rw [eulerSquarefreeWickNormalizedDefect] at hdefect
    norm_num at hdefect
  · intro a b zeta ha hb hweyl
    exact eulerWickQuadraticScalarGauge_weyl_phase_eq_one ha hb hweyl

/-- Nonlinear one-variable formal reparametrization does not repair the collapse: two commuting
quadratic EWQ generators with the same `-1` cotangent character must be the same germ. -/
theorem eulerWickQuadraticNonlinearFormalGauge_eq
    (F : Fin 2 → ℂ⟦X⟧)
    (h0 : ∀ i, constantCoeff (F i) = 0)
    (h1 : ∀ i, coeff 1 (F i) = -1)
    (hinv : ∀ i, subst (F i) (F i) = X)
    (hcomm : ∀ i j, subst (F i) (F j) = subst (F j) (F i)) :
    F 0 = F 1 :=
  GaloisForLFunctions.FormalGerm.commutingFormalInvolutionFamily_derivative_neg_one_eq
    F h0 h1 hinv hcomm 0 1

/-- Hence no faithful nonlinear action of the two literal EWQ gauges exists on one formal
complex coordinate while retaining their common quadratic tangent character. -/
theorem eulerWickQuadraticNonlinearFormalGauge_not_injective
    (F : Fin 2 → ℂ⟦X⟧)
    (h0 : ∀ i, constantCoeff (F i) = 0)
    (h1 : ∀ i, coeff 1 (F i) = -1)
    (hinv : ∀ i, subst (F i) (F i) = X)
    (hcomm : ∀ i j, subst (F i) (F j) = subst (F j) (F i)) :
    ¬ Function.Injective F := by
  intro hF
  have heq := eulerWickQuadraticNonlinearFormalGauge_eq F h0 h1 hinv hcomm
  have : (0 : Fin 2) = 1 := hF heq
  norm_num at this

end

end GaloisForLFunctions.RHTower
