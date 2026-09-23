import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.XiTraceHankelCriterion
import GaloisForLFunctions.RHTower.CriticalTraceMomentGerm
import GaloisForLFunctions.RHTower.AllGradePrimePowerCorona
import GaloisForLFunctions.RHTower.FESchwarzPrimeCoronaHorizontalGradeCollapse
import GaloisForLFunctions.RHTower.SingularCoronaResidueIncidenceTrilemma

open Complex Filter Metric Set Topology ComplexConjugate
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/- Exact formal content of the Route A terminal verdict.  Each field is a literal analytic,
topological, corona, or residue theorem; no route conclusion is encoded as an assumption. -/
set_option linter.unusedVariables false in
structure RouteASourceTraceHankelFinalVerdictPackage : Prop where
  sourceTargetIdentity : ∀ {z : ℂ},
    0 < (1 / 2 + z * Complex.I).re →
    1 / 2 + z * Complex.I ≠ 1 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
    continuedPrimeArchSourceRelativeTrace z = xiRelativeResolventTrace z
  targetPositivityExactlyRH :
    XiCentralTraceHankelNonnegative ↔ RiemannHypothesis
  reciprocalSquareMomentBridge : ∀ {z : ℂ}, XiC z ≠ 0 →
    xiRelativeResolventTrace z =
      -z * ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q
  finiteHankelMomentExpansion : ∀ p : Polynomial ℝ,
    xiCentralTraceHankel p =
      ∑ k ∈ Finset.range ((p.map (algebraMap ℝ ℂ) ^ (2 : ℕ)).natDegree + 1),
        (p.map (algebraMap ℝ ℂ) ^ (2 : ℕ)).coeff k * xiCentralReciprocalMoment k
  normalizedTraceMomentInversion : ∀ (g : ℂ → ℂ), DifferentiableAt ℂ g 0 →
    normalizedTraceMomentGerm
      (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g
  nonlinearEulerOrbitCompleteness : ∀ (f : ℂ → ℂ) {r₀ r₁ epsilon : ℝ},
    ∀ (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁), r₁ < 1 / 2 → 0 < epsilon →
    ∀ (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁)),
      (∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z) →
      (∀ z : ℂ, f (conj z) = conj (f z)) →
      ∀ S : Finset Nat.Primes,
        criticalDiscRestriction f r₀
            (hf.continuousOn_ball.mono (closedBall_subset_closedBall hr01.le)) ∈
          (criticalDiscRealEulerIncrementGroup r₀ S epsilon).topologicalClosure
  continuousQuotientCollapse : ∀ {r₀ r₁ epsilon : ℝ} (S : Finset Nat.Primes)
    {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (A : C(CriticalClosedDisc r₀, ℂ) → Y), Continuous A →
    (∀ x g, g ∈ criticalDiscRealEulerIncrementGroup r₀ S epsilon → A (x + g) = A x) →
    ∀ (f : ℂ → ℂ),
      ∀ (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁), r₁ < 1 / 2 → 0 < epsilon →
      ∀ (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁)),
        (∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z) →
        (∀ z : ℂ, f (conj z) = conj (f z)) →
        A (criticalDiscRestriction f r₀
          (hf.continuousOn_ball.mono (closedBall_subset_closedBall hr01.le))) = A 0
  analyticHankelConeInstability : ∀ {f : ℂ → ℂ}
    {r₀ r₁ B closeEpsilon orbitEpsilon : ℝ},
    ∀ (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) (hr01 : r₀ < r₁)
      (hf : DiffContOnCl ℂ f (ball 0 r₁)),
      (∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ B) →
      0 ≤ B → 0 < closeEpsilon → 0 < orbitEpsilon →
      (∀ z, f (-z) = f z) → (∀ z, conj (f (conj z)) = f z) →
      ∀ (S : Finset Nat.Primes), r₁ < 1 / 2 →
      ∃ g : ℂ → ℂ,
        ∃ hg : DiffContOnCl ℂ g (ball 0 r₁),
          (∀ z ∈ closedBall (0 : ℂ) r₀, ‖g z - f z‖ < closeEpsilon) ∧
          ¬ AnalyticTraceHankelNonnegative g ∧
          criticalDiscRestriction (evenMomentToCriticalTrace g) r₀
              ((diffContOnCl_evenMomentToCriticalTrace g hg).continuousOn_ball.mono
                (closedBall_subset_closedBall hr01.le)) ∈
            (criticalDiscRealEulerIncrementGroup r₀ S orbitEpsilon).topologicalClosure ∧
          normalizedTraceMomentGerm
              (criticalTraceToCenteredOdd (evenMomentToCriticalTrace g)) = g
  higherEulerGradesVanish : ∀ {a : ℕ → ℝ},
    (∀ p, |a p| ≤ 1) →
    Tendsto (fun X => primePowerQuotient (eulerRayHigher a) X) atTop (nhds 0)
  finiteAlgebraicCoronaBlindness : ∀ {M S : Finset ℤ} {c : ℤ → ℤ → ℂ}
    {a t : ℝ} {mStar : ℤ},
    ∀ (ha : 0 < a),
      (∀ m ∈ M, m ≤ mStar) → mStar ∈ M →
      (∃ x : ℝ, horizontalGradeProfile S c t mStar x ≠ 0) →
      MemMarcinkiewiczLogLayer
        (absField (horizontalPrimeExponentialField M S c a t)) →
      ∃ hnonpos : ∀ m ∈ M, m ≤ 0,
        horizontalPrimeExponentialClass M S c a t ha.le hnonpos =
          horizontalGradeZeroPartClass M S c t
  scalarGraphFibreDichotomy : ∀ (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ),
    marcinkiewiczVerticalFibre D L = ⊥ ∨ marcinkiewiczVerticalFibre D L = ⊤
  canonicalResidueClosableExactlyRH :
    RiemannHypothesis ↔ IsClosableMarcinkiewicz residueDomain residueFunctional
  shiftedResidueClosableExactlyZeroFree : ∀ {z : ℂ}, z ∈ RightStrip →
    (IsClosableShiftedCorona z ↔
      ∀ ρ ∈ RightStrip, z.re < ρ.re → riemannZeta ρ ≠ 0)

/-- Closed unconditional synthesis of every proved Route A mechanism used by the final verdict. -/
theorem routeASourceTraceHankelFinalVerdict_unconditional :
    RouteASourceTraceHankelFinalVerdictPackage := by
  refine {
    sourceTargetIdentity := ?_
    targetPositivityExactlyRH := xiCentralTraceHankelNonnegative_iff_riemannHypothesis
    reciprocalSquareMomentBridge := ?_
    finiteHankelMomentExpansion := xiCentralTraceHankel_eq_moment_sum
    normalizedTraceMomentInversion :=
      normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace
    nonlinearEulerOrbitCompleteness := ?_
    continuousQuotientCollapse := ?_
    analyticHankelConeInstability := ?_
    higherEulerGradesVanish := ?_
    finiteAlgebraicCoronaBlindness := ?_
    scalarGraphFibreDichotomy := marcinkiewiczVerticalFibre_eq_bot_or_top
    canonicalResidueClosableExactlyRH := riemannHypothesis_iff_residueFunctional_isClosable
    shiftedResidueClosableExactlyZeroFree := ?_ }
  · intro z hspos hs1 hzeta
    exact continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hspos hs1 hzeta
  · intro z hz
    exact xiRelativeResolventTrace_eq_reciprocalSquareResolvent hz
  · intro f r₀ r₁ epsilon hr₀ hr01 hr1 hepsilon hf hodd hschwarz S
    exact criticalDisc_analytic_odd_schwarz_mem_realEulerIncrementGroup_closure
      f hr₀ hr01 hr1 hepsilon hf hodd hschwarz S
  · intro r₀ r₁ epsilon S Y _ _ A hA hinvariant f hr₀ hr01 hr1 hepsilon hf hodd hschwarz
    exact criticalDisc_continuous_finiteUnitInvariant_eq_base
      S A hA hinvariant f hr₀ hr01 hr1 hepsilon hf hodd hschwarz
  · intro f r₀ r₁ B closeEpsilon orbitEpsilon hr₀ hr₀1 hr01 hf hB hB0 hclose
      horbit heven hschwarz S hr1
    exact exists_close_realEulerOrbit_normalizedTraceHankel_failure
      hr₀ hr₀1 hr01 hf hB hB0 hclose horbit heven hschwarz S hr1
  · intro a ha
    exact tendsto_primePowerQuotient_eulerRayHigher ha
  · intro M S c a t mStar ha hM hstar hnonzero hb
    exact horizontalFiniteAlgebraicCoronaBlindness ha hM hstar hnonzero hb
  · exact fun hz => isClosableShiftedCorona_iff_zeroFree_above hz

end RHTower
