import GaloisForLFunctions.HTGeometry.GammaFactorialMovingHarmonicResidue
import GaloisForLFunctions.HTGeometry.GammaIterationAlgebraicIndependence

/-!
# The complete first-jet boundary of the Gamma iterate tower

After multiplying every derivative by the Gamma factorial scale, the depth-`k+1` first jet factors
exactly through the two microscope coordinates

`a = Gamma(t)` and `b = s * Gamma'(t)`.

Its factorial boundary is the depth-`k` first jet at `a`, with every derivative multiplied by
`a²`.  Consequently the only collapsed coordinate is the first pair `b = a²`; all later value and
derivative coordinates retain the preceding first jet.  This is the analytic counterpart of the
principal Riccati kernel.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

abbrev GammaIterateFirstJetIndex (k : ℕ) := Fin 1 ⊕ (Fin k × Fin 2)

/-- Point, then for each positive iterate its derivative followed by its value. -/
def gammaIterateFirstJetTuple (k : ℕ) (z : ℂ) : GammaIterateFirstJetIndex k → ℂ
  | Sum.inl _ => z
  | Sum.inr (j, slot) => Fin.cases
      (iteratedDeriv 1 (gammaIterate ((j : ℕ) + 1)) z)
      (fun _ => gammaIterate ((j : ℕ) + 1) z) slot

theorem iteratedDeriv_one_gammaIterate_succ {k : ℕ} {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet (k + 1)) :
    iteratedDeriv 1 (gammaIterate (k + 1)) z =
      iteratedDeriv 1 (gammaIterate k) (Complex.Gamma z) *
        iteratedDeriv 1 Complex.Gamma z := by
  rw [gammaIterateRegularSet_succ] at hz
  rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_one]
  simpa [Function.comp_def, gammaIterate] using deriv_comp z
    (analyticAt_gammaIterate hz.2).differentiableAt
    (analyticAt_Gamma z hz.1).differentiableAt

theorem analyticAt_gammaIterateFirstJetTupleCoordinate {k : ℕ} {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet k) (i : GammaIterateFirstJetIndex k) :
    AnalyticAt ℂ (fun w => gammaIterateFirstJetTuple k w i) z := by
  rcases i with (j | ⟨j, slot⟩)
  · simpa [gammaIterateFirstJetTuple] using!
      (analyticAt_id : AnalyticAt ℂ id z)
  · have hj : (j : ℕ) + 1 ≤ k := by omega
    have hzj : z ∈ gammaIterateRegularSet ((j : ℕ) + 1) :=
      gammaIterateRegularSet_antitone hj hz
    induction slot using Fin.cases with
    | zero =>
        simpa [gammaIterateFirstJetTuple] using
          analyticAt_iteratedDeriv_of_analyticAt (analyticAt_gammaIterate hzj) 1
    | succ slot =>
        have hslot : slot = 0 := Subsingleton.elim _ _
        subst slot
        simpa [gammaIterateFirstJetTuple] using!
          analyticAt_gammaIterate hzj

def gammaIterateScaledFirstJetData (k : ℕ) (s z : ℂ) : Fin k × Fin 2 → ℂ
  | (j, slot) => Fin.cases
      (s * iteratedDeriv 1 (gammaIterate ((j : ℕ) + 1)) z)
      (fun _ => gammaIterate ((j : ℕ) + 1) z) slot

abbrev gammaIterateScaledFirstJetTail := gammaIterateScaledFirstJetData

def gammaFirstJetCompositionData (k : ℕ) (a b : ℂ) : Fin (k + 1) × Fin 2 → ℂ
  | (j, slot) => Fin.cases
      (b * iteratedDeriv 1 (gammaIterate (j : ℕ)) a)
      (fun _ => gammaIterate (j : ℕ) a) slot

abbrev gammaFirstJetCompositionTail := gammaFirstJetCompositionData

/-- Exact chain-rule factorization of the scaled depth-`k+1` first jet. -/
theorem gammaIterateScaledFirstJetTail_eq_composition
    {k : ℕ} {s z : ℂ} (hz : z ∈ gammaIterateRegularSet (k + 1)) :
    gammaIterateScaledFirstJetTail (k + 1) s z =
      gammaFirstJetCompositionTail k (Complex.Gamma z)
        (s * iteratedDeriv 1 Complex.Gamma z) := by
  funext i
  rcases i with ⟨j, slot⟩
  induction slot using Fin.cases with
  | zero =>
      simp only [gammaIterateScaledFirstJetTail, gammaIterateScaledFirstJetData,
        gammaFirstJetCompositionTail, gammaFirstJetCompositionData, Fin.cases_zero]
      rw [iteratedDeriv_one_gammaIterate_succ
        (gammaIterateRegularSet_antitone (by omega) hz)]
      ring
  | succ slot =>
      have hslot : slot = 0 := Subsingleton.elim _ _
      subst slot
      change gammaIterate ((j : ℕ) + 1) z =
        gammaIterate (j : ℕ) (Complex.Gamma z)
      rfl

/-- The first-jet factorial boundary.  Only the first derivative coordinate collapses, to `a²`;
all later derivative coordinates are multiplied by the same nonzero factor `a²`. -/
def gammaFirstJetBoundaryTail (k : ℕ) (a : ℂ) : Fin (k + 1) × Fin 2 → ℂ :=
  gammaFirstJetCompositionTail k a (a ^ 2)

/-- Coordinatewise convergence of the complete scaled first jet to its Riccati boundary. -/
theorem tendsto_gammaIterateScaledFirstJetTail_factorialBlowUp
    {k : ℕ} {x : ℂ}
    (hk : 1 ≤ k)
    (hx : x ∈ localGammaMicroscopeDomain (gammaIterateRegularSet k))
    (hxLeft : x ∈ gammaFactorialMicroscopeDomain)
    (i : Fin (k + 1) × Fin 2) :
    Tendsto (fun n => gammaIterateScaledFirstJetTail (k + 1)
        (reciprocalGammaFactorialScale n)
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x) i)
      atTop (𝓝 (gammaFirstJetBoundaryTail k ((-x)⁻¹) i)) := by
  have hA := tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.tendsto_at hx.1
  have hB := iteratedDeriv_outerGamma_factorialBlowUp_tendsto
    id (fun _ _ => analyticAt_id) hxLeft 1
  rw [iteratedDeriv_one_outerReciprocalLimit_id x hx.1] at hB
  have hB' : Tendsto (fun n => reciprocalGammaFactorialScale n *
      iteratedDeriv 1 Complex.Gamma
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      atTop (𝓝 (((-x)⁻¹) ^ 2)) := by
    simpa [iteratedDeriv_factorialBlowUpZoom, outerReciprocalLimit] using hB
  have hreg : (-x)⁻¹ ∈ gammaIterateRegularSet k := hx.2
  have hcomp : Tendsto (fun n : ℕ => gammaFirstJetCompositionTail k
      (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      (reciprocalGammaFactorialScale n * iteratedDeriv 1 Complex.Gamma
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x)) i)
      atTop (𝓝 (gammaFirstJetBoundaryTail k ((-x)⁻¹) i)) := by
    rcases i with ⟨j, slot⟩
    have hj : (j : ℕ) ≤ k := Nat.le_of_lt_succ j.isLt
    have hregj : (-x)⁻¹ ∈ gammaIterateRegularSet (j : ℕ) :=
      gammaIterateRegularSet_antitone hj hreg
    induction slot using Fin.cases with
    | zero =>
        have hjet :=
          (analyticAt_iteratedDeriv_of_analyticAt
            (analyticAt_gammaIterate hregj) 1).continuousAt.tendsto.comp hA
        simpa [gammaFirstJetCompositionTail, gammaFirstJetCompositionData,
          gammaFirstJetBoundaryTail] using hB'.mul hjet
    | succ slot =>
        have hslot : slot = 0 := Subsingleton.elim _ _
        subst slot
        have hvalue := (analyticAt_gammaIterate hregj).continuousAt.tendsto.comp hA
        simpa [gammaFirstJetCompositionTail, gammaFirstJetCompositionData,
          gammaFirstJetBoundaryTail] using! hvalue
  apply hcomp.congr'
  filter_upwards [eventually_factorialBlowUp_input_gammaIterateRegular hk hx]
    with n hn
  exact congrFun (gammaIterateScaledFirstJetTail_eq_composition hn).symm i

end

end GaloisForLFunctions
