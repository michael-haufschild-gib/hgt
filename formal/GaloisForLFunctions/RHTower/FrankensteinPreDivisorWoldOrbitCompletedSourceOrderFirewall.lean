import GaloisForLFunctions.RHTower.FrankensteinCCMGammaWoldCubicJuliaOrbitDescent
import GaloisForLFunctions.RHTower.FrankensteinMatrixCompleteBoundaryRestriction

/-!
# Pre-divisor Wold-orbit completed-source order firewall

The completed CCM--Gamma source landing is defined before the second selected divisor residue.
This makes it possible to state the proposed positive completed-source order literally on a
punctured source neighbourhood rather than only after specialization to a Xi divisor.

The resulting order is impossible at every retained strict-right divisor once the Wold clock is
sufficiently deep.  Indeed, finite-dimensional Loewner order makes trace monotone, while the
source landing tends to the finite Wold-regularized orbit response; that response eventually
strictly exceeds the complete primitive Euler budget.  The same argument excludes every positive
Gram-remainder conservation on the punctured source neighbourhood.

Consequently, global existence of either local source order or positive conservation is equivalent
to RH.  This is stronger than the post-divisor scalar firewall: it proves that positivity cannot be
established first on the literal completed source and then carried through the selected residue by
closedness.  A successful producer must therefore use a genuinely signed/indefinite source law or
an order operation that is not preserved by the divisor residue.
-/

open Complex Matrix Filter Set Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Primitive Euler budget with the shared Julia environment retained as a second operator
corner. -/
def sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator
    (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c : ℝ) : ℂ), 0;
    0, 4]

/-- Literal completed-source orbit operator before the second selected CCM--Gamma residue. -/
def frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding c q N v : ℝ) : ℂ), 0;
    0, 4]

/-- Post-residue finite orbit operator, with the same shared environment corner. -/
def sourceZeroHorizontalWoldRegularizedJuliaOrbitResponseOperator
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N : ℝ) : ℂ), 0;
    0, 4]

@[simp] theorem re_trace_sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator
    (c : ℂ) :
    (sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator c).trace.re =
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c + 4 := by
  simp [sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator,
    Matrix.trace, Fin.sum_univ_two]

@[simp] theorem re_trace_frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    (frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator c q N v).trace.re =
      frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding c q N v + 4 := by
  simp [frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator,
    Matrix.trace, Fin.sum_univ_two]

@[simp] theorem re_trace_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponseOperator
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (sourceZeroHorizontalWoldRegularizedJuliaOrbitResponseOperator c q N).trace.re =
      sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N + 4 := by
  simp [sourceZeroHorizontalWoldRegularizedJuliaOrbitResponseOperator,
    Matrix.trace, Fin.sum_univ_two]

/-- Local pre-divisor order proposed by the completed-source route: on a punctured neighbourhood
of the second CCM--Gamma pole, the literal source orbit is Loewner-dominated by the primitive Euler
budget operator. -/
def FrankensteinPreDivisorWoldOrbitCompletedSourceOrderAt
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : Prop :=
  ∀ᶠ v : ℂ in
      nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ),
    frankensteinMatrixLoewnerLE
      (frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator c q N v)
      (sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator c)

/-- Positive conservation form of the same source target.  Defect is an independently visible
two-channel Gram; it is not defined as the formal difference of budget and orbit. -/
def FrankensteinPreDivisorWoldOrbitCompletedSourceConservationAt
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : Prop :=
  ∀ᶠ v : ℂ in
      nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ),
    ∃ D : Matrix (Fin 2) (Fin 2) ℂ,
      sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator c =
        frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator c q N v + Dᴴ * D

/-- A positive Gram-remainder conservation gives the genuine local Loewner order. -/
theorem frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt_of_conservation
    {c : ℂ} {q : XiRightZeroCopy} {N : ℕ}
    (h : FrankensteinPreDivisorWoldOrbitCompletedSourceConservationAt c q N) :
    FrankensteinPreDivisorWoldOrbitCompletedSourceOrderAt c q N := by
  filter_upwards [h] with v hv
  rcases hv with ⟨D, hD⟩
  unfold frankensteinMatrixLoewnerLE
  have hdiff :
      sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator c -
          frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator c q N v =
        Dᴴ * D := by
    rw [hD]
    abel
  rw [hdiff]
  exact Matrix.posSemidef_conjTranspose_mul_self D

/-- Closedness of scalar trace order transports a local pre-divisor Loewner comparison through
the selected CCM--Gamma residue. -/
theorem sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_le_budget_of_preDivisorOrder
    {c : ℂ} {q : XiRightZeroCopy} {N : ℕ}
    (horder : FrankensteinPreDivisorWoldOrbitCompletedSourceOrderAt c q N) :
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N ≤
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c := by
  by_contra hnot
  have hgt :
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N :=
    lt_of_not_ge hnot
  have hlanding :=
    tendsto_frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding c q N
  have hsourceGT :
      ∀ᶠ v : ℂ in
          nhdsWithin
            (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
            ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ),
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
          frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding c q N v :=
    hlanding.eventually (eventually_gt_nhds hgt)
  obtain ⟨v, hvOrder, hvGT⟩ := (horder.and hsourceGT).exists
  have htrace := matrix_re_trace_mono_of_frankensteinLoewnerLE hvOrder
  simp only [re_trace_frankensteinCCMGammaWoldOrbitPreDivisorSourceOperator,
    re_trace_sourceHorizontalWoldRegularizedJuliaOrbitBudgetOperator] at htrace
  linarith

/-- **Pre-divisor operator firewall.**  On every retained strict-right Xi copy and every nonzero
coefficient, all sufficiently deep literal Wold-orbit source operators fail the proposed local
completed-source Loewner bound. -/
theorem eventually_not_frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      ¬ FrankensteinPreDivisorWoldOrbitCompletedSourceOrderAt c q N := by
  filter_upwards
    [eventually_sourceBudget_lt_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse hc q]
      with N hoverspend
  intro horder
  have hle :=
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_le_budget_of_preDivisorOrder horder
  linarith

/-- No positive Gram-remainder conservation survives on a retained strict-right copy. -/
theorem eventually_not_frankensteinPreDivisorWoldOrbitCompletedSourceConservationAt
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      ¬ FrankensteinPreDivisorWoldOrbitCompletedSourceConservationAt c q N := by
  filter_upwards
    [eventually_not_frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt hc q]
      with N hnotOrder
  exact fun hconservation => hnotOrder
    (frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt_of_conservation hconservation)

/-- Global cofinal local-order target on every retained strict-right copy. -/
def EveryFrankensteinPreDivisorWoldOrbitCompletedSourceOrder : Prop :=
  ∀ (q : XiRightZeroCopy) (c : ℂ), c ≠ 0 →
    ∀ᶠ N : ℕ in atTop,
      FrankensteinPreDivisorWoldOrbitCompletedSourceOrderAt c q N

/-- Global cofinal positive-conservation target on every retained strict-right copy. -/
def EveryFrankensteinPreDivisorWoldOrbitCompletedSourceConservation : Prop :=
  ∀ (q : XiRightZeroCopy) (c : ℂ), c ≠ 0 →
    ∀ᶠ N : ℕ in atTop,
      FrankensteinPreDivisorWoldOrbitCompletedSourceConservationAt c q N

/-- The literal pre-divisor operator order is already exactly RH-strength. -/
theorem everyFrankensteinPreDivisorWoldOrbitCompletedSourceOrder_iff_riemannHypothesis :
    EveryFrankensteinPreDivisorWoldOrbitCompletedSourceOrder ↔ RiemannHypothesis := by
  constructor
  · intro hlaw
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have horder := hlaw q 1 one_ne_zero
    have hnot :=
      eventually_not_frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt
        (c := (1 : ℂ)) one_ne_zero q
    obtain ⟨N, hN, hnotN⟩ := (horder.and hnot).exists
    exact hnotN hN
  · intro hRH q
    haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim q

/-- The positive Gram-remainder conservation formulation is likewise exactly RH-strength. -/
theorem everyFrankensteinPreDivisorWoldOrbitCompletedSourceConservation_iff_riemannHypothesis :
    EveryFrankensteinPreDivisorWoldOrbitCompletedSourceConservation ↔ RiemannHypothesis := by
  constructor
  · intro hlaw
    apply everyFrankensteinPreDivisorWoldOrbitCompletedSourceOrder_iff_riemannHypothesis.mp
    intro q c hc
    filter_upwards [hlaw q c hc] with N hN
    exact frankensteinPreDivisorWoldOrbitCompletedSourceOrderAt_of_conservation hN
  · intro hRH q
    haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim q

end

end RHTower
