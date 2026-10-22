import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices

/-!
# The averaged budget is exactly admission

A continuation criterion is worth having only if it is not stronger than the conclusion it serves.
For the averaged budget this can be decided, and the answer is exact: on an interval whose right
end is admitted, an averaged budget on `[a, c]` holds **if and only if** the family is admitted at
`a`.  The parameter average of the relative loss *is* the logarithm of the ratio of the shifted
energies, so no slack remains between hypothesis and conclusion
(`averagedContinuation_iff_admits`).

Two consequences fix the shape of the programme's open problem.

* The damping-averaged criterion is an **equivalence** with the Riemann hypothesis
  (`riemannHypothesis_iff_cofinal_averagedDampingContinuation`): cofinal averaged budgets are RH,
  and RH returns them.  So nothing is lost by working with averages, and nothing extra is being
  assumed.
* The **pointwise** budget is a strictly stronger demand than admission, and the gap is not an
  artefact of the arithmetic: a family can be admitted at *every* parameter — the state RH
  asserts — and still carry no pointwise linear budget on any nondegenerate interval
  (`exists_admits_everywhere_not_linearContinuation`).  The thinning spike of
  `TheDampingAverageOfTheRelativeLossSuffices` is such a family: at the midpoint its relative loss
  exceeds every constant over the horizons while its energy stays below `exp π − 1`.

Hence a pointwise horizon-free bound on the negative part of the signed work is not known to
follow from RH, while its parameter average is equivalent to RH.  The obligation to aim at is the
averaged one.
-/

open Set Filter Finset MeasureTheory RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {E : ℝ → ℕ → ℝ} {E' : ℕ → ℝ → ℝ} {a c : ℝ}

/-! ## §1. Admission returns the averaged budget -/

/-- **Admission at the left end is an averaged budget.**  The constant is `log(1 + B)`: the ratio
of the shifted energies is bounded because the numerator is. -/
theorem AveragedContinuation.of_admits (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c)
    (ha : Admits E a) : AveragedContinuation E E' a c := by
  obtain ⟨B, hB⟩ := ha
  refine ⟨Real.log (1 + max B 0), fun T => ⟨hint T, ?_⟩⟩
  rw [integral_relativeLoss_eq hac (fun ε hε => hE0 ε hε T) (hEd T) (hint T)]
  have hca : (0 : ℝ) < 1 + E a T := by linarith [hE0 a (left_mem_Icc.mpr hac) T]
  have hlogc : 0 ≤ Real.log (1 + E c T) :=
    Real.log_nonneg (by linarith [hE0 c (right_mem_Icc.mpr hac) T])
  have hmono : Real.log (1 + E a T) ≤ Real.log (1 + max B 0) :=
    Real.log_le_log hca (by linarith [(hB T).trans (le_max_left B 0)])
  linarith

/-- **The averaged budget is exactly admission.**  With the right end admitted, an averaged budget
on `[a, c]` and admission at `a` are the same statement. -/
theorem averagedContinuation_iff_admits (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c)
    (hc : Admits E c) : AveragedContinuation E E' a c ↔ Admits E a :=
  ⟨fun h => Admits.of_averagedContinuation hac hE0 hEd h hc,
    AveragedContinuation.of_admits hac hE0 hEd hint⟩

/-! ## §2. The arithmetic dictionary entry -/

/-- The averaged damping budget on `[a, c]`, for an admitted right end, is membership of `a` in the
admissible damping set. -/
theorem averagedDampingContinuation_iff_admits {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    AveragedDampingContinuation a c ↔ Admits dampedMobiusEnergy a :=
  averagedContinuation_iff_admits hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (fun T _ hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T)
    (fun T => intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T) hc

/-- The averaged damping budget on `[a, c]` is membership of `a` in `receiverDampings`. -/
theorem mem_receiverDampings_iff_averagedDampingContinuation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    a ∈ receiverDampings ↔ AveragedDampingContinuation a c :=
  (mem_receiverDampings_iff_admits ha).trans
    (averagedDampingContinuation_iff_admits ha hac hc).symm

/-- **The averaged damping criterion is an equivalence with the Riemann hypothesis.**  Cofinal
averaged budgets from half damping are RH, and RH supplies them.  So the averaged demand is
calibrated: neither weaker nor stronger than the conclusion. -/
theorem riemannHypothesis_iff_cofinal_averagedDampingContinuation :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ a < δ ∧
      AveragedDampingContinuation a (1 / 2) := by
  constructor
  · intro h δ hδ
    have hmin : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
    refine ⟨min δ (1 / 2) / 2, by positivity, by linarith [min_le_left δ (1 / 2 : ℝ)], ?_⟩
    have hx0 : 0 < min δ (1 / 2 : ℝ) / 2 := by positivity
    have hxc : min δ (1 / 2 : ℝ) / 2 ≤ 1 / 2 := by
      linarith [min_le_right δ (1 / 2 : ℝ)]
    exact (averagedDampingContinuation_iff_admits hx0 hxc
      (admits_dampedMobiusEnergy_of_half_le le_rfl)).mpr
      (admits_dampedMobiusEnergy_of_riemannHypothesis h hx0)
  · intro h
    refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
    obtain ⟨x, hx0, hxδ, hcont⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    refine ⟨x, hx0, lt_of_lt_of_le hxδ (min_le_left _ _), ?_⟩
    exact (averagedDampingContinuation_iff_admits hx0
      (le_of_lt (lt_of_lt_of_le hxδ (min_le_right _ _)))
      (admits_dampedMobiusEnergy_of_half_le le_rfl)).mp hcont

/-! ## §3. The pointwise budget is stronger than the conclusion -/

/-- The thinning spike is admitted at every parameter: its scale never exceeds `π`. -/
theorem admits_lossSpikeEnergy (ε₀ ε : ℝ) : Admits (lossSpikeEnergy ε₀) ε :=
  ⟨Real.exp Real.pi - 1, fun T => by
    have h := Real.exp_le_exp.mpr (lossSpikeScale_le_pi ε₀ T ε)
    simp only [lossSpikeEnergy]
    linarith⟩

/-- **A pointwise budget can fail in the admitted state.**  On every nondegenerate interval there
is a differentiable nonnegative energy family admitted at *every* parameter — the state the Riemann
hypothesis asserts for the arithmetic family — whose averaged budget is `π` and which carries no
pointwise linear continuation budget at all.  So a pointwise horizon-free bound on the loss is not
a consequence of admission: the programme's open demand should be stated in averaged form, where
hypothesis and conclusion coincide. -/
theorem exists_admits_everywhere_not_linearContinuation (hac : a < c) :
    ∃ (F : ℝ → ℕ → ℝ) (F' : ℕ → ℝ → ℝ),
      (∀ ε T, 0 ≤ F ε T) ∧ (∀ T ε, HasDerivAt (fun x => F x T) (F' T ε) ε) ∧
        (∀ ε, Admits F ε) ∧
          AveragedContinuation F F' a c ∧ ¬ LinearContinuation F F' a c :=
  ⟨lossSpikeEnergy ((a + c) / 2), lossSpikeEnergyDeriv ((a + c) / 2),
    fun ε T => lossSpikeEnergy_nonneg _ ε T, fun T ε => hasDerivAt_lossSpikeEnergy _ T ε,
    fun ε => admits_lossSpikeEnergy _ ε, averagedContinuation_lossSpikeEnergy _ hac.le,
    not_linearContinuation_lossSpikeEnergy ⟨by linarith, by linarith⟩⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
