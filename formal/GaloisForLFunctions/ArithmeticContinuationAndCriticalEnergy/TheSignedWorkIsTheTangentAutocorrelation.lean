import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingContinuationCriterion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheScalarDampingWorkIsAlreadyPaid
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensationNeedsItsCrossTerms

/-!
# The signed work is the autocorrelation of the tangent in the damping

The complete signed work pairs the centred source with its own damping tangent.  The source is the
damping primitive of that tangent, so the work is a *self*-pairing of the tangent family across
dampings:

`W_T(ε) = ⟪A_δ, E_ε⟫_T + ∫_δ^ε ⟪E_η, E_ε⟫_T dη`  for every `0 < δ ≤ ε`,

and letting `δ ↓ 0`, where the source collapses to the constant one, the first term becomes the
scalar moment that is already paid.  So the open covariance half of the continuation demand is the
**damping autocorrelation** of the centred damped Chebyshev function:

`K_T(η, ε) = Σ_{n ≤ T} E_η(n) E_ε(n) / (n(n+1))`,

a Gram kernel of one family of vectors, whose diagonal `K_T(ε, ε) = ‖E_ε‖_T²` is nonnegative.
Hence the obstruction to backward continuation is entirely *off-diagonal anti-correlation* between
the tangents at different dampings, and two criteria follow with no estimate on any norm:

* if the autocorrelation is nonnegative on each `(0, ε]`, the continuation budget is the paid
  scalar constant, and RH follows (`riemannHypothesis_of_nonneg_tangentCorrelation`);
* if the total anti-correlation `∫_δ^ε [K_T(η, ε)]⁻ dη` is merely bounded, uniformly in the
  horizon and in the inner endpoint, the same conclusion holds
  (`riemannHypothesis_of_bounded_anticorrelationTotal`).

This replaces the quantitative demand (a horizon-free budget dominating the loss) by a *sign* on a
two-damping arithmetic correlation.  Cauchy–Schwarz recovers the tangent-norm route from the
diagonal, so nothing is lost: `|K_T(η, ε)| ≤ ‖E_η‖_T ‖E_ε‖_T` is the only inequality the norm
route ever used.
-/

open Set Filter Finset Topology MeasureTheory RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The damping autocorrelation of the tangent -/

/-- **The damping autocorrelation of the centred damped Chebyshev function**: the pronic pairing of
the tangents at two dampings, read to horizon `T`. -/
def tangentCorrelation (T : ℕ) (η ε : ℝ) : ℝ :=
  pronicPairing T (dampedChebyshevError η) (dampedChebyshevError ε)

/-- On the diagonal the autocorrelation is the tangent energy: the kernel is a Gram kernel, so all
negativity is off-diagonal. -/
theorem tangentCorrelation_self (T : ℕ) (ε : ℝ) :
    tangentCorrelation T ε ε = pronicNorm T (dampedChebyshevError ε) ^ 2 := by
  rw [tangentCorrelation, pronicPairing, pronicNorm_sq]
  exact sum_congr rfl fun n _ => by rw [← sq]

theorem tangentCorrelation_symm (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε = tangentCorrelation T ε η := by
  rw [tangentCorrelation, tangentCorrelation, pronicPairing, pronicPairing]
  exact sum_congr rfl fun n _ => by ring

/-- Cauchy–Schwarz for the autocorrelation: the only inequality the tangent-norm route uses. -/
theorem tangentCorrelation_le_mul_pronicNorm (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε ≤
      pronicNorm T (dampedChebyshevError η) * pronicNorm T (dampedChebyshevError ε) :=
  sum_mul_div_le_pronicNorm T (dampedChebyshevError η) (dampedChebyshevError ε)

theorem continuousOn_tangentCorrelation (T : ℕ) (ε : ℝ) :
    ContinuousOn (fun η => tangentCorrelation T η ε) (Ioi 0) := by
  unfold tangentCorrelation pronicPairing
  exact continuousOn_finsetSum _ fun n _ =>
    (((continuousOn_dampedChebyshevError n).mul continuousOn_const).div_const _)

theorem intervalIntegrable_tangentCorrelation {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (T : ℕ) :
    IntervalIntegrable (fun η => tangentCorrelation T η ε) volume δ ε := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hδε]
  exact (continuousOn_tangentCorrelation T ε).mono fun x hx => mem_Ioi.mpr (lt_of_lt_of_le hδ hx.1)

/-! ## §2. The work as a pairing with the past plus the autocorrelation integral -/

/-- **The signed work splits into a pairing with the source at an inner damping and the
autocorrelation integral between the two dampings.**  The exact integral form of the source
(`A_ε − A_δ = ∫_δ^ε E_η`) is what makes the work a self-pairing of the tangent family. -/
theorem signedDampingWork_eq_pairing_add_integral {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (T : ℕ) :
    signedDampingWork ε T =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix δ) (dampedChebyshevError ε) +
        ∫ η in δ..ε, tangentCorrelation T η ε := by
  have hint : ∀ n ∈ Finset.Icc 1 T, IntervalIntegrable
      (fun η => dampedChebyshevError η n * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) volume δ ε := by
    intro n _
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hδε]
    exact (((continuousOn_dampedChebyshevError n).mul continuousOn_const).div_const _).mono
      fun x hx => mem_Ioi.mpr (lt_of_lt_of_le hδ hx.1)
  have hswap : (∫ η in δ..ε, tangentCorrelation T η ε) =
      ∑ n ∈ Icc 1 T, (∫ η in δ..ε, dampedChebyshevError η n) * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    unfold tangentCorrelation pronicPairing
    rw [intervalIntegral.integral_finsetSum hint]
    refine sum_congr rfl fun n _ => ?_
    have hfun : (fun η => dampedChebyshevError η n * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
        fun η => dampedChebyshevError η n *
          (dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))) :=
      funext fun η => by ring
    rw [hfun, intervalIntegral.integral_mul_const]
    ring
  rw [signedDampingWork, hswap, pronicPairing, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← pmPowerDampedCenteredDivisorPrefix_sub_eq_integral hδ hδε n]
  ring

/-- **The scalar moment is the limit of the inner pairing.**  At zero damping the source collapses
to the constant one, so the inner pairing tends to the first pronic moment of the tangent — the
quantity already paid on every positive damping half-line. -/
theorem tendsto_pronicPairing_prefix_nhdsGT_zero (T : ℕ) (ε : ℝ) :
    Tendsto (fun δ => pronicPairing T (pmPowerDampedCenteredDivisorPrefix δ)
        (dampedChebyshevError ε)) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Icc 1 T, dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1)))) := by
  unfold pronicPairing
  refine tendsto_finsetSum _ fun n hn => ?_
  have h := (tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1).mul
    (tendsto_const_nhds (x := dampedChebyshevError ε n) (f := 𝓝[>] (0 : ℝ)))
  simpa using h.div_const ((n : ℝ) * ((n : ℝ) + 1))

/-! ## §3. A sign on the autocorrelation is a continuation budget -/

/-- **A nonnegative autocorrelation leaves only the paid scalar moment.**  No norm is estimated:
the work is bounded below by the first pronic moment of the tangent. -/
theorem scalarMoment_le_signedDampingWork_of_nonneg_tangentCorrelation {ε : ℝ} (hε : 0 < ε)
    (T : ℕ) (hK : ∀ η ∈ Ioc 0 ε, 0 ≤ tangentCorrelation T η ε) :
    (∑ n ∈ Icc 1 T, dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      signedDampingWork ε T := by
  refine le_of_tendsto (tendsto_pronicPairing_prefix_nhdsGT_zero T ε) ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  have hpos : 0 ≤ ∫ η in δ..ε, tangentCorrelation T η ε :=
    intervalIntegral.integral_nonneg hδ.2.le fun η hη =>
      hK η ⟨lt_of_lt_of_le hδ.1 hη.1, hη.2⟩
  rw [signedDampingWork_eq_pairing_add_integral hδ.1 hδ.2.le T]
  linarith

/-- **The sign of the autocorrelation is a continuation budget.**  If the tangents at smaller
dampings are not anti-correlated with the tangent at `ε`, the continuation budget is the *constant*
coming from the already paid scalar moment, on every interval `[a, c]` with `a > 0`. -/
theorem dampingContinuation_of_nonneg_tangentCorrelation {a c : ℝ} (ha : 0 < a)
    (hK : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ c → 0 ≤ tangentCorrelation T η ε) :
    DampingContinuation a c := by
  obtain ⟨K, hK0, hbound⟩ := exists_uniform_scalar_damping_work_bound ha
  refine ⟨fun ε => 2 * K * ε, fun _ => 2 * K, fun ε _ => ?_, ?_⟩
  · simpa using (hasDerivAt_id ε).const_mul (2 * K)
  · intro T ε hε
    have hε0 : 0 < ε := lt_of_lt_of_le ha hε.1
    have hge := scalarMoment_le_signedDampingWork_of_nonneg_tangentCorrelation hε0 T
      fun η hη => hK T η ε hη.1 hη.2 hε.2
    have habs := abs_le.mp (hbound ε hε.1 T)
    have hE := dampedMobiusEnergy_nonneg ε T
    rw [dampedMobiusEnergyDeriv]
    nlinarith [habs.1, habs.2]

/-- **The autocorrelation sign criterion for the Riemann hypothesis.**  A sign, not an estimate:
nonnegative damping autocorrelation of the centred damped Chebyshev function below half damping
gives RH. -/
theorem riemannHypothesis_of_nonneg_tangentCorrelation
    (hK : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 → 0 ≤ tangentCorrelation T η ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation fun _ ha _ =>
    dampingContinuation_of_nonneg_tangentCorrelation ha hK

/-! ## §4. Bounded anti-correlation is enough -/

/-- **A bounded total of anti-correlation also pays the budget.**  The sign may fail, provided the
negative part of the autocorrelation has one bounded damping integral for every horizon and every
inner endpoint. -/
theorem dampingContinuation_of_bounded_anticorrelationTotal {a c Q : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q)
    (hK : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ c → ∀ δ ∈ Ioo 0 ε,
      (∫ η in δ..ε, max 0 (-tangentCorrelation T η ε)) ≤ Q) :
    DampingContinuation a c := by
  obtain ⟨K, hK0, hbound⟩ := exists_uniform_scalar_damping_work_bound ha
  refine ⟨fun ε => (2 * K + 2 * Q) * ε, fun _ => 2 * K + 2 * Q, fun ε _ => ?_, ?_⟩
  · simpa using (hasDerivAt_id ε).const_mul (2 * K + 2 * Q)
  · intro T ε hε
    have hε0 : 0 < ε := lt_of_lt_of_le ha hε.1
    have hge : (∑ n ∈ Icc 1 T, dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))) - Q ≤
        signedDampingWork ε T := by
      refine le_of_tendsto (tendsto_pronicPairing_prefix_nhdsGT_zero T ε |>.sub_const Q) ?_
      filter_upwards [Ioo_mem_nhdsGT hε0] with δ hδ
      have hneg : IntervalIntegrable
          (fun η => max 0 (-tangentCorrelation T η ε)) volume δ ε := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ.2.le]
        exact continuousOn_const.sup
          (((continuousOn_tangentCorrelation T ε).mono fun x hx =>
            mem_Ioi.mpr (lt_of_lt_of_le hδ.1 hx.1)).neg)
      have hmono : (∫ η in δ..ε, -max 0 (-tangentCorrelation T η ε)) ≤
          ∫ η in δ..ε, tangentCorrelation T η ε :=
        intervalIntegral.integral_mono_on hδ.2.le hneg.neg
          (intervalIntegrable_tangentCorrelation hδ.1 hδ.2.le T)
          fun η _ => neg_le_of_neg_le (le_max_right _ _)
      rw [intervalIntegral.integral_neg] at hmono
      have hQle := hK T ε hε0 hε.2 δ hδ
      rw [signedDampingWork_eq_pairing_add_integral hδ.1 hδ.2.le T]
      linarith
    have habs := abs_le.mp (hbound ε hε.1 T)
    have hE := dampedMobiusEnergy_nonneg ε T
    rw [dampedMobiusEnergyDeriv]
    nlinarith [habs.1, habs.2]

/-- **The bounded-anti-correlation criterion for the Riemann hypothesis.** -/
theorem riemannHypothesis_of_bounded_anticorrelationTotal {Q : ℝ} (hQ : 0 ≤ Q)
    (hK : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → ∀ δ ∈ Ioo 0 ε,
      (∫ η in δ..ε, max 0 (-tangentCorrelation T η ε)) ≤ Q) :
    RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation fun _ ha _ =>
    dampingContinuation_of_bounded_anticorrelationTotal ha hQ hK

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
