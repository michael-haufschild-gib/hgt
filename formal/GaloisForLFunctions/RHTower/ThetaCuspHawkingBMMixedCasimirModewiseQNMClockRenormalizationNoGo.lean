import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinMixedCasimirPoleFillLanding
import GaloisForLFunctions.RHTower.ThetaCuspHawkingReducedSecondOrderChiralJostReturnDeterminant

/-!
# HB modewise QNM clock-renormalization no-go

The actual mixed-Casimir correction at `(2,5)` is nonzero.  Use it as the literal scalar seed of
the reduced doubled-grade Einstein--Teukolsky source.  The source vanishes on one Xi fibre exactly
on the critical wall and vanishes globally exactly under RH.

The normalized derivative of every simple Birmingham--Mokhtari Jost zero is nonzero.  Therefore
the standard perturbative QNM solvability equation has a unique modewise frequency correction:

```text
delta_n(q) = -source(q) / JostDerivative(n).
```

Adding its frequency-jet term cancels the exact source at every Xi QNM.  Consequently the returned
Jost channel and Evans determinant vanish unconditionally on every fibre, even off wall where both
the raw source and its unique counterterm are nonzero.  Modewise QNM solvability is therefore
RH-blind.  The sharp survivor is exact: requiring every modewise frequency correction itself to
vanish is equivalent to RH.

This kills the HB producer chain

```text
literal corrected source -> higher-order QNM solvability / clock renormalization
  -> returned-Jost extinction -> RH.
```

A viable HB producer must independently forbid mode-dependent frequency renormalization and prove
the global standard-clock condition; perturbative solvability cannot supply it.

`[NEW] [HB] [QNM SOLVABILITY] [CLOCK RENORMALIZATION NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal mixed-Casimir-corrected scalar seed at the audited chamber point `(2,5)`. -/
def d4BMMixedCasimirCorrectedActualScalarSeed : ℂ :=
  d4BMMixedCasimirPoleFillMultiplier 2 5 *
    d4BMActualTwoFiveUnfoldedScalarSource

theorem d4BMMixedCasimirCorrectedActualScalarSeed_ne_zero :
    d4BMMixedCasimirCorrectedActualScalarSeed ≠ 0 := by
  rw [d4BMMixedCasimirCorrectedActualScalarSeed,
    d4BMMixedCasimirPoleFillMultiplier_two_five]
  exact mul_ne_zero (by norm_num) d4BM_actualTwoFiveUnfoldedScalarSource_ne_zero

/-- Exact doubled-grade reduced Einstein--Teukolsky source with the literal corrected seed. -/
def d4BMMixedCasimirReducedSecondOrderChiralSource (q : XiZeroCopy) : ℂ :=
  d4ThetaReducedSecondOrderChiralTeukolskyGradeSource
    d4BMMixedCasimirCorrectedActualScalarSeed 0 0 q
      (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q))

theorem d4BMMixedCasimirReducedSecondOrderChiralSource_ne_zero_iff
    (q : XiZeroCopy) :
    d4BMMixedCasimirReducedSecondOrderChiralSource q ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  exact d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
    d4BMMixedCasimirCorrectedActualScalarSeed_ne_zero 0 0 0 q

theorem d4BMMixedCasimirReducedSecondOrderChiralSource_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMMixedCasimirReducedSecondOrderChiralSource q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hoff
    exact (d4BMMixedCasimirReducedSecondOrderChiralSource_ne_zero_iff q).mpr hoff hzero
  · intro hline
    by_contra hsource
    exact (d4BMMixedCasimirReducedSecondOrderChiralSource_ne_zero_iff q).mp hsource hline

/-- Unique modewise QNM-frequency correction absorbing the exact source projection. -/
def d4BMMixedCasimirModewiseQNMClockCounterterm
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  -d4BMMixedCasimirReducedSecondOrderChiralSource q /
    teukolskyNormalizedJostOmegaDerivative n

theorem d4BMMixedCasimirModewiseQNMClockCounterterm_cancels
    (n : ℕ) (q : XiZeroCopy) :
    d4BMMixedCasimirReducedSecondOrderChiralSource q +
        d4BMMixedCasimirModewiseQNMClockCounterterm n q *
          teukolskyNormalizedJostOmegaDerivative n = 0 := by
  rw [d4BMMixedCasimirModewiseQNMClockCounterterm]
  field_simp [teukolskyNormalizedJostOmegaDerivative_ne_zero]
  ring

theorem d4BMMixedCasimirModewiseQNMClockCounterterm_unique
    (n : ℕ) (q : XiZeroCopy) (delta : ℂ) :
    d4BMMixedCasimirReducedSecondOrderChiralSource q +
          delta * teukolskyNormalizedJostOmegaDerivative n = 0 ↔
      delta = d4BMMixedCasimirModewiseQNMClockCounterterm n q := by
  constructor
  · intro h
    rw [d4BMMixedCasimirModewiseQNMClockCounterterm]
    apply (eq_div_iff (teukolskyNormalizedJostOmegaDerivative_ne_zero n)).2
    linear_combination h
  · rintro rfl
    exact d4BMMixedCasimirModewiseQNMClockCounterterm_cancels n q

theorem d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMMixedCasimirModewiseQNMClockCounterterm n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMMixedCasimirModewiseQNMClockCounterterm,
    div_eq_zero_iff, neg_eq_zero,
    d4BMMixedCasimirReducedSecondOrderChiralSource_eq_zero_iff]
  exact or_iff_left (teukolskyNormalizedJostOmegaDerivative_ne_zero n)

theorem forall_d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      d4BMMixedCasimirModewiseQNMClockCounterterm n q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_zero_iff_rh
    d4BMMixedCasimirCorrectedActualScalarSeed_ne_zero n 0 0]
  constructor
  · intro h q
    exact (d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff n q).mp (h q)
      |> (d4BMMixedCasimirReducedSecondOrderChiralSource_eq_zero_iff q).mpr
  · intro h q
    apply (d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff n q).mpr
    exact (d4BMMixedCasimirReducedSecondOrderChiralSource_eq_zero_iff q).mp (h q)

/-- Spectral cross source after the modewise QNM-frequency correction. -/
def d4BMMixedCasimirModewiseClockRenormalizedCrossSource
    (n : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4ThetaReducedSecondOrderChiralTeukolskyCrossSource
      d4BMMixedCasimirCorrectedActualScalarSeed 0 0 q z +
    d4BMMixedCasimirModewiseQNMClockCounterterm n q *
      teukolskyNormalizedJostOmegaDerivative n

/-- The unique clock correction cancels the exact source at its own Xi QNM fibre. -/
theorem d4BMMixedCasimirModewiseClockRenormalizedCrossSource_xi_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMMixedCasimirModewiseClockRenormalizedCrossSource n q
        (xiSpectralPoint q) = 0 := by
  simpa [d4BMMixedCasimirModewiseClockRenormalizedCrossSource,
    d4ThetaReducedSecondOrderChiralTeukolskyCrossSource,
    d4BMMixedCasimirReducedSecondOrderChiralSource] using
      d4BMMixedCasimirModewiseQNMClockCounterterm_cancels n q

/-- Returned Jost channel with exact modewise QNM-frequency renormalization. -/
def d4BMMixedCasimirModewiseClockRenormalizedReturnedJost
    (n : ℕ) (q : XiZeroCopy) (horizonPhase : ℂ → ℂ)
    (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega horizonPhase
    (d4BMMixedCasimirModewiseClockRenormalizedCrossSource n q)

theorem d4BMMixedCasimirModewiseClockRenormalizedReturnedJost_qnmPlus_eq_zero
    (n : ℕ) (q : XiZeroCopy) (horizonPhase : ℂ → ℂ) :
    d4BMMixedCasimirModewiseClockRenormalizedReturnedJost n q horizonPhase
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (xiSpectralPoint q) = 0 := by
  rw [d4BMMixedCasimirModewiseClockRenormalizedReturnedJost,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus]
  exact d4BMMixedCasimirModewiseClockRenormalizedCrossSource_xi_eq_zero n q

/-- Modewise frequency renormalization makes the returned Evans determinant vanish on every Xi
fibre, independently of RH and independently of the multiplicative horizon phase. -/
theorem d4BMMixedCasimirModewiseClockRenormalizedReturnDeterminant_qnmPlus_eq_zero
    (n : ℕ) (q : XiZeroCopy) (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4BMMixedCasimirModewiseClockRenormalizedReturnedJost n q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) = 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus,
    d4BMMixedCasimirModewiseClockRenormalizedReturnedJost_qnmPlus_eq_zero,
    zero_mul]

/-- Off wall, determinant extinction is sourceful: both literal source and its unique frequency
counterterm are nonzero. -/
theorem d4BMMixedCasimirModewiseClockRenormalized_offLine_brightCancellation
    (n : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMMixedCasimirReducedSecondOrderChiralSource q ≠ 0 ∧
      d4BMMixedCasimirModewiseQNMClockCounterterm n q ≠ 0 ∧
      d4BMMixedCasimirModewiseClockRenormalizedCrossSource n q
        (xiSpectralPoint q) = 0 := by
  refine ⟨
    (d4BMMixedCasimirReducedSecondOrderChiralSource_ne_zero_iff q).mpr hoff,
    ?_,
    d4BMMixedCasimirModewiseClockRenormalizedCrossSource_xi_eq_zero n q⟩
  exact (d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff n q).not.mpr hoff

/-- Closed route certificate: higher-order modewise QNM solvability gives universal returned-Jost
extinction, while imposing zero frequency correction is pointwise the critical wall and globally
RH. -/
def D4BMMixedCasimirModewiseQNMClockRenormalizationNoGo : Prop :=
  (∀ (n : ℕ) (q : XiZeroCopy) (delta : ℂ),
    d4BMMixedCasimirReducedSecondOrderChiralSource q +
          delta * teukolskyNormalizedJostOmegaDerivative n = 0 ↔
      delta = d4BMMixedCasimirModewiseQNMClockCounterterm n q) ∧
  (∀ (n : ℕ) (q : XiZeroCopy),
    d4BMMixedCasimirModewiseQNMClockCounterterm n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ n : ℕ,
    (∀ q : XiZeroCopy,
      d4BMMixedCasimirModewiseQNMClockCounterterm n q = 0) ↔
        RiemannHypothesis) ∧
  (∀ (n : ℕ) (q : XiZeroCopy) (horizonPhase : ℂ → ℂ),
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4BMMixedCasimirModewiseClockRenormalizedReturnedJost n q horizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) = 0) ∧
  (∀ (n : ℕ) (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
    d4BMMixedCasimirReducedSecondOrderChiralSource q ≠ 0 ∧
      d4BMMixedCasimirModewiseQNMClockCounterterm n q ≠ 0 ∧
      d4BMMixedCasimirModewiseClockRenormalizedCrossSource n q
        (xiSpectralPoint q) = 0)

/-- Premise-free Lean certificate killing the modewise QNM clock-renormalization producer class. -/
theorem d4BMMixedCasimirModewiseQNMClockRenormalization_noGo :
    D4BMMixedCasimirModewiseQNMClockRenormalizationNoGo := by
  exact ⟨
    d4BMMixedCasimirModewiseQNMClockCounterterm_unique,
    d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff,
    forall_d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff_rh,
    d4BMMixedCasimirModewiseClockRenormalizedReturnDeterminant_qnmPlus_eq_zero,
    d4BMMixedCasimirModewiseClockRenormalized_offLine_brightCancellation⟩

end

end RHTower
