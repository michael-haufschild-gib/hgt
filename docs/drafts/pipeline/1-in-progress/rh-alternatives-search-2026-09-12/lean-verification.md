# Lean declaration verification

Both commands ran from `/Users/michael/Documents/code/hgt/formal` and completed with exit code 0. Twelve declarations checked; only `propext`, `Classical.choice`, `Quot.sound` reported. This checks installed compiled imports, not a rebuild of the source tree.

The first combinatorics attempt used unqualified `FP_partition_regular` and failed. Source namespace inspection corrected it to `Hindman.FP_partition_regular`; the corrected run below passed.

## Audit

Command: `lake env lean /tmp/hgt-rh-alternatives.Xyeskm/Audit.lean`

```lean
import GaloisForLFunctions.RHTower.CoherentTower
import GaloisForLFunctions.RHTower.RouteEParityColumnLoadCircularityNoGo
import GaloisForLFunctions.RHTower.SpeiserCriticalLineSignLaw
import GaloisForLFunctions.RHTower.SpeiserCriticalPacketGauge
import GaloisForLFunctions.RHTower.BoundedClockZeroTransfer
import GaloisForLFunctions.HTGeometry.AlmostPeriodicHull
import GaloisForLFunctions.HTGeometry.UnimodularRounding

#check @RHTower.nonvanishing_of_exists_roots_all_two_powers_preconnected
#check @RHTower.FiniteRowStochasticKernel.two_mul_signedSum_eq_signedColumnDefect
#check @RHTower.routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis
#check @RHTower.re_logDeriv_riemannZeta_criticalLine_neg
#check @RHTower.SpeiserGauge.logDeriv_expGauge
#check @RHTower.boundedVerticalClockApproximationCertificate_iff_riemannHypothesis
#check @GaloisForLFunctions.bohrAP_exists_large_return
#check @GaloisForLFunctions.HTGeometry.exists_unimodular_rounding

#print axioms RHTower.nonvanishing_of_exists_roots_all_two_powers_preconnected
#print axioms RHTower.FiniteRowStochasticKernel.two_mul_signedSum_eq_signedColumnDefect
#print axioms RHTower.routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis
#print axioms RHTower.re_logDeriv_riemannZeta_criticalLine_neg
#print axioms RHTower.SpeiserGauge.logDeriv_expGauge
#print axioms RHTower.boundedVerticalClockApproximationCertificate_iff_riemannHypothesis
#print axioms GaloisForLFunctions.bohrAP_exists_large_return
#print axioms GaloisForLFunctions.HTGeometry.exists_unimodular_rounding
```

```text
@RHTower.nonvanishing_of_exists_roots_all_two_powers_preconnected : ∀ {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ},
  IsOpen Ω →
    IsPreconnected Ω →
      z₀ ∈ Ω →
        AnalyticOnNhd ℂ f Ω →
          f z₀ ≠ 0 → (∀ (k : ℕ), ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ 2 ^ k = f s) → ∀ s ∈ Ω, f s ≠ 0
@RHTower.FiniteRowStochasticKernel.two_mul_signedSum_eq_signedColumnDefect : ∀ {ι : Type u_1} [inst : Fintype ι]
  (P : RHTower.FiniteRowStochasticKernel ι ι) (sign : ι → ℝ),
  (∀ (i j : ι), P.weight i j ≠ 0 → sign i + sign j = 0) → 2 * ∑ i, sign i = ∑ j, sign j * (1 - P.columnLoad j)
RHTower.routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis : RHTower.RouteEParityColumnDefectAllStrictHalfPowerBound →
  RiemannHypothesis
@RHTower.re_logDeriv_riemannZeta_criticalLine_neg : ∀ {τ : ℝ},
  20 ≤ τ → riemannZeta (1 / 2 + ↑τ * Complex.I) ≠ 0 → (logDeriv riemannZeta (1 / 2 + ↑τ * Complex.I)).re < 0
@RHTower.SpeiserGauge.logDeriv_expGauge : ∀ {Q F : ℂ → ℂ},
  Differentiable ℂ Q →
    Differentiable ℂ F → ∀ {z : ℂ}, F z ≠ 0 → logDeriv (fun w => Complex.exp (Q w) * F w) z = deriv Q z + logDeriv F z
RHTower.boundedVerticalClockApproximationCertificate_iff_riemannHypothesis : RHTower.BoundedVerticalClockApproximationCertificate ↔
  RiemannHypothesis
@GaloisForLFunctions.bohrAP_exists_large_return : ∀ {f : BoundedContinuousFunction ℝ ℂ},
  GaloisForLFunctions.IsBohrAP f →
    ∀ {ε : ℝ}, 0 < ε → ∀ (N : ℝ), ∃ t, N ≤ t ∧ dist (GaloisForLFunctions.bcfTranslate t f) f < ε
@GaloisForLFunctions.HTGeometry.exists_unimodular_rounding : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ} (x : Fin n → E) (a : Fin n → ℂ),
  (∀ (j : Fin n), ‖a j‖ ≤ 1) →
    ∀ {C : ℝ},
      (∀ (j : Fin n), ‖x j‖ ≤ C) →
        0 ≤ C → ∃ b, (∀ (j : Fin n), ‖b j‖ = 1) ∧ ‖∑ j, b j • x j - ∑ j, a j • x j‖ ≤ ↑(Module.finrank ℂ E) * C
'RHTower.nonvanishing_of_exists_roots_all_two_powers_preconnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RHTower.FiniteRowStochasticKernel.two_mul_signedSum_eq_signedColumnDefect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RHTower.routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RHTower.re_logDeriv_riemannZeta_criticalLine_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHTower.SpeiserGauge.logDeriv_expGauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHTower.boundedVerticalClockApproximationCertificate_iff_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaloisForLFunctions.bohrAP_exists_large_return' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisForLFunctions.HTGeometry.exists_unimodular_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## CombinatoricsAudit

Command: `lake env lean /tmp/hgt-rh-alternatives.Xyeskm/CombinatoricsAudit.lean`

```lean
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Hindman
import GaloisForLFunctions.RHTower.RecurrenceZeroDensity
#check @char_dvd_card_solutions
#check @MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
#check @Hindman.FP_partition_regular
#check @RHTower.recurrence_excludes_zero
#print axioms char_dvd_card_solutions
#print axioms MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
#print axioms Hindman.FP_partition_regular
#print axioms RHTower.recurrence_excludes_zero
```

```text
@char_dvd_card_solutions : ∀ {K : Type u_1} {σ : Type u_2} [inst : Fintype K] [inst_1 : Field K] [inst_2 : Fintype σ]
  [inst_3 : DecidableEq σ] [inst_4 : DecidableEq K] (p : ℕ) [CharP K p] {f : MvPolynomial σ K},
  f.totalDegree < Fintype.card σ → p ∣ Fintype.card { x // (MvPolynomial.eval x) f = 0 }
@MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero : ∀ {R : Type u_1} [inst : CommRing R] {σ : Type u_2}
  [Finite σ] [IsDomain R] (f : MvPolynomial σ R) (t : σ →₀ ℕ),
  MvPolynomial.coeff t f ≠ 0 →
    f.totalDegree = Finsupp.degree t →
      ∀ (S : σ → Finset R), (∀ (i : σ), t i < (S i).card) → ∃ s, (∀ (i : σ), s i ∈ S i) ∧ (MvPolynomial.eval s) f ≠ 0
@Hindman.FP_partition_regular : ∀ {M : Type u_1} [inst : Semigroup M] (a : Stream' M) (s : Set (Set M)),
  s.Finite → Hindman.FP a ⊆ ⋃₀ s → ∃ c ∈ s, ∃ b, Hindman.FP b ⊆ c
@RHTower.recurrence_excludes_zero : ∀ {δ ε T N : ℝ}, 0 < δ → 0 < T → δ * T ≤ N → N ≤ ε * T → ε < δ → False
'char_dvd_card_solutions' depends on axioms: [propext, Classical.choice, Quot.sound]
'MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Hindman.FP_partition_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHTower.recurrence_excludes_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```
