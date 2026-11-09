import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowersAtEveryGapSet
import GaloisForLFunctions.SurfaceOfSpecZ.HyperbolicQuotientsJetCarriersAndCoupledDamping

/-!
# The Stepanov bound is a prime count

By the explicit formula the trace of the smoothed Frobenius graph of degree `d` splits as
(`smoothedPrime_add_smoothedArchPole_eq_orbitCorr`)

  `c_B(log d) = A(d) − P(d)`,

with `P(d) = Re Σ_n Λ(n) n^{−½} (k_d(log n) + k_d(−log n))`, `k_d = B(· − log d) ⋆ B̃`, the smoothed von
Mangoldt count in the window of `d` (`primeWindow`), and `A(d)` its archimedean-plus-pole prediction
(`archPoleWindow`). The lower side is therefore an upper bound on primes:

**Theorem** (`riemannHypothesis_iff_primeWindow_le_of_powGaps`). For every degree set `D` with gaps
`O(x^θ)`, `θ < 1`, RH holds iff `P(d) ≤ A(d) + K` for all `d ∈ D` and some constant `K`: at each degree
the smoothed prime count exceeds its prediction by at most a constant. At the primes
(`riemannHypothesis_iff_primeWindow_le_primes`) and at the `nᵏ`
(`riemannHypothesis_iff_primeWindow_le_kthPowers`).

The prediction and the count are both of size `√d`; only their difference is bounded. On a curve
this is Stepanov's bound `N_n ≤ qⁿ + 1 + C q^{n/2}` at the degrees of a gap set.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

/-- The smoothed von Mangoldt count in the window of the degree `d`. -/
def primeWindow (d : ℕ) : ℝ := -smoothedPrimeKernel cubicSpline d 1

/-- Its archimedean-plus-pole prediction. -/
def archPoleWindow (d : ℕ) : ℝ := smoothedArchPoleKernel cubicSpline d 1

/-- **The trace is prediction minus count.** -/
theorem orbitCorr_log_eq_archPoleWindow_sub_primeWindow (d : ℕ) :
    zetaScalingDatum.orbitCorr splineCycle (Real.log d) = archPoleWindow d - primeWindow d := by
  have h := smoothedPrime_add_smoothedArchPole_eq_orbitCorr
    (f := cubicSpline) ⟨contDiff_cubicSpline, hasCompactSupport_cubicSpline⟩ d 1
  rw [Nat.cast_one, Real.log_one, sub_zero] at h
  have hc : zetaScalingDatum.orbitCorr splineCycle (Real.log d) =
      zetaScalingDatum.orbitCorr (0, 0, ⟨cubicSpline, contDiff_cubicSpline,
        hasCompactSupport_cubicSpline⟩) (Real.log d) := rfl
  rw [hc, primeWindow, archPoleWindow, ← h]
  ring

/-- **The Stepanov bound at a gap set is a prime count.** -/
theorem riemannHypothesis_iff_primeWindow_le_of_powGaps {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ d ∈ D, primeWindow d ≤ archPoleWindow d + K := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun d _ => ?_⟩
    have h := (riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH) (Real.log d)
    rw [ScalingDatum.HasseWeilAt] at h
    have h1 := (abs_le.mp h).1
    rw [orbitCorr_log_eq_archPoleWindow_sub_primeWindow] at h1
    linarith
  · rintro ⟨K, hK⟩
    refine riemannHypothesis_iff_zetaZeroConfig_onLine.mpr
      (onLine_of_bddBelow_of_powGaps _ temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hθ1
        hD (K := 2 * K) fun d hd => ?_)
    have h := hK d hd
    rw [← orbitCorr_eq_re_lagStructure_spline]
    have := orbitCorr_log_eq_archPoleWindow_sub_primeWindow d
    linarith

/-- **At the primes.** -/
theorem riemannHypothesis_iff_primeWindow_le_primes :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime → primeWindow p ≤ archPoleWindow p + K :=
  riemannHypothesis_iff_primeWindow_le_of_powGaps (θ := 2 / 3) (by norm_num)
    (powGaps_primes (by norm_num) (by norm_num))

/-- **At the `k`-th powers.** -/
theorem riemannHypothesis_iff_primeWindow_le_kthPowers {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      primeWindow (n ^ k) ≤ archPoleWindow (n ^ k) + K := by
  rw [riemannHypothesis_iff_primeWindow_le_of_powGaps (one_sub_inv_lt_one hk) (powGaps_kthPowers hk)]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun n hn => hK _ ⟨n, hn, rfl⟩⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, fun d ⟨n, hn, hd⟩ => hd ▸ hK n hn⟩

end GaloisForLFunctions.SurfaceOfSpecZ
