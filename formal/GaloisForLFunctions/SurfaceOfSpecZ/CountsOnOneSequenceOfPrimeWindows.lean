import GaloisForLFunctions.SurfaceOfSpecZ.OnlyDeepOrdinatesNeedSeparation

/-!
# Counts on one sequence of prime windows

The count door needs only the primes of one sparse sequence of windows of fixed ratio, if the
off-line zeros of `ζ` have separated ordinates. Suppose the zeros of `ζ` off the critical line,
with their conjugates, have `δ`-separated ordinates. Then RH holds if and only if, for arbitrarily
large `T`, every effective class `Γ_1 + Γ_p`, `p` prime with `log p ∈ [T, T + 80/δ + 1]`, carries
an `ℕ`-count `K(m)` with Tate limit `K(m)/m² → δ_p(1, 1)`
(`riemannHypothesis_iff_effectiveCounts_prime_windows_of_offLine_separated`).

A count with that limit makes the defect `δ_p(1, 1) = 2c_B(0) + 2c_B(log p)` nonnegative, which is
the Stepanov bound `2 Re S(log p) ≥ −2c_B(0)` at `p`; the prime windows then decide
(`riemannHypothesis_of_prime_windows_of_offLine_separated`).
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open CountingHolography

/-- **RH is a count on one sequence of prime windows**, if the off-line ordinates are
`δ`-separated. -/
theorem riemannHypothesis_iff_effectiveCounts_prime_windows_of_offLine_separated {δ : ℝ}
    (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates zetaZeroConfig 0 δ) :
    RiemannHypothesis ↔ ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 →
      ∃ K : ℕ → ℕ, Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop
        (𝓝 (planeDefect p (1, 1))) := by
  constructor
  · intro hRH U
    refine ⟨U, le_rfl, fun p hp _ _ => ?_⟩
    have h := planeDefect_nonneg_of_RH hRH hp.pos 1 1
    exact ⟨fun m => ⌊(m : ℝ) ^ 2 * planeDefect p (1, 1)⌋₊, tendsto_floor_div_sq h⟩
  · intro h
    refine riemannHypothesis_of_prime_windows_of_offLine_separated hδ hsep
      (K := 2 * zetaScalingDatum.orbitCorr splineCycle 0) fun U => ?_
    obtain ⟨T, hTU, hT⟩ := h U
    refine ⟨T, hTU, fun p hp h1 h2 => ?_⟩
    obtain ⟨K, hK⟩ := hT p hp h1 h2
    have hnn := ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [planeDefect_one_one, orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_eq_re_lagStructure_spline] at hnn
    rw [orbitCorr_eq_re_lagStructure_spline]
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
