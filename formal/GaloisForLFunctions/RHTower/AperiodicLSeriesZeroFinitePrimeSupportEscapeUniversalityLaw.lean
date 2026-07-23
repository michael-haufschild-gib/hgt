import GaloisForLFunctions.RHTower.FinitePrimeSectorDichotomy

/-!
# Aperiodic L-series zeros force finite-prime support escape

Finite-prime multiplicative L-series zeros ride complete vertical arithmetic progressions.
Consequently, any aperiodic zero in the open right half-plane certifies that the coefficient
support escapes every finite prime sector.
-/

namespace RHTower

open Complex

noncomputable section

/-- **Aperiodic L-series zero finite-prime support-escape universality law.**

If a multiplicative L-series is norm-summable throughout the open right half-plane and has an
aperiodic zero there, then for every finite prime set `P` some nonzero coefficient index is not
`P`-factored. -/
theorem aperiodicLSeriesZero_forces_escape_every_finitePrimeSector
    {a : ArithmeticFunction ℂ}
    (hmul : a.IsMultiplicative)
    (hsum : ∀ s : ℂ, 0 < s.re →
      Summable (fun n => ‖LSeries.term (fun n => a n) s n‖))
    {s : ℂ} (hs : 0 < s.re)
    (haper : AperiodicZeroAt (LSeries fun n => a n) s) :
    ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      ∃ n : ℕ, a n ≠ 0 ∧ n ∉ Nat.factoredNumbers P := by
  intro P hP
  by_contra hescape
  have hsupp : ∀ n, a n ≠ 0 → n ∈ Nat.factoredNumbers P := by
    intro n hn
    by_contra hnP
    exact hescape ⟨n, hn, hnP⟩
  exact haper.2
    (finitePrime_zero_periodic hmul hP hsupp hsum hs haper.1)

end

end RHTower
