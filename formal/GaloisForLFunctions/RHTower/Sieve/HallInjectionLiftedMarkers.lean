import GaloisForLFunctions.RHTower.Sieve.MarkerGoodSupply
import GaloisForLFunctions.RHTower.Sieve.MarkerCellFromGoodOuter
import GaloisForLFunctions.RHTower.Sieve.MarkerCountUpper
import GaloisForLFunctions.RHTower.Sieve.WindowMatching

/-!
# The Hall injection with the markers restricted to good starts

`Sieve/WindowMatching.exists_hall_injection_primes_of_cells` needs a lower bound on the cell size at
**every** marker.  The corpus's own supply estimate keeps only the markers whose reciprocal start is
outside an exceptional set, and pays the *largest* reciprocal fibre for each discarded start — the
factor `log X`.  Here the discarded markers are counted by the device of `Sieve/MarkerLossDevice`
instead, so an exceptional start-set of size `#S` costs `√(#S·(#M + 2Pi))` markers and half the
markers survive as soon as `#S·(#M + 2Pi) ≤ (#M)²/4`.
-/

namespace RHTower.Sieve

open Finset

/-- **The Hall injection with the markers restricted to good starts.** -/
theorem exists_hall_injection_lifted_markers {X H M₀ Q z Y K : ℕ} {S : Finset ℕ} {Pi c : ℝ}
    (hM : 3 ≤ M₀) (hXH : X + H ≤ M₀ * M₀) (C : ℕ → Finset ℕ)
    (hsep : ∀ p ∈ bigPrimeSet M₀ (Q * M₀), ∀ q ∈ bigPrimeSet M₀ (Q * M₀), p < q →
      X / q = X / p → q ≤ p + K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ (Q * M₀)).filter
          (fun p => p + d ∈ bigPrimeSet M₀ (Q * M₀))).card : ℕ) : ℝ) ≤ Pi)
    (hthr : ((S.card : ℕ) : ℝ) * ((((bigPrimeSet M₀ (Q * M₀)).card : ℕ) : ℝ) + 2 * Pi)
      ≤ ((((bigPrimeSet M₀ (Q * M₀)).card : ℕ) : ℝ)) ^ (2 : ℕ) / 4)
    (hCsub : ∀ p, C p ⊆ windowCell X H p)
    (hc : ∀ p ∈ (bigPrimeSet M₀ (Q * M₀)).filter (fun p => X / p ∉ S),
      c ≤ (((C p).card : ℕ) : ℝ))
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ ((((bigPrimeSet M₀ (Q * M₀)).card : ℕ) : ℝ)) / 2 * c) (hc0 : 0 ≤ c) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ w ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f w ∈ RHTower.markerBlockTargets
            ((bigPrimeSet M₀ (Q * M₀)).filter (fun p => X / p ∉ S)) C)
      ∧ ∀ w ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f w : ℤ) - (w : ℤ)| ≤ (H : ℤ) := by
  classical
  set M : Finset ℕ := bigPrimeSet M₀ (Q * M₀) with hMdef
  set P : Finset ℕ := M.filter (fun p => X / p ∉ S) with hPdef
  have hsupply : ((M.card : ℕ) : ℝ) / 2 ≤ ((P.card : ℕ) : ℝ) :=
    half_card_le_card_markers_start_notMem hsep hpair hthr
  have hPM : P ⊆ M := Finset.filter_subset _ _
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => prime_of_mem_bigPrimeSet (hPM hp)
  have hppos : ∀ p ∈ P, 0 < p := fun p hp => (hprime p hp).pos
  have hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a := by
    intro p hp a ha
    exact pos_of_mem_windowCell (hppos p hp) (hCsub p ha)
  have hw : ∀ p ∈ P, ∀ a ∈ C p, X < a * p ∧ a * p ≤ X + H := by
    intro p hp a ha
    exact (mem_windowCell_iff (hppos p hp)).1 (hCsub p ha)
  have hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r := by
    intro p hp a ha r hr
    have hprod := (hw p hp a ha).2
    have hMp : M₀ < p := lt_of_mem_bigPrimeSet (hPM hp)
    have hMr : M₀ < r := lt_of_mem_bigPrimeSet (hPM hr)
    have haM : a ≤ M₀ := by
      by_contra hcon
      have h1 : M₀ + 1 ≤ a := by omega
      have h2 : M₀ + 1 ≤ p := by omega
      have h3 : (M₀ + 1) * (M₀ + 1) ≤ a * p := Nat.mul_le_mul h1 h2
      have h4 : a * p ≤ M₀ * M₀ := le_trans hprod hXH
      nlinarith
    omega
  have hnum' : 2 * (H : ℝ) / Real.log Y
      + ((Y * Y : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ ((P.card : ℕ) : ℝ) * c :=
    le_trans hnum (mul_le_mul_of_nonneg_right hsupply hc0)
  exact exists_hall_injection_primes_of_cells P C hprime hposC hsmall hc hw hY hYz hz hlog hnum'

end RHTower.Sieve
