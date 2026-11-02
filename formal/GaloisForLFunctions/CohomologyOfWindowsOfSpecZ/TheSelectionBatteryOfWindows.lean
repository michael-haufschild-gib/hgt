import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.ArithmeticCountingPositivity.NearMaximalGapsDoNotForceWeilPositivity

/-!
# Selection on windows

Which axioms of a window theory select `ζ`? Every structural law of the window datum holds for every
weight on the prime powers; the window of length `A` reads only the Euler factors at `p ≤ e^A`
(`weilFullFunctional_congr_window`).

* **Windows below `log p` are blind to the Euler factor at `p`**
  (`weilFullFunctional_primeFlip_eq`): flipping the sign of `Λ` on the powers of a prime
  `p > e^A` does not change the Weil functional of any window test of length `A`.
* **No window of bounded length selects `ζ`** (`exists_flip_twin_of_window`): for every `A` there is
  a weight with `|λ| = Λ` (the same jump counts, the same Markov form in absolute value), the same
  Weil functional as `ζ` on every window of length `A`, and **not** Weil positive. A property of
  windows of bounded length that `ζ` has, a datum violating positivity has too; selection needs
  windows of every length, i.e. a law in `A`.

With the calibration over `𝔽_q` (the golden fake has integral counts, Euler product and functional
equation and no window cohomology) and the Epstein fakes of LST (positive definite counts with
real zeros in `(½, 1)`), this places selection: neither local counts nor soft structure decide;
a window theory selects only through its `h¹` at every length.
-/

noncomputable section

open Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open ArithmeticCountingPositivity RenormalizedArithmeticPotentialTheory

/-- Below `p` the flip of `p` does not change `Λ`. -/
theorem primeFlipWeight_eq_of_lt {p n : ℕ} (hn : n < p) :
    primeFlipWeight p n = ArithmeticFunction.vonMangoldt n := by
  rw [primeFlipWeight, finiteFlip, Finset.prod_singleton, Nat.factorization_eq_zero_of_lt hn,
    pow_zero, one_mul]

/-- **Windows below `log p` do not see the Euler factor at `p`.** -/
theorem weilFullFunctional_primeFlip_eq {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) {p : ℕ}
    (hp : windowLevel A < p) :
    RHTower.weilFullFunctional (primeFlipWeight p)
        (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) =
      RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) :=
  weilFullFunctional_congr_window hH fun _ _ hn => primeFlipWeight_eq_of_lt (lt_of_le_of_lt hn hp)

/-- **No window of bounded length selects `ζ`**: for every length `A` some weight with the same
absolute jump weights agrees with `Λ` on every window test of length `A` and is not Weil
positive. -/
theorem exists_flip_twin_of_window (A : ℝ) :
    ∃ lam : ℕ → ℝ, ¬ RHTower.WeilPositiveFull lam ∧
      (∀ n, |lam n| = ArithmeticFunction.vonMangoldt n) ∧
      ∀ H : ℝ → ℝ, IsWindowTest A H →
        RHTower.weilFullFunctional lam (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) =
          RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (windowLevel A + 1)
  exact ⟨primeFlipWeight p, primeFlip_not_weilPositiveFull hp, abs_primeFlipWeight p,
    fun H hH => weilFullFunctional_primeFlip_eq hH (by omega)⟩

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
