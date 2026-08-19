import GaloisForLFunctions.RHTower.Sieve.MarkerCellSign
import GaloisForLFunctions.RHTower.Sieve.PairFibre

/-!
# A good outer factor supplies the marker's cell

The corpus's step-1 conclusion is a sign count on `Ioc (fibreStartIdx x a) (fibreStartIdx x a +
fibreLen x h a)` for a good outer factor `a`.  A marker prime `p` whose reciprocal start `⌊X/p⌋`
equals that of `a`, and whose window is long enough to contain the fibre, inherits the count on its
own cell `windowCell X H p`.  That is the hypothesis `hc` of
`Sieve/WindowMatching.exists_hall_injection_primes_of_cells`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **A good outer factor supplies the marker's cell.** -/
theorem card_windowCell_sign_ge_of_goodOuter {x h : ℝ} {X H p a : ℕ} {σ : ℤ} {c : ℝ}
    (hstart : fibreStartIdx x a = X / p)
    (hfit : (X / p + fibreLen x h a) * p ≤ X + H)
    (hp : 0 < p)
    (hsign : c ≤ ((((Finset.Ioc (fibreStartIdx x a)
        (fibreStartIdx x a + fibreLen x h a)).filter (fun b => moebius b = σ)).card : ℕ) : ℝ)) :
    c ≤ ((((windowCell X H p).filter (fun b => moebius b = σ)).card : ℕ) : ℝ) := by
  classical
  have hsub : Finset.Ioc (X / p) (X / p + fibreLen x h a) ⊆ windowCell X H p :=
    Ioc_subset_windowCell (lt_succ_div_mul hp) hfit
  rw [hstart] at hsign
  exact card_sign_windowCell_ge hsub hsign

end RHTower.Sieve
