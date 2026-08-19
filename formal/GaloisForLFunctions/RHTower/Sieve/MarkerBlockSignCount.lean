import GaloisForLFunctions.RHTower.Sieve.ScaledBadStart
import GaloisForLFunctions.RHTower.Sieve.MarkerSignWindowCount
import GaloisForLFunctions.RHTower.Sieve.MarkerCellFromGoodOuter
import GaloisForLFunctions.RHTower.Sieve.GoodMarkerData

/-!
# The sign count of a physical window, supplied by a block of markers

A marker whose reciprocal start carries a good fibre, and whose cell is long enough to contain that
fibre but not more than twice as long, inherits a definite proportion of one Möbius sign among its
cofactors — hence the opposite sign among its products.  Summing the cells harmonically gives the
sign count of the window.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A good fibre carries a definite count of either nonzero Möbius sign. -/
theorem goodFibre_count {y hy : ℝ} {a : ℕ} {σ : ℤ} (h : goodFibre y hy a)
    (hσ : σ = 1 ∨ σ = -1) :
    (3 / 16) * squarefreeDensity * (fibreLen y hy a : ℝ)
      ≤ (((Finset.Ioc (fibreStartIdx y a) (fibreStartIdx y a + fibreLen y hy a)).filter
          (fun n => moebius n = -σ)).card : ℝ) := by
  rcases hσ with rfl | rfl
  · simpa using h.2
  · simpa using h.1

/-- **The sign count of the physical window, from a block of good markers.** -/
theorem card_sign_window_ge_of_goodStarts {y hy : ℝ} {X H M₀ Q : ℕ} {σ : ℤ} {rho S B : ℝ}
    (P : Finset ℕ) (hPsub : P ⊆ bigPrimeSet M₀ (Q * M₀)) (hXH : X + H ≤ M₀ * M₀)
    (hrho : 0 ≤ rho) (hσ : σ = 1 ∨ σ = -1)
    (hgood : ∀ p ∈ P, ∃ a, fibreStartIdx y a = X / p ∧ goodFibre y hy a
        ∧ (X / p + fibreLen y hy a) * p ≤ X + H
        ∧ rho * ((H : ℝ) / (p : ℝ) - 1)
            ≤ (3 / 16) * squarefreeDensity * (fibreLen y hy a : ℝ))
    (hS : S ≤ ∑ p ∈ P, 1 / (p : ℝ)) (hB : ((P.card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  refine card_sign_window_ge P hPsub hXH hrho ?_ hS hB
  intro p hp
  obtain ⟨a, hstart, hgf, hfit, hmaj⟩ := hgood p hp
  have hppos : 0 < p := (prime_of_mem_bigPrimeSet (hPsub hp)).pos
  refine card_windowCell_sign_ge_of_goodOuter (x := y) (h := hy) (a := a)
    hstart hfit hppos ?_
  exact le_trans hmaj (goodFibre_count hgf hσ)

/-- **The cell bound at one good marker.**  This is the per-marker form: the fibre data `(y, hy, m)`
may vary with the marker, which is what a family of dyadic marker blocks needs. -/
theorem cell_bound_of_good_start {y hy : ℝ} {X H p m : ℕ} {σ : ℤ} {rho : ℝ}
    (hy4 : 4 ≤ y) (hy0 : 0 < hy) (hsy : Real.sqrt y = (m : ℝ)) (hp : 0 < p)
    (hσ : σ = 1 ∨ σ = -1) (ht1 : 1 ≤ X / p)
    (htlow : (m : ℝ) / 2 ≤ ((X / p : ℕ) : ℝ))
    (hthigh : ((X / p : ℕ) : ℝ) + 1 ≤ (m : ℝ))
    (hnot : X / p ∉ badStart y hy)
    (hfit : (hy * (((X / p : ℕ) : ℝ) + 1) / (m : ℝ) + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsupply : rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (hy * ((X / p : ℕ) : ℝ) / (m : ℝ) - 1)) :
    rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell X H p).filter (fun b => moebius b = -σ)).card : ℕ) : ℝ) := by
  classical
  obtain ⟨a, hstart, hgf, hfit', hmaj⟩ :=
    exists_good_marker_data hy4 hy0 hsy hp ht1 htlow hthigh hnot hfit hsupply
  exact card_windowCell_sign_ge_of_goodOuter (x := y) (h := hy) (a := a)
    hstart hfit' hp (le_trans hmaj (goodFibre_count hgf hσ))

end RHTower.Sieve
