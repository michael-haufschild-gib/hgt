import GaloisForLFunctions.RHTower.Sieve.StartFibreLength

/-!
# The data a good marker supplies

A marker whose reciprocal start lies in the realisable range and outside the exceptional image
carries a good fibre.  Two numerical conditions then make that fibre usable: it must fit inside the
marker's cell, and it must fill a definite proportion of it.  Both are inequalities between the
marker, the window and the cofactor window alone — the outer factor has been eliminated by the
two-sided length bound.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The good-marker package.** -/
theorem exists_good_marker_data {y hy : ℝ} {X H p m : ℕ} {rho : ℝ}
    (hy4 : 4 ≤ y) (hy0 : 0 < hy) (hsy : Real.sqrt y = (m : ℝ)) (hp : 0 < p)
    (ht1 : 1 ≤ X / p)
    (htlow : (m : ℝ) / 2 ≤ ((X / p : ℕ) : ℝ))
    (hthigh : ((X / p : ℕ) : ℝ) + 1 ≤ (m : ℝ))
    (hnot : X / p ∉ badStart y hy)
    (hfit : (hy * (((X / p : ℕ) : ℝ) + 1) / (m : ℝ) + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsupply : rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (hy * ((X / p : ℕ) : ℝ) / (m : ℝ) - 1)) :
    ∃ a, fibreStartIdx y a = X / p ∧ goodFibre y hy a
      ∧ (X / p + fibreLen y hy a) * p ≤ X + H
      ∧ rho * ((H : ℝ) / (p : ℝ) - 1)
          ≤ (3 / 16) * squarefreeDensity * (fibreLen y hy a : ℝ) := by
  classical
  obtain ⟨a, ha1, _hmem, hstart, hgf, halow, hahigh⟩ :=
    exists_goodFibre_of_start (y := y) (hy := hy) (t := X / p) hy0.le hy4 ht1
      (by rw [hsy]; exact htlow) (by rw [hsy]; exact hthigh) hnot
  obtain ⟨hlow, hhigh⟩ := fibreLen_bounds hy4 hy0.le ht1 ha1 hstart halow hahigh
  rw [hsy] at hlow hhigh
  refine ⟨a, hstart, hgf, ?_, ?_⟩
  · -- the fibre fits inside the cell
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hstep : ((fibreLen y hy a : ℕ) : ℝ) * (p : ℝ) ≤ (H : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hhigh hpR.le) hfit
    have hnat : fibreLen y hy a * p ≤ H := by
      have : (((fibreLen y hy a * p : ℕ)) : ℝ) ≤ ((H : ℕ) : ℝ) := by
        push_cast
        exact hstep
      exact_mod_cast this
    have hdiv : X / p * p ≤ X := Nat.div_mul_le_self X p
    calc (X / p + fibreLen y hy a) * p = X / p * p + fibreLen y hy a * p := by ring
      _ ≤ X + H := Nat.add_le_add hdiv hnat
  · -- the fibre fills a definite proportion of the cell
    have hD : (0 : ℝ) ≤ (3 / 16) * squarefreeDensity := by
      have := squarefreeDensity_pos
      positivity
    exact le_trans hsupply (mul_le_mul_of_nonneg_left hlow hD)

end RHTower.Sieve
