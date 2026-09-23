import GaloisForLFunctions.RHTower.Sieve.GallagherBoundedHeight
import GaloisForLFunctions.RHTower.Sieve.LogPolyTranslation
import GaloisForLFunctions.RHTower.Sieve.CauchyCellEnergy

/-!
# The Brun–Titchmarsh mean square on a translated cell

Translating the frequency by `u` multiplies the `n`-th coefficient of a Dirichlet polynomial by the
unimodular factor `n^{-iu}`, so the adaptive Gallagher–Brun–Titchmarsh mean square at height `2`
transfers verbatim to every cell of that length, with the same arithmetic right-hand side
`∑_q ‖a_q‖² log q / q`.  This is the estimate a Cauchy-weighted energy consumes cell by cell; the
sharp near-diagonal weight of `integral_Icc_normSq_logPoly_shift_le_prime_sharp` is the wrong one
here, since it costs `q/log q` rather than `log q/q`.
-/

namespace RHTower.Sieve

open Real MeasureTheory

noncomputable section

/-- The Dirichlet weight `log n / n` commutes with the unimodular twist. -/
theorem twist_weighted (a : ℕ → ℂ) (u : ℝ) :
    (fun p : ℕ => (a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ))
        * Complex.exp (((2 * Real.pi * (u * Real.log p) : ℝ) : ℂ) * Complex.I))
      = fun p : ℕ => (a p
            * Complex.exp (((2 * Real.pi * (u * Real.log p) : ℝ) : ℂ) * Complex.I))
          * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ) := by
  funext p
  ring

/-- **Lemma B on an arbitrary cell.**  The adaptive mean square at height `2` holds on every
interval of that length, with an arithmetic right-hand side that does not see the translation. -/
theorem integral_cell_normSq_logPoly_bt_le {S : Finset ℕ} (hs : ∀ m ∈ S, Nat.Prime m)
    {a : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖a n‖ ≤ 1) (u : ℝ) :
    (∫ w in (u - 1 / Real.pi)..(u + 1 / Real.pi),
        ‖logPoly (fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ (2 : ℕ))
      ≤ 4500 * ∑ p ∈ S, ‖a p‖ ^ (2 : ℕ) * Real.log p / (p : ℝ) + 16 / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ) with hb
  set ρ : ℝ := 1 / Real.pi with hρ
  have hρ0 : (0 : ℝ) < ρ := by rw [hρ]; positivity
  have hle : (-ρ : ℝ) ≤ ρ := by linarith
  set c : ℕ → ℂ := fun n : ℕ =>
    a n * Complex.exp (((2 * Real.pi * (u * Real.log n) : ℝ) : ℂ) * Complex.I) with hc
  have hshift : (∫ w in (u - ρ)..(u + ρ), ‖logPoly b S w‖ ^ (2 : ℕ))
      = ∫ w in (-ρ)..ρ,
          ‖logPoly (fun p : ℕ => c p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ (2 : ℕ) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := -ρ) (b := ρ) (fun w : ℝ => ‖logPoly b S w‖ ^ (2 : ℕ)) u
    have hrw : ∀ w : ℝ, ‖logPoly b S (w + u)‖ ^ (2 : ℕ)
        = ‖logPoly (fun p : ℕ => c p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ (2 : ℕ) := by
      intro w
      rw [logPoly_add_right b S u w, hb, twist_weighted a u]
    rw [← funext hrw, h]
    congr 1 <;> ring
  rw [hshift]
  have hIcc : (∫ w in (-ρ)..ρ,
        ‖logPoly (fun p : ℕ => c p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-ρ) ρ,
          ‖logPoly (fun p : ℕ => c p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc]
  have hρeq : ρ = 2 / (2 * Real.pi) := by rw [hρ]; field_simp
  rw [hρeq]
  have hcbdd : ∀ n : ℕ, ‖c n‖ ≤ 1 := by
    intro n
    rw [hc, norm_twist a u n]
    exact hbdd n
  have hmain := gallagher_bt_mean_square_all hs (a := c) hcbdd
  refine hmain.trans (le_of_eq ?_)
  have hnorm : ∀ p : ℕ, ‖c p‖ ^ (2 : ℕ) = ‖a p‖ ^ (2 : ℕ) := by
    intro p
    rw [hc, norm_twist a u p]
  simp only [hnorm]
  ring

end

end RHTower.Sieve
