import GaloisForLFunctions.RHTower.Sieve.FibreNonRoughKernel
import GaloisForLFunctions.RHTower.Sieve.RamareComplex

/-!
# The non-rough Möbius polynomial is exactly the Ramaré bilinear form

Restricting `μ` to the integers carrying a designated prime factor removes precisely the rough term
of Ramaré's decomposition, so the restricted Dirichlet polynomial *is* the bilinear form — an
identity, with no error.  That is what makes the restricted weight usable: it is unit-bounded, so
the fibre bridge carries it, and it factors over designated prime times cofactor, so the
large-values machinery applies to it.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The restricted polynomial is the Ramaré bilinear form.** -/
theorem logPoly_nonRoughMoebius_eq_ramare (P s : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((nonRoughMoebius P n : ℝ) : ℂ)) s w
      = ∑ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
          (((moebius n : ℤ) : ℂ)
              * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
            / ((primeFactorsIn P n).card : ℂ) := by
  classical
  rw [logPoly_eq_ramare_add_rough (fun n => ((nonRoughMoebius P n : ℝ) : ℂ)) P s w]
  have hrough : ∑ n ∈ {n ∈ s | primeFactorsIn P n = ∅},
      ((nonRoughMoebius P n : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have hemp : primeFactorsIn P n = ∅ := (Finset.mem_filter.1 hn).2
    have hzero : nonRoughMoebius P n = 0 := by
      rw [nonRoughMoebius, if_neg]
      rw [hemp]
      exact Finset.not_nonempty_empty
    rw [hzero]
    push_cast
    ring
  have hmain : ∀ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
      (((nonRoughMoebius P n : ℝ) : ℂ)
          * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
        / ((primeFactorsIn P n).card : ℂ)
      = ∑ n ∈ {n ∈ s | p ∣ n},
          (((moebius n : ℤ) : ℂ)
              * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
            / ((primeFactorsIn P n).card : ℂ) := by
    intro p hp
    refine Finset.sum_congr rfl fun n hn => ?_
    have hdvd : p ∣ n := (Finset.mem_filter.1 hn).2
    have hne : (primeFactorsIn P n).Nonempty := ⟨p, mem_primeFactorsIn.2 ⟨hp, hdvd⟩⟩
    have hval : nonRoughMoebius P n = ((moebius n : ℤ) : ℝ) := by
      rw [nonRoughMoebius, if_pos hne]
    rw [hval]
    push_cast
    ring
  rw [hrough, add_zero, Finset.sum_congr rfl hmain]

/-- **The Möbius fibre mean square against the Ramaré bilinear polynomial.**  The full chain with
no Turán–Kubilius loss: no `1/W²` on the spectral term, and the sieve error squared. -/
theorem sum_sq_fibreSum_moebius_le_ramareBilinear_kernel {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ (2 : ℕ)
                * ‖∑ p ∈ Nat.primesLE z, ∑ n ∈ {n ∈ fibreIndex x h | p ∣ n},
                    (((moebius n : ℤ) : ℂ)
                        * Complex.exp
                            (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
                      / ((primeFactorsIn (Nat.primesLE z) n).card : ℂ)‖ ^ (2 : ℕ))
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ (2 : ℕ) := by
  have hbase := sum_sq_fibreSum_moebius_le_nonRough_kernel hx hh0 hhx hz hr hlam
  have hpoly : ∀ w : ℝ,
      ‖logPoly (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
          (fibreIndex x h) w‖ ^ (2 : ℕ)
        = ‖∑ p ∈ Nat.primesLE z, ∑ n ∈ {n ∈ fibreIndex x h | p ∣ n},
            (((moebius n : ℤ) : ℂ)
                * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))
              / ((primeFactorsIn (Nat.primesLE z) n).card : ℂ)‖ ^ (2 : ℕ) := by
    intro w
    rw [logPoly_nonRoughMoebius_eq_ramare]
  simp only [hpoly] at hbase
  exact hbase

end

end RHTower.Sieve
