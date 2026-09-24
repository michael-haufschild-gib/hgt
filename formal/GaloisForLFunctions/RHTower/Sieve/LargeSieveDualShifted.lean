import GaloisForLFunctions.RHTower.Sieve.LargeSieveDual

/-!
# Translated dual Farey large sieve

A phase rotation of each Farey coefficient gives the same large-sieve energy
bound on every finite observation block. This is the window estimate needed
to pass from complete-period residue variance to physical-cell leakage.
-/

noncomputable section
open Finset

namespace RHTower.Sieve

theorem largeSieve_dual_fareySet_shifted
    (T B : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (b : ℕ × ℕ → ℂ) :
    ∑ n : Fin B,
        ‖∑ p ∈ fareySet Q,
          b p * (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))) ^ (T + (n : ℕ))‖ ^ (2 : ℕ) ≤
      ((B : ℝ) + (Q : ℝ) ^ (2 : ℕ) *
          (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1))) *
        ∑ p ∈ fareySet Q, ‖b p‖ ^ (2 : ℕ) := by
  let c : ℕ × ℕ → ℂ := fun p =>
    b p * (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))) ^ T
  have h := largeSieve_dual_fareySet B hQ c
  have hnorm :
      (∑ p ∈ fareySet Q, ‖c p‖ ^ (2 : ℕ)) =
        ∑ p ∈ fareySet Q, ‖b p‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [c, norm_pow, norm_circleFreq]
  have hterm (n : Fin B) :
      (∑ p ∈ fareySet Q,
        b p * (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))) ^ (T + (n : ℕ))) =
      ∑ p ∈ fareySet Q,
        c p * (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))) ^ (n : ℕ) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [c, pow_add]
    ring
  simpa only [hterm, hnorm] using h

end RHTower.Sieve
