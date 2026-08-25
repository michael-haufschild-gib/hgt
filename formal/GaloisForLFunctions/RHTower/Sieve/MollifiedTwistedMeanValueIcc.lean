import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedDiagonalIcc

/-!
# Mollified twisted mean value on initial ranges

This is the AFE-ready form of the mollified twisted mean-value theorem.  Both supports are initial
positive intervals, so the geometric bound is `L * M`, the source cardinality is `L`, and the main
term is the explicit gcd-reduced scale sum.
-/

open Finset Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- Explicit gcd-reduced main term for initial AFE and mollifier ranges. -/
def mollifiedTwistedDiagonalIcc
    (a b u v : ℕ → ℂ) (L M : ℕ) (sigma : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M,
    (u h * (starRingEnd ℂ) (v k)) *
      (∑ d ∈ Finset.Icc 1
          (L / max (k / Nat.gcd h k) (h / Nat.gcd h k)),
        twistedCoeff a b sigma
          ((k / Nat.gcd h k) * d) ((h / Nat.gcd h k) * d))

theorem mollifiedTwistedDiagonal_eq_Icc
    (a b u v : ℕ → ℂ) (L M : ℕ) (sigma : ℝ) :
    mollifiedTwistedDiagonal a b u v (Finset.Icc 1 L) (Finset.Icc 1 M) sigma =
      mollifiedTwistedDiagonalIcc a b u v L M sigma := by
  rw [mollifiedTwistedDiagonalIcc]
  apply mollifiedTwistedDiagonal_Icc
  intro h hh
  exact (Finset.mem_Icc.mp hh).1

/-- Initial-range mollified twisted mean value with every geometric support
bound and the full gcd-reduced main term made explicit. -/
theorem integral_mollified_cdpoly_Icc_error
    (a b u v : ℕ → ℂ) (L M : ℕ) (sigma : ℝ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ∈ Finset.Icc 1 L, ∀ n ∈ Finset.Icc 1 L,
      ‖twistedCoeff a b sigma m n‖ ≤ C)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly a (Finset.Icc 1 L) sigma t *
              (starRingEnd ℂ) (cdpoly b (Finset.Icc 1 L) sigma t)) *
            (cdpoly u (Finset.Icc 1 M) 0 t *
              (starRingEnd ℂ) (cdpoly v (Finset.Icc 1 M) 0 t))) -
        (U : ℂ) * mollifiedTwistedDiagonalIcc a b u v L M sigma‖
      ≤ (4 * (L : ℝ) * C * ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (∑ h ∈ Finset.Icc 1 M, ‖u h‖) *
          (∑ k ∈ Finset.Icc 1 M, ‖v k‖) := by
  have hbase := integral_mollified_cdpoly_error a b u v
    (Finset.Icc 1 L) (Finset.Icc 1 M) sigma
    (fun n hn => (Finset.mem_Icc.mp hn).1)
    (fun h hh => (Finset.mem_Icc.mp hh).1)
    (B := ((L * M : ℕ) : ℝ)) (by positivity)
    (fun n hn j hj => by
      exact_mod_cast Nat.mul_le_mul (Finset.mem_Icc.mp hn).2 (Finset.mem_Icc.mp hj).2)
    hC0 hC T U
  rw [mollifiedTwistedDiagonal_eq_Icc] at hbase
  simpa [Nat.card_Icc] using hbase

end RHTower.Sieve
