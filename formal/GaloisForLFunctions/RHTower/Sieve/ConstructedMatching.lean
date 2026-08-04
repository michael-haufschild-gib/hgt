import GaloisForLFunctions.RHTower.Sieve.MarkerSupplyMatching
import GaloisForLFunctions.RHTower.Sieve.WindowCell

/-!
# The matching with both families constructed

Taking the markers to be the primes of `(M, QM]` and the cofactors to be the window cells removes
the last piece of unspecified data.  Every hypothesis of the matching theorem is now either an
arithmetic relation between the parameters or a comparison of elementary functions of them.

The cell size is at least `H/(QM) − 1` because a marker is at most `QM`, and the cofactors stay
below `M` because a marker exceeds `M` while the products stay below `M²`.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- **The matching with markers and cofactors both constructed.** -/
theorem exists_hall_injection_constructed {X H M Q z Y : ℕ}
    (hM : 3 ≤ M) (hQ : 1 ≤ Q) (hXH : X + H ≤ M * M)
    (hcH : (((Q * M : ℕ) : ℝ)) ≤ (H : ℝ))
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (Real.log Q - 2 * mertensFirstConst) * (M : ℝ) / Real.log M
          * ((H : ℝ) / ((Q * M : ℕ) : ℝ) - 1)) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hQM : 0 < Q * M := Nat.mul_pos (by omega) (by omega)
  have hQMR : (0 : ℝ) < ((Q * M : ℕ) : ℝ) := by exact_mod_cast hQM
  have hppos : ∀ p ∈ bigPrimeSet M (Q * M), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
  refine exists_hall_injection_bigPrime (windowCell X H) hM hQ
    (fun p hp a ha => pos_of_mem_windowCell (hppos p hp) ha) ?_ ?_ ?_
    (fun p hp a ha => (mem_windowCell_iff (hppos p hp)).1 ha) hY hYz hz hlog hnum
  · -- cofactors are at most `M`
    intro p hp a ha
    have hprod := ((mem_windowCell_iff (hppos p hp)).1 ha).2
    have hMp : M < p := lt_of_mem_bigPrimeSet hp
    by_contra hcon
    have h1 : M + 1 ≤ a := by omega
    have h2 : M + 1 ≤ p := by omega
    have h3 : (M + 1) * (M + 1) ≤ a * p := Nat.mul_le_mul h1 h2
    have h4 : a * p ≤ M * M := le_trans hprod hXH
    nlinarith
  · -- the cell size is nonnegative after the shift
    have h1 : (1 : ℝ) ≤ (H : ℝ) / ((Q * M : ℕ) : ℝ) := (one_le_div hQMR).2 hcH
    linarith
  · -- every cell has at least `H/(QM) − 1` members
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos p hp
    have hple : p ≤ Q * M := by
      rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
      omega
    have hpleR : (p : ℝ) ≤ ((Q * M : ℕ) : ℝ) := by exact_mod_cast hple
    have hdiv : (H : ℝ) / ((Q * M : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg H) hpR hpleR
    have hgt := card_windowCell_gt X H p (hppos p hp)
    linarith

end RHTower.Sieve
