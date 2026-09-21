import GaloisForLFunctions.RHTower.EulerDeletionTerminalCoefficientCollapse
import GaloisForLFunctions.RHTower.EulerDeletionReverseTailFuturePrimeSupport

/-!
# Upper-half prime support of physical Euler-deletion residuals

Above the midpoint of the physical cutoff, every nontrivial residual coprime to the
chronological clock is a single prime.  The singleton residual already has zero cofactor total,
so the literal selected EDQ block has an exact prime-residual form.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction

namespace RHTower.DeletionResidueMartingale

attribute [local instance] Classical.propDecidable

/-- In the upper half of the physical cutoff, a nontrivial future residual is prime. -/
theorem eq_one_or_prime_of_mem_futureResidualCarrier_of_upper_half
    {N L m : ℕ} (hN : N ≤ 2 * L) (hm : m ∈ futureResidualCarrier N L) :
    m = 1 ∨ m.Prime := by
  obtain ⟨hmIcc, hmclock⟩ := mem_filter.mp hm
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) (mem_Icc.mp hmIcc).1
  by_cases hmone : m = 1
  · exact Or.inl hmone
  · right
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hmone
    have hpclock : ¬ p ∣ clock L := by
      intro hclock
      have hpgcd : p ∣ Nat.gcd m (clock L) := Nat.dvd_gcd hpd hclock
      rw [hmclock.gcd_eq_one] at hpgcd
      exact hp.not_dvd_one hpgcd
    have hLp : L < p := by
      by_contra hnot
      exact hpclock (dvd_clock (m := p) (n := L) hp.pos (Nat.le_of_not_gt hnot))
    have hmN : m ≤ N := (mem_Icc.mp hmIcc).2
    have hmp : m = p := eq_of_le_two_mul_layer_of_dvd_of_gt hN hmN hmpos hpd hLp
    simpa [hmp] using hp

/-- The complete upper-half physical residual total is exactly its prime-residual total; the
singleton residual cancels and every other residual is prime. -/
theorem futureOldCofactorCarrier_total_eq_prime_period_coefficient_of_upper_half
    (N L t : ℕ) (x : ℝ) (hLN : L ≤ N) (hN : N ≤ 2 * L) :
    (∑ m ∈ futureResidualCarrier N L,
      ∑ r ∈ futureOldCofactorCarrier N L m,
        clockResidualBetaWeight L t (canonicalClockRatio N L - 1) x (m * r)) =
      ∑ m ∈ (futureResidualCarrier N L).filter Nat.Prime,
        ((moebius m : ℤ) : ℝ) *
          ((∑ a ∈ range (m - 1),
            cofactorReducedResiduePrefix m t (clock L) a * x ^ (a * clock L) -
            complementBoundaryTail N L m t x) *
            ∑ q ∈ range ((canonicalClockRatio N L - 1) / m + 1),
              x ^ (q * (m * clock L))) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro m hm
  by_cases hp : m.Prime
  · rw [if_pos hp]
    exact futureOldCofactorCarrier_sum_eq_single_period_coefficient t x hLN hm
  · rcases eq_one_or_prime_of_mem_futureResidualCarrier_of_upper_half hN hm with hmone | hmprime
    · subst m
      rw [if_neg hp]
      exact futureOldCofactorCarrier_one_sum_eq_zero N L t
        (canonicalClockRatio N L - 1) x
    · exact (hp hmprime).elim

/-- Prime members of the physical future residual carrier are exactly the primes beyond the
current clock index and within the physical cutoff. -/
theorem futureResidualCarrier_filter_prime_eq_prime_Icc
    (N L : ℕ) :
    (futureResidualCarrier N L).filter Nat.Prime = (Icc (L + 1) N).filter Nat.Prime := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpcarrier, hpprime⟩ := mem_filter.mp hp
    obtain ⟨hpIcc, hpcop⟩ := mem_filter.mp hpcarrier
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, (mem_Icc.mp hpIcc).2⟩, hpprime⟩
    have hpgt : L < p := by
      by_contra hnot
      have hpclock : p ∣ clock L :=
        dvd_clock (m := p) (n := L) hpprime.pos (Nat.le_of_not_gt hnot)
      exact (hpprime.coprime_iff_not_dvd.mp hpcop) hpclock
    omega
  · intro hp
    obtain ⟨hpIcc, hpprime⟩ := mem_filter.mp hp
    apply mem_filter.mpr
    have hpone : 1 ≤ p := le_trans (by omega) hpprime.two_le
    refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hpone, (mem_Icc.mp hpIcc).2⟩, ?_⟩, hpprime⟩
    refine hpprime.coprime_iff_not_dvd.mpr fun hpclock => ?_
    have hple : p ≤ L := prime_dvd_clock_le hpprime hpclock
    exact (not_lt_of_ge hple (Nat.lt_of_succ_le (mem_Icc.mp hpIcc).1)).elim

/-- Upper-half physical prime-residual form of one literal EDQ selected block. -/
theorem truncatedDivisorBlockKernel_eq_source_prime_period_cofactors_of_upper_half
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ m ∈ (futureResidualCarrier N (l + 1)).filter Nat.Prime,
              ((moebius m : ℤ) : ℝ) *
                ((∑ a ∈ range (m - 1),
                  cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
                    x ^ (a * clock (l + 1)) -
                  complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) *
                  ∑ q ∈ range ((canonicalClockRatio N (l + 1) - 1) / m + 1),
                    x ^ (q * (m * clock (l + 1))))) *
        (1 - x ^ clock N)⁻¹) /
      (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  rw [truncatedDivisorBlockKernel_eq_source_futureCofactor N l u b x hlN,
    futureOldCofactorCarrier_total_eq_prime_period_coefficient_of_upper_half
      N (l + 1) (u + b * clock l + 1) x (Nat.succ_le_iff.mpr hlN) hN]

/-- The upper-half EDQ selected block is an exact finite sum over the ordinary prime interval
`(l + 1, N]`, with no residual-carrier predicate remaining. -/
theorem truncatedDivisorBlockKernel_eq_source_prime_interval_period_cofactors_of_upper_half
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ m ∈ (Icc (l + 2) N).filter Nat.Prime,
              ((moebius m : ℤ) : ℝ) *
                ((∑ a ∈ range (m - 1),
                  cofactorReducedResiduePrefix m (u + b * clock l + 1) (clock (l + 1)) a *
                    x ^ (a * clock (l + 1)) -
                  complementBoundaryTail N (l + 1) m (u + b * clock l + 1) x) *
                  ∑ q ∈ range ((canonicalClockRatio N (l + 1) - 1) / m + 1),
                    x ^ (q * (m * clock (l + 1))))) *
        (1 - x ^ clock N)⁻¹) /
      (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  rw [truncatedDivisorBlockKernel_eq_source_prime_period_cofactors_of_upper_half
    N l u b x hlN hN,
    futureResidualCarrier_filter_prime_eq_prime_Icc N (l + 1)]

end RHTower.DeletionResidueMartingale
