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

/-- In the upper-half range, a future prime has no nontrivial old cofactor under the physical
cutoff. This removes the reduced-residue cofactor sum before any averaging. -/
theorem futureOldCofactorCarrier_eq_singleton_of_upper_half_prime
    {N L p : ℕ} (hN : N ≤ 2 * L) (hp : p.Prime)
    (hLp : L < p) (hpN : p ≤ N) :
    futureOldCofactorCarrier N L p = {1} := by
  ext r
  constructor
  · intro hr
    have hrdiv : r ∣ clock L := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrdiv (clock_pos L)
    have hpr : p * r ≤ N := (Finset.mem_filter.mp hr).2.1
    have hrone : r = 1 := by
      by_contra hne
      have hrge : 2 ≤ r := by omega
      have htwo : 2 * p ≤ p * r := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hrge
      omega
    simp [hrone]
  · intro hr
    have hrone : r = 1 := by simpa using hr
    subst r
    have hC0 : clock L ≠ 0 := (clock_pos L).ne'
    simp [futureOldCofactorCarrier, hpN, hp.squarefree, hC0]

/-- The surviving upper-half prime fibre is one literal signed divisor-window prefix. The
proper-modulus boundary and the full reduced-residue period cancel exactly in this range. -/
theorem futureOldCofactorCarrier_prime_sum_eq_window_prefix_of_upper_half
    {N L p : ℕ} (hN : N ≤ 2 * L) (hp : p.Prime)
    (hLp : L < p) (hpN : p ≤ N) (t Q : ℕ) (x : ℝ) :
    (∑ r ∈ futureOldCofactorCarrier N L p,
      clockResidualBetaWeight L t Q x (p * r)) =
      ((moebius p : ℤ) : ℝ) *
        ∑ s ∈ range Q,
          (∑ i ∈ range (s + 1),
            divisorWindowDiscrepancy p (t + i * clock L) (clock L)) *
              x ^ (s * clock L) := by
  rw [futureOldCofactorCarrier_eq_singleton_of_upper_half_prime hN hp hLp hpN]
  simp only [sum_singleton, mul_one]
  exact (moebius_divisor_betaPrefix_eq_clockResidualBetaWeight L p t Q x).symm

/-- Any physical interval multiple discrepancy is a difference of two fractional remainders.
This exact form exposes its short phase period in the starting point. -/
theorem interval_multiple_discrepancy_eq_remainder
    (d t H : ℕ) (hd : 0 < d) :
    (H : ℝ) / (d : ℝ) -
        ((#{k ∈ Ioc t (t + H) | d ∣ k} : ℕ) : ℝ) =
      (((t + H) % d : ℕ) : ℝ) / (d : ℝ) -
        ((t % d : ℕ) : ℝ) / (d : ℝ) := by
  rw [Sieve.card_filter_dvd_Ioc d t (t + H) (Nat.le_add_right t H)]
  have hq : t / d ≤ (t + H) / d :=
    Nat.div_le_div_right (Nat.le_add_right t H)
  rw [Nat.cast_sub hq]
  have hA : (((t + H) % d : ℕ) : ℝ) + (d : ℝ) * (((t + H) / d : ℕ) : ℝ) =
      (t + H : ℕ) := by exact_mod_cast (Nat.mod_add_div (t + H) d)
  have hB : ((t % d : ℕ) : ℝ) + (d : ℝ) * ((t / d : ℕ) : ℝ) =
      (t : ℝ) := by exact_mod_cast (Nat.mod_add_div t d)
  have he : (H : ℝ) = (t + H : ℕ) - (t : ℝ) := by push_cast; ring
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdiff : (H : ℝ) =
      ((((t + H) % d : ℕ) : ℝ) - ((t % d : ℕ) : ℝ)) +
        (d : ℝ) *
          (((((t + H) / d : ℕ) : ℝ)) - ((t / d : ℕ) : ℝ)) := by
    rw [he]
    linarith [hA, hB]
  rw [hdiff]
  field_simp [hd0]
  ring

/-- Every incomplete divisor-window prefix is strictly below one in absolute value, uniformly
in modulus, window length, starting phase and prefix length. -/
theorem interval_multiple_discrepancy_abs_lt_one
    (d t H : ℕ) (hd : 0 < d) :
    |(H : ℝ) / (d : ℝ) -
      ((#{k ∈ Ioc t (t + H) | d ∣ k} : ℕ) : ℝ)| < 1 := by
  rw [interval_multiple_discrepancy_eq_remainder d t H hd]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hA := Nat.mod_lt (t + H) hd
  have hB := Nat.mod_lt t hd
  have hA0 : 0 ≤ (((t + H) % d : ℕ) : ℝ) / (d : ℝ) := by positivity
  have hB0 : 0 ≤ ((t % d : ℕ) : ℝ) / (d : ℝ) := by positivity
  have hA1 : (((t + H) % d : ℕ) : ℝ) / (d : ℝ) < 1 := by
    apply (div_lt_iff₀ hdR).mpr
    simpa using (show (((t + H) % d : ℕ) : ℝ) < (d : ℝ) by exact_mod_cast hA)
  have hB1 : ((t % d : ℕ) : ℝ) / (d : ℝ) < 1 := by
    apply (div_lt_iff₀ hdR).mpr
    simpa using (show ((t % d : ℕ) : ℝ) < (d : ℝ) by exact_mod_cast hB)
  rw [abs_lt]
  constructor <;> linarith

/-- The actual chronological prime prefix is one short-period sawtooth. -/
theorem divisorWindowDiscrepancy_prefix_eq_remainder
    (d t C s : ℕ) (hd : 0 < d) (hC : 0 < C) :
    (∑ i ∈ range (s + 1), divisorWindowDiscrepancy d (t + i * C) C) =
      (((t + (s + 1) * C) % d : ℕ) : ℝ) / (d : ℝ) -
        ((t % d : ℕ) : ℝ) / (d : ℝ) := by
  rw [divisorWindowDiscrepancy_prefix_eq_intervalDiscrepancy d t C s hC]
  simpa only [Nat.cast_mul] using
    interval_multiple_discrepancy_eq_remainder d t ((s + 1) * C) hd

theorem divisorWindowDiscrepancy_prefix_abs_lt_one
    (d t C s : ℕ) (hd : 0 < d) (hC : 0 < C) :
    |∑ i ∈ range (s + 1), divisorWindowDiscrepancy d (t + i * C) C| < 1 := by
  rw [divisorWindowDiscrepancy_prefix_eq_intervalDiscrepancy d t C s hC]
  simpa only [Nat.cast_mul] using
    interval_multiple_discrepancy_abs_lt_one d t ((s + 1) * C) hd

/-- The entire upper-half physical residual is a sum of elementary prime window prefixes;
there are no old-cofactor or reduced-residue terms left. -/
theorem futureOldCofactorCarrier_total_eq_prime_window_prefix_of_upper_half
    (N L t Q : ℕ) (x : ℝ) (hN : N ≤ 2 * L) :
    (∑ m ∈ futureResidualCarrier N L,
      ∑ r ∈ futureOldCofactorCarrier N L m,
        clockResidualBetaWeight L t Q x (m * r)) =
      ∑ p ∈ (Icc (L + 1) N).filter Nat.Prime,
        ((moebius p : ℤ) : ℝ) *
          ∑ s ∈ range Q,
            (∑ i ∈ range (s + 1),
              divisorWindowDiscrepancy p (t + i * clock L) (clock L)) *
                x ^ (s * clock L) := by
  calc
    _ = ∑ m ∈ futureResidualCarrier N L,
        if m.Prime then
          ((moebius m : ℤ) : ℝ) *
            ∑ s ∈ range Q,
              (∑ i ∈ range (s + 1),
                divisorWindowDiscrepancy m (t + i * clock L) (clock L)) *
                  x ^ (s * clock L)
        else 0 := by
          apply sum_congr rfl
          intro m hm
          by_cases hp : m.Prime
          · rw [if_pos hp]
            have hmem : m ∈ (Icc (L + 1) N).filter Nat.Prime := by
              rw [← futureResidualCarrier_filter_prime_eq_prime_Icc N L]
              exact mem_filter.mpr ⟨hm, hp⟩
            have hmIcc := (mem_filter.mp hmem).1
            have hmLower : L + 1 ≤ m := (mem_Icc.mp hmIcc).1
            have hmLp : L < m := by omega
            have hmN : m ≤ N := (mem_Icc.mp hmIcc).2
            exact futureOldCofactorCarrier_prime_sum_eq_window_prefix_of_upper_half
              hN hp hmLp hmN t Q x
          · rw [if_neg hp]
            rcases eq_one_or_prime_of_mem_futureResidualCarrier_of_upper_half hN hm with
              hmone | hmprime
            · subst m
              exact futureOldCofactorCarrier_one_sum_eq_zero N L t Q x
            · exact (hp hmprime).elim
    _ = ∑ p ∈ (futureResidualCarrier N L).filter Nat.Prime,
        ((moebius p : ℤ) : ℝ) *
          ∑ s ∈ range Q,
            (∑ i ∈ range (s + 1),
              divisorWindowDiscrepancy p (t + i * clock L) (clock L)) *
                x ^ (s * clock L) := by rw [sum_filter]
    _ = _ := by rw [futureResidualCarrier_filter_prime_eq_prime_Icc]

/-- The selected EDQ upper-half block is a physical prime sawtooth sum, not a primitive
reduced-residue sum. This is the exact form for weighted prime-pair covariance estimates. -/
theorem truncatedDivisorBlockKernel_eq_source_prime_window_prefix_of_upper_half
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    truncatedDivisorBlockKernel N l u b x =
      (x ^ (u + b * clock l) *
        ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
            ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
              ((moebius p : ℤ) : ℝ) *
                ∑ s ∈ range (canonicalClockRatio N (l + 1) - 1),
                  (∑ i ∈ range (s + 1),
                    divisorWindowDiscrepancy p
                      (u + b * clock l + 1 + i * clock (l + 1))
                      (clock (l + 1))) * x ^ (s * clock (l + 1))) *
        (1 - x ^ clock N)⁻¹) /
      (∑ a ∈ range (clock (l + 1)), x ^ a) := by
  rw [truncatedDivisorBlockKernel_eq_source_futureCofactor N l u b x hlN,
    futureOldCofactorCarrier_total_eq_prime_window_prefix_of_upper_half
      N (l + 1) (u + b * clock l + 1)
      (canonicalClockRatio N (l + 1) - 1) x hN]

end RHTower.DeletionResidueMartingale
