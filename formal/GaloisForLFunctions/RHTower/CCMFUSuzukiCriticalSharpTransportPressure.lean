import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalMultiPrimeTransportPressure

/-!
# Sharp one-prime transport pressure for the critical CCM--FU source

The earlier locality obstruction used a cellwise lower bound and therefore
retained only half of the prime atom.  The exact completed block law already
contains the whole `Λ(p) / p` atom.  This module extracts that atom before any
estimate and compares it with the exact polar logarithmic drift.

Thus a forward block beginning at a prime can become nonpositive only after
its polar transport budget has paid the full harmonic prime mass.  This does
not bound the RH-bearing signed reporter: it sharpens the necessary memory
law which every proposed growing-range cancellation mechanism must satisfy.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- A nonpositive completed forward block beginning at a prime has enough
polar logarithmic drift to pay the *full* prime atom `log p / p`.

Unlike the cellwise pressure inequality, this is obtained directly from the
literal finite `vonMangoldt` block sum, so no part of the prime atom is lost
before cancellation with the polar continuum. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_full_log_budget
    {p L : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    Real.log (p : ℝ) / p ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_nonpos_forwardBlock_vonMangoldt_budget
      (p := p) (L := L) hp3 hblock
  have hmem : p ∈ Finset.Icc p (p + L) := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩
  have hterm_nonneg : ∀ k ∈ Finset.Icc p (p + L),
      0 ≤ ArithmeticFunction.vonMangoldt k / (k : ℝ) := by
    intro k _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hprime : Real.log (p : ℝ) / p =
      ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlower : Real.log (p : ℝ) / p ≤
      ∑ k ∈ Finset.Icc p (p + L), ArithmeticFunction.vonMangoldt k / (k : ℝ) := by
    rw [hprime]
    exact Finset.single_le_sum hterm_nonneg hmem
  exact hlower.trans hbudget

/-- Every selected finite family of prime atoms inside a nonpositive completed
forward block consumes its full harmonic mass from the one polar drift budget.

This is the source-level aggregate form of the sharp law.  It is deliberately
stated for an arbitrary finite selected family: any proposed block transport
must pay all prime atoms it leaves in that block simultaneously. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_forwardBlock_full_log_budget
    {p L : ℕ} (hp3 : 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc p (p + L))
    (hprime : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, Real.log (q : ℝ) / q) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_nonpos_forwardBlock_vonMangoldt_budget
      (p := p) (L := L) hp3 hblock
  have hrewrite :
      (∑ q ∈ S, Real.log (q : ℝ) / q) =
        ∑ q ∈ S, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hprime q hq)]
  rw [hrewrite]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hS (fun q hq _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))).trans hbudget

/-- Aggregate sharp harmonic-memory law for every selected finite family of
prime atoms in a nonpositive forward block. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_forwardBlock_full_harmonic_radius
    {p L : ℕ} (hp3 : 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc p (p + L))
    (hprime : ∀ q ∈ S, q.Prime) :
    ((p - 1 : ℕ) : ℝ) * (∑ q ∈ S, Real.log (q : ℝ) / q) ≤ (L + 1 : ℕ) := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_finsetPrime_nonpos_forwardBlock_full_log_budget
      hp3 hblock S hS hprime
  have hspan := log_suzukiCheckpointCritical_forwardBlock_drift_le
    (p := p - 1) (L := L + 1) (by omega : 1 ≤ p - 1)
  have hspan' :
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    have hindex : p - 1 + (L + 1) = p + L := by omega
    simpa only [hindex] using hspan
  have hmain : (∑ q ∈ S, Real.log (q : ℝ) / q) ≤
      ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := hbudget.trans hspan'
  have hpminus : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  calc
    ((p - 1 : ℕ) : ℝ) * (∑ q ∈ S, Real.log (q : ℝ) / q) ≤
        ((p - 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain hpminus.le
    _ = (L + 1 : ℕ) := by field_simp

/-- Sharp harmonic-memory law for a nonpositive completed forward block.

The required range pays the full starting prime atom at the natural
`p - 1` polar scale.  In particular, a growing-memory source transport must
meet this stronger constraint before it can cancel even its first prime;
the theorem makes no assertion about the signed global reporter. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_full_harmonic_radius
    {p L : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    ((p - 1 : ℕ) : ℝ) * (Real.log (p : ℝ) / p) ≤ (L + 1 : ℕ) := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_full_log_budget
      hp hp3 hblock
  have hspan := log_suzukiCheckpointCritical_forwardBlock_drift_le
    (p := p - 1) (L := L + 1) (by omega : 1 ≤ p - 1)
  have hspan' :
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    have hindex : p - 1 + (L + 1) = p + L := by omega
    simpa only [hindex] using hspan
  have hmain : Real.log (p : ℝ) / p ≤
      ((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := hbudget.trans hspan'
  have hpminus : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  calc
    ((p - 1 : ℕ) : ℝ) * (Real.log (p : ℝ) / p) ≤
        ((p - 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain hpminus.le
    _ = (L + 1 : ℕ) := by field_simp

end

end RHTower
