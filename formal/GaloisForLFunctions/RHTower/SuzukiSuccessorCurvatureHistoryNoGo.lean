import GaloisForLFunctions.RHTower.SuzukiPrunedBoundaryExcursionDefect
import GaloisForLFunctions.HTGeometry.SmoothNumbers

/-!
# Forward Suzuki curvature cells cannot carry ordered history

The literal signed Suzuki curvature at index `n` is supported on the successor interval
`[log n, log (n + 1)]`.  This file embeds that interval's displacement canonically in the
existing prime-valuation seam: take the difference of the bundled prime-exponent vectors of
`n + 1` and `n`.

Its seam coordinate is exactly `log (n + 1) - log n`, hence is strictly positive.  Therefore every
strict-aperture pruned shift belonging to a forward successor cell commutes with every other one.
Equivalently, their boundary-excursion skew is identically zero.

This is a sharp source-side no-go for the apparent curvature/history bridge: the forward
successor geometry of the curvature cells cannot transport the nonzero oriented Suzuki chronology
port.  A viable two-port lift must retain a reflected or other defect leg; merely re-indexing the
signed curvature cells by their forward endpoint displacements necessarily abelianizes history.
No estimate, target normalization, zero-location premise, or RH hypothesis is used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Canonical integral prime-valuation vector of a positive natural source endpoint. -/
def suzukiCurvatureEndpointValuation (n : ℕ) : SuzukiSeamValuation :=
  Finsupp.mapRange (fun e : ℕ => (e : ℤ)) (by simp)
    (primeExponentVector n)

/-- The source valuation displacement of the `n`th successor curvature cell. -/
def suzukiCurvatureSuccessorValuation (n : ℕ) : SuzukiSeamValuation :=
  suzukiCurvatureEndpointValuation (n + 1) - suzukiCurvatureEndpointValuation n

/-- A natural endpoint's valuation coordinate is its literal logarithmic height. -/
theorem primeSeamCoordinate_suzukiCurvatureEndpointValuation
    {n : ℕ} (hn : n ≠ 0) :
    primeSeamCoordinate (suzukiCurvatureEndpointValuation n) = Real.log (n : ℝ) := by
  calc
    primeSeamCoordinate (suzukiCurvatureEndpointValuation n) =
        (suzukiCurvatureEndpointValuation n).sum
          fun p z => (z : ℝ) * Real.log (p : ℕ) := by
      rw [primeSeamCoordinate_apply]
      apply Finsupp.sum_congr
      intro p hp
      rw [zsmul_eq_mul]
    _ = (primeExponentVector n).sum fun p k => (k : ℝ) * Real.log (p : ℕ) := by
      simp [suzukiCurvatureEndpointValuation, Finsupp.sum_mapRange_index]
    _ = Real.log (n : ℝ) := (log_nat_eq_sum_factorization hn).symm

/-- The valuation coordinate of a successor cell is exactly its source interval length. -/
theorem primeSeamCoordinate_suzukiCurvatureSuccessorValuation
    {n : ℕ} (hn : 0 < n) :
    primeSeamCoordinate (suzukiCurvatureSuccessorValuation n) =
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  rw [suzukiCurvatureSuccessorValuation, map_sub,
    primeSeamCoordinate_suzukiCurvatureEndpointValuation (Nat.succ_ne_zero n),
    primeSeamCoordinate_suzukiCurvatureEndpointValuation hn.ne']

/-- Every forward curvature-cell displacement is strictly positive. -/
theorem primeSeamCoordinate_suzukiCurvatureSuccessorValuation_pos
    {n : ℕ} (hn : 0 < n) :
    0 < primeSeamCoordinate (suzukiCurvatureSuccessorValuation n) := by
  rw [primeSeamCoordinate_suzukiCurvatureSuccessorValuation hn]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnp1R : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hltR : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self n
  linarith [Real.strictMonoOn_log hnR hnp1R hltR]

/-- A prime endpoint carries exactly its visible exponent-one Suzuki valuation atom. -/
theorem suzukiCurvatureEndpointValuation_prime (p : Nat.Primes) :
    suzukiCurvatureEndpointValuation (p : ℕ) = suzukiPrimePowerStep (p, 1) := by
  ext q
  by_cases hqp : q = p
  · subst q
    simp only [suzukiCurvatureEndpointValuation, suzukiPrimePowerStep,
      Finsupp.mapRange_apply, primeExponentVector_apply, Finsupp.single_eq_same]
    simpa using (Nat.factorization_pow_self (n := 1) p.2)
  · have hpq : ¬p = q := fun h => hqp h.symm
    simp only [suzukiCurvatureEndpointValuation, suzukiPrimePowerStep,
      Finsupp.mapRange_apply, primeExponentVector_apply,
      Finsupp.single_apply, if_neg hpq]
    norm_cast
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdiv
    rcases (Nat.dvd_prime p.2).mp hdiv with hqone | hqeq
    · exact q.2.ne_one hqone
    · exact hqp (Subtype.ext hqeq)

/-- The reflected literal curvature cell from `log 2` to `log 3` factors into the exact
prime-two forward atom followed by the reflected prime-three atom.  This is a valuation identity;
it retains the two atomic legs rather than replacing them by their scalar displacement. -/
theorem suzukiCurvatureSuccessorValuation_two_reflection_factorization :
    -suzukiCurvatureSuccessorValuation 2 =
      suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1) +
        -suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1) := by
  rw [suzukiCurvatureSuccessorValuation]
  change -(suzukiCurvatureEndpointValuation 3 - suzukiCurvatureEndpointValuation 2) = _
  rw [neg_sub]
  rw [suzukiCurvatureEndpointValuation_prime ⟨2, Nat.prime_two⟩,
    suzukiCurvatureEndpointValuation_prime ⟨3, Nat.prime_three⟩]
  rw [sub_eq_add_neg]

/-- **Forward-cell commutation law.** Strict aperture pruning cannot create chronology from two
literal forward successor displacements. -/
theorem suzukiCurvatureSuccessorPruned_commute
    (a : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    suzukiOrientedSupportPrunedShift a (suzukiCurvatureSuccessorValuation m) ∘L
        suzukiOrientedSupportPrunedShift a (suzukiCurvatureSuccessorValuation n) =
      suzukiOrientedSupportPrunedShift a (suzukiCurvatureSuccessorValuation n) ∘L
        suzukiOrientedSupportPrunedShift a (suzukiCurvatureSuccessorValuation m) := by
  exact suzukiOrientedSupportPrunedShift_comp_commute_of_nonneg_coordinates
    a (suzukiCurvatureSuccessorValuation m) (suzukiCurvatureSuccessorValuation n)
    (primeSeamCoordinate_suzukiCurvatureSuccessorValuation_pos hm).le
    (primeSeamCoordinate_suzukiCurvatureSuccessorValuation_pos hn).le

/-- **Forward-cell history no-go.** The complete boundary-excursion skew vanishes on every pair
of literal forward successor curvature cells. -/
theorem suzukiCurvatureSuccessor_boundaryExcursion_skew_eq_zero
    (a : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    suzukiPrunedBoundaryExcursion a (suzukiCurvatureSuccessorValuation m)
        (suzukiCurvatureSuccessorValuation n) -
      suzukiPrunedBoundaryExcursion a (suzukiCurvatureSuccessorValuation n)
        (suzukiCurvatureSuccessorValuation m) = 0 := by
  rw [← suzukiPrunedCompression_commutator_eq_boundaryExcursion]
  exact sub_eq_zero.mpr (suzukiCurvatureSuccessorPruned_commute a hm hn)

/-- **Reflected-cell history survivor.**  The factorization of the reflected `2 → 3` curvature
cell uses the literal prime-two and reflected-prime-three legs, and those exact two legs have a
nonzero boundary-excursion skew at a physical aperture.  Thus forward curvature cells
abelianize, but the source-defined reflected two-leg carrier does not. -/
theorem exists_suzukiCurvatureSuccessorTwo_reflectedFactorized_boundaryExcursion_skew_nonzero :
    ∃ a : ℝ, 0 < a ∧
      suzukiPrunedBoundaryExcursion a (suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1))
          (-suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1)) -
        suzukiPrunedBoundaryExcursion a (-suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1))
          (suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1)) ≠ 0 := by
  obtain ⟨a, ha, hnoncommuting⟩ :=
    exists_suzukiOrientedSupportPrunedShift_primeTwo_negPrimeThree_noncommuting
  refine ⟨a, ha, ?_⟩
  intro hzero
  apply hnoncommuting
  apply sub_eq_zero.mp
  rw [suzukiPrunedCompression_commutator_eq_boundaryExcursion]
  exact hzero

end

end GaloisForLFunctions.RHTower
