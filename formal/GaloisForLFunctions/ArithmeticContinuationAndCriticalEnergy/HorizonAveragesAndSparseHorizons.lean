import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# Horizon averages and sparse horizons suffice

Admission asks for a bound on the energy at *every* observation horizon.  The critical energy is
nondecreasing in the horizon, because each horizon adds one pronic cell, and monotonicity converts
far weaker data into admission:

* a bound along any cofinal set of horizons — dyadic horizons, say — is admission
  (`Admits.of_cofinal_horizons`, `Admits.of_dyadic_horizons`);
* a bound on the **Cesàro means** over horizons is admission, with the loss of a factor two
  (`Admits.of_cesaro`), and conversely admission bounds the means, so the two are equivalent
  (`admits_iff_cesaro`).

This matters because mean values over a growing range are what the analytic machinery produces,
while a bound at every single horizon is not.  The reduction is exact: no horizon-uniform bound is
being assumed, only a bound on the averages.

Both statements are proved for an arbitrary horizon-monotone family and then instantiated at the
damped Möbius critical energy, giving the corresponding criteria for the Riemann hypothesis
(`riemannHypothesis_of_cofinal_cesaro`, `riemannHypothesis_of_cofinal_dyadic`).
-/

open Finset RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {E : ℝ → ℕ → ℝ} {ε C : ℝ}

/-! ## §1. Sparse horizons -/

/-- **A bound along cofinal horizons is admission.**  Monotonicity in the horizon fills the gaps. -/
theorem Admits.of_cofinal_horizons (hmono : Monotone (E ε)) {s : ℕ → ℕ}
    (hs : ∀ T : ℕ, ∃ j, T ≤ s j) (hC : ∀ j, E ε (s j) ≤ C) : Admits E ε := by
  refine ⟨C, fun T => ?_⟩
  obtain ⟨j, hj⟩ := hs T
  exact (hmono hj).trans (hC j)

/-- Dyadic horizons suffice. -/
theorem Admits.of_dyadic_horizons (hmono : Monotone (E ε))
    (hC : ∀ j : ℕ, E ε (2 ^ j) ≤ C) : Admits E ε :=
  Admits.of_cofinal_horizons hmono (fun T => ⟨T, Nat.le_of_lt (Nat.lt_two_pow_self)⟩) hC

/-! ## §2. Horizon averages -/

/-- **Cesàro bounds over horizons are admission.**  Monotonicity turns an average bound into a
pointwise one at the cost of a factor two: the second half of the range already carries more than
half the mass. -/
theorem Admits.of_cesaro (hmono : Monotone (E ε)) (hpos : ∀ T, 0 ≤ E ε T)
    (hC : ∀ N : ℕ, (∑ T ∈ range (N + 1), E ε T) ≤ C * ((N : ℝ) + 1)) : Admits E ε := by
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, mul_one] at h0
    exact le_trans (hpos 0) h0
  refine ⟨2 * C, fun M => ?_⟩
  -- the horizons from `M` to `2M+1` all carry at least `E ε M`
  have hsub : Ico M (2 * M + 2) ⊆ range (2 * M + 2) := by
    intro T hT
    rw [mem_Ico] at hT
    exact mem_range.mpr hT.2
  have hlow : ((Ico M (2 * M + 2)).card : ℝ) * E ε M ≤ ∑ T ∈ Ico M (2 * M + 2), E ε T := by
    have h := Finset.card_nsmul_le_sum (Ico M (2 * M + 2)) (E ε) (E ε M)
      fun T hT => hmono (mem_Ico.mp hT).1
    simpa [nsmul_eq_mul] using h
  have hpart : (∑ T ∈ Ico M (2 * M + 2), E ε T) ≤ ∑ T ∈ range (2 * M + 2), E ε T :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => hpos T
  have htot := hC (2 * M + 1)
  have hcast : (((2 * M + 1 : ℕ) : ℝ) + 1) = 2 * (M : ℝ) + 2 := by push_cast; ring
  rw [hcast] at htot
  have hcard : ((Ico M (2 * M + 2)).card : ℝ) = (M : ℝ) + 2 := by
    rw [Nat.card_Ico]
    have h : 2 * M + 2 - M = M + 2 := by omega
    rw [h]
    push_cast
    ring
  rw [hcard] at hlow
  have hsum : (2 * M + 1 : ℕ) + 1 = 2 * M + 2 := by omega
  rw [hsum] at htot
  have hM2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
  have hkey : ((M : ℝ) + 2) * E ε M ≤ C * (2 * (M : ℝ) + 2) := by linarith
  have hfinal : ((M : ℝ) + 2) * E ε M ≤ ((M : ℝ) + 2) * (2 * C) := by nlinarith
  exact le_of_mul_le_mul_left (by linarith [hfinal]) hM2

/-- Admission bounds the horizon averages, so the averaged form is equivalent. -/
theorem admits_iff_cesaro (hmono : Monotone (E ε)) (hpos : ∀ T, 0 ≤ E ε T) :
    Admits E ε ↔ ∃ C : ℝ, ∀ N : ℕ, (∑ T ∈ range (N + 1), E ε T) ≤ C * ((N : ℝ) + 1) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, fun N => ?_⟩
    calc (∑ T ∈ range (N + 1), E ε T) ≤ ∑ _T ∈ range (N + 1), max B 0 :=
          sum_le_sum fun T _ => (hB T).trans (le_max_left B 0)
      _ = max B 0 * ((N : ℝ) + 1) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  · rintro ⟨C, hC⟩
    exact Admits.of_cesaro hmono hpos hC

/-! ## §3. The arithmetic criteria -/

/-- **Cofinal Cesàro bounds give the Riemann hypothesis.**  At dampings accumulating at zero only
the horizon averages of the critical energy have to be bounded. -/
theorem riemannHypothesis_of_cofinal_cesaro
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ C : ℝ, ∀ N : ℕ,
      (∑ T ∈ range (N + 1), dampedMobiusEnergy ε T) ≤ C * ((N : ℝ) + 1)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, C, hC⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ, Admits.of_cesaro (dampedMobiusEnergy_mono ε)
    (fun T => dampedMobiusEnergy_nonneg ε T) hC⟩

/-- **Cofinal dyadic bounds give the Riemann hypothesis.** -/
theorem riemannHypothesis_of_cofinal_dyadic
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ C : ℝ, ∀ j : ℕ,
      dampedMobiusEnergy ε (2 ^ j) ≤ C) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, C, hC⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ, Admits.of_dyadic_horizons (dampedMobiusEnergy_mono ε) hC⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
