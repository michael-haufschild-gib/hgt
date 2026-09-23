import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicMarkedBoundary

/-!
# Literal source boundary for the matched--quantile parabolic codiagonal

The matched-minus-quantile parabolic codiagonal has zero mass, so every unmarked self- or
cross-form is blind to its second coordinate.  This module constructs the only relevant port from
the literal source itself: the sum of the matched and quantile moment carriers.  Its pairing with
the codiagonal is a difference of full parabolic forms, and hence a strict off-diagonal sum of
the actual cross-cell transport kernels.  The diagonal cells cancel identically.

No sign or cofinal estimate is assumed or asserted.  The resulting strict-cross kernel is the
precise source quantity which must be controlled to advance the third-grade Cesàro route.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Finite sum of literal matched parabolic cells. -/
def ccmActualHeadMatchedParabolicAggregate (K : ℕ) : Fin 3 → ℝ :=
  ∑ n ∈ Finset.range (K + 1), ccmActualHeadMatchedParabolicMoment (n + 2)

/-- Finite sum of the equal-mass literal quantile parabolic cells. -/
def ccmActualHeadQuantileParabolicAggregate (K : ℕ) : Fin 3 → ℝ :=
  ∑ n ∈ Finset.range (K + 1), ccmActualHeadQuantileParabolicMoment (n + 2)

/-- The nonzero-mass source boundary formed without adding any external datum. -/
def ccmActualHeadMatchedQuantileParabolicSourceBoundary (K : ℕ) : Fin 3 → ℝ :=
  ccmActualHeadMatchedParabolicAggregate K +
    ccmActualHeadQuantileParabolicAggregate K

/-- Total critical-Mellin mass of the finite physical head. -/
def ccmActualHeadParabolicMass (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2)

/-- The existing codiagonal is literally the difference of the two source aggregates. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_eq_aggregate_sub (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K =
      ccmActualHeadMatchedParabolicAggregate K -
        ccmActualHeadQuantileParabolicAggregate K := by
  rfl

theorem ccmActualHeadMatchedParabolicAggregate_zero (K : ℕ) :
    ccmActualHeadMatchedParabolicAggregate K 0 = ccmActualHeadParabolicMass K := by
  simp [ccmActualHeadMatchedParabolicAggregate, ccmActualHeadParabolicMass,
    ccmActualHeadMatchedParabolicMoment_zero]

theorem ccmActualHeadQuantileParabolicAggregate_zero (K : ℕ) :
    ccmActualHeadQuantileParabolicAggregate K 0 = ccmActualHeadParabolicMass K := by
  simp [ccmActualHeadQuantileParabolicAggregate, ccmActualHeadParabolicMass,
    ccmActualHeadQuantileParabolicMoment_zero]

/-- The literal source boundary has twice the finite head mass, so it can observe the hidden
second codiagonal coordinate. -/
theorem ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0 =
      2 * ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadMatchedQuantileParabolicSourceBoundary]
  simp only [Pi.add_apply]
  rw [ccmActualHeadMatchedParabolicAggregate_zero,
    ccmActualHeadQuantileParabolicAggregate_zero]
  ring

theorem ccmParabolicPairing_sub_add_eq_form_sub (v w : Fin 3 → ℝ) :
    ccmParabolicPairing (v - w) (v + w) =
      ccmParabolicForm v - ccmParabolicForm w := by
  simp only [ccmParabolicPairing, ccmParabolicForm, Pi.sub_apply, Pi.add_apply]
  ring

/-- The source boundary pairing is exactly the difference of complete matched and quantile
parabolic forms. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        ccmParabolicForm (ccmActualHeadQuantileParabolicAggregate K) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_eq_aggregate_sub,
    ccmActualHeadMatchedQuantileParabolicSourceBoundary]
  exact ccmParabolicPairing_sub_add_eq_form_sub _ _

/-- The literal source-form difference observes the second codiagonal coordinate, while
retaining the visible first coordinate and the actual source-boundary coefficient. -/
theorem ccmActualHeadMatchedQuantileParabolicSourceBoundary_observes_two (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        ccmParabolicForm (ccmActualHeadQuantileParabolicAggregate K) =
      (2 * ccmActualHeadParabolicMass K) *
          ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 -
        ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 *
          ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 := by
  rw [← ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing]
  rw [ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero]

theorem ccmParabolicPairing_add_left (u v w : Fin 3 → ℝ) :
    ccmParabolicPairing (u + v) w =
      ccmParabolicPairing u w + ccmParabolicPairing v w := by
  simp only [ccmParabolicPairing, Pi.add_apply]
  ring

theorem ccmParabolicPairing_add_right (u v w : Fin 3 → ℝ) :
    ccmParabolicPairing u (v + w) =
      ccmParabolicPairing u v + ccmParabolicPairing u w := by
  simp only [ccmParabolicPairing, Pi.add_apply]
  ring

theorem ccmParabolicPairing_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Fin 3 → ℝ) (w : Fin 3 → ℝ) :
    ccmParabolicPairing (∑ i ∈ s, f i) w =
      ∑ i ∈ s, ccmParabolicPairing (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ccmParabolicPairing]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ccmParabolicPairing_add_left, ih]

theorem ccmParabolicPairing_sum_right {ι : Type*} (v : Fin 3 → ℝ)
    (s : Finset ι) (f : ι → Fin 3 → ℝ) :
    ccmParabolicPairing v (∑ i ∈ s, f i) =
      ∑ i ∈ s, ccmParabolicPairing v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ccmParabolicPairing]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ccmParabolicPairing_add_right, ih]

theorem ccmActualHeadMatchedParabolicAggregate_form (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (K + 1),
        ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment (m + 2))
          (ccmActualHeadMatchedParabolicMoment (n + 2)) := by
  rw [ccmParabolicForm_eq_pairing_self]
  unfold ccmActualHeadMatchedParabolicAggregate
  rw [ccmParabolicPairing_sum_left]
  apply Finset.sum_congr rfl
  intro m hm
  exact ccmParabolicPairing_sum_right _ _ _

theorem ccmActualHeadQuantileParabolicAggregate_form (K : ℕ) :
    ccmParabolicForm (ccmActualHeadQuantileParabolicAggregate K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (K + 1),
        ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment (m + 2))
          (ccmActualHeadQuantileParabolicMoment (n + 2)) := by
  rw [ccmParabolicForm_eq_pairing_self]
  unfold ccmActualHeadQuantileParabolicAggregate
  rw [ccmParabolicPairing_sum_left]
  apply Finset.sum_congr rfl
  intro m hm
  exact ccmParabolicPairing_sum_right _ _ _

/-- Full source-form difference, expanded as a double sum before diagonal cancellation. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_doubleCross
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (K + 1),
        (ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment (m + 2))
          (ccmActualHeadMatchedParabolicMoment (n + 2)) -
        ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment (m + 2))
          (ccmActualHeadQuantileParabolicMoment (n + 2))) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadMatchedParabolicAggregate_form,
    ccmActualHeadQuantileParabolicAggregate_form]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_sub_distrib]

theorem ccmActualHeadQuantileParabolicPairing_self_eq_matched (n : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment n)
        (ccmActualHeadMatchedParabolicMoment n) =
      ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment n)
        (ccmActualHeadQuantileParabolicMoment n) := by
  rw [← ccmParabolicForm_eq_pairing_self, ← ccmParabolicForm_eq_pairing_self]
  exact (ccmActualHeadQuantileParabolicForm_eq_matched n).symm

/-- **Diagonal-cancellation law.** The source boundary pairing receives no contribution from an
individual matched/quantile cell; only interactions between distinct physical cells survive. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        (ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment (m + 2))
          (ccmActualHeadMatchedParabolicMoment (n + 2)) -
        ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment (m + 2))
          (ccmActualHeadQuantileParabolicMoment (n + 2))) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_doubleCross]
  apply Finset.sum_congr rfl
  intro m hm
  have hmem : m ∈ Finset.range (K + 1) := hm
  rw [← Finset.sum_erase_add (Finset.range (K + 1))
    (fun n =>
      ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment (m + 2))
          (ccmActualHeadMatchedParabolicMoment (n + 2)) -
        ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment (m + 2))
          (ccmActualHeadQuantileParabolicMoment (n + 2))) hmem]
  rw [ccmActualHeadQuantileParabolicPairing_self_eq_matched]
  ring

/-- Exact oriented cross-cell kernel: signed displacement--moment transport, minus its unavoidable
quadratic displacement debt. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernel (m n : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment m)
        (ccmActualHeadMatchedParabolicMoment n) -
      ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment m)
        (ccmActualHeadQuantileParabolicMoment n) =
      -(ccmActualHeadMatchedQuantilePolarDisplacement n -
          ccmActualHeadMatchedQuantilePolarDisplacement m) *
        (ccmActualHeadMatchedParabolicMoment m 0 *
            ccmActualHeadMatchedParabolicMoment n 1 -
          ccmActualHeadMatchedParabolicMoment m 1 *
            ccmActualHeadMatchedParabolicMoment n 0) -
      (ccmActualHeadMatchedQuantilePolarDisplacement n -
          ccmActualHeadMatchedQuantilePolarDisplacement m) ^ (2 : ℕ) / 2 *
        (criticalMellinAtomWeight m * criticalMellinAtomWeight n) := by
  rw [ccmActualHeadQuantileParabolicPairing_transport]
  ring

/-- Exact source-level hard core: a literal nonzero-mass boundary reads the hidden codiagonal
coordinate through the complete strict cross-cell oriented transport, with every quadratic debt
retained. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_crossKernel
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        (-(ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
          (ccmActualHeadMatchedParabolicMoment (m + 2) 0 *
              ccmActualHeadMatchedParabolicMoment (n + 2) 1 -
            ccmActualHeadMatchedParabolicMoment (m + 2) 1 *
              ccmActualHeadMatchedParabolicMoment (n + 2) 0) -
        (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) ^ (2 : ℕ) / 2 *
          (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2))) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedQuantileParabolicCrossKernel (m + 2) (n + 2)

end RHTower
