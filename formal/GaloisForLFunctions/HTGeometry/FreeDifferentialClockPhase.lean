import GaloisForLFunctions.HTGeometry.DifferentialVariationalBoundaryPair
import GaloisForLFunctions.HTGeometry.FreeDifferentialBoundedOrbit

/-!
# The intrinsic clock phase in the free differential field

This leaf states the variational phase law in the coordinates the card's Theorem C uses: the
differential order `ord_x(σⁿ)` of a reversible finite-rank clock.

* `freeDifferentialOrderTranslationLength_eq_zero_iff` — the intrinsic clock speed
  `ell_delta(σ) = lim ord_x(σⁿ)/n` vanishes exactly when `ord_x(σⁿ)` is bounded.  The
  order-oriented Cartan vector is antitone with zero sum, so its vanishing top coordinate forces the
  whole vector to vanish; the zero-speed theorem then produces a bounded Euclidean orbit, which the
  corpus comparison converts back into bounded differential order.
* `freeDifferentialOrderTranslationLength_pos_iff` — **the sharp gap `(21)`**: differential-order
  growth is either bounded or genuinely linear, with no unbounded sublinear regime.
* `freeDifferential_boundaryPair_iff` — **`(22)`**: the intrinsic clock speed is strictly positive
  exactly when `σ` carries the canonical boundary pair, a proper attracting subspace together with a
  proper repelling subspace of the completed coordinate space.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C] {r : ℕ}

/-- The order-oriented and forward Cartan translation vectors vanish together. -/
theorem freeDifferentialReverseCartanTranslationVector_eq_zero_iff
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    freeDifferentialReverseCartanTranslationVector σ = 0 ↔
      differentialVariationalCartanTranslationVector
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ = 0 := by
  constructor
  · intro h
    funext j
    have := congrFun h j.rev
    simp only [freeDifferentialReverseCartanTranslationVector, Fin.rev_rev,
      Pi.zero_apply, neg_eq_zero] at this
    exact this
  · intro h
    funext i
    simp only [freeDifferentialReverseCartanTranslationVector, Pi.zero_apply,
      neg_eq_zero]
    exact congrFun h i.rev

/-- **Free differential-order speed vanishes exactly in the bounded phase.** -/
theorem freeDifferentialOrderTranslationLength_eq_zero_iff
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    freeOrderGauge.translationLength σ = 0 ↔ FreeDifferentialOrderPowersBounded σ := by
  classical
  constructor
  · intro h
    have h0 : freeDifferentialReverseCartanTranslationVector σ 0 = 0 := by
      rw [← freeDifferentialOrderTranslationLength_eq_reverseCartan_zero]
      exact h
    have hanti := freeDifferentialReverseCartanTranslationVector_antitone σ
    have hsum := freeDifferentialReverseCartanTranslationVector_sum_eq_zero σ
    have hle : ∀ i, freeDifferentialReverseCartanTranslationVector σ i ≤ 0 := by
      intro i
      rw [← h0]
      exact hanti (Fin.zero_le i)
    have hzero : freeDifferentialReverseCartanTranslationVector σ = 0 := by
      funext i
      by_contra hne
      have hlt : freeDifferentialReverseCartanTranslationVector σ i < 0 :=
        lt_of_le_of_ne (hle i) hne
      have hstrict : ∑ j, freeDifferentialReverseCartanTranslationVector σ j <
          ∑ _j : Fin (r + 1), (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
      rw [hsum] at hstrict
      simp at hstrict
    have hcartan :=
      (freeDifferentialReverseCartanTranslationVector_eq_zero_iff σ).1 hzero
    have hTL :=
      (differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ).2 hcartan
    have hbounded :=
      differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ hTL
    exact (freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded σ).1 hbounded
  · intro h
    have hbounded : DifferentialVariationalEuclideanOrbitBounded
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ :=
      (freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded σ).2 h
    have hcartan :=
      differentialVariationalEuclideanOrbitBounded_implies_cartanVector_eq_zero
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ hbounded
    have hzero := (freeDifferentialReverseCartanTranslationVector_eq_zero_iff σ).2 hcartan
    rw [freeDifferentialOrderTranslationLength_eq_reverseCartan_zero, hzero]
    rfl

/-- **The exact rank-two free-field gap `(21)`.**  Differential-order growth of a reversible
finite-rank clock is either bounded or genuinely linear. -/
theorem freeDifferentialOrderTranslationLength_pos_iff
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    0 < freeOrderGauge.translationLength σ ↔ ¬ FreeDifferentialOrderPowersBounded σ := by
  constructor
  · intro hpos hb
    rw [(freeDifferentialOrderTranslationLength_eq_zero_iff σ).2 hb] at hpos
    exact lt_irrefl 0 hpos
  · intro hb
    refine lt_of_le_of_ne (freeDifferentialOrderTranslationLength_nonneg σ) ?_
    intro hzero
    exact hb ((freeDifferentialOrderTranslationLength_eq_zero_iff σ).1 hzero.symm)

omit [CharZero C] in
/-- The free base point is the projective class of the standard lattice. -/
theorem freeDifferentialProjectiveBasePoint_eq_mk (n : ℕ) :
    freeDifferentialProjectiveBasePoint (C := C) n =
      Quotient.mk _ (DiffOp.standardCompletedPseudoDiffOpLattice
        (K := JetField C (Fin n)) (ι := Fin n)) := rfl

/-- **`(22)` in the free differential field.**  The intrinsic clock speed is strictly positive
exactly when the automorphism carries the canonical boundary pair. -/
theorem freeDifferential_boundaryPair_iff
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    (variationalAttractingSubspace σ
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) ≠ ⊤ ∧
        variationalRepellingSubspace σ
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) ≠ ⊤) ↔
      0 < freeOrderGauge.translationLength σ := by
  rw [variationalBoundaryPair_iff, freeDifferentialOrderTranslationLength_pos_iff,
    ← freeDifferentialProjectiveBasePoint_eq_mk]
  constructor
  · intro hpos hb
    have hzero :=
      differentialVariationalEuclideanOrbitBounded_implies_translationLength_eq_zero
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ
        ((freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded σ).2 hb)
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · intro hb
    refine lt_of_le_of_ne
      ((differentialVariationalEuclideanOrbitGauge
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1))).translationLength_nonneg σ) ?_
    intro hzero
    exact hb ((freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded σ).1
      (differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ hzero.symm))

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
