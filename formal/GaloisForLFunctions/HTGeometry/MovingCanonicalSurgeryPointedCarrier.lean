import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicOrbitInvariance
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalSurgery

/-!
# Pointed-carrier invariance under canonical-product surgery

Exact finite canonical and even-canonical surgery changes each translated
generator by an element of the embedded rational coordinate field.  Hence
the pointed generator class modulo `ℂ(z)` is unchanged at every shift.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Ordinary canonical surgery preserves the pointed generator class
modulo the embedded rational coordinate field at every translation. -/
theorem movingCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRationalGaugeClass
        (movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t h) =
      upperEndRationalGaugeClass
        (movingCanonicalTranslatedUpperEndMero θ h) := by
  letI := isDomain_upperEndAnalyticSubring
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq_iff_sub_mem,
    movingCanonicalSurgeryTranslateFamily_eq_add_rational,
    add_sub_cancel_left]
  exact upperEndRatfuncToMero_mem_rationalCoordinateField _

/-- Even canonical surgery preserves the pointed generator class
modulo the embedded rational coordinate field at every translation. -/
theorem movingEvenCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRationalGaugeClass
        (movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t h) =
      upperEndRationalGaugeClass
        (movingEvenCanonicalTranslatedUpperEndMero θ h) := by
  letI := isDomain_upperEndAnalyticSubring
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq_iff_sub_mem,
    movingEvenCanonicalSurgeryTranslateFamily_eq_add_rational,
    add_sub_cancel_left]
  exact upperEndRatfuncToMero_mem_rationalCoordinateField _

/-- No invariant of the pointed ordinary-canonical generator class
modulo `ℂ(z)` can recover the finite surgery count. -/
theorem
    no_movingCanonicalSurgeryCount_selector_of_rationalGaugeClass
    (θ : BoundedRealSequence) :
    ¬ ∃ S : upperEndMeroModuloRationalCoordinate → ℕ,
      ∀ (k : ℕ) (aIdx bIdx : Fin k → ℕ)
        (t : Fin k → ℂ),
        S (upperEndRationalGaugeClass
          (movingCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t 0)) = k := by
  letI := isDomain_upperEndAnalyticSubring
  rintro ⟨S, hS⟩
  let a0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let b0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let t0 : Fin 0 → ℂ := fun i => Fin.elim0 i
  let a1 : Fin 1 → ℕ := fun _ => 0
  let b1 : Fin 1 → ℕ := fun _ => 1
  let t1 : Fin 1 → ℂ := fun _ => Complex.I
  have h0 := hS 0 a0 b0 t0
  have h1 := hS 1 a1 b1 t1
  have hclass :
      upperEndRationalGaugeClass
          (movingCanonicalSurgeryTranslateFamily
            θ a0 b0 t0 0) =
        upperEndRationalGaugeClass
          (movingCanonicalSurgeryTranslateFamily
            θ a1 b1 t1 0) :=
    (movingCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
      θ a0 b0 t0 0).trans
      (movingCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
        θ a1 b1 t1 0).symm
  have : (0 : ℕ) = 1 := by
    rw [← h0, ← h1, hclass]
  omega

/-- No invariant of the pointed even-canonical generator class
modulo `ℂ(z)` can recover the exact even surgery index `2k`. -/
theorem
    no_movingEvenCanonicalSurgeryIndex_selector_of_rationalGaugeClass
    (θ : BoundedRealSequence) :
    ¬ ∃ S : upperEndMeroModuloRationalCoordinate → ℕ,
      ∀ (k : ℕ) (aIdx bIdx : Fin k → ℕ)
        (t : Fin k → ℂ),
        S (upperEndRationalGaugeClass
          (movingEvenCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t 0)) = k + k := by
  letI := isDomain_upperEndAnalyticSubring
  rintro ⟨S, hS⟩
  let a0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let b0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let t0 : Fin 0 → ℂ := fun i => Fin.elim0 i
  let a1 : Fin 1 → ℕ := fun _ => 0
  let b1 : Fin 1 → ℕ := fun _ => 1
  let t1 : Fin 1 → ℂ := fun _ => 1 + Complex.I
  have h0 := hS 0 a0 b0 t0
  have h1 := hS 1 a1 b1 t1
  have hclass :
      upperEndRationalGaugeClass
          (movingEvenCanonicalSurgeryTranslateFamily
            θ a0 b0 t0 0) =
        upperEndRationalGaugeClass
          (movingEvenCanonicalSurgeryTranslateFamily
            θ a1 b1 t1 0) :=
    (movingEvenCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
      θ a0 b0 t0 0).trans
      (movingEvenCanonicalSurgeryTranslateFamily_rationalGaugeClass_eq
        θ a1 b1 t1 0).symm
  have hcount : (0 : ℕ) + 0 = 1 + 1 := by
    rw [← h0, ← h1, hclass]
  omega

end

end GaloisForLFunctions.HTGeometry
