import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFiniteEnergyLocalFEReflectionNoGo

/-!
# Parikh--Wilczek reciprocal-energy completion

Finite physical energy support cannot carry a spectrally independent local
functional-equation reverse. This file formalizes the sharp positive survivor:
reciprocal energy forces an inversion-stable support completion containing the
entire reciprocal tail, and on all positive energies the forced reciprocal map
does satisfy the two Mellin-grade reflection identities exactly.

This is a support classification, not a claim that Hawking source dynamics
supplies the completed seam or preserves its contact terms.
-/

namespace RHTower

noncomputable section

/-- Smallest positive energy completion of `(0,X)` stable under reciprocal
energy. -/
def pwMinimalReciprocalEnergyCompletion (X x : ℝ) : Prop :=
  (0 < x ∧ x < X) ∨ (0 < x⁻¹ ∧ x⁻¹ < X)

/-- The minimal completion is closed under reciprocal energy. -/
theorem pwMinimalReciprocalEnergyCompletion_inv
    (X x : ℝ) :
    pwMinimalReciprocalEnergyCompletion X x →
      pwMinimalReciprocalEnergyCompletion X x⁻¹ := by
  intro hx
  rcases hx with hx | hx
  · right
    simpa using hx
  · left
    exact hx

/-- Every point in the reciprocal completion is nonzero. -/
theorem pwMinimalReciprocalEnergyCompletion_ne_zero
    {X x : ℝ} (hx : pwMinimalReciprocalEnergyCompletion X x) : x ≠ 0 := by
  rcases hx with hx | hx
  · exact ne_of_gt hx.1
  · intro hzero
    simp [hzero] at hx

/-- Every inversion-closed extension of the physical interval contains its
minimal reciprocal completion. -/
theorem pwMinimalReciprocalEnergyCompletion_subset
    {X : ℝ} {S : ℝ → Prop}
    (hinterior : ∀ x : ℝ, 0 < x → x < X → S x)
    (hinv : ∀ x : ℝ, x ≠ 0 → S x → S x⁻¹) :
    ∀ x : ℝ, pwMinimalReciprocalEnergyCompletion X x → S x := by
  intro x hx
  rcases hx with hx | hx
  · exact hinterior x hx.1 hx.2
  · have hsource : S x⁻¹ := hinterior x⁻¹ hx.1 hx.2
    have hne : x⁻¹ ≠ 0 := ne_of_gt hx.1
    have hback := hinv x⁻¹ hne hsource
    simpa using hback

/-- The reciprocal tail beyond `X⁻¹` is forced into every inversion-closed
extension of `(0,X)`. -/
theorem pwReciprocalTail_forced
    {X : ℝ} (hX : 0 < X) {S : ℝ → Prop}
    (hinterior : ∀ x : ℝ, 0 < x → x < X → S x)
    (hinv : ∀ x : ℝ, x ≠ 0 → S x → S x⁻¹)
    {y : ℝ} (hy : X⁻¹ < y) : S y := by
  have hy0 : 0 < y := lt_trans (inv_pos.mpr hX) hy
  have hyinvX : y⁻¹ < X := (inv_lt_comm₀ hy0 hX).2 hy
  have hsource : S y⁻¹ := hinterior y⁻¹ (inv_pos.mpr hy0) hyinvX
  have hne : y⁻¹ ≠ 0 := inv_ne_zero hy0.ne'
  have hback := hinv y⁻¹ hne hsource
  simpa using hback

/-- A spectrally independent reciprocal-energy reverse on all positive
energies, satisfying the two Mellin-grade identities that force reflection. -/
structure PWGlobalReciprocalFEReflectionData where
  energyMap : ℝ → ℝ
  weight : ℝ → ℝ
  mapsPositive : ∀ {x : ℝ}, 0 < x → 0 < energyMap x
  mellinGradeOne : ∀ {x : ℝ}, 0 < x → weight x = x⁻¹
  mellinGradeTwo : ∀ {x : ℝ}, 0 < x →
    weight x * energyMap x = x⁻¹ ^ (2 : ℕ)

/-- The forced reciprocal map and weight realize the global two-grade
functional-equation reverse. -/
def pwGlobalReciprocalFEReflectionData : PWGlobalReciprocalFEReflectionData where
  energyMap := fun x => x⁻¹
  weight := fun x => x⁻¹
  mapsPositive := by
    intro x hx
    exact inv_pos.mpr hx
  mellinGradeOne := by
    intro x hx
    rfl
  mellinGradeTwo := by
    intro x hx
    simp only [pow_two]

/-- The global reciprocal two-grade reflection datum exists unconditionally. -/
theorem nonempty_PWGlobalReciprocalFEReflectionData :
    Nonempty PWGlobalReciprocalFEReflectionData :=
  ⟨pwGlobalReciprocalFEReflectionData⟩

end

end RHTower
