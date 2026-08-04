import Mathlib.FieldTheory.Galois.Basic
import GaloisForLFunctions.HTGeometry.NonautonomousIsogenyTransport
import GaloisForLFunctions.HTGeometry.NonautonomousStableCore

/-!
# A degree count identifies a subfield with a fixed field

Artin's theorem computes the degree of a field over the fixed field of a finite automorphism group,
with no assumption on the ambient extension.  So a subfield which is fixed by the group and has the
right degree below the field *is* the fixed field: the two are nested and equidimensional.

This turns the deck description of a covering into a numerical statement.  For a covering whose deck
group is the translations by the kernel of a map, one needs only that the kernel translations fix the
image and that the degree equals the order of the kernel — no descent theory.
-/

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Artin's degree formula without ambient finiteness.**  The field has degree the order of the
group over the fixed field of any finite automorphism group. -/
theorem finrank_fixedField_eq_card_of_finite (H : Subgroup (F ≃ₐ[K] F)) [Finite H] :
    Module.finrank (fixedField H) F = Nat.card H := by
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H F

/-- **A fixed subfield of the right degree is the whole fixed field.**  Nested and equidimensional
forces equality, so the fixed field is pinned by a degree count. -/
theorem eq_fixedField_of_le_of_finrank_eq (H : Subgroup (F ≃ₐ[K] F)) [Finite H]
    {L : IntermediateField K F} (hle : L ≤ fixedField H) [FiniteDimensional L F]
    (hrank : Module.finrank L F = Nat.card H) :
    L = fixedField H := by
  have hM : Module.finrank (extendScalars hle) F = Nat.card H :=
    finrank_fixedField_eq_card_of_finite H
  have htower : Module.finrank L (extendScalars hle)
      * Module.finrank (extendScalars hle) F = Module.finrank L F :=
    Module.finrank_mul_finrank _ _ _
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hone : Module.finrank L (extendScalars hle) = 1 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [one_mul, ← hM, htower, hrank, hM]
  have hbot : extendScalars hle = ⊥ := finrank_eq_one_iff.1 hone
  refine le_antisymm hle ?_
  intro x hx
  have hx' : x ∈ extendScalars hle := hx
  rw [hbot, IntermediateField.mem_bot] at hx'
  obtain ⟨y, rfl⟩ := hx'
  exact y.2

/-! ### The deck hypothesis of a nonautonomous protocol -/

variable {G : ℕ → Type*} [∀ i, CommGroup (G i)]

/-- **The depthwise deck description from a degree count.**  If the translations by a prefix kernel
fix the prefix image and the image has degree the order of that kernel, then the image is exactly the
fixed field of those translations — which is the hypothesis the tail theorems consume. -/
theorem prefixImage_eq_fixedField_of_finrank_eq
    (φ : ℕ → F →ₐ[K] F) (i n : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    [Finite ((prefixKernel a i n).map ρ)]
    [FiniteDimensional (IntermediateField.map (forwardPrefix φ i n) ⊤) F]
    (hfix : IntermediateField.map (forwardPrefix φ i n) ⊤ ≤
      fixedField ((prefixKernel a i n).map ρ))
    (hdeg : Module.finrank (IntermediateField.map (forwardPrefix φ i n) ⊤) F
      = Nat.card ((prefixKernel a i n).map ρ)) :
    IntermediateField.map (forwardPrefix φ i n) ⊤ = fixedField ((prefixKernel a i n).map ρ) :=
  eq_fixedField_of_le_of_finrank_eq _ hfix hdeg

/-- **Kernel translations fix the prefix image.**  If the field protocol is the pullback of the group
protocol -- translation on the source pulls back to translation by the image -- then every direction
killed by a prefix composite acts trivially on that prefix's image.  This is one half of the deck
description, and it is free: no geometry, only equivariance. -/
theorem prefixImage_le_fixedField_of_equivariant
    (φ : ℕ → F →ₐ[K] F) (i n : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F))
    (hequiv : ∀ (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y)) :
    IntermediateField.map (forwardPrefix φ i n) ⊤ ≤
      fixedField ((prefixKernel a i n).map (ρ i)) := by
  rintro x hx
  rw [IntermediateField.mem_fixedField_iff]
  rintro f hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨y, -, rfl⟩ := hx
  have hg' : prefixHom a i n g = 1 := hg
  have h := hequiv g y
  rw [hg', map_one] at h
  simpa using h

/-- **The depthwise deck description from equivariance and a degree count.**  The only geometric input
left is that the degree of a prefix equals the order of its kernel. -/
theorem prefixImage_eq_fixedField_of_equivariant_of_finrank_eq
    (φ : ℕ → F →ₐ[K] F) (i n : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F))
    [Finite ((prefixKernel a i n).map (ρ i))]
    [FiniteDimensional (IntermediateField.map (forwardPrefix φ i n) ⊤) F]
    (hequiv : ∀ (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y))
    (hdeg : Module.finrank (IntermediateField.map (forwardPrefix φ i n) ⊤) F
      = Nat.card ((prefixKernel a i n).map (ρ i))) :
    IntermediateField.map (forwardPrefix φ i n) ⊤ = fixedField ((prefixKernel a i n).map (ρ i)) :=
  eq_fixedField_of_le_of_finrank_eq _
    (prefixImage_le_fixedField_of_equivariant φ i n a ρ hequiv) hdeg

end

end GaloisForLFunctions.HTGeometry
