import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy

/-!
# The transverse action of the context-order kernel

The equality-pattern kernel is the constant `1 + t` on the harmonic complement of the constant
section, at every order and for every scale.  Together with the two constant-line actions this
exhibits the whole spectrum of the kernel: one eigenvalue `1 - (m-1)t` on the constant line and the
eigenvalue `1 + t` on its orthogonal complement, so the local and global fracture is a statement
about the constant line alone.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The harmonic projection annihilates exactly the balanced sections. -/
theorem simplexEffectiveHarmonicProjection_mulVec_eq_zero_iff (x : ι → ℂ) :
    _root_.HTGeometry.simplexEffectiveHarmonicProjection *ᵥ x = 0 ↔ ∑ i, x i = 0 := by
  have hcard : ((Fintype.card ι : ℂ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h
    have h0 : (_root_.HTGeometry.simplexEffectiveHarmonicProjection *ᵥ x)
        (Classical.arbitrary ι) = 0 := by rw [h]; rfl
    have hval : ((Fintype.card ι : ℂ))⁻¹ * ∑ i, x i = 0 := by
      rw [← h0]
      simp [Matrix.mulVec, dotProduct, _root_.HTGeometry.simplexEffectiveHarmonicProjection,
        ← Finset.mul_sum]
    rcases mul_eq_zero.mp hval with hz | hz
    · exact absurd (inv_eq_zero.mp hz) hcard
    · exact hz
  · intro h
    funext j
    simp [Matrix.mulVec, dotProduct, _root_.HTGeometry.simplexEffectiveHarmonicProjection,
      ← Finset.mul_sum, h]

/-- **The transverse eigenvalue.**  On the harmonic complement the context kernel acts as `1 + t`. -/
theorem contextOrderKernel_transverse_action (t : ℝ) (x : ι → ℂ)
    (hx : _root_.HTGeometry.simplexEffectiveHarmonicProjection *ᵥ x = 0) :
    contextOrderKernel (ι := ι) t *ᵥ x = ((1 + t : ℝ) : ℂ) • x := by
  rw [contextOrderKernel_decomposition, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    hx, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_zero, smul_zero, add_zero]

/-- The transverse eigenvalue in balanced-section form. -/
theorem contextOrderKernel_transverse_action_of_sum_zero (t : ℝ) (x : ι → ℂ)
    (hx : ∑ i, x i = 0) :
    contextOrderKernel (ι := ι) t *ᵥ x = ((1 + t : ℝ) : ℂ) • x :=
  contextOrderKernel_transverse_action t x
    ((simplexEffectiveHarmonicProjection_mulVec_eq_zero_iff x).mpr hx)

/-- **The transverse eigenvalue is the same at every proper context and at the full one.** -/
theorem balancedContext_local_transverse_action (r : ℕ) (x : Fin (r + 2) → ℂ)
    (hx : ∑ i, x i = 0) :
    contextOrderKernel (ι := Fin (r + 2)) (balancedContextScale r) *ᵥ x
      = ((1 + balancedContextScale r : ℝ) : ℂ) • x :=
  contextOrderKernel_transverse_action_of_sum_zero _ x hx

theorem balancedContext_global_transverse_action (r : ℕ) (x : Fin (r + 3) → ℂ)
    (hx : ∑ i, x i = 0) :
    contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r) *ᵥ x
      = ((1 + balancedContextScale r : ℝ) : ℂ) • x :=
  contextOrderKernel_transverse_action_of_sum_zero _ x hx

end

end GaloisForLFunctions.HTGeometry
