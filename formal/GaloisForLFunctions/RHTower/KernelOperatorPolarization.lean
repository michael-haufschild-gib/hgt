import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Polarization of the Hilbert–Schmidt energy of a kernel operator

`hsNormSq_kernelOperator_eq_norm_sq` computes the Hilbert–Schmidt energy of a kernel operator as
the `L²` energy of its field.  This file polarizes that identity: the Hilbert–Schmidt inner product
of two kernel operators is the integral of the pointwise pairing of the two fields, read through
the Riesz isometry.  Because `E →L[ℂ] ℂ` carries no inner product instance the pairing is written
on the Riesz vectors, where the conjugate linearity of `toDual.symm` exchanges the two arguments.
-/

open MeasureTheory Filter Topology

namespace RHTower

noncomputable section

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

section Kernel

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure α) [IsFiniteMeasure μ]

/-- The pointwise polarization of a kernel operator: the inner product of the two images is the
integral of the pointwise pairing of the two fields. -/
theorem inner_kernelOperator_apply (K L : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    (inner ℂ (kernelOperator (E := E) μ K e) (kernelOperator (E := E) μ L e) : ℂ)
      = ∫ x, (inner ℂ (K x e) (L x e) : ℂ) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hK := (evalBilinear (𝕜 := ℂ) (E := E)).coeFn_holder
    (r := (2 : ENNReal)) K (Lp.const ∞ μ e)
  have hL := (evalBilinear (𝕜 := ℂ) (E := E)).coeFn_holder
    (r := (2 : ENNReal)) L (Lp.const ∞ μ e)
  have hconst := Lp.coeFn_const (p := ∞) μ e
  filter_upwards [hK, hL, hconst] with x hKx hLx hcx
  show (inner ℂ ((kernelOperator (E := E) μ K e : Lp ℂ 2 μ) x)
      ((kernelOperator (E := E) μ L e : Lp ℂ 2 μ) x) : ℂ) = _
  rw [kernelOperator, kernelOperatorMap_apply, kernelOperator, kernelOperatorMap_apply,
    hKx, hLx, hcx]
  simp [evalBilinear]

end Kernel

end

end RHTower
