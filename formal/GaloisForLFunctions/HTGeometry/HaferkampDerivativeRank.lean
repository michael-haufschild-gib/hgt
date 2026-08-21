import GaloisForLFunctions.HTGeometry.HaferkampAmbientProductDerivative

/-!
# Rank lower bounds from independent circuit-derivative images

This finite-dimensional linear-algebra bridge is the terminal step of the
Appendix-B rank induction: once one derivative image has been produced for
each selected independent Pauli direction, the derivative range has at least
that many complex dimensions.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A complex-linear map whose images of `T` supplied directions are linearly
independent has range finrank at least `T`. -/
theorem finrank_range_ge_of_linearIndependent_images
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {T : ℕ} (D : V →ₗ[ℂ] W) (directions : Fin T → V)
    (himages : LinearIndependent ℂ (fun i => D (directions i))) :
    T ≤ Module.finrank ℂ D.range := by
  let values : Fin T → D.range := fun i => ⟨D (directions i), ⟨directions i, rfl⟩⟩
  have hcomp : LinearIndependent ℂ (D.range.subtype ∘ values) := by
    simpa [values, Function.comp_def] using himages
  have hvalues : LinearIndependent ℂ values :=
    LinearIndependent.of_comp D.range.subtype hcomp
  calc
    T = (Set.range values).finrank ℂ := by
      simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range values)) := rfl
    _ ≤ Module.finrank ℂ D.range := Submodule.finrank_le _

/-- Nonzero pointwise complex rescaling preserves a finite independent family.
This is used after stripping the circuit's total unitary from the Appendix-B
derivative images. -/
theorem linearIndependent_smul_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
  {T : Type*} (v : T → V) (hv : LinearIndependent ℂ v)
    (c : T → ℂ) (hc : ∀ i, c i ≠ 0) :
    LinearIndependent ℂ (fun i => c i • v i) := by
  let u : T → ℂˣ := fun i => Units.mk0 (c i) (hc i)
  rw [show (fun i => c i • v i) = u • v by
    funext i
    simp [u, Pi.smul_apply']]
  exact hv.units_smul u

end GaloisForLFunctions.HTGeometry
