import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceDilation
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSection
import GaloisForLFunctions.HTGeometry.NestedProjectionConvergence

/-!
# Co-Poisson quotient dilation collapses to the Sonin aperture projection

Both normalized dilation orientations carry the closed co-Poisson source at aperture `b` into
the source at the smaller aperture `r⁻¹ b`.  By Hilbert adjunction, both orientations therefore
carry the orthogonal complement at `r⁻¹ b` back into the orthogonal complement at `b`.

Consequently the co-Poisson part of the quotient projection is identically zero after either
dilation on the actual next-aperture quotient.  On that domain the two Route R bonding maps are
exactly the corresponding normalized dilations followed only by the Sonin aperture projection.
This removes the co-Poisson source projection from the remaining dagger comparison in both Gamma
orientations; any surviving defect is a pure aperture defect.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Forward normalized dilation sends the smaller-aperture source orthogonal back into the
larger-aperture source orthogonal. -/
theorem evenDilation_mem_coPoissonSourceOrthogonal
    {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r) {f : evenSubspace}
    (hf : f ∈ (burnolCoPoissonSourceSpace (r⁻¹ * b))ᗮ) :
    evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f ∈
      (burnolCoPoissonSourceSpace b)ᗮ := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  rw [Submodule.mem_orthogonal] at hf ⊢
  intro c hc
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_evenDilationCLM]
  exact hf _ (evenInverseDilation_mem_coPoissonSourceSpace hb hr1 hc)

/-- Adjoint normalized dilation sends the smaller-aperture source orthogonal back into the
larger-aperture source orthogonal. -/
theorem evenInverseDilation_mem_coPoissonSourceOrthogonal
    {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r) {f : evenSubspace}
    (hf : f ∈ (burnolCoPoissonSourceSpace (r⁻¹ * b))ᗮ) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f ∈
      (burnolCoPoissonSourceSpace b)ᗮ := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  rw [Submodule.mem_orthogonal] at hf ⊢
  intro c hc
  rw [← ContinuousLinearMap.adjoint_inner_left,
    adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
  simp only [inv_inv]
  exact hf _ (evenDilation_mem_coPoissonSourceSpace hb hr1 hc)

/-- On a vector orthogonal to the co-Poisson source, projection to the co-Poisson quotient is
just projection to the ambient extended Sonin space. -/
theorem burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ (burnolCoPoissonSourceSpace b)ᗮ) :
    burnolCoPoissonQuotientProjection b hb f =
      burnolExtendedSoninProjection b hb f := by
  letI : Fact (0 < b) := ⟨hb⟩
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  change (burnolCoPoissonQuotientSpace b).starProjection f =
    (soninExtendedSpace b).starProjection f
  rw [burnolCoPoissonQuotientSpace,
    GaloisForLFunctions.HTGeometry.starProjection_inf_orthogonal_apply
      (burnolCoPoissonSourceSpace_le_soninExtendedSpace hb),
    (burnolCoPoissonSourceSpace b).starProjection_apply_eq_zero_iff.mpr hf, sub_zero]

/-- Both co-Poisson quotient projections collapse to Sonin projections after bilateral dilation
of an actual next-aperture quotient vector. -/
theorem burnolCoPoissonQuotientProjection_bilateralDilation_eq_soninProjection
    {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonQuotientSpace (r⁻¹ * b)) :
    burnolCoPoissonQuotientProjection b hb
        (evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f) =
        burnolExtendedSoninProjection b hb
          (evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f) ∧
      burnolCoPoissonQuotientProjection b hb
        (evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f) =
        burnolExtendedSoninProjection b hb
          (evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f) := by
  constructor
  · apply burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal hb
    exact evenDilation_mem_coPoissonSourceOrthogonal hb hr1 hf.2
  · apply burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal hb
    exact evenInverseDilation_mem_coPoissonSourceOrthogonal hb hr1 hf.2

/-- Route R's forward Gamma/co-Poisson/Sonin bonding map has no co-Poisson projection term on its
actual quotient domain. -/
theorem coPoissonQuotientForward_eq_soninProjection_of_mem_next
    {a r : ℝ} (ha : 0 < a) (hr1 : 1 ≤ r) (j : ℕ) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 1))) :
    coPoissonQuotientForward a r ha (lt_of_lt_of_le zero_lt_one hr1) j f =
      burnolExtendedSoninProjection (soninAperture a r j)
        (soninAperture_pos ha (lt_of_lt_of_le zero_lt_one hr1) j)
        (evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hf' : f ∈ burnolCoPoissonQuotientSpace
      (r⁻¹ * soninAperture a r j) := by
    rwa [← soninAperture_succ hr j]
  rw [coPoissonQuotientForward, ContinuousLinearMap.comp_apply]
  exact burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal
    (soninAperture_pos ha hr j)
    (evenInverseDilation_mem_coPoissonSourceOrthogonal
      (soninAperture_pos ha hr j) hr1 hf'.2)

/-- Route R's inverse Gamma/co-Poisson/Sonin bonding map has no co-Poisson projection term on its
actual quotient domain. -/
theorem coPoissonQuotientInverse_eq_soninProjection_of_mem_next
    {a r : ℝ} (ha : 0 < a) (hr1 : 1 ≤ r) (j : ℕ) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 1))) :
    coPoissonQuotientInverse a r ha (lt_of_lt_of_le zero_lt_one hr1) j f =
      burnolExtendedSoninProjection (soninAperture a r j)
        (soninAperture_pos ha (lt_of_lt_of_le zero_lt_one hr1) j)
        (evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hf' : f ∈ burnolCoPoissonQuotientSpace
      (r⁻¹ * soninAperture a r j) := by
    rwa [← soninAperture_succ hr j]
  rw [coPoissonQuotientInverse, ContinuousLinearMap.comp_apply]
  exact burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal
    (soninAperture_pos ha hr j)
    (evenDilation_mem_coPoissonSourceOrthogonal
      (soninAperture_pos ha hr j) hr1 hf'.2)

end RHTower
