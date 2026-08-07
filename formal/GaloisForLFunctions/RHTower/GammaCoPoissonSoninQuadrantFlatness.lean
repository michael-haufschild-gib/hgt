import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSyzygy
import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceDilation

/-!
# Full-quotient flatness of the co-Poisson bonding maps

Both normalized dilations carry the closed co-Poisson source space one aperture step down, so a
vector of the quotient at level `j+2` is already orthogonal to the source space at level `j+1` after
either dilation.  The source correction in the middle projection therefore drops out of both
composite paths, and each of them acts on the quotient at level `j+2` exactly as the projection onto
the quotient at level `j`.  Hence the two paths agree:

`T_j^+ T_{j+1}^- = T_j^- T_{j+1}^+`  on  `Y_{j+2}`.

No completeness theorem for the zero evaluators is used: the identity is an aperture-monotonicity
statement about the source space, not a statement about zeta zeros.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {a r : ℝ}

/-- On the extended Sonine space the quotient projection is the vector minus its source
projection. -/
theorem burnolCoPoissonQuotientProjection_eq_sub {b : ℝ} (hb : 0 < b) {v : evenSubspace}
    (hv : v ∈ soninExtendedSpace b) :
    burnolCoPoissonQuotientProjection b hb v = v - burnolCoPoissonSourceProjection b v := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  change (burnolCoPoissonQuotientSpace b).starProjection v = _
  refine (burnolCoPoissonQuotientSpace b).eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine ⟨(soninExtendedSpace b).sub_mem hv
      (burnolCoPoissonSourceSpace_le_soninExtendedSpace hb
        ((burnolCoPoissonSourceSpace b).starProjection_apply_mem v)), ?_⟩
    exact Submodule.sub_starProjection_mem_orthogonal v
  · intro w hw
    have hsub : v - (v - burnolCoPoissonSourceProjection b v) =
        burnolCoPoissonSourceProjection b v := by abel
    rw [hsub]
    exact Submodule.inner_right_of_mem_orthogonal
      (burnolCoPoissonSourceProjection_apply_mem b v) hw.2

/-- The quotient projection is self-adjoint, in the form the composite paths consume. -/
theorem inner_burnolCoPoissonQuotientProjection_swap {b : ℝ} (hb : 0 < b) (x y : evenSubspace) :
    ⟪burnolCoPoissonQuotientProjection b hb x, y⟫_ℂ =
      ⟪x, burnolCoPoissonQuotientProjection b hb y⟫_ℂ := by
  have hE := adjoint_burnolCoPoissonQuotientProjection b hb
  have key := ContinuousLinearMap.adjoint_inner_left
    (burnolCoPoissonQuotientProjection b hb) y x
  rw [hE] at key
  exact key

/-- A quotient vector two apertures up stays orthogonal to the source space after either
dilation. -/
theorem evenDilation_mem_sourceSpace_orthogonal (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    evenDilationCLM r hr x ∈ (burnolCoPoissonSourceSpace (soninAperture a r (j + 1)))ᗮ := by
  intro c hc
  have hstep : evenDilationCLM r⁻¹ (inv_pos.mpr hr) c ∈
      burnolCoPoissonSourceSpace (soninAperture a r (j + 2)) := by
    have h := evenInverseDilation_mem_coPoissonSourceSpace
      (soninAperture_pos ha hr (j + 1)) hr1 hc
    rwa [← soninAperture_succ hr (j + 1)] at h
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r hr) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) := adjoint_evenDilationCLM r hr
  have hkey := ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r hr) x c
  rw [hadj] at hkey
  rw [← hkey]
  exact Submodule.inner_right_of_mem_orthogonal hstep hx.2

theorem evenInverseDilation_mem_sourceSpace_orthogonal (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (j : ℕ) {x : evenSubspace}
    (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    evenDilationCLM r⁻¹ (inv_pos.mpr hr) x ∈
      (burnolCoPoissonSourceSpace (soninAperture a r (j + 1)))ᗮ := by
  intro c hc
  have hstep : evenDilationCLM r hr c ∈
      burnolCoPoissonSourceSpace (soninAperture a r (j + 2)) := by
    have h := evenDilation_mem_coPoissonSourceSpace
      (soninAperture_pos ha hr (j + 1)) hr1 hc
    rwa [← soninAperture_succ hr (j + 1)] at h
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) =
      evenDilationCLM r hr := by
    rw [adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
    congr 1
    exact inv_inv r
  have hkey := ContinuousLinearMap.adjoint_inner_left
    (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) x c
  rw [hadj] at hkey
  rw [← hkey]
  exact Submodule.inner_right_of_mem_orthogonal hstep hx.2

/-- Both composite paths act on the quotient two apertures up as the projection onto the quotient
below. -/
theorem inner_coPoissonQuotientForward_inverse (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2)))
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r j)) :
    ⟪coPoissonQuotientForward a r ha hr j
        (coPoissonQuotientInverse a r ha hr (j + 1) x), f⟫_ℂ = ⟪x, f⟫_ℂ := by
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hUf : evenDilationCLM r hr f ∈ soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r hr) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) := adjoint_evenDilationCLM r hr
  have hmid := burnolCoPoissonQuotientProjection_eq_sub
    (soninAperture_pos ha hr (j + 1)) hUf
  have hunit : ⟪evenDilationCLM r hr x, evenDilationCLM r hr f⟫_ℂ = ⟪x, f⟫_ℂ :=
    (evenDilationUnitary r hr).inner_map_map x f
  have hzero : ⟪evenDilationCLM r hr x,
      burnolCoPoissonSourceProjection (soninAperture a r (j + 1))
        (evenDilationCLM r hr f)⟫_ℂ = 0 := by
    have hmem := burnolCoPoissonSourceProjection_apply_mem (soninAperture a r (j + 1))
      (evenDilationCLM r hr f)
    have horth := evenDilation_mem_sourceSpace_orthogonal ha hr hr1 j hx
    rw [inner_eq_zero_symm]
    exact Submodule.inner_right_of_mem_orthogonal hmem horth
  rw [coPoissonQuotientForward, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf,
    ← hadj, ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r hr) f
      (coPoissonQuotientInverse a r ha hr (j + 1) x),
    coPoissonQuotientInverse, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_swap, hmid, inner_sub_right, hzero, sub_zero, hunit]

theorem inner_coPoissonQuotientInverse_forward (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2)))
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r j)) :
    ⟪coPoissonQuotientInverse a r ha hr j
        (coPoissonQuotientForward a r ha hr (j + 1) x), f⟫_ℂ = ⟪x, f⟫_ℂ := by
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hUf : evenDilationCLM r⁻¹ (inv_pos.mpr hr) f ∈
      soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenInverseDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) =
      evenDilationCLM r hr := by
    rw [adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
    congr 1
    exact inv_inv r
  have hmid := burnolCoPoissonQuotientProjection_eq_sub
    (soninAperture_pos ha hr (j + 1)) hUf
  have hunit : ⟪evenDilationCLM r⁻¹ (inv_pos.mpr hr) x,
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) f⟫_ℂ = ⟪x, f⟫_ℂ :=
    (evenDilationUnitary r⁻¹ (inv_pos.mpr hr)).inner_map_map x f
  have hzero : ⟪evenDilationCLM r⁻¹ (inv_pos.mpr hr) x,
      burnolCoPoissonSourceProjection (soninAperture a r (j + 1))
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) f)⟫_ℂ = 0 := by
    have hmem := burnolCoPoissonSourceProjection_apply_mem (soninAperture a r (j + 1))
      (evenDilationCLM r⁻¹ (inv_pos.mpr hr) f)
    have horth := evenInverseDilation_mem_sourceSpace_orthogonal ha hr hr1 j hx
    rw [inner_eq_zero_symm]
    exact Submodule.inner_right_of_mem_orthogonal hmem horth
  rw [coPoissonQuotientInverse, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf,
    ← hadj, ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) f
      (coPoissonQuotientForward a r ha hr (j + 1) x),
    coPoissonQuotientForward, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_swap, hmid, inner_sub_right, hzero, sub_zero, hunit]

/-- **Full-quotient flatness.**  The two-path commutator vanishes on the whole co-Poisson
quotient. -/
theorem coPoissonQuotientCommutator_eq_zero (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    coPoissonQuotientCommutator a r ha hr j x = 0 := by
  have hEq : coPoissonQuotientForward a r ha hr j
      (coPoissonQuotientInverse a r ha hr (j + 1) x) =
      coPoissonQuotientInverse a r ha hr j
        (coPoissonQuotientForward a r ha hr (j + 1) x) := by
    refine eq_of_forall_inner_eq_of_mem
      (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
      (coPoissonQuotientForward_apply_mem a r ha hr j _)
      (coPoissonQuotientInverse_apply_mem a r ha hr j _) ?_
    intro f hf
    rw [inner_coPoissonQuotientForward_inverse ha hr hr1 j hx hf,
      inner_coPoissonQuotientInverse_forward ha hr hr1 j hx hf]
  rw [coPoissonQuotientCommutator]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, hEq, sub_self]

end RHTower
