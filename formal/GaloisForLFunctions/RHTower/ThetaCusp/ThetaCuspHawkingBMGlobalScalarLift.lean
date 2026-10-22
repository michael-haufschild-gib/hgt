import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalDistributionEquation

/-!
The original quotient L² vector has an actual modular scalar lift, native identification, and L² control on every compact chart.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- Only finitely many modular pullbacks from a compact chart meet the full
closed cell, although the cell itself has a noncompact cusp. -/
theorem compact_cell_pullbacks_finite (K : Set UpperHalfPlane) (hK : IsCompact K) :
    ∃ s : Finset PSL2Z, ∀ γ ∉ s, ∀ z ∈ K, γ • z ∉ fd := by
  classical
  have hc : Continuous (fun z : UpperHalfPlane => max z.im (1/z.im)) :=
    UpperHalfPlane.continuous_im.max (continuous_const.div UpperHalfPlane.continuous_im
      (fun z => z.im_ne_zero))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    hK (truncated_cell_compact M)
  refine ⟨hfin.toFinset,?_⟩
  intro γ hγ z hz hfd
  apply hγ
  simp only [Set.Finite.mem_toFinset]
  refine ⟨γ • z,⟨z,hz,rfl⟩,hfd,?_⟩
  exact (modular_orbit_height_le γ z).trans ((le_abs_self _).trans (hM z hz))

/-- The actual scalar L² representative extended by zero from the open cell. -/
def cellExtension (u : Space) : UpperHalfPlane → ℂ := fdo.indicator u

/-- The full modular scalar lift of the original quotient L² vector. -/
def globalLift (u : Space) : UpperHalfPlane → ℂ := periodize (cellExtension u)

/-- The zero extension belongs to the original full upper-half-plane L² space. -/
theorem cellExtension_memLp (u : Space) :
    MemLp (cellExtension u) 2 (volume : Measure UpperHalfPlane) := by
  apply (memLp_indicator_iff_restrict isOpen_fdo.measurableSet).mpr
  exact (Lp.memLp u).mono_measure (Measure.restrict_mono fdo_subset_fd le_rfl)

/-- The constructed scalar lift is pointwise invariant under every modular element. -/
theorem globalLift_invariant (u : Space) (γ : PSL2Z) (z : UpperHalfPlane) :
    globalLift u (γ • z) = globalLift u z := periodize_invariant _ γ z

/-- On the closed cell the actual lift is exactly the specified zero extension. -/
theorem globalLift_eq_on_fd (u : Space) (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalLift u z = cellExtension u z := by
  apply periodize_eq_on_fd _ _ z hz
  intro w hw
  by_contra hn
  exact hw (by simp [cellExtension,Set.indicator_of_notMem hn])

/-- The globally invariant scalar lift represents the original vector in its native measure. -/
theorem globalLift_ae_eq (u : Space) : globalLift u =ᵐ[measure] (u : UpperHalfPlane → ℂ) := by
  filter_upwards [ae_mem_interior] with z hz
  rw [globalLift_eq_on_fd u z (fdo_subset_fd hz)]
  simp [cellExtension,hz]

/-- On every compact chart one fixed finite sum realizes all scalar lifts. -/
theorem globalLift_compact_sum (K : Set UpperHalfPlane) (hK : IsCompact K) :
    ∃ s : Finset PSL2Z, ∀ u : Space, ∀ z ∈ K,
      globalLift u z = ∑ γ ∈ s, cellExtension u (γ • z) := by
  obtain ⟨s,hs⟩ := compact_cell_pullbacks_finite K hK
  refine ⟨s,?_⟩
  intro u z hz
  apply tsum_eq_sum
  intro γ hγ
  have hn : γ • z ∉ fdo := fun hi => hs γ hγ z hz (fdo_subset_fd hi)
  simp [cellExtension,hn]

/-- The actual globally invariant lift has L² control on every compact chart. -/
theorem globalLift_memLp_compact (u : Space) (K : Set UpperHalfPlane) (hK : IsCompact K) :
    MemLp (globalLift u) 2 ((volume : Measure UpperHalfPlane).restrict K) := by
  obtain ⟨s,hs⟩ := globalLift_compact_sum K hK
  have ht (γ : PSL2Z) : MemLp (fun z => cellExtension u (γ • z)) 2
      ((volume : Measure UpperHalfPlane).restrict K) :=
    ((cellExtension_memLp u).comp_measurePreserving (measurePreserving_smul γ volume)).mono_measure
      Measure.restrict_le_self
  apply MemLp.ae_eq (f := fun z => ∑ γ ∈ s, cellExtension u (γ • z))
  · filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact (hs u z hz).symm
  · exact memLp_finsetSum s (fun γ _ => ht γ)

/-- Local integrability is proved for the actual scalar lift on the whole half-plane. -/
theorem globalLift_locallyIntegrable (u : Space) :
    LocallyIntegrable (globalLift u) (volume : Measure UpperHalfPlane) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  haveI : IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  exact (globalLift_memLp_compact u K hK).integrable (by norm_num)

end
end RHTower.D4BMModularCore
