import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalChartTests

/-!
Finite translate bounds and exact native integral unfolding for compact modular tests.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- Only finitely many translates of an arbitrary compact test meet the entire
closed modular cell. The finite set includes every possible seam contribution. -/
theorem compact_test_cell_translates_finite (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f) :
    ∃ s : Finset PSL2Z, ∀ γ ∉ s, ∀ z ∈ fd, f (γ • z) = 0 := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_cell_bound (tsupport f) hf
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    (truncated_cell_compact M) hf
  refine ⟨hfin.toFinset,?_⟩
  intro γ hγ z hz
  by_contra hn
  apply hγ
  simp only [Set.Finite.mem_toFinset]
  exact ⟨γ • z,⟨z,⟨hz,hM z ⟨γ,subset_tsupport f hn⟩⟩,rfl⟩,subset_tsupport f hn⟩

/-- Compact support makes every pointwise modular orbit series summable, including
orbits through elliptic fixed points. -/
theorem compact_test_orbit_summable (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f)
    (z : UpperHalfPlane) : Summable (fun γ : PSL2Z => f (γ • z)) := by
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    (isCompact_singleton (x := z)) hf
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro γ hγ
  exact ⟨γ • z,⟨z,mem_singleton z,rfl⟩,subset_tsupport f hγ⟩

/-- The actual full cell trace is one finite sum; no omitted translate can carry
a hidden term at a joined modular side. -/
theorem compact_test_cell_periodize_sum (g : CompactChartTest) :
    ∃ s : Finset PSL2Z, ∀ z ∈ fd, periodize g.field z = ∑ γ ∈ s, g.field (γ • z) := by
  classical
  obtain ⟨s,hs⟩ := compact_test_cell_translates_finite g.field g.compact
  refine ⟨s,?_⟩
  intro z hz
  exact tsum_eq_sum (fun γ hγ => hs γ hγ z hz)

/-- All absolute translate integrals are summable for an actual compact chart
test, from a proved finite set covering the entire cell. -/
theorem compact_test_cell_integral_norm_summable (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f) :
    Summable (fun γ : PSL2Z => ∫ z : UpperHalfPlane in fd, ‖f (γ • z)‖) := by
  classical
  obtain ⟨s,hs⟩ := compact_test_cell_translates_finite f hf
  apply summable_of_ne_finset_zero (s := s)
  intro γ hγ
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
  simp [hs γ hγ z hz]

/-- Full modular periodization unfolds exactly against the original hyperbolic
measure for every compact smooth chart test, with all convergence discharged. -/
theorem compact_test_periodize_integral (f : UpperHalfPlane → ℂ) (hf : HasCompactSupport f)
    (hi : Integrable f) :
    (∫ z : UpperHalfPlane, periodize f z ∂measure) = ∫ z : UpperHalfPlane, f z := by
  have ht (γ : PSL2Z) : IntegrableOn (fun z : UpperHalfPlane => f (γ • z)) fd :=
    ((measurePreserving_smul γ volume).integrable_comp_emb
      (measurableEmbedding_const_smul γ) |>.mpr hi).integrableOn
  rw [isFundamentalDomain_fd.integral_eq_tsum'' f hi,
    integral_tsum_of_summable_integral_norm ht (compact_test_cell_integral_norm_summable f hf)]
  rfl

/-- Compact-test pairing unfolds against any locally integrable modular field.
The actual finite translate bound discharges every sum and integral interchange. -/
theorem compact_test_modular_pairing_unfold (g : CompactChartTest) (u : UpperHalfPlane → ℂ)
    (hu : LocallyIntegrable u) (hinv : ∀ γ : PSL2Z, ∀ z, u (γ • z) = u z) :
    (∫ z : UpperHalfPlane, periodize g.field z * u z ∂measure) =
      ∫ z : UpperHalfPlane, g.field z * u z := by
  have hi : Integrable (fun z => g.field z * u z) := by
    simpa only [smul_eq_mul] using
      hu.integrable_smul_left_of_hasCompactSupport (𝕜 := ℂ) (g := g.field)
        (ChartSmooth.continuous g.smooth) g.compact
  have hk : HasCompactSupport (fun z => g.field z * u z) :=
    g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  have he := compact_test_periodize_integral _ hk hi
  have hprod (z : UpperHalfPlane) : periodize (fun w => g.field w * u w) z =
      periodize g.field z * u z := by
    simp only [periodize,hinv,tsum_mul_right]
  simpa only [hprod] using he

end
end RHTower.D4BMModularCore
