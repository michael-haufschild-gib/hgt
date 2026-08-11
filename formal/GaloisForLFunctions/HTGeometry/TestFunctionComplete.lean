import GaloisForLFunctions.HTGeometry.TestFunctionCauchy
import GaloisForLFunctions.HTGeometry.UniformIteratedDerivLimit

/-!
# Completeness of the test space

A Cauchy sequence in the test space has uniformly Cauchy derivatives at every order; the uniform
limits form a chain of derivatives, so the limit of the sequence itself is smooth with exactly
those derivatives, and its support stays inside the fixed compact set.  Uniform convergence at
every order is convergence in the seminorm topology, so the space is complete.

Separation comes from the order-zero seminorm: a nonzero test function has nonzero supremum.

* `deningerTest_exists_tendsto_of_cauchySeq` : Cauchy sequences converge.
* `instCompleteSpaceDeningerTest` : the test space is complete.
* `instT1SpaceDeningerTest` : the test space is separated.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology TopologicalSpace

section Complete

variable {J : Compacts ℝ}

instance instIsCountablyGeneratedUniformityDeningerTest (J : Compacts ℝ) :
    (uniformity (DeningerTest J)).IsCountablyGenerated := by
  have h : (𝓝 (0 : DeningerTest J)).IsCountablyGenerated :=
    FirstCountableTopology.nhds_generated_countable 0
  exact @IsUniformAddGroup.uniformity_countably_generated (DeningerTest J) _ _ _ h

/-- **Cauchy sequences in the test space converge.** -/
theorem deningerTest_exists_tendsto_of_cauchySeq (u : ℕ → DeningerTest J) (hu : CauchySeq u) :
    ∃ v : DeningerTest J, Filter.Tendsto u Filter.atTop (𝓝 v) := by
  have hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) ((u n : ℝ → ℂ)) := fun n => (u n).2.1
  have huc : ∀ m, UniformCauchySeqOn
      (fun n => iteratedDeriv m ((u n : ℝ → ℂ))) Filter.atTop Set.univ :=
    fun m => uniformCauchySeqOn_iteratedDeriv_of_cauchySeq hu m
  choose g hg using fun m => exists_tendstoUniformly_of_uniformCauchySeq (huc m)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (g 0) :=
    contDiff_infty_of_tendstoUniformly_iteratedDeriv hsmooth hg
  have hiter : ∀ m, iteratedDeriv m (g 0) = g m :=
    iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv hsmooth hg
  have hpt : ∀ t : ℝ, Filter.Tendsto (fun n => (u n : ℝ → ℂ) t) Filter.atTop (𝓝 (g 0 t)) := by
    intro t
    have h0 := (hg 0).tendsto_at t
    simpa [iteratedDeriv_zero] using h0
  have hsupp : tsupport (g 0) ⊆ (J : Set ℝ) :=
    tsupport_subset_of_tendsto J.isCompact.isClosed hpt fun n => (u n).2.2
  have hmem : g 0 ∈ deningerTestSpace (J : Set ℝ) := ⟨hcd, hsupp⟩
  refine ⟨⟨g 0, hmem⟩, ?_⟩
  rw [(withSeminorms_deningerTest J).tendsto_nhds]
  intro m eps heps
  have hhalf : 0 < eps / 2 := by linarith
  have hunif := (Metric.tendstoUniformly_iff.mp (hg m)) (eps / 2) hhalf
  filter_upwards [hunif] with n hn
  have hcoe : deningerTestFamily J m (u n - ⟨g 0, hmem⟩)
      = deningerTestSupNorm m ((u n : ℝ → ℂ) - g 0) := by
    show deningerTestSupNorm m
      (((u n - ⟨g 0, hmem⟩ : DeningerTest J) : ℝ → ℂ)) = _
    rw [Submodule.coe_sub]
  rw [hcoe]
  refine lt_of_le_of_lt (deningerTestSupNorm_le m (c := eps / 2) fun t => ?_) (by linarith)
  have hsplit : iteratedDeriv m ((u n : ℝ → ℂ) - g 0) t
      = iteratedDeriv m ((u n : ℝ → ℂ)) t - iteratedDeriv m (g 0) t :=
    iteratedDeriv_sub_of_mem (J := J) (u n).2 hmem m t
  rw [hsplit, hiter m]
  have hdist := hn t
  rw [dist_eq_norm] at hdist
  rw [← neg_sub, norm_neg]
  exact hdist.le

instance instCompleteSpaceDeningerTest (J : Compacts ℝ) : CompleteSpace (DeningerTest J) :=
  UniformSpace.complete_of_cauchySeq_tendsto deningerTest_exists_tendsto_of_cauchySeq

/-- The order-zero seminorm separates points. -/
theorem deningerTestFamily_separating {phi : DeningerTest J} (hphi : phi ≠ 0) :
    ∃ m, deningerTestFamily J m phi ≠ 0 := by
  refine ⟨0, ?_⟩
  have hne : (phi : ℝ → ℂ) ≠ 0 := by
    intro h
    exact hphi (Subtype.ext h)
  obtain ⟨t, ht⟩ : ∃ t, (phi : ℝ → ℂ) t ≠ 0 := Function.ne_iff.mp hne
  have hpos : 0 < ‖(phi : ℝ → ℂ) t‖ := norm_pos_iff.mpr ht
  have hle : ‖(phi : ℝ → ℂ) t‖ ≤ deningerTestSupNorm 0 (phi : ℝ → ℂ) := by
    have := norm_iteratedDeriv_le_supNorm J.isCompact phi.2 0 t
    rwa [iteratedDeriv_zero] at this
  intro hzero
  have hzero' : deningerTestSupNorm 0 (phi : ℝ → ℂ) = 0 := hzero
  rw [hzero'] at hle
  linarith

instance instT1SpaceDeningerTest (J : Compacts ℝ) : T1Space (DeningerTest J) :=
  (withSeminorms_deningerTest J).T1_of_separating fun _ hx => deningerTestFamily_separating hx

end Complete

end GaloisForLFunctions.HTGeometry
