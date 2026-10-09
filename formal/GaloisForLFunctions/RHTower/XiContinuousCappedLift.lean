import GaloisForLFunctions.RHTower.XiPeripheralCaps
import GaloisForLFunctions.RHTower.XiIsolatedMarkedPunctures
import GaloisForLFunctions.HTGeometry.PuncturedLocalGluing

open Topology Set Function Filter
open scoped UpperHalfPlane

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Each actual deleted source point admits a continuous cap extension of its lift. -/
theorem exists_local_capped_xi_lift
    (H : Subgroup (coveringDeckGroup markedUniversalCover))
    (F : C(Source ({0} : Finset ℝ), MarkedImageCover H))
    (hF : ∀ s, (markedImageProjection H (F s) : ℂ) = xi s)
    (b : Bool) (a : ℂ) (ha : xi a = peripheralCenter b) :
    ∃ G : ℂ → CappedMarkedCover H, ContinuousAt G a ∧
      (∀ᶠ z in 𝓝[≠] a, ∀ hz : z ∈ sourceSet ({0} : Finset ℝ),
        G z = (finitePeripheralCapData H).old (F ⟨z, hz⟩)) ∧
      cappedMarkedProjection H (G a) = xi a := by
  classical
  obtain ⟨r, hr, hsub⟩ := exists_punctured_source_disk_at_mark b a ha
  let S := puncturedSourceDisk a r
  have hSo : IsOpen S := isOpen_puncturedSourceDisk a r
  have hSn : S ∈ 𝓝[≠] a := by
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨r, hr, fun z hz => ?_⟩
    exact ⟨hz.2, by simpa only [Metric.mem_ball, dist_eq_norm] using hz.1⟩
  letI : PathConnectedSpace S :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_puncturedSourceDisk a r hr)
  let g₀ : C(S, peripheralPreimage H b) :=
    ⟨fun z => ⟨F ⟨z.val, (hsub z.val z.property).1⟩, by
      change ‖(markedImageProjection H (F ⟨z.val, (hsub z.val z.property).1⟩) : ℂ) -
        peripheralCenter b‖ < 1 / 4
      rw [hF]
      exact (hsub z.val z.property).2⟩,
      (F.continuous.comp (continuous_subtype_val.subtype_mk
        (fun z : S => (hsub z.val z.property).1))).subtype_mk (fun z => by
          change ‖(markedImageProjection H (F ⟨z.val, (hsub z.val z.property).1⟩) : ℂ) -
            peripheralCenter b‖ < 1 / 4
          rw [hF]
          exact (hsub z.val z.property).2)⟩
  let z₀ : S := Classical.choice inferInstance
  let j : PeripheralIndex H := ⟨b, ConnectedComponents.mk (g₀ z₀)⟩
  have hcc : connectedComponent (g₀ z₀) = connectedComponent (peripheralRepresentative H j) :=
    ConnectedComponents.coe_eq_coe.mp (peripheralRepresentative_component H j).symm
  have hmem (z : S) : g₀ z ∈ connectedComponent (peripheralRepresentative H j) := by
    rw [← hcc]
    exact (isPreconnected_range g₀.continuous).subset_connectedComponent
      (mem_range_self z₀) (mem_range_self z)
  let gc : C(S, PeripheralComponent H j) :=
    ⟨fun z => ⟨g₀ z, hmem z⟩, g₀.continuous.subtype_mk _⟩
  let g : ℂ → PeripheralComponent H j :=
    fun z => if hz : z ∈ S then gc ⟨z, hz⟩ else gc z₀
  have hgon : ContinuousOn g S := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert gc.continuous using 1
    funext z
    change (if hz : z.val ∈ S then gc ⟨z.val, hz⟩ else gc z₀) = gc z
    rw [dif_pos z.property]
  have hgc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt g z := by
    filter_upwards [hSn] with z hz
    exact hgon.continuousAt (hSo.mem_nhds hz)
  have hgval (z : ℂ) (hz : z ∈ S) :
      (g z).val.val = F ⟨z, (hsub z hz).1⟩ := by
    dsimp [g]
    rw [dif_pos hz]
    rfl
  let f : ℂ → ℂ := fun z => (xi z - peripheralCenter b) * 4
  have hf : AnalyticAt ℂ f a :=
    ((xi_differentiable.analyticAt a).sub analyticAt_const).mul analyticAt_const
  have hfa : f a = 0 := by simp [f, ha]
  have hfg : ∀ᶠ z in 𝓝[≠] a, (peripheralComponentProjection H j (g z) : ℂ) = f z := by
    filter_upwards [hSn] with z hz
    change ((markedImageProjection H (g z).val.val : ℂ) - peripheralCenter b) * 4 = f z
    rw [hgval z hz, hF]
  obtain ⟨n, hn, D, hD, _, _⟩ := analytic_zero_lift_in_open_cover_component
    (isCoveringMap_markedImageProjection H) (isOpen_peripheralTarget b)
    (peripheralTargetChart b) (peripheralRepresentative H j) hf hfa g hgc hfg
  let i : FinitePeripheralIndex H := ⟨j, ⟨⟨n, hn, D, hD⟩⟩⟩
  let u : ℂ → ℂ := fun z => ((chosenPeripheralPowerChart H i).homeomorph (g z) : ℂ)
  have huc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt u z := by
    filter_upwards [hgc] with z hz
    exact continuous_subtype_val.continuousAt.comp
      ((chosenPeripheralPowerChart H i).homeomorph.continuous.continuousAt.comp hz)
  have hfnz : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    filter_upwards [hfg] with z hz
    rw [← hz]
    exact (peripheralComponentProjection H j (g z)).property.1
  have hpow : ∀ᶠ z in 𝓝[≠] a, u z ^ (chosenPeripheralPowerChart H i).degree = f z := by
    filter_upwards [hfg] with z hz
    have he := congrArg Subtype.val ((chosenPeripheralPowerChart H i).projection (g z))
    change (peripheralComponentProjection H j (g z) : ℂ) = u z ^
      (chosenPeripheralPowerChart H i).degree at he
    exact he.symm.trans hz
  have hua := analyticAt_update_zero_of_punctured_continuous_root
    (chosenPeripheralPowerChart H i).positive hf hfa huc hfnz hpow
  have hub (z : ℂ) : ‖update u a 0 z‖ < 1 := by
    by_cases hz : z = a
    · subst z
      simp
    · rw [update_of_ne hz]
      exact ((chosenPeripheralPowerChart H i).homeomorph (g z)).property.2
  let uc : ℂ → UnitCapDisk := fun z => ⟨update u a 0 z, hub z⟩
  let G : ℂ → CappedMarkedCover H := (finitePeripheralCapData H).cap i ∘ uc
  have huc0 : uc a = unitCapCenter := by
    apply Subtype.ext
    simp [uc, unitCapCenter]
  refine ⟨G, (finitePeripheralCapData H).continuous_cap i |>.continuousAt.comp
    (tendsto_subtype_rng.mpr hua.continuousAt), ?_, ?_⟩
  · filter_upwards [hSn, self_mem_nhdsWithin] with z hz hza
    intro hzs
    have hucn : uc z ≠ unitCapCenter := by
      intro h
      have he := congrArg Subtype.val h
      change update u a 0 z = 0 at he
      rw [update_of_ne hza] at he
      exact ((chosenPeripheralPowerChart H i).homeomorph (g z)).property.1 he
    have hcoord : puncturedCapHomeomorph ⟨uc z, hucn⟩ =
        (chosenPeripheralPowerChart H i).homeomorph (g z) := by
      apply Subtype.ext
      change update u a 0 z = u z
      exact update_of_ne hza _ _
    change (finitePeripheralCapData H).cap i (uc z) = _
    rw [(finitePeripheralCapData H).cap_ne_center i hucn]
    change (finitePeripheralCapData H).old
      (peripheralComponentToRegion H j ((chosenPeripheralPowerChart H i).homeomorph.symm
        (puncturedCapHomeomorph ⟨uc z, hucn⟩))).val = _
    rw [hcoord, Homeomorph.symm_apply_apply, peripheralComponentToRegion_val, hgval z hz]
  · change cappedMarkedProjection H ((finitePeripheralCapData H).cap i (uc a)) = xi a
    rw [huc0, cappedMarkedProjection_cap, ha]
    change peripheralCenter b + (0 : ℂ) ^ (chosenPeripheralPowerChart H i).degree / 4 =
      peripheralCenter b
    simp [(chosenPeripheralPowerChart H i).positive.ne']

/-- The actual lift extends continuously over the whole source plane, preserving Xi. -/
theorem exists_capped_xi_lift_extension
    (H : Subgroup (coveringDeckGroup markedUniversalCover))
    (F : C(Source ({0} : Finset ℝ), MarkedImageCover H))
    (hF : ∀ s, (markedImageProjection H (F s) : ℂ) = xi s) :
    ∃ G : C(ℂ, CappedMarkedCover H),
      (∀ s : Source ({0} : Finset ℝ), G s = (finitePeripheralCapData H).old (F s)) ∧
      ∀ z, cappedMarkedProjection H (G z) = xi z := by
  let F₀ : C(Source ({0} : Finset ℝ), CappedMarkedCover H) :=
    ⟨fun s => (finitePeripheralCapData H).old (F s),
      (finitePeripheralCapData H).continuous_old.comp F.continuous⟩
  apply exists_continuous_extension_of_punctured_local_extensions
    (isOpen_sourceSet {0}) (fun a _ => untwisted_sourceSet_mem_punctured_nhds a)
    F₀ (cappedMarkedProjection H) xi
  · intro s
    exact hF s
  · intro a ha
    by_cases h0 : xi a = 0
    · exact exists_local_capped_xi_lift H F hF false a h0
    · have h1 : xi a = -1 := by
        by_contra hne
        exact ha ((mem_untwisted_sourceSet a).mpr ⟨h0, hne⟩)
      exact exists_local_capped_xi_lift H F hF true a h1

/-- Unconditional continuous capped factorization of actual Xi, retaining the
exact-image source lift and its surjection on fundamental groups. -/
theorem xi_continuous_capped_image_factorization :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      ∃ F : C(Source ({0} : Finset ℝ), MarkedImageCover H),
      ∃ hF : F (sourceZero {0}) = Quotient.mk (MulAction.orbitRel H ℍ) markedUniversalCoverPoint.val,
      ∃ G : C(ℂ, CappedMarkedCover H),
      (∀ z, cappedMarkedProjection H (G z) = xi z) ∧
      (∀ s : Source ({0} : Finset ℝ), G s = (finitePeripheralCapData H).old (F s)) ∧
      Surjective (FundamentalGroup.mapOfEq F hF) := by
  obtain ⟨H, F, hF, hproj, hsurj⟩ := xi_exact_image_cover_factorization
  obtain ⟨G, hG, hGp⟩ := exists_capped_xi_lift_extension H F hproj
  exact ⟨H, F, hF, G, hGp, hG, hsurj⟩

end
end RHTower.XiMarkedMonodromy
