import GaloisForLFunctions.RHTower.DeningerTestL2Scale
import Mathlib.Topology.Separation.Profinite

/-!
# Uniform approximation by locally constant test functions

In a locally compact Hausdorff totally disconnected space the compact open sets form a
neighbourhood basis, and every compact set is contained in a compact open set.  A continuous
function with compact support is therefore approximated uniformly by a locally constant function:
cover a compact open set containing the support by compact opens on which the function varies by
less than the prescribed amount, and glue the sampled values along that finite cover.

Gluing is possible because a compact open set of a Hausdorff space is clopen, so a function defined
by cases along it is again locally constant.

* `deningerExists_compactOpen_nhds` : compact open neighbourhood basis.
* `deningerExists_compactOpen_superset` : a compact set lies in a compact open set.
* `deningerPiecewise_isLocallyConstant` : gluing along a clopen set.
* `deningerExists_locallyConstant_approx` : **uniform approximation by a test function.**
-/

namespace RHTower

open TopologicalSpace

section Piecewise

variable {Y : Type*} [TopologicalSpace Y]

/-- **Gluing along a clopen set preserves local constancy.** -/
theorem deningerPiecewise_isLocallyConstant {U : Set Y} [DecidablePred (· ∈ U)]
    (hU : IsClopen U) {a b : Y → ℝ} (ha : IsLocallyConstant a) (hb : IsLocallyConstant b) :
    IsLocallyConstant (U.piecewise a b) := by
  intro s
  have hset : U.piecewise a b ⁻¹' s = (U ∩ a ⁻¹' s) ∪ (Uᶜ ∩ b ⁻¹' s) := by
    ext y
    by_cases hy : y ∈ U <;> simp [Set.piecewise, hy]
  rw [hset]
  exact (hU.2.inter (ha s)).union (hU.1.isOpen_compl.inter (hb s))

end Piecewise

section ZeroDimensional

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
variable [TotallyDisconnectedSpace Y]

/-- **The compact open sets form a neighbourhood basis** of a locally compact Hausdorff totally
disconnected space. -/
theorem deningerExists_compactOpen_nhds {x : Y} {U : Set Y} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V ∈ deningerCompactOpens Y, x ∈ V ∧ V ⊆ U := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hVclopen, hxV, hVK⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := Y)).mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hxK)
  refine ⟨V, ⟨hVclopen.2, ?_⟩, hxV, hVK.trans (interior_subset.trans hKU)⟩
  exact hK.of_isClosed_subset hVclopen.1 (hVK.trans interior_subset)

/-- **A compact set is contained in a compact open set.** -/
theorem deningerExists_compactOpen_superset {K : Set Y} (hK : IsCompact K) :
    ∃ S ∈ deningerCompactOpens Y, K ⊆ S := by
  classical
  have hnhds : ∀ x ∈ K, ∃ V ∈ deningerCompactOpens Y, x ∈ V :=
    fun x _ => by
      obtain ⟨V, hV, hxV, -⟩ := deningerExists_compactOpen_nhds (isOpen_univ (X := Y))
        (Set.mem_univ x)
      exact ⟨V, hV, hxV⟩
  choose! V hV hxV using hnhds
  have hcover : K ⊆ ⋃ x ∈ K, V x := fun x hx => Set.mem_biUnion hx (hxV x hx)
  obtain ⟨t, hts, htfin, htcover⟩ :=
    hK.elim_finite_subcover_image (fun x hx => (hV x hx).1) hcover
  refine ⟨⋃ x ∈ t, V x, ⟨isOpen_biUnion fun x hx => (hV x (hts hx)).1, ?_⟩, htcover⟩
  exact htfin.isCompact_biUnion fun x hx => (hV x (hts hx)).2

omit [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
/-- A compact open set of a Hausdorff space is clopen. -/
theorem deningerCompactOpen_isClopen {U : Set Y} (hU : U ∈ deningerCompactOpens Y) :
    IsClopen U := ⟨hU.2.isClosed, hU.1⟩

omit [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
/-- **Gluing sampled values along a finite family of compact open sets.**  If the function varies
by at most `ε` on each member, a locally constant function supported in the union approximates it
there to within `ε`. -/
theorem deningerExists_locallyConstant_of_cover {f : Y → ℝ} {ε : ℝ}
    (V : Y → Set Y) (t : Finset Y) (hV : ∀ x ∈ t, V x ∈ deningerCompactOpens Y)
    (hosc : ∀ x ∈ t, ∀ y ∈ V x, |f y - f x| ≤ ε) :
    ∃ g : Y → ℝ, IsLocallyConstant g ∧ Function.support g ⊆ ⋃ x ∈ t, V x ∧
      ∀ y ∈ ⋃ x ∈ t, V x, |f y - g y| ≤ ε := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, IsLocallyConstant.const 0, by simp, by simp⟩
  | insert x t hx ih =>
      obtain ⟨g, hgconst, hgsupp, hgapprox⟩ :=
        ih (fun y hy => hV y (Finset.mem_insert_of_mem hy))
          (fun y hy => hosc y (Finset.mem_insert_of_mem hy))
      have hVx : V x ∈ deningerCompactOpens Y := hV x (Finset.mem_insert_self x t)
      have hclopen : IsClopen (V x) := deningerCompactOpen_isClopen hVx
      refine ⟨(V x).piecewise (fun _ => f x) g,
        deningerPiecewise_isLocallyConstant hclopen (IsLocallyConstant.const _) hgconst,
        ?_, ?_⟩
      · intro y hy
        by_cases hyx : y ∈ V x
        · exact Set.mem_biUnion (Finset.mem_insert_self x t) hyx
        · have hgy : g y ≠ 0 := by
            rw [Function.mem_support, Set.piecewise_eq_of_notMem _ _ _ hyx] at hy
            exact hy
          obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hgsupp hgy)
          exact Set.mem_biUnion (Finset.mem_insert_of_mem hz) hyz
      · intro y hy
        by_cases hyx : y ∈ V x
        · rw [Set.piecewise_eq_of_mem _ _ _ hyx]
          exact hosc x (Finset.mem_insert_self x t) y hyx
        · rw [Set.piecewise_eq_of_notMem _ _ _ hyx]
          obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
          rcases Finset.mem_insert.mp hz with rfl | hzt
          · exact absurd hyz hyx
          · exact hgapprox y (Set.mem_biUnion hzt hyz)

/-- **A continuous function with compact support is uniformly approximated by a locally constant
test function**, with the error supported in a fixed compact open set. -/
theorem deningerExists_locallyConstant_approx {f : Y → ℝ} (hf : Continuous f)
    (hsupp : HasCompactSupport f) :
    ∃ S ∈ deningerCompactOpens Y, Function.support f ⊆ S ∧ ∀ ε > 0,
      ∃ g : Y → ℝ, g ∈ DeningerTestSpace Y ∧ Function.support g ⊆ S ∧
        ∀ y, |f y - g y| ≤ ε := by
  classical
  obtain ⟨S, hS, hSsupp⟩ := deningerExists_compactOpen_superset hsupp
  have hfS : Function.support f ⊆ S := (subset_tsupport f).trans hSsupp
  refine ⟨S, hS, hfS, ?_⟩
  intro ε hε
  have hnhds : ∀ x ∈ S, ∃ V ∈ deningerCompactOpens Y, x ∈ V ∧ V ⊆ S ∩ f ⁻¹' Set.Ioo
      (f x - ε) (f x + ε) := by
    intro x _
    refine deningerExists_compactOpen_nhds (hS.1.inter (hf.isOpen_preimage _ isOpen_Ioo)) ?_
    exact ⟨‹x ∈ S›, by constructor <;> linarith⟩
  choose! V hV hxV hVsub using hnhds
  have hcover : S ⊆ ⋃ x ∈ S, V x := fun x hx => Set.mem_biUnion hx (hxV x hx)
  obtain ⟨t, hts, htfin, htcover⟩ :=
    hS.2.elim_finite_subcover_image (fun x hx => (hV x hx).1) hcover
  have hmem : ∀ x, x ∈ htfin.toFinset ↔ x ∈ t := fun x => htfin.mem_toFinset
  have hmemS : ∀ x ∈ htfin.toFinset, x ∈ S := fun x hx => hts ((hmem x).mp hx)
  have hosc : ∀ x ∈ htfin.toFinset, ∀ y ∈ V x, |f y - f x| ≤ ε := by
    intro x hx y hy
    have hy' := (hVsub x (hmemS x hx) hy).2
    rw [abs_le]
    constructor <;> [linarith [hy'.1]; linarith [hy'.2]]
  obtain ⟨g, hgconst, hgsupp, hgapprox⟩ :=
    deningerExists_locallyConstant_of_cover V htfin.toFinset
      (fun x hx => hV x (hmemS x hx)) hosc
  have hunion : (⋃ x ∈ htfin.toFinset, V x) ⊆ S := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp hy
    exact (hVsub x (hmemS x hx) hyx).1
  have hcoverS : S ⊆ ⋃ x ∈ htfin.toFinset, V x := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (htcover hy)
    exact Set.mem_biUnion ((hmem x).mpr hx) hyx
  have hgS : Function.support g ⊆ S := hgsupp.trans hunion
  refine ⟨g, ⟨hgconst, ?_⟩, hgS, ?_⟩
  · exact hS.2.of_isClosed_subset (deningerSupport_isClosed hgconst) hgS
  · intro y
    by_cases hy : y ∈ S
    · exact hgapprox y (hcoverS hy)
    · have hfy : f y = 0 := by
        by_contra hne
        exact hy (hfS hne)
      have hgy : g y = 0 := by
        by_contra hne
        exact hy (hgS hne)
      rw [hfy, hgy, sub_zero, abs_zero]
      exact hε.le

end ZeroDimensional

end RHTower
