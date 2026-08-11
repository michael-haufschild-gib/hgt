import Mathlib

/-!
# The Baire step of the open mapping theorem

For a continuous surjective linear map into a Baire topological vector space, the closure of the
image of any neighbourhood of the origin is again a neighbourhood of the origin.  This is the half
of the open mapping theorem that uses only the Baire property of the target; removing the closure
needs completeness and metrizability of the source.

* `closure_sub_closure_subset` : `\overline A - \overline A \subseteq \overline{A - A}`.
* `closure_image_mem_nhds_zero` : **the Baire step.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

/-- The difference of closures lies in the closure of the difference. -/
theorem closure_sub_closure_subset (A : Set F) :
    closure A - closure A ⊆ closure (A - A) := by
  rintro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.1 hz
  have hcont : Continuous fun p : F × F => p.1 - p.2 := continuous_fst.sub continuous_snd
  have hmem : (x, y) ∈ closure (A ×ˢ A) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  have himg := image_closure_subset_closure_image hcont
    (Set.mem_image_of_mem (fun p : F × F => p.1 - p.2) hmem)
  refine closure_mono ?_ himg
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact Set.mem_sub.2 ⟨a, ha, b, hb, rfl⟩

private theorem natSucc_norm (n : ℕ) : ‖((n : 𝕜) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : 𝕜) + 1) = ((n + 1 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
  push_cast
  ring

private theorem natSucc_ne_zero (n : ℕ) : ((n : 𝕜) + 1) ≠ 0 := by
  intro hzero
  have h1 := natSucc_norm (𝕜 := 𝕜) n
  rw [hzero, norm_zero] at h1
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  linarith

/-- A linear map carries a scaled set to the scaled image. -/
theorem image_smul_set_linear (f : E →ₗ[𝕜] F) (c : 𝕜) (S : Set E) :
    f '' (c • S) = c • (f '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨f v, Set.mem_image_of_mem _ hv, by rw [map_smul]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨c • v, ⟨v, hv, rfl⟩, by rw [map_smul]⟩

/-- **The Baire step.**  If `f` is a continuous surjective linear map onto a Baire space, then the
closure of the image of any neighbourhood of the origin is a neighbourhood of the origin. -/
theorem closure_image_mem_nhds_zero [BaireSpace F] (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hsurj : Function.Surjective f) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    closure (f '' U) ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨W, hW, hWU⟩ := exists_nhds_zero_half hU
  set V : Set E := balancedCore 𝕜 W with hVdef
  have hVnhds : V ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hW
  have hVbal : Balanced 𝕜 V := balancedCore_balanced W
  have hVW : V ⊆ W := balancedCore_subset W
  have hVV : V - V ⊆ U := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.1 hz
    have hnb : -b ∈ V := by
      rw [← hVbal.neg_eq]
      exact Set.neg_mem_neg.2 hb
    have hsum : a + -b ∈ U := hWU a (hVW ha) (-b) (hVW hnb)
    simpa [sub_eq_add_neg] using hsum
  -- the scaled images cover the target
  have hcover : (⋃ n : ℕ, closure (f '' (((n : 𝕜) + 1) • V))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    have habs : ∀ᶠ a in Bornology.cobounded 𝕜, ({x} : Set E) ⊆ a • V :=
      absorbent_nhds_zero (𝕜 := 𝕜) hVnhds x
    have htend : Filter.Tendsto (fun n : ℕ => ((n : 𝕜) + 1)) Filter.atTop
        (Bornology.cobounded 𝕜) := by
      refine tendsto_norm_atTop_iff_cobounded.1 ?_
      have hfun : (fun n : ℕ => ‖((n : 𝕜) + 1)‖) = fun n : ℕ => (n : ℝ) + 1 :=
        funext fun n => natSucc_norm n
      rw [hfun]
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    obtain ⟨n, hn⟩ := (htend.eventually habs).exists
    exact Set.mem_iUnion.2 ⟨n,
      subset_closure (Set.mem_image_of_mem _ (hn (Set.mem_singleton x)))⟩
  obtain ⟨n, hne⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n : ℕ => isClosed_closure) hcover
  -- undo the scaling
  have hne0 : ((n : 𝕜) + 1) ≠ 0 := natSucc_ne_zero n
  set g : F ≃ₜ F := Homeomorph.smulOfNeZero ((n : 𝕜) + 1) hne0 with hgdef
  have hgimg : ∀ S : Set F, ⇑g '' S = ((n : 𝕜) + 1) • S := fun S => Set.image_smul
  have hVint : (interior (closure (f '' V))).Nonempty := by
    rw [image_smul_set_linear, ← hgimg, ← g.image_closure, ← g.image_interior] at hne
    exact hne.of_image
  obtain ⟨y₀, hy₀⟩ := hVint
  -- translate the interior point to the origin
  have hopen : IsOpen ((fun y : F => y + y₀) ⁻¹' interior (closure (f '' V))) :=
    isOpen_interior.preimage (continuous_id.add continuous_const)
  have hzero : (0 : F) ∈ (fun y : F => y + y₀) ⁻¹' interior (closure (f '' V)) := by
    simpa using hy₀
  refine Filter.mem_of_superset (hopen.mem_nhds hzero) ?_
  intro z hz
  have h1 : z + y₀ ∈ closure (f '' V) := interior_subset hz
  have h2 : y₀ ∈ closure (f '' V) := interior_subset hy₀
  have hsub : z ∈ closure (f '' V) - closure (f '' V) :=
    Set.mem_sub.2 ⟨z + y₀, h1, y₀, h2, by abel⟩
  refine closure_mono ?_ (closure_sub_closure_subset _ hsub)
  intro w hw
  obtain ⟨a, hav, b, hbv, rfl⟩ := Set.mem_sub.1 hw
  obtain ⟨u, hu, rfl⟩ := hav
  obtain ⟨v, hv, rfl⟩ := hbv
  refine ⟨u - v, hVV (Set.mem_sub.2 ⟨u, hu, v, hv, rfl⟩), ?_⟩
  rw [map_sub]

end GaloisForLFunctions
