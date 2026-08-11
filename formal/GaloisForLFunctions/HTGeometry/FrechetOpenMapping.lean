import GaloisForLFunctions.HTGeometry.FrechetCauchy
import GaloisForLFunctions.HTGeometry.FrechetOpenMappingStep

/-!
# The open mapping theorem for Fréchet spaces

A continuous surjective linear map between complete, metrizable, Hausdorff topological vector
spaces is open.  mathlib proves this for Banach spaces by a norm estimate; the Fréchet case replaces
the norm by a halving basis of balanced neighbourhoods of the origin.

The Baire step gives `closure (f '' U) ∈ 𝓝 0`; the series step removes the closure by writing a
point of the closure as the image of a convergent series whose terms lie in successively smaller
basis members.

* `closure_image_subset_image` : **the closure is removed.**
* `isOpenMap_of_surjective` : **the open mapping theorem.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology Uniformity

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul 𝕜 E] [CompleteSpace E] [FirstCountableTopology E]
variable [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
  [ContinuousSMul 𝕜 F] [FirstCountableTopology F] [T2Space F] [BaireSpace F]

/-- A neighbourhood of the origin contains a symmetric one with the same property. -/
theorem exists_symm_subset {N : Set F} (hN : N ∈ 𝓝 (0 : F)) :
    ∃ M : Set F, M ∈ 𝓝 (0 : F) ∧ -M = M ∧ M ⊆ N := by
  have hneg : -N ∈ 𝓝 (0 : F) := by
    have hc : ContinuousAt (fun x : F => -x) 0 := continuous_neg.continuousAt
    have hpre := hc.preimage_mem_nhds (by simpa using hN)
    have heq : (fun x : F => -x) ⁻¹' N = -N := by
      ext x
      simp [Set.mem_neg]
    rwa [heq] at hpre
  refine ⟨N ∩ -N, Filter.inter_mem hN hneg, ?_, Set.inter_subset_left⟩
  ext x
  simp only [Set.mem_neg, Set.mem_inter_iff, neg_neg]
  tauto

/-- **The closure can be removed.**  A point in the closure of the image of a late basis member is
already the image of an earlier one. -/
theorem closure_image_subset_image (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hsurj : Function.Surjective f) {C : ℕ → Set E} {D : ℕ → Set F}
    (hCmem : ∀ m, C m ∈ 𝓝 (0 : E)) (hCbal : ∀ m, Balanced 𝕜 (C m))
    (hChalf : ∀ m, C (m + 1) + C (m + 1) ⊆ C m)
    (hCbasis : (𝓝 (0 : E)).HasBasis (fun _ : ℕ => True) C)
    (hDbal : ∀ k, Balanced 𝕜 (D k))
    (hDhalf : ∀ k, D (k + 1) + D (k + 1) ⊆ D k)
    (hDbasis : (𝓝 (0 : F)).HasBasis (fun _ : ℕ => True) D)
    (n : ℕ) :
    closure (f '' C (n + 2)) ⊆ f '' C n := by
  classical
  have hCzero : ∀ m, (0 : E) ∈ C m := fun m => mem_of_mem_nhds (hCmem m)
  have hCsymm : ∀ m, -C m = C m := fun m => (hCbal m).neg_eq
  have hDmem : ∀ k, D k ∈ 𝓝 (0 : F) := fun k => hDbasis.mem_of_mem (i := k) trivial
  have hDzero : ∀ k, (0 : F) ∈ D k := fun k => mem_of_mem_nhds (hDmem k)
  have hclos : ∀ m, closure (f '' C m) ∈ 𝓝 (0 : F) :=
    fun m => closure_image_mem_nhds_zero f hf hsurj (hCmem m)
  intro y hy
  -- the total selector for one approximation step
  have hsel : ∀ (k : ℕ) (z : F), ∃ p : E × F,
      z ∈ closure (f '' C (n + 2 + k)) →
        (p.1 ∈ C (n + 2 + k) ∧ p.2 = z - f p.1
          ∧ p.2 ∈ closure (f '' C (n + 2 + (k + 1))) ∧ p.2 ∈ D k) := by
    intro k z
    by_cases hz : z ∈ closure (f '' C (n + 2 + k))
    · obtain ⟨M, hMmem, hMsymm, hMsub⟩ :=
        exists_symm_subset (Filter.inter_mem (hclos (n + 2 + (k + 1))) (hDmem k))
      obtain ⟨x, hxC, hxN⟩ := exists_approx_of_mem_closure_image f hz hMmem hMsymm
      exact ⟨(x, z - f x), fun _ => ⟨hxC, rfl, (hMsub hxN).1, (hMsub hxN).2⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hz⟩
  choose sel hsel using hsel
  set Y : ℕ → F := fun k => Nat.rec y (fun j prev => (sel j prev).2) k with hYdef
  set X : ℕ → E := fun k => (sel k (Y k)).1 with hXdef
  -- the invariant
  have hYmem : ∀ k, Y k ∈ closure (f '' C (n + 2 + k)) := by
    intro k
    induction k with
    | zero => exact hy
    | succ j ih => exact (hsel j (Y j) ih).2.2.1
  have hXmem : ∀ k, X k ∈ C (n + 1 + 1 + k) := by
    intro k
    have := (hsel k (Y k) (hYmem k)).1
    have hidx : n + 2 + k = n + 1 + 1 + k := by omega
    rwa [hidx] at this
  have hYsucc : ∀ k, Y (k + 1) = Y k - f (X k) := fun k => (hsel k (Y k) (hYmem k)).2.1
  have hYD : ∀ k, Y (k + 1) ∈ D k := fun k => (hsel k (Y k) (hYmem k)).2.2.2
  -- the partial sums
  set s : ℕ → E := fun q => ∑ i ∈ Finset.range q, X i with hsdef
  have hscauchy : CauchySeq s :=
    cauchySeq_of_halvingBasis hCbasis hCzero hChalf hCsymm X (n + 1) hXmem
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hscauchy
  have hsmem : ∀ q, s q ∈ C (n + 1) :=
    fun q => halvingBasis_sum_mem hCzero hChalf q (n + 1) X fun i _ => hXmem i
  have hxmem : x ∈ C n := by
    have hcl : x ∈ closure (C (n + 1)) :=
      mem_closure_of_tendsto hx (Filter.Eventually.of_forall hsmem)
    have hadd := closure_subset_add (hCmem (n + 1)) (hCsymm (n + 1)) hcl
    exact hChalf n hadd
  -- the image of the limit is the given point
  have hYeq : ∀ q, Y q = y - f (s q) := by
    intro q
    induction q with
    | zero =>
      show y = y - f (∑ i ∈ Finset.range 0, X i)
      simp
    | succ j ih =>
      rw [hYsucc j, ih]
      show y - f (∑ i ∈ Finset.range j, X i) - f (X j)
        = y - f (∑ i ∈ Finset.range (j + 1), X i)
      rw [Finset.sum_range_succ, map_add]
      abel
  have hYtendsto : Filter.Tendsto Y Filter.atTop (𝓝 (0 : F)) := by
    refine hDbasis.tendsto_right_iff.2 fun j _ => ?_
    refine Filter.eventually_atTop.2 ⟨j + 1, fun q hq => ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    exact halvingBasis_mono hDzero hDhalf (by omega) (hYD r)
  have hfs : Filter.Tendsto (fun q => f (s q)) Filter.atTop (𝓝 y) := by
    have hy0 : Filter.Tendsto (fun q => y - Y q) Filter.atTop (𝓝 (y - 0)) :=
      Filter.Tendsto.const_sub y hYtendsto
    rw [sub_zero] at hy0
    refine hy0.congr fun q => ?_
    rw [hYeq q]
    abel
  have hfx : Filter.Tendsto (fun q => f (s q)) Filter.atTop (𝓝 (f x)) :=
    (hf.tendsto x).comp hx
  have : f x = y := tendsto_nhds_unique hfx hfs
  exact ⟨x, hxmem, this⟩

/-- **The open mapping theorem for Fréchet spaces.**  A continuous surjective linear map between
complete, metrizable, Hausdorff topological vector spaces is open. -/
theorem isOpenMap_of_surjective (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsOpenMap f := by
  obtain ⟨C, hCmem, hCbal, hChalf, hCbasis⟩ := exists_halvingBasis (𝕜 := 𝕜) (E := E)
  obtain ⟨D, hDmem, hDbal, hDhalf, hDbasis⟩ := exists_halvingBasis (𝕜 := 𝕜) (E := F)
  have hkey : ∀ U ∈ 𝓝 (0 : E), f '' U ∈ 𝓝 (0 : F) := by
    intro U hU
    obtain ⟨n, _, hnU⟩ := hCbasis.mem_iff.1 hU
    have h1 : closure (f '' C (n + 2)) ⊆ f '' C n :=
      closure_image_subset_image f hf hsurj hCmem hCbal hChalf hCbasis hDbal hDhalf hDbasis n
    have h2 : closure (f '' C (n + 2)) ∈ 𝓝 (0 : F) :=
      closure_image_mem_nhds_zero f hf hsurj (hCmem (n + 2))
    exact Filter.mem_of_superset h2 (h1.trans (Set.image_mono hnU))
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxS, rfl⟩
  have hpre : (fun w : E => x + w) ⁻¹' S ∈ 𝓝 (0 : E) := by
    have hc : ContinuousAt (fun w : E => x + w) 0 :=
      (continuous_const.add continuous_id).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hS.mem_nhds hxS)
  have hsub : f '' ((fun w : E => x + w) ⁻¹' S) ⊆ (fun z : F => f x + z) ⁻¹' (f '' S) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨x + w, hw, by rw [map_add]⟩
  have hmem : (fun z : F => f x + z) ⁻¹' (f '' S) ∈ 𝓝 (0 : F) :=
    Filter.mem_of_superset (hkey _ hpre) hsub
  have hmapeq : Filter.map (fun z : F => f x + z) (𝓝 (0 : F)) = 𝓝 (f x) := by
    simpa using map_add_left_nhds (f x) (0 : F)
  rw [← hmapeq]
  exact hmem

/-- **The bounded inverse theorem for Fréchet spaces.**  A continuous linear bijection between
complete, metrizable, Hausdorff topological vector spaces has continuous inverse. -/
theorem continuous_symm_of_continuous (e : E ≃ₗ[𝕜] F) (he : Continuous e) :
    Continuous e.symm := by
  rw [continuous_def]
  intro S hS
  have hpre : (e.symm) ⁻¹' S = e '' S := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [hpre]
  exact isOpenMap_of_surjective e.toLinearMap he e.surjective S hS

end GaloisForLFunctions
