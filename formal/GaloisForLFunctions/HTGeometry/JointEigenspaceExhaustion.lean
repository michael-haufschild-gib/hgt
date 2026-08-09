import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Tactic.Abel

/-!
# Only realized characters carry joint eigenvectors

If an independent family of subspaces exhausts the whole module and each member is a simultaneous
eigenspace for a family of operators, then no unrealized scalar pattern carries a joint
eigenvector.

The proof is a finite induction along the partial sums of the exhausting family: a joint
eigenvector lying in a partial sum has its leading component killed by the operator that separates
its pattern from that component's character, and independence then removes the component
altogether.  No projector and no direct-sum machinery is used.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K M J ι : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Simultaneous eigenspace of a family of operators for a scalar pattern. -/
def jointEigenspace (T : J → M →ₗ[K] M) (s : J → K) : Submodule K M :=
  ⨅ j, LinearMap.ker (T j - s j • LinearMap.id)

theorem mem_jointEigenspace_iff (T : J → M →ₗ[K] M) (s : J → K) (x : M) :
    x ∈ jointEigenspace T s ↔ ∀ j, T j x = s j • x := by
  simp only [jointEigenspace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/-- **Unrealized patterns carry no joint eigenvector.** -/
theorem jointEigenspace_eq_bot_of_forall_ne
    (T : J → M →ₗ[K] M) (V : ι → Submodule K M) (c : ι → J → K)
    (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤)
    (hc : ∀ i, ∀ x ∈ V i, ∀ j, T j x = c i j • x)
    (s : J → K) (hs : ∀ i, c i ≠ s) :
    jointEigenspace T s = ⊥ := by
  classical
  have hVinv : ∀ (i : ι) (j : J), Submodule.map (T j) (V i) ≤ V i := by
    rintro i j y ⟨x, hx, rfl⟩
    rw [hc i x hx j]
    exact Submodule.smul_mem _ _ hx
  have hinv : ∀ (S : Set ι) (j : J) (z : M),
      z ∈ (⨆ i ∈ S, V i) → T j z ∈ ⨆ i ∈ S, V i := by
    intro S j z hz
    have hle : Submodule.map (T j) (⨆ i ∈ S, V i) ≤ ⨆ i ∈ S, V i := by
      rw [Submodule.map_iSup]
      refine iSup_le fun i => ?_
      rw [Submodule.map_iSup]
      exact iSup_le fun hi => le_trans (hVinv i j) (le_biSup V hi)
    exact hle ⟨z, hz, rfl⟩
  have key : ∀ (F : Finset ι) (x : M), (∀ j, T j x = s j • x) →
      x ∈ (⨆ i ∈ (↑F : Set ι), V i) → x = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro x _ hx
        simpa using hx
    | @insert i F' hi ih =>
        intro x hx hmem
        rw [Finset.coe_insert, iSup_insert] at hmem
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hmem
        obtain ⟨j, hj⟩ : ∃ j, c i j ≠ s j := by
          by_contra hcon
          exact hs i (funext fun j => by
            by_contra hne
            exact hcon ⟨j, hne⟩)
        have hTy : T j y = c i j • y := hc i y hy j
        have hTz : T j z ∈ ⨆ i' ∈ (↑F' : Set ι), V i' := hinv _ j z hz
        have hsum : c i j • y + T j z = s j • y + s j • z := by
          have h := hx j
          rw [map_add, hTy, smul_add] at h
          exact h
        have hyz : (s j - c i j) • y = T j z - s j • z := by
          have h2 : T j z = s j • y + s j • z - c i j • y := by
            rw [← hsum]
            abel
          rw [h2, sub_smul]
          abel
        have hyW : y ∈ ⨆ i' ∈ (↑F' : Set ι), V i' := by
          have hmem2 : (s j - c i j) • y ∈ ⨆ i' ∈ (↑F' : Set ι), V i' := by
            rw [hyz]
            exact Submodule.sub_mem _ hTz (Submodule.smul_mem _ _ hz)
          exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr (Ne.symm hj))).mp hmem2
        have hdisj : Disjoint (V i) (⨆ i' ∈ (↑F' : Set ι), V i') :=
          hV.disjoint_biSup (by simpa using hi)
        have hy0 : y = 0 := by
          have hbot := hdisj.eq_bot
          have hmem3 : y ∈ V i ⊓ ⨆ i' ∈ (↑F' : Set ι), V i' := ⟨hy, hyW⟩
          rw [hbot] at hmem3
          simpa using hmem3
        subst hy0
        rw [zero_add] at hx ⊢
        exact ih z hx hz
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' := (mem_jointEigenspace_iff T s x).mp hx
  have hxtop : x ∈ ⨆ (F : Finset ι), ⨆ i ∈ F, V i := by
    rw [← iSup_eq_iSup_finset]
    exact htop ▸ Submodule.mem_top
  have hdir : Directed (· ≤ ·) (fun F : Finset ι => ⨆ i ∈ F, V i) := by
    intro F₁ F₂
    exact ⟨F₁ ∪ F₂,
      iSup₂_mono' fun i hi => ⟨i, Finset.mem_union_left _ hi, le_rfl⟩,
      iSup₂_mono' fun i hi => ⟨i, Finset.mem_union_right _ hi, le_rfl⟩⟩
  obtain ⟨F, hF⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hxtop
  simpa using key F x hx' hF

end GaloisForLFunctions.HTGeometry
