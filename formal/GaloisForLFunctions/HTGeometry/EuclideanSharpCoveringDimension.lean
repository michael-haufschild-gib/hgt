import GaloisForLFunctions.HTGeometry.BrickCoverCompact
import GaloisForLFunctions.HTGeometry.CoveringDimensionShrinking

/-!
# The sharp covering dimension of a compact set in Euclidean space

A compact subset of `ℝ^k` has Lebesgue covering dimension at most `k`.  The shrinking is the brick
cover: `k + 1` shifted families of open boxes cover the space, no point lies in more than one box of
a single family, and the mesh can be made smaller than any Lebesgue number of a given cover.  Each
brick is therefore contained in one member of the cover, and grouping the bricks by a chosen such
member gives a shrinking whose order is the order `k + 1` of the brick cover.

This is the exact bound: the matching lower bound is that `[0,1]^k` does not embed in `ℝ^{k-1}`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- A subsingleton space has covering dimension zero. -/
theorem hasCoverDimLE_zero_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] :
    HasCoverDimLE X 0 := by
  classical
  intro ι _ U hUopen hUcov
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨U, hUopen, fun i => subset_rfl, hUcov, fun x => (hX.false x).elim⟩
  obtain ⟨x⟩ := hX
  have hx : x ∈ ⋃ i, U i := by rw [hUcov]; exact Set.mem_univ x
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hx
  refine ⟨fun i => if i = i₀ then U i₀ else ∅, fun i => ?_, fun i => ?_, ?_, fun y => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hUopen i₀
    · exact isOpen_empty
  · dsimp only
    split_ifs with h
    · rw [h]
    · exact Set.empty_subset _
  · refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨i₀, ?_⟩
    rw [Subsingleton.elim y x]
    split_ifs with h
    · exact hi₀
    · exact absurd rfl h
  · refine le_trans (Set.ncard_le_ncard (t := ({i₀} : Set ι)) ?_ (Set.finite_singleton i₀)) ?_
    · intro i hi
      simp only [Set.mem_setOf_eq] at hi
      split_ifs at hi with h
      · exact h
      · exact absurd hi (Set.notMem_empty y)
    · simp

/-- **The sharp covering dimension bound.**  A compact subset of `ℝ^k` has covering dimension at
most `k`. -/
theorem hasCoverDimLE_of_isCompact_euclidean {k : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin k))} (hK : IsCompact K) : HasCoverDimLE (↥K) k := by
  classical
  intro ι _ U hUopen hUcov
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · haveI : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
      ⟨fun x y => PiLp.ext fun i => i.elim0⟩
    haveI : Subsingleton (↥K) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
    exact hasCoverDimLE_zero_of_subsingleton U hUopen hUcov
  rcases isEmpty_or_nonempty (↥K) with hKe | hKne
  · exact ⟨U, hUopen, fun i => subset_rfl, hUcov, fun x => (hKe.false x).elim⟩
  haveI : Nonempty ι := by
    obtain ⟨x⟩ := hKne
    have hx : x ∈ ⋃ i, U i := by rw [hUcov]; exact Set.mem_univ x
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp hx
    exact ⟨i⟩
  -- lift the cover to open sets of the ambient space
  choose W hWopen hWpre using fun i => isOpen_induced_iff.mp (hUopen i)
  have hKsub : K ⊆ ⋃ i, W i := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥K) ∈ ⋃ i, U i := by rw [hUcov]; exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [← hWpre i] at hi
    exact hi
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := lebesgue_number_lemma_of_metric hK hWopen hKsub
  -- a brick cover of mesh below the Lebesgue number
  have hsq : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  obtain ⟨δ, hδpos, hδmesh⟩ : ∃ δ : ℝ, 0 < δ ∧ Real.sqrt k * δ < δ₀ :=
    ⟨δ₀ / (2 * Real.sqrt k), by positivity, by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith⟩
  obtain ⟨N, B, hBopen, -, hBcov, hBmesh, hBord⟩ :=
    exists_enumerated_brick_cover hk hK hδpos
  -- each used brick sits inside one member of the cover
  set P : ℕ → Prop := fun p => p < N ∧ ∃ x, x ∈ B p ∧ x ∈ K with hP
  have hchoice : ∀ p, P p → ∃ i, B p ⊆ W i := by
    rintro p ⟨-, x, hxB, hxK⟩
    obtain ⟨i, hi⟩ := hδ₀ x hxK
    refine ⟨i, fun y hy => hi ?_⟩
    rw [mem_ball]
    exact lt_of_le_of_lt (hBmesh p y hy x hxB) hδmesh
  set g : ℕ → ι := fun p => if h : P p then (hchoice p h).choose else Classical.arbitrary ι with hg
  have hgspec : ∀ p, P p → B p ⊆ W (g p) := by
    intro p hp
    simp only [hg, dif_pos hp]
    exact (hchoice p hp).choose_spec
  set Vamb : ι → Set (EuclideanSpace ℝ (Fin k)) :=
    fun i => ⋃ p ∈ (Finset.range N).filter (fun p => P p ∧ g p = i), B p with hVamb
  refine ⟨fun i => Subtype.val ⁻¹' Vamb i, fun i => ?_, fun i => ?_, ?_, fun x => ?_⟩
  · exact IsOpen.preimage continuous_subtype_val (isOpen_biUnion fun p _ => hBopen p)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hPp, hgp⟩ := hp
    rw [← hWpre i]
    have := hgspec p hPp hxp
    rwa [hgp] at this
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨p, hpN, hxp⟩ := hBcov (x : EuclideanSpace ℝ (Fin k)) x.2
    have hPp : P p := ⟨hpN, ⟨(x : EuclideanSpace ℝ (Fin k)), hxp, x.2⟩⟩
    refine Set.mem_iUnion.mpr ⟨g p, Set.mem_iUnion₂.mpr ⟨p, ?_, hxp⟩⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hpN, hPp, rfl⟩
  · -- the order bound transfers from the brick cover
    set S : Finset ι := Finset.univ.filter (fun i => (x : EuclideanSpace ℝ (Fin k)) ∈ Vamb i)
      with hS
    have hmemS : ∀ i, i ∈ S ↔ (x : EuclideanSpace ℝ (Fin k)) ∈ Vamb i := by
      intro i
      rw [hS, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
    have hpick : ∀ i ∈ S, ∃ p, p < N ∧ P p ∧ g p = i ∧
        (x : EuclideanSpace ℝ (Fin k)) ∈ B p := by
      intro i hi
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp ((hmemS i).mp hi)
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact ⟨p, hp.1, hp.2.1, hp.2.2, hxp⟩
    choose π hπN hπP hπg hπB using hpick
    have key : ∃ T : Finset ℕ, T.card = S.card ∧ (∀ p ∈ T, p < N) ∧
        (∀ p ∈ T, (x : EuclideanSpace ℝ (Fin k)) ∈ B p) := by
      refine ⟨S.attach.image (fun i : {y // y ∈ S} => π i.1 i.2), ?_, ?_, ?_⟩
      · have hinj : Set.InjOn (fun i : {y // y ∈ S} => π i.1 i.2)
            (S.attach : Set {y // y ∈ S}) := by
          intro a ha b hb hab
          simp only at hab
          have hgg : g (π a.1 a.2) = g (π b.1 b.2) := by rw [hab]
          rw [hπg a.1 a.2, hπg b.1 b.2] at hgg
          exact Subtype.ext hgg
        rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
      · intro p hp
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
        exact hπN a.1 a.2
      · intro p hp
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
        exact hπB a.1 a.2
    obtain ⟨T, hTcard, hTlt, hTmem⟩ := key
    have hbound := hBord (x : EuclideanSpace ℝ (Fin k)) T hTlt hTmem
    have hset : {i : ι | x ∈ Subtype.val ⁻¹' Vamb i} = (S : Set ι) := by
      ext i
      rw [Set.mem_setOf_eq, Finset.mem_coe, hmemS i]
      rfl
    rw [hset, Set.ncard_coe_finset]
    omega

end GaloisForLFunctions.HTGeometry
