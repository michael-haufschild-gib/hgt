import GaloisForLFunctions.HTGeometry.EuclideanSphereCoveringBound
import GaloisForLFunctions.HTGeometry.CoveringDimensionShrinking

/-!
# Compact subsets of Euclidean space have finite covering dimension

Every compact subset of `ℝ^m` admits, for each finite open cover, an open shrinking whose order is
bounded by a constant depending only on `m`.  The proof is volumetric: a maximal `δ/4`-separated net
of the compact set gives balls of radius `δ/2` that refine the cover, and the packing bound says no
point of `ℝ^m` can lie in more than `5^m` of those balls.

This supplies the finiteness input that the hull-dimension reduction needs, without the sharp
`ind ℝ^m ≤ m` theorem.
-/

open MeasureTheory Metric Set

namespace HTGeometry

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- A maximal separated net, returning the separation as well as the net property.  The
`exists_separated_net` of `EuclideanSphereCoveringBound` discards the separation, which is exactly
what the multiplicity bound needs. -/
theorem exists_separated_net_with_sep [Nontrivial E]
    {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (A : Set E) (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ C : Finset E, ↑C ⊆ A ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → η < dist x y) ∧
      ∀ x ∈ A, ∃ z ∈ C, dist x z ≤ η := by
  classical
  have hpow : (0 : ℝ) < (η / 2) ^ m := by positivity
  set B : ℝ := (R + η / 2) ^ m / (η / 2) ^ m with hB
  set K : Set ℕ := {n | ∃ C : Finset E, ↑C ⊆ A ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → η < dist x y) ∧ C.card = n} with hK
  have hKne : K.Nonempty := ⟨0, ∅, by simp, by simp, by simp⟩
  have hKbdd : ∀ n ∈ K, n ≤ ⌈B⌉₊ := by
    rintro n ⟨C, hCA, hCsep, rfl⟩
    have hcard := card_mul_pow_le_of_separated_finset hη hR C
      (fun x hx => hA x (hCA hx)) hCsep
    have hle : (C.card : ℝ) ≤ B := by rw [hB, le_div_iff₀ hpow]; linarith
    have : (C.card : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hle (Nat.le_ceil B)
    exact_mod_cast this
  have hmem : sSup K ∈ K := Nat.sSup_mem hKne ⟨⌈B⌉₊, hKbdd⟩
  obtain ⟨C, hCA, hCsep, hCcard⟩ := hmem
  refine ⟨C, hCA, hCsep, ?_⟩
  intro x hx
  by_contra hcon
  push Not at hcon
  have hxC : x ∉ C := by
    intro hxmem
    have hxx := hcon x hxmem
    rw [dist_self] at hxx
    linarith
  have hins : (insert x C).card = C.card + 1 := Finset.card_insert_of_notMem hxC
  have hsep' : ∀ u ∈ insert x C, ∀ v ∈ insert x C, u ≠ v → η < dist u v := by
    intro u hu v hv huv
    rw [Finset.mem_insert] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact absurd rfl huv
      · exact hcon v hv
    · rcases hv with rfl | hv
      · rw [dist_comm]
        exact hcon u hu
      · exact hCsep u hu v hv huv
  have hmemK : C.card + 1 ∈ K := ⟨insert x C, by
      intro y hy
      rw [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hCA hy, hsep', hins⟩
  have hle := le_csSup ⟨⌈B⌉₊, hKbdd⟩ hmemK
  rw [hCcard] at hle
  omega

/-- **Compact subsets of Euclidean space have finite covering dimension.**  Every finite open cover
of a compact `K ⊆ ℝ^m` has an open shrinking of order at most `5^m`. -/
theorem hasCoverDimLE_of_isCompact [Nontrivial E] {K : Set E} (hK : IsCompact K) :
    HasCoverDimLE (↥K) (5 ^ m - 1) := by
  classical
  intro ι _ U hUopen hUcov
  rcases isEmpty_or_nonempty (↥K) with hKe | hKne
  · exact ⟨U, hUopen, fun i => subset_rfl, hUcov, fun x => (hKe.false x).elim⟩
  haveI : Nonempty ι := by
    obtain ⟨x⟩ := hKne
    have hx : x ∈ ⋃ i, U i := by rw [hUcov]; exact Set.mem_univ x
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact ⟨i⟩
  choose W hWopen hWpre using fun i => isOpen_induced_iff.mp (hUopen i)
  have hKsub : K ⊆ ⋃ i, W i := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥K) ∈ ⋃ i, U i := by rw [hUcov]; exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [← hWpre i] at hi
    exact hi
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric hK hWopen hKsub
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : E)
  set R : ℝ := max R0 0 with hRdef
  have hR : (0 : ℝ) ≤ R := le_max_right _ _
  have hAnorm : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxb := hR0 hx
    rw [mem_closedBall, dist_zero_right] at hxb
    exact le_trans hxb (le_max_left _ _)
  obtain ⟨C, hCK, hCsep, hCnet⟩ :=
    exists_separated_net_with_sep (m := m) (η := δ / 4) (R := R) (by linarith) hR K hAnorm
  let g : E → ι := fun z => if h : ∃ i, ball z δ ⊆ W i then h.choose else Classical.arbitrary ι
  have hg : ∀ z ∈ K, ball z δ ⊆ W (g z) := by
    intro z hz
    have h : ∃ i, ball z δ ⊆ W i := hδ z hz
    simp only [g, dif_pos h]
    exact h.choose_spec
  set Vset : ι → Set E := fun i => ⋃ z ∈ (C.filter (fun z => g z = i)), ball z (δ / 2) with hVset
  refine ⟨fun i => Subtype.val ⁻¹' (Vset i), fun i => ?_, fun i => ?_, ?_, fun x => ?_⟩
  · exact IsOpen.preimage continuous_subtype_val
      (isOpen_biUnion fun z _ => isOpen_ball)
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
    rw [Finset.mem_filter] at hz
    have hzK : z ∈ K := hCK hz.1
    have hball : (x : E) ∈ ball z δ := by
      rw [mem_ball]
      have := mem_ball.mp hxz
      linarith
    have hxW : (x : E) ∈ W (g z) := hg z hzK hball
    rw [hz.2] at hxW
    rw [← hWpre i]
    exact hxW
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨z, hzC, hxz⟩ := hCnet (x : E) x.2
    refine Set.mem_iUnion.mpr ⟨g z, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨z, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hzC, rfl⟩
    · rw [mem_ball]
      linarith
  · set Sx : Set E := {z | z ∈ C ∧ dist (x : E) z < δ / 2} with hSx
    have hSxfin : Sx.Finite := Set.Finite.subset C.finite_toSet (fun z hz => hz.1)
    have hsub : {i | x ∈ Subtype.val ⁻¹' (Vset i)} ⊆ g '' Sx := by
      intro i hi
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hi
      rw [Finset.mem_filter] at hz
      exact ⟨z, ⟨hz.1, mem_ball.mp hxz⟩, hz.2⟩
    have hinj : Function.Injective (fun z : E => z - (x : E)) := fun a b h => sub_left_inj.mp h
    set T : Set E := (fun z : E => z - (x : E)) '' Sx with hT
    have hTnorm : ∀ w ∈ T, ‖w‖ ≤ δ / 2 := by
      rintro _ ⟨z, hz, rfl⟩
      have := hz.2
      rw [dist_eq_norm] at this
      rw [← norm_neg]
      simpa using le_of_lt this
    have hTsep : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → δ / 4 < dist u v := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
      have hab : a ≠ b := fun h => hne (by rw [h])
      have := hCsep a ha.1 b hb.1 hab
      simpa [dist_eq_norm, sub_sub_sub_cancel_right] using this
    obtain ⟨hTfin, hTcard⟩ :=
      finite_and_ncard_le_of_separated (m := m) (η := δ / 4) (R := δ / 2)
        (by linarith) (by linarith) T hTnorm hTsep
    have hpow : (0 : ℝ) < (δ / 8) ^ m := by positivity
    have hrw : (δ / 2 + δ / 4 / 2) ^ m = (5 : ℝ) ^ m * (δ / 8) ^ m := by
      rw [← mul_pow]
      ring_nf
    have hTle : (T.ncard : ℝ) ≤ (5 : ℝ) ^ m := by
      rw [hrw] at hTcard
      have h4 : δ / 4 / 2 = δ / 8 := by ring
      rw [h4] at hTcard
      exact le_of_mul_le_mul_right (by linarith [hTcard]) hpow
    have hTnat : T.ncard ≤ 5 ^ m := by exact_mod_cast hTle
    have hScard : Sx.ncard = T.ncard := (Set.ncard_image_of_injective Sx hinj).symm
    have himg : (g '' Sx).ncard ≤ Sx.ncard := Set.ncard_image_le hSxfin
    have hfinal : {i | x ∈ Subtype.val ⁻¹' (Vset i)}.ncard ≤ 5 ^ m := by
      refine le_trans (Set.ncard_le_ncard hsub (hSxfin.image g)) ?_
      exact le_trans himg (by rw [hScard]; exact hTnat)
    have hgoal : {i | x ∈ (fun i => Subtype.val ⁻¹' Vset i) i}.ncard ≤ 5 ^ m := hfinal
    have h51 : 1 ≤ 5 ^ m := Nat.one_le_pow _ _ (by norm_num)
    omega

end HTGeometry
