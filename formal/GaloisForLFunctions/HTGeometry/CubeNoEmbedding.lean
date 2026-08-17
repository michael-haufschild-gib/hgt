import GaloisForLFunctions.HTGeometry.CubeSeparation
import GaloisForLFunctions.HTGeometry.SeparatorMap

/-!
# The `m`-cube does not embed in `ℝ^k` for `k < m`

An injective continuous image of the cube in a space of strictly smaller dimension would carry the
`m` pairs of opposite faces to `m` pairs of uniformly separated compact sets.  A fine brick cover of
the image has order `k + 1`, so the associated partition of unity, weighted by vectors in general
position, gives a map to `ℝ^m` that never vanishes and has the sign of each coordinate prescribed
on the two members of the corresponding pair.  Pulling back its coordinate zero sets produces `m`
separators of the opposite faces of the cube with empty intersection, contradicting the separation
theorem for the cube.

This is the Lebesgue dimension of Euclidean space in the form used by dimension theory: it forbids
a topological embedding of `[0,1]^m` into `ℝ^k` whenever `k < m`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- Two disjoint nonempty compact sets in a metric space are uniformly separated. -/
theorem exists_pos_lt_dist_of_disjoint_compact {X : Type*} [MetricSpace X] {A B : Set X}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hd : ∀ y ∈ A, y ∉ B) : ∃ ε > 0, ∀ y ∈ A, ∀ y' ∈ B, ε < dist y y' := by
  obtain ⟨y₀, hy₀A, hy₀min⟩ := hA.exists_isMinOn hAne (Metric.continuous_infDist_pt B).continuousOn
  have hpos : 0 < infDist y₀ B := by
    rw [← Metric.infDist_pos_iff_notMem_closure hBne, hB.isClosed.closure_eq]
    exact hd y₀ hy₀A
  refine ⟨infDist y₀ B / 2, by linarith, ?_⟩
  intro y hy y' hy'
  have h1 : infDist y₀ B ≤ infDist y B := isMinOn_iff.mp hy₀min y hy
  have h2 : infDist y B ≤ dist y y' := Metric.infDist_le_dist_of_mem hy'
  linarith

/-- **No continuous injection of the `m`-cube into a space of dimension below `m`.** -/
theorem not_injOn_unitCube {k m : ℕ} (hkm : k < m)
    (h : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (hc : ContinuousOn h (unitCube m)) : ¬ Set.InjOn h (unitCube m) := by
  classical
  intro hinj
  have hm : 0 < m := by omega
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- in dimension zero the target is a single point, but the cube has two vertices
    subst hk0
    have hne : (0 : EuclideanSpace ℝ (Fin m)) ≠ cubeOne m := by
      intro hEq
      have := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z ⟨0, hm⟩) hEq
      simp at this
    refine hne (hinj (zero_mem_unitCube m) (cubeOne_mem_unitCube m) ?_)
    exact PiLp.ext fun i => i.elim0
  · -- the faces and their images
    set faceLo : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
      fun i => {x | x ∈ unitCube m ∧ x i = 0} with hfaceLo
    set faceHi : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
      fun i => {x | x ∈ unitCube m ∧ x i = 1} with hfaceHi
    have hfaceLoClosed : ∀ i, IsClosed (faceLo i) := by
      intro i
      have : faceLo i = unitCube m ∩ (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' {0} := by
        ext x; simp [hfaceLo, Set.mem_inter_iff, and_comm]
      rw [this]
      exact (isClosed_unitCube m).inter
        (isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    have hfaceHiClosed : ∀ i, IsClosed (faceHi i) := by
      intro i
      have : faceHi i = unitCube m ∩ (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' {1} := by
        ext x; simp [hfaceHi, Set.mem_inter_iff, and_comm]
      rw [this]
      exact (isClosed_unitCube m).inter
        (isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    have hfaceLoSub : ∀ i, faceLo i ⊆ unitCube m := fun i x hx => hx.1
    have hfaceHiSub : ∀ i, faceHi i ⊆ unitCube m := fun i x hx => hx.1
    have hfaceLoCompact : ∀ i, IsCompact (faceLo i) := fun i =>
      (isCompact_unitCube m).of_isClosed_subset (hfaceLoClosed i) (hfaceLoSub i)
    have hfaceHiCompact : ∀ i, IsCompact (faceHi i) := fun i =>
      (isCompact_unitCube m).of_isClosed_subset (hfaceHiClosed i) (hfaceHiSub i)
    set P : Fin m → Set (EuclideanSpace ℝ (Fin k)) := fun i => h '' faceLo i with hP
    set Q : Fin m → Set (EuclideanSpace ℝ (Fin k)) := fun i => h '' faceHi i with hQ
    have hPcompact : ∀ i, IsCompact (P i) := fun i =>
      (hfaceLoCompact i).image_of_continuousOn (hc.mono (hfaceLoSub i))
    have hQcompact : ∀ i, IsCompact (Q i) := fun i =>
      (hfaceHiCompact i).image_of_continuousOn (hc.mono (hfaceHiSub i))
    have hPne : ∀ i, (P i).Nonempty := by
      intro i
      exact ⟨h 0, ⟨0, ⟨zero_mem_unitCube m, by simp⟩, rfl⟩⟩
    have hQne : ∀ i, (Q i).Nonempty := by
      intro i
      exact ⟨h (cubeOne m), ⟨cubeOne m, ⟨cubeOne_mem_unitCube m, by simp⟩, rfl⟩⟩
    have hdisj : ∀ i, ∀ y ∈ P i, y ∉ Q i := by
      rintro i y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
      have := hinj hx'.1 hx.1 hxx
      subst this
      have h0 := hx.2
      have h1 := hx'.2
      rw [h0] at h1
      norm_num at h1
    -- a uniform separation constant
    have hsepi : ∀ i, ∃ ε > 0, ∀ y ∈ P i, ∀ y' ∈ Q i, ε < dist y y' := fun i =>
      exists_pos_lt_dist_of_disjoint_compact (hPcompact i) (hQcompact i) (hPne i) (hQne i)
        (hdisj i)
    choose εi hεipos hεi using hsepi
    have huniv : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    set ε : ℝ := Finset.univ.inf' huniv εi with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef, Finset.lt_inf'_iff]
      exact fun i _ => hεipos i
    have hsep : ∀ i, ∀ y ∈ P i, ∀ y' ∈ Q i, ε < dist y y' := by
      intro i y hy y' hy'
      have hle : ε ≤ εi i := Finset.inf'_le _ (Finset.mem_univ i)
      exact lt_of_le_of_lt hle (hεi i y hy y' hy')
    -- the nonvanishing separating map on the image of the cube
    obtain ⟨u, hucont, huP, huQ, hune⟩ :=
      exists_separating_map (K := h '' unitCube m) hk hkm
        ((isCompact_unitCube m).image_of_continuousOn hc) hεpos hsep
    set g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun x => u (h x) with hg
    have hgcont : ∀ i : Fin m, ContinuousOn (fun x => g x i) (unitCube m) := by
      intro i
      refine ContinuousOn.comp (g := fun v : EuclideanSpace ℝ (Fin m) => v i)
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousOn ?_ (fun x _ => Set.mem_univ _)
      exact hucont.comp hc fun x hx => ⟨x, hx, rfl⟩
    -- the induced separators
    set U : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
      fun i => {x | x ∈ unitCube m ∧ g x i < 0} with hU
    set W : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
      fun i => {x | x ∈ unitCube m ∧ 0 < g x i} with hW
    set L : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
      fun i => {x | x ∈ unitCube m ∧ g x i = 0} with hL
    have hclosurearg : ∀ (i : Fin m) (V : Set (EuclideanSpace ℝ (Fin m))) (c : Set ℝ),
        V ⊆ unitCube m → (∀ x ∈ V, g x i ∈ c) → ∀ x ∈ closure V, g x i ∈ closure c := by
      intro i V c hVsub hVc x hx
      have hxcube : x ∈ unitCube m := by
        have := closure_mono hVsub hx
        rwa [(isClosed_unitCube m).closure_eq] at this
      have hwithin : ContinuousWithinAt (fun z => g z i) V x :=
        ((hgcont i) x hxcube).mono hVsub
      have hmem := hwithin.mem_closure_image hx
      exact closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hVc z hz) hmem
    have hUW : ∀ i, ∀ x ∈ U i, x ∉ closure (W i) := by
      intro i x hx hcl
      have hsubset : W i ⊆ unitCube m := fun z hz => hz.1
      have := hclosurearg i (W i) (Set.Ioi 0) hsubset (fun z hz => hz.2) x hcl
      rw [closure_Ioi] at this
      exact absurd hx.2 (not_lt.mpr this)
    have hWU : ∀ i, ∀ x ∈ W i, x ∉ closure (U i) := by
      intro i x hx hcl
      have hsubset : U i ⊆ unitCube m := fun z hz => hz.1
      have := hclosurearg i (U i) (Set.Iio 0) hsubset (fun z hz => hz.2) x hcl
      rw [closure_Iio] at this
      exact absurd hx.2 (not_lt.mpr this)
    have hAface : ∀ i, ∀ x ∈ unitCube m, x i = 0 → x ∈ U i := by
      intro i x hx hxi
      refine ⟨hx, ?_⟩
      exact huP i (h x) ⟨x, ⟨hx, hxi⟩, rfl⟩ ⟨x, hx, rfl⟩
    have hBface : ∀ i, ∀ x ∈ unitCube m, x i = 1 → x ∈ W i := by
      intro i x hx hxi
      refine ⟨hx, ?_⟩
      exact huQ i (h x) ⟨x, ⟨hx, hxi⟩, rfl⟩ ⟨x, hx, rfl⟩
    have hcover : ∀ x ∈ unitCube m, ∀ i, x ∈ U i ∨ x ∈ W i ∨ x ∈ L i := by
      intro x hx i
      rcases lt_trichotomy (g x i) 0 with hlt | heq | hgt
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr (Or.inr ⟨hx, heq⟩)
      · exact Or.inr (Or.inl ⟨hx, hgt⟩)
    obtain ⟨x, hxcube, hxL⟩ :=
      exists_mem_iInter_of_separators hcover hUW hWU
        (fun i => ⟨0, hAface i 0 (zero_mem_unitCube m) (by simp)⟩)
        (fun i => ⟨cubeOne m, hBface i (cubeOne m) (cubeOne_mem_unitCube m) (by simp)⟩)
        hAface hBface
    obtain ⟨i, hi⟩ := hune (h x) ⟨x, hxcube, rfl⟩
    exact hi (hxL i).2

end GaloisForLFunctions.HTGeometry
