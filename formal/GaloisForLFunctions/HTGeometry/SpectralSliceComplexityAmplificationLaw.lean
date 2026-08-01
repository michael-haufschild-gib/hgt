import GaloisForLFunctions.HTGeometry.SyndeticDenseOrbitLaw

/-!
# Spectral-slice complexity amplification

A low-dimensional recurrent orbit can inherit a hardness threshold certified
in a much larger ambient space.  The missing mechanism is not mixing: a
family of orbit closures covers the ambient space.  Any point outside a proper
closed low-complexity set belongs to one member of that family; its preimage is
a nonempty open hard region on that compact slice.  A dense one-parameter flow
on the slice then visits that globally certified hard region syndetically.

Consequently the certifiable complexity scale is controlled by ambient
entropy, not by the dimension of one spectral torus.  The second theorem adds
an easy interior point on every slice and obtains ordered easy--hard--easy
alternation forever.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Ambient-to-slice hardness amplification.** If a continuous family of
compact recurrent slices covers an ambient space, every proper closed ambient
target is avoided syndetically by the dense flow on at least one slice. -/
theorem coveredCompactSlices_properClosedTarget_avoided_syndetically
    {T : Type*} [TopologicalSpace T] [AddGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    {P X : Type*} [TopologicalSpace X]
    (orbit : ℝ →+ T) (hdense : DenseRange orbit)
    (embed : P → T → X) (hembed : ∀ p, Continuous (embed p))
    (hcover : ∀ x : X, ∃ p z, embed p z = x)
    {C : Set X} (hCclosed : IsClosed C) (hCproper : C ≠ Set.univ) :
    ∃ p : P, ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ t ∈ Set.Icc a (a + L), embed p (orbit t) ∉ C := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem C).mp hCproper
  obtain ⟨p, z, hpz⟩ := hcover x
  let U : Set T := embed p ⁻¹' Cᶜ
  have hUopen : IsOpen U := hCclosed.isOpen_compl.preimage (hembed p)
  have hUne : U.Nonempty := by
    refine ⟨z, ?_⟩
    change embed p z ∉ C
    simpa [hpz] using hx
  obtain ⟨L, hL, hhits⟩ :=
    denseAddOrbit_open_hits_syndetically orbit hdense hUopen hUne
  refine ⟨p, L, hL, fun a ↦ ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  exact ⟨t, ht, hhard⟩

/-- **Ambient-scale easy--hard alternation law.** In addition to ambient
coverage, suppose every slice contains a designated point in the interior of
the low-complexity region.  Then one slice alternates forever from that easy
interior to the globally certified hard complement and back, with one finite
bound on every leg.

This theorem removes the apparent dimension-linear ceiling of a direct
volume bound on one spectral torus: `C` may be shown proper using the entropy
of the full ambient state or unitary space. -/
theorem coveredCompactSlices_easyHard_alternate_syndetically
    {T : Type*} [TopologicalSpace T] [AddGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    {P X : Type*} [TopologicalSpace X]
    (orbit : ℝ →+ T) (hdense : DenseRange orbit)
    (embed : P → T → X) (hembed : ∀ p, Continuous (embed p))
    (hcover : ∀ x : X, ∃ p z, embed p z = x)
    (base : T) {C : Set X} (hCclosed : IsClosed C)
    (hCproper : C ≠ Set.univ)
    (hbase : ∀ p, embed p base ∈ interior C) :
    ∃ p : P, ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tEasy ∈ Set.Icc a (a + L),
      ∃ tHard ∈ Set.Ioc tEasy (tEasy + L),
      ∃ tEasy' ∈ Set.Ioc tHard (tHard + L),
        embed p (orbit tEasy) ∈ interior C ∧
        embed p (orbit tHard) ∉ C ∧
        embed p (orbit tEasy') ∈ interior C := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem C).mp hCproper
  obtain ⟨p, z, hpz⟩ := hcover x
  let U : Set T := embed p ⁻¹' interior C
  let V : Set T := embed p ⁻¹' Cᶜ
  have hUopen : IsOpen U := isOpen_interior.preimage (hembed p)
  have hUne : U.Nonempty := ⟨base, hbase p⟩
  have hVopen : IsOpen V := hCclosed.isOpen_compl.preimage (hembed p)
  have hVne : V.Nonempty := by
    refine ⟨z, ?_⟩
    change embed p z ∉ C
    simpa [hpz] using hx
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro y hyU hyV
    exact hyV (interior_subset hyU)
  obtain ⟨L, hL, hhits⟩ :=
    denseAddOrbit_disjoint_open_targets_alternate_syndetically
      orbit hdense hUopen hUne hVopen hVne hdisj
  refine ⟨p, L, hL, fun a ↦ ?_⟩
  obtain ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
      hEasy, hHard, hEasy'⟩ := hhits a
  exact ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
    hEasy, hHard, hEasy'⟩

/-- **One hard seed forces permanent complexity alternation.** A single point
outside a closed low-complexity region is enough: if it lies on a compact
recurrent slice whose dense flow also contains an easy interior point, then
that same autonomous flow alternates easy--hard--easy forever with uniformly
bounded gaps.

This is the mechanism that lets ambient unitary geometry certify the depth of
one static Hamiltonian.  Ambient geometry is needed only to produce the hard
seed; compact recurrence amplifies that one seed into infinitely many ordered
hard epochs. -/
theorem compactSlice_hardSeed_easyHard_alternate_syndetically
    {T : Type*} [TopologicalSpace T] [AddGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    {X : Type*} [TopologicalSpace X]
    (orbit : ℝ →+ T) (hdense : DenseRange orbit)
    (embed : T → X) (hembed : Continuous embed)
    (base seed : T) {C : Set X} (hCclosed : IsClosed C)
    (hbase : embed base ∈ interior C) (hseed : embed seed ∉ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tEasy ∈ Set.Icc a (a + L),
      ∃ tHard ∈ Set.Ioc tEasy (tEasy + L),
      ∃ tEasy' ∈ Set.Ioc tHard (tHard + L),
        embed (orbit tEasy) ∈ interior C ∧
        embed (orbit tHard) ∉ C ∧
        embed (orbit tEasy') ∈ interior C := by
  let U : Set T := embed ⁻¹' interior C
  let V : Set T := embed ⁻¹' Cᶜ
  have hUopen : IsOpen U := isOpen_interior.preimage hembed
  have hUne : U.Nonempty := ⟨base, hbase⟩
  have hVopen : IsOpen V := hCclosed.isOpen_compl.preimage hembed
  have hVne : V.Nonempty := ⟨seed, hseed⟩
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro y hyU hyV
    exact hyV (interior_subset hyU)
  obtain ⟨L, hL, hhits⟩ :=
    denseAddOrbit_disjoint_open_targets_alternate_syndetically
      orbit hdense hUopen hUne hVopen hVne hdisj
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
      hEasy, hHard, hEasy'⟩ := hhits a
  exact ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
    hEasy, hHard, hEasy'⟩

end GaloisForLFunctions.HTGeometry
