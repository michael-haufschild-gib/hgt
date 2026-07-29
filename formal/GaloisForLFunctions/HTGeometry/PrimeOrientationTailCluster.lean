import GaloisForLFunctions.HTGeometry.PrimeOrientationConstraintOpacity
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Compactness.Compact

/-!
# Tail-cluster constraints of prime orientations

A countable family of Boolean prime orientations determines a sequence in its full orientation
cube.  This file identifies the finite patterns recurring infinitely often with the finite
projections of the sequence's tail-cluster set.

The main theorem is the exact corona-annihilator law: a finite cylinder-linear combination of the
orientation signs vanishes away from finitely many coordinates if and only if its continuous
linear form vanishes on every tail-cluster constraint.  Thus the tail quotient is read entirely on
the compact cluster geometry, without choosing a trajectory or a representative at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Restrict a full orientation pattern to a finite coordinate set. -/
def orientationRestriction {J : Type*} (I : Finset J) (x : J → Bool) : I → Bool :=
  fun i => x i

theorem continuous_orientationRestriction {J : Type*} (I : Finset J) :
    Continuous (orientationRestriction I) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (i : J) : Continuous (fun x : J → Bool => x i))

/-- The finite cylinder cut out by one restricted Boolean pattern. -/
def orientationCylinder {J : Type*} (I : Finset J) (b : I → Bool) :
    Set (J → Bool) :=
  orientationRestriction I ⁻¹' {b}

theorem isClopen_orientationCylinder {J : Type*} (I : Finset J) (b : I → Bool) :
    IsClopen (orientationCylinder I b) := by
  constructor
  · exact (isClosed_discrete ({b} : Set (I → Bool))).preimage
      (continuous_orientationRestriction I)
  · exact (isOpen_discrete ({b} : Set (I → Bool))).preimage
      (continuous_orientationRestriction I)

theorem mem_orientationCylinder_iff {J : Type*} (I : Finset J)
    (b : I → Bool) (x : J → Bool) :
    x ∈ orientationCylinder I b ↔ ∀ i : I, x i = b i := by
  simp only [orientationCylinder, Set.mem_preimage, Set.mem_singleton_iff,
    orientationRestriction, funext_iff]

/-- The compact tail-cluster constraint of a sequence in the orientation cube. -/
def primeOrientationTailClusterSet {J : Type*} (θ : ℕ → (J → Bool)) : Set (J → Bool) :=
  {x | MapClusterPt x atTop θ}

theorem isClosed_primeOrientationTailClusterSet
    {J : Type*} (θ : ℕ → (J → Bool)) :
    IsClosed (primeOrientationTailClusterSet θ) := by
  have hset : primeOrientationTailClusterSet θ =
      ⋂ n : ℕ, closure (θ '' Ici n) := by
    ext x
    simp only [primeOrientationTailClusterSet, Set.mem_setOf_eq,
      mapClusterPt_atTop_iff_forall_mem_closure, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun n => isClosed_closure

theorem primeOrientationTailClusterSet_nonempty
    {J : Type*} (θ : ℕ → (J → Bool)) :
    (primeOrientationTailClusterSet θ).Nonempty := by
  obtain ⟨x, -, hx⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (J → Bool))).exists_mapClusterPt_of_frequently
      (show ∃ᶠ n in atTop, θ n ∈ (Set.univ : Set (J → Bool)) by
        rw [Nat.frequently_atTop_iff_infinite]
        exact Set.infinite_univ)
  exact ⟨x, hx⟩

/-- A finite pattern occurs infinitely often exactly when it extends to a point of the full
tail-cluster constraint. -/
theorem orientationPattern_fiber_infinite_iff_tailCluster_extension
    {J : Type*} (θ : ℕ → (J → Bool)) (I : Finset J) (b : I → Bool) :
    {n | orientationRestriction I (θ n) = b}.Infinite ↔
      ∃ x ∈ primeOrientationTailClusterSet θ, orientationRestriction I x = b := by
  constructor
  · intro hinf
    have hfreq : ∃ᶠ n in atTop, θ n ∈ orientationCylinder I b := by
      rw [Nat.frequently_atTop_iff_infinite]
      simpa only [orientationCylinder, Set.preimage_setOf_eq,
        Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    have hcompact : IsCompact (orientationCylinder I b) :=
      (isClopen_orientationCylinder I b).1.isCompact
    obtain ⟨x, hxC, hxcluster⟩ := hcompact.exists_mapClusterPt_of_frequently hfreq
    exact ⟨x, hxcluster, hxC⟩
  · rintro ⟨x, hxcluster, hxI⟩
    have hxC : x ∈ orientationCylinder I b := hxI
    have hfreq : ∃ᶠ n in atTop, θ n ∈ orientationCylinder I b :=
      hxcluster.frequently ((isClopen_orientationCylinder I b).2.mem_nhds hxC)
    rw [Nat.frequently_atTop_iff_infinite] at hfreq
    simpa only [orientationCylinder, Set.preimage_setOf_eq,
      Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] using hfreq

/-- **Canonical inverse-limit law.**  The tail-cluster constraint consists exactly of the full
orientation patterns whose restriction to every finite coordinate chamber recurs infinitely
often. -/
theorem mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur
    {J : Type*} (θ : ℕ → (J → Bool)) (x : J → Bool) :
    x ∈ primeOrientationTailClusterSet θ ↔
      ∀ I : Finset J,
        {n | orientationRestriction I (θ n) = orientationRestriction I x}.Infinite := by
  classical
  constructor
  · intro hx I
    exact (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I
      (orientationRestriction I x)).2 ⟨x, hx, rfl⟩
  · intro hrecur
    rw [primeOrientationTailClusterSet, Set.mem_setOf_eq, mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
    obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp htopen x hxt
    have hfreq : ∃ᶠ n in atTop,
        orientationRestriction I (θ n) = orientationRestriction I x := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact hrecur I
    exact hfreq.mono fun n hn => hts (hpi fun j hj => by
      have hj' : θ n j = x j := congrFun hn ⟨j, hj⟩
      rw [hj']
      exact (hu j hj).2)

/-- Every finite chamber of the full tail constraint is exactly the tail constraint of the
restricted orientation sequence. -/
theorem image_tailCluster_orientationRestriction
    {J : Type*} (θ : ℕ → (J → Bool)) (I : Finset J) :
    orientationRestriction I '' primeOrientationTailClusterSet θ =
      primeOrientationTailClusterSet (fun n => orientationRestriction I (θ n)) := by
  classical
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (continuous_orientationRestriction I).continuousAt.mapClusterPt hx
  · intro hy
    have hinf : {n | orientationRestriction I (θ n) = y}.Infinite := by
      have hfull :=
        (orientationPattern_fiber_infinite_iff_tailCluster_extension
          (fun n => orientationRestriction I (θ n)) Finset.univ
          (orientationRestriction Finset.univ y)).2 ⟨y, hy, rfl⟩
      simpa [orientationRestriction, funext_iff] using hfull
    obtain ⟨x, hx, hxy⟩ :=
      (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I y).1 hinf
    exact ⟨x, hx, hxy⟩

/-- **Finite-observable constraint law.**  Two arbitrary observations of a finite orientation
cylinder agree away from finitely many prime coordinates exactly when they agree at every point of
the complete tail-cluster constraint. -/
theorem finiteObservable_eventuallyEq_iff_eq_tailCluster
    {J A : Type*} (θ : ℕ → (J → Bool)) (I : Finset J)
    (f g : (I → Bool) → A) :
    {n | f (orientationRestriction I (θ n)) ≠
        g (orientationRestriction I (θ n))}.Finite ↔
      ∀ x ∈ primeOrientationTailClusterSet θ,
        f (orientationRestriction I x) = g (orientationRestriction I x) := by
  classical
  constructor
  · intro hfinite x hx
    by_contra hxne
    let b : I → Bool := orientationRestriction I x
    have hinf : {n | orientationRestriction I (θ n) = b}.Infinite :=
      (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I b).2 ⟨x, hx, rfl⟩
    apply (hinf.mono ?_) hfinite
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    rw [hn]
    exact hxne
  · intro hagree
    let badPatterns : Finset (I → Bool) :=
      Finset.univ.filter fun b => f b ≠ g b
    let fibre (b : I → Bool) : Set ℕ :=
      {n | orientationRestriction I (θ n) = b}
    have hfibre : ∀ b ∈ badPatterns, (fibre b).Finite := by
      intro b hb
      by_contra hfinite
      have hinf : (fibre b).Infinite := hfinite
      obtain ⟨x, hxcluster, hxb⟩ :=
        (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I b).1 hinf
      have hxeq := hagree x hxcluster
      have hbne : f b ≠ g b := (Finset.mem_filter.mp hb).2
      exact hbne (hxb ▸ hxeq)
    let U : Set ℕ := ⋃ b ∈ (badPatterns : Set (I → Bool)), fibre b
    have hUfinite : U.Finite := by
      apply badPatterns.finite_toSet.biUnion
      intro b hb
      exact hfibre b (by simpa using hb)
    apply hUfinite.subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    let b : I → Bool := orientationRestriction I (θ n)
    have hbmem : b ∈ badPatterns := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ b, hn⟩
    exact Set.mem_iUnion₂.mpr ⟨b, hbmem, rfl⟩

/-- The finite cylinder-linear functional attached to a coefficient vector. -/
def orientationLinearForm {J : Type*} (I : Finset J) (c : I → ℂ)
    (x : J → Bool) : ℂ :=
  ∑ i, c i * primeDirichletSign (x i)

/-- **Tail-cluster annihilator law.**  A finite linear combination of orientation signs vanishes
off a finite coordinate set exactly when its cylinder-linear functional vanishes on the complete
tail-cluster constraint. -/
theorem tailRelation_iff_linearForm_vanishes_tailCluster
    {J : Type*} (θ : ℕ → (J → Bool)) (I : Finset J) (c : I → ℂ) :
    {n | orientationLinearForm I c (θ n) ≠ 0}.Finite ↔
      ∀ x ∈ primeOrientationTailClusterSet θ, orientationLinearForm I c x = 0 := by
  classical
  constructor
  · intro hfinite x hx
    by_contra hxne
    let b : I → Bool := orientationRestriction I x
    have hinf : {n | orientationRestriction I (θ n) = b}.Infinite :=
      (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I b).2 ⟨x, hx, rfl⟩
    apply (hinf.mono ?_) hfinite
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    have hform : orientationLinearForm I c (θ n) =
        orientationLinearForm I c x := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : θ n i = x i := congrFun hn i
      rw [hi]
    exact hform ▸ hxne
  · intro hvanish
    let badPatterns : Finset (I → Bool) :=
      Finset.univ.filter fun b =>
        (∑ i, c i * primeDirichletSign (b i)) ≠ 0
    let fibre (b : I → Bool) : Set ℕ :=
      {n | orientationRestriction I (θ n) = b}
    have hfibre : ∀ b ∈ badPatterns, (fibre b).Finite := by
      intro b hb
      by_contra hfinite
      have hinf : (fibre b).Infinite := hfinite
      obtain ⟨x, hxcluster, hxb⟩ :=
        (orientationPattern_fiber_infinite_iff_tailCluster_extension θ I b).1 hinf
      have hxzero := hvanish x hxcluster
      have hxeq : orientationLinearForm I c x =
          ∑ i, c i * primeDirichletSign (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : x i = b i := congrFun hxb i
        rw [hi]
      have hbne : (∑ i, c i * primeDirichletSign (b i)) ≠ 0 :=
        (Finset.mem_filter.mp hb).2
      exact hbne (hxeq ▸ hxzero)
    let U : Set ℕ := ⋃ b ∈ (badPatterns : Set (I → Bool)), fibre b
    have hUfinite : U.Finite := by
      apply badPatterns.finite_toSet.biUnion
      intro b hb
      exact hfibre b (by simpa using hb)
    apply hUfinite.subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    let b : I → Bool := orientationRestriction I (θ n)
    have hbmem : b ∈ badPatterns := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ b, ?_⟩
      have hbfun : b = fun i : I => θ n i := by
        funext i
        rfl
      have hform :
          orientationLinearForm I c (θ n) =
            ∑ i, c i * primeDirichletSign (b i) := by
        rw [orientationLinearForm, hbfun]
      intro hzero
      exact hn (hform.trans hzero)
    refine Set.mem_iUnion₂.mpr ⟨b, ?_, ?_⟩
    · exact hbmem
    · rfl

/-- On all coordinates, the cylinder-linear form is the ordinary finite coefficient sum. -/
theorem orientationLinearForm_univ {J : Type*} [Fintype J]
    (c : J → ℂ) (ε : J → ℕ → Bool) (n : ℕ) :
    orientationLinearForm Finset.univ (fun i => c i) (fun j => ε j n) =
      ∑ j, c j * primeDirichletSign (ε j n) := by
  classical
  simp only [orientationLinearForm]
  rw [← Finset.sum_subtype Finset.univ (by intro j; simp)
    (fun j => c j * primeDirichletSign (ε j n))]

/-- **Corona-span law.**  A finite prime-orientation family is independent modulo finite support
exactly when its coordinate signs are linearly independent as functions on the compact
tail-cluster constraint. -/
theorem primeOrientationTailIndependent_iff_tailClusterLinearIndependent
    {J : Type*} [Fintype J] (ε : J → ℕ → Bool) :
    PrimeOrientationTailIndependent ε ↔
      ∀ c : J → ℂ,
        (∀ x ∈ primeOrientationTailClusterSet (fun n j => ε j n),
          orientationLinearForm Finset.univ (fun i => c i) x = 0) →
        c = 0 := by
  classical
  constructor
  · intro htail c hcluster
    apply htail c
    have hfinite :=
      (tailRelation_iff_linearForm_vanishes_tailCluster
        (fun n j => ε j n) Finset.univ (fun i => c i)).2 hcluster
    simpa only [orientationLinearForm_univ] using hfinite
  · intro hcluster c hfinite
    apply hcluster c
    apply (tailRelation_iff_linearForm_vanishes_tailCluster
      (fun n j => ε j n) Finset.univ (fun i => c i)).1
    simpa only [orientationLinearForm_univ] using hfinite

/-- Repeat every term of a Boolean-orientation sequence infinitely often, using the canonical
pairing of natural numbers. -/
def infinitelyRepeatedOrientation {J : Type*} (θ : ℕ → (J → Bool)) :
    ℕ → (J → Bool) := fun n => θ (Nat.unpair n).1

/-- Every finite pattern attained by the original sequence occurs infinitely often in its
canonical repetition. -/
theorem infinitelyRepeatedOrientation_pattern_fiber_infinite
    {J : Type*} (θ : ℕ → (J → Bool)) (I : Finset J) (b : I → Bool)
    (hattain : ∃ n, orientationRestriction I (θ n) = b) :
    {n | orientationRestriction I (infinitelyRepeatedOrientation θ n) = b}.Infinite := by
  classical
  obtain ⟨n, hn⟩ := hattain
  let f : ℕ → ℕ := fun m => Nat.pair n m
  have hf : Function.Injective f := by
    intro a c hac
    have hright := congrArg (fun k => (Nat.unpair k).2) hac
    simpa [f, Nat.unpair_pair] using hright
  apply (Set.infinite_range_of_injective hf).mono
  intro k hk
  obtain ⟨m, rfl⟩ := hk
  simpa [f, infinitelyRepeatedOrientation, Nat.unpair_pair] using hn

/-- **Canonical repeated-sequence cluster law.**  The tail cluster of the canonical infinite
repetition is exactly the inverse-limit closure of the finite patterns attained by the original
sequence. -/
theorem mem_tailCluster_infinitelyRepeatedOrientation_iff
    {J : Type*} (θ : ℕ → (J → Bool)) (x : J → Bool) :
    x ∈ primeOrientationTailClusterSet (infinitelyRepeatedOrientation θ) ↔
      ∀ I : Finset J, ∃ n, orientationRestriction I (θ n) = orientationRestriction I x := by
  rw [mem_primeOrientationTailClusterSet_iff_all_finite_patterns_recur]
  constructor
  · intro h I
    obtain ⟨n, hn⟩ := (h I).nonempty
    exact ⟨(Nat.unpair n).1, hn⟩
  · intro h I
    exact infinitelyRepeatedOrientation_pattern_fiber_infinite θ I
      (orientationRestriction I x) (h I)

/-- Set form of the canonical repeated-sequence cluster law. -/
theorem tailCluster_infinitelyRepeatedOrientation
    {J : Type*} (θ : ℕ → (J → Bool)) :
    primeOrientationTailClusterSet (infinitelyRepeatedOrientation θ) =
      {x | ∀ I : Finset J, ∃ n,
        orientationRestriction I (θ n) = orientationRestriction I x} := by
  ext x
  exact mem_tailCluster_infinitelyRepeatedOrientation_iff θ x

/-- Any constraint characterized by the finite patterns attained by a sequence is realized exactly
as the tail cluster of its canonical infinite repetition.  For a dense sequence in a closed subset
of the Boolean cube, the hypothesis is the usual finite-cylinder characterization of closure. -/
theorem tailCluster_infinitelyRepeatedOrientation_eq
    {J : Type*} (θ : ℕ → (J → Bool)) (K : Set (J → Bool))
    (hK : ∀ x, x ∈ K ↔ ∀ I : Finset J, ∃ n,
      orientationRestriction I (θ n) = orientationRestriction I x) :
    primeOrientationTailClusterSet (infinitelyRepeatedOrientation θ) = K := by
  ext x
  rw [mem_tailCluster_infinitelyRepeatedOrientation_iff, hK]

end

end GaloisForLFunctions.HTGeometry
