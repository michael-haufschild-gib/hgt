import GaloisForLFunctions.HTGeometry.CompactTailDenseConstraintKernel
import GaloisForLFunctions.HTGeometry.CountablePrimeProfileRealization
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Topology.Constructions.SumProd

/-!
# Prime constraint joinings

A cofinally tail-complete source has a sharp finite-correlation dichotomy. Sampling all injective
finite coordinate configurations forces the full Cartesian power of its local constraint set.
Nevertheless, a coupled cofinal family of disjoint prime configurations can realize every
nonempty countable subdirect relation while the one-prime recurrent locus remains the whole local
value space.

Thus finite correlation is not hidden in the local source and is not created by unrestricted
multiplication. It is exactly additional joining data: the rule selecting which distinct
coordinates are observed together.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Ordered pairs of distinct coordinates. -/
abbrev DistinctPair (P : Type*) := {pq : P × P // pq.1 ≠ pq.2}

/-- The two-point source profile sampled at distinct coordinates. -/
def distinctPairProfile {P V : Type*} (x : P → V) : DistinctPair P → V × V :=
  fun pq => (x pq.1.1, x pq.1.2)

/-- Finite configurations of pairwise distinct coordinates. -/
abbrev DistinctConfiguration (P I : Type*) :=
  {a : I → P // Function.Injective a}

/-- The source profile sampled on a finite injective coordinate configuration. -/
def distinctConfigurationProfile {P I V : Type*} (x : P → V) :
    DistinctConfiguration P I → I → V :=
  fun a i => x (a.1 i)

/-- A countable row of `I` labelled slots is again a countable prime set. -/
noncomputable def chosenJoiningPrimeEquiv (I : Type*) [Fintype I] [Nonempty I] :
    (ℕ × I) ≃ Nat.Primes :=
  Classical.choice (inferInstance : Nonempty ((ℕ × I) ≃ Nat.Primes))

/-- Place a coupled profile into disjoint prime slots. -/
def joinedPrimeSource {I V : Type*}
    (E : (ℕ × I) ≃ Nat.Primes) (y : ℕ → I → V) : Nat.Primes → V :=
  fun p => y (E.symm p).1 (E.symm p).2

/-- The prime configuration formed by one complete row of slots. -/
def joinedPrimeConfiguration {I : Type*}
    (E : (ℕ × I) ≃ Nat.Primes) (n : ℕ) : DistinctConfiguration Nat.Primes I :=
  ⟨fun i => E (n, i), fun i j hij => by
    have hp := E.injective hij
    exact congrArg Prod.snd hp⟩

@[simp]
theorem joinedPrimeSource_configuration_apply {I V : Type*}
    (E : (ℕ × I) ≃ Nat.Primes) (y : ℕ → I → V) (n : ℕ) (i : I) :
    joinedPrimeSource E y ((joinedPrimeConfiguration E n).1 i) = y n i := by
  simp [joinedPrimeSource, joinedPrimeConfiguration]

/-- A finite-coordinate relation whose every coordinate projection is the full local space. -/
def IsSubdirectConstraint {I V : Type*} (C : Set (I → V)) : Prop :=
  ∀ i v, ∃ c ∈ C, c i = v

/-- **Coupled-prime realization.** Every recurrent subdirect relation carried by a countable
coupled profile is realized by one prime source. The source itself recurrently sees every local
value, while the selected disjoint prime rows retain exactly the prescribed joining. -/
theorem joinedPrimeSource_realizes_subdirect_recurringConstraint
    {I V : Type*} [Fintype I] [Nonempty I]
    (E : (ℕ × I) ≃ Nat.Primes) (y : ℕ → I → V) (C : Set (I → V))
    (hy : recurringValueSet y = C) (hC : IsSubdirectConstraint C) :
    recurringValueSet (joinedPrimeSource E y) = Set.univ ∧
      CofinitelyRecurring (joinedPrimeSource E y) ∧
      recurringValueSet
          (fun n => distinctConfigurationProfile (joinedPrimeSource E y)
            (joinedPrimeConfiguration E n)) = C := by
  classical
  have hlocal : ∀ v : V,
      v ∈ recurringValueSet (joinedPrimeSource E y) := by
    intro v
    let i₀ : I := Classical.choice inferInstance
    obtain ⟨c, hcC, hcval⟩ := hC i₀ v
    have hcRec : c ∈ recurringValueSet y := by simpa [hy] using hcC
    let A : Set ℕ := {n | y n = c}
    have hA : A.Infinite := hcRec
    haveI : Infinite A := hA.to_subtype
    let f : A → Nat.Primes := fun n => E (n.1, i₀)
    have hf : Function.Injective f := by
      intro n m hnm
      apply Subtype.ext
      have hrow := congrArg (fun z : Nat.Primes => (E.symm z).1) hnm
      simpa [f] using hrow
    apply Set.infinite_of_injective_forall_mem hf
    intro n
    change joinedPrimeSource E y (f n) = v
    simpa [f, joinedPrimeSource, hcval] using congrFun n.2 i₀
  constructor
  · ext v
    simp only [Set.mem_univ, iff_true]
    exact hlocal v
  constructor
  · rw [CofinitelyRecurring]
    have hempty :
        {p | joinedPrimeSource E y p ∉
          recurringValueSet (joinedPrimeSource E y)} = ∅ := by
      ext p
      simp [hlocal]
    rw [hempty]
    exact Set.finite_empty
  · have hprofile :
        (fun n => distinctConfigurationProfile (joinedPrimeSource E y)
          (joinedPrimeConfiguration E n)) = y := by
      funext n i
      exact joinedPrimeSource_configuration_apply E y n i
    rw [hprofile, hy]

/-- A chosen enumeration of a nonempty countable type. -/
noncomputable def chosenNatSurjection (W : Type*) [Nonempty W] [Countable W] : ℕ → W :=
  Classical.choose (exists_surjective_nat W)

theorem chosenNatSurjection_surjective (W : Type*) [Nonempty W] [Countable W] :
    Function.Surjective (chosenNatSurjection W) :=
  Classical.choose_spec (exists_surjective_nat W)

/-- Repeat every point of a nonempty countable constraint relation infinitely often. -/
def repeatedCountableConstraintProfile {I V : Type*}
    (C : Set (I → V)) [Nonempty C] [Countable C] : ℕ → I → V :=
  fun n => (chosenNatSurjection C (Nat.unpair n).1).1

theorem repeatedCountableConstraintProfile_fiber_infinite
    {I V : Type*} (C : Set (I → V)) [Nonempty C] [Countable C]
    (c : I → V) (hc : c ∈ C) :
    {n | repeatedCountableConstraintProfile C n = c}.Infinite := by
  let cC : C := ⟨c, hc⟩
  obtain ⟨k, hk⟩ := chosenNatSurjection_surjective C cC
  let f : ℕ → ℕ := fun m => Nat.pair k m
  have hf : Function.Injective f := by
    intro m n hmn
    have hright := congrArg (fun z => (Nat.unpair z).2) hmn
    simpa [f, Nat.unpair_pair] using hright
  apply (Set.infinite_range_of_injective hf).mono
  intro n hn
  obtain ⟨m, rfl⟩ := hn
  funext i
  have hkval := congrArg (fun z : C => z.1 i) hk
  simpa [f, repeatedCountableConstraintProfile, cC, Nat.unpair_pair] using hkval

/-- The repeated profile has exactly the prescribed relation as its recurrent locus. -/
theorem recurringValueSet_repeatedCountableConstraintProfile
    {I V : Type*} (C : Set (I → V)) [Nonempty C] [Countable C] :
    recurringValueSet (repeatedCountableConstraintProfile C) = C := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨n, rfl⟩ := recurringValueSet_subset_range
      (repeatedCountableConstraintProfile C) hc
    exact (chosenNatSurjection C (Nat.unpair n).1).2
  · intro c hc
    exact repeatedCountableConstraintProfile_fiber_infinite C c hc

/-- **Countable joining universality.** Every nonempty countable subdirect finite-coordinate
constraint relation is the exact recurrent joining of disjoint prime rows from one cofinally
recurrent source whose local recurrent locus is the whole value space. -/
theorem exists_primeSource_realizing_countable_subdirectConstraint
    {I V : Type*} [Fintype I] [Nonempty I]
    (C : Set (I → V)) [Nonempty C] [Countable C]
    (hC : IsSubdirectConstraint C) :
    ∃ (x : Nat.Primes → V)
      (a : ℕ → DistinctConfiguration Nat.Primes I),
      recurringValueSet x = Set.univ ∧
        CofinitelyRecurring x ∧
        recurringValueSet (fun n => distinctConfigurationProfile x (a n)) = C := by
  let E : (ℕ × I) ≃ Nat.Primes := chosenJoiningPrimeEquiv I
  let y : ℕ → I → V := repeatedCountableConstraintProfile C
  let x : Nat.Primes → V := joinedPrimeSource E y
  let a : ℕ → DistinctConfiguration Nat.Primes I := joinedPrimeConfiguration E
  refine ⟨x, a, ?_⟩
  exact joinedPrimeSource_realizes_subdirect_recurringConstraint E y C
    (recurringValueSet_repeatedCountableConstraintProfile C) hC

/-- Infinite exact recurrence of every value implies cofinite tail density on the whole value
space, for any topology on that space. -/
theorem cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ
    {P V : Type*} [TopologicalSpace V] (x : P → V)
    (hx : recurringValueSet x = Set.univ) :
    CofiniteTailDenseOn x Set.univ := by
  constructor
  · exact Set.subset_univ _
  · intro v hv
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rw [frequently_cofinite_iff_infinite]
    have hvRec : v ∈ recurringValueSet x := by
      rw [hx]
      exact Set.mem_univ v
    exact hvRec.mono fun p hp => by
      have hvS : v ∈ s := mem_of_mem_nhds hs
      change x p = v at hp
      change x p ∈ s
      rw [hp]
      exact hvS

/-- A finite family of infinite sets admits a system of distinct representatives. -/
theorem exists_injective_mem_of_forall_infinite
    {P I : Type*} [Fintype I] (A : I → Set P) (hA : ∀ i, (A i).Infinite) :
    ∃ f : I → P, Function.Injective f ∧ ∀ i, f i ∈ A i := by
  classical
  choose t htA htcard using fun i => (hA i).exists_subset_card_eq (Fintype.card I)
  have hHall : ∀ s : Finset I, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hs : s = ∅
    · simp [hs]
    · obtain ⟨i, hi⟩ := s.nonempty_iff_ne_empty.mpr hs
      calc
        s.card ≤ Fintype.card I := Finset.card_le_univ s
        _ = (t i).card := (htcard i).symm
        _ ≤ (s.biUnion t).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem t hi)
  obtain ⟨f, hf, hft⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  exact ⟨f, hf, fun i => htA i (hft i)⟩

theorem cofiniteTailDenseOn_distinctConfigurationProfile
    {P I V : Type*} [Fintype I] [Nonempty I] [TopologicalSpace V]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K) :
    CofiniteTailDenseOn (distinctConfigurationProfile (I := I) x)
      (Set.univ.pi fun _ : I => K) := by
  classical
  constructor
  · rintro _ ⟨a, rfl⟩ i _
    exact hx.1 ⟨a.1 i, rfl⟩
  · intro v hv
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rw [frequently_cofinite_iff_infinite]
    rw [nhds_pi] at hs
    obtain ⟨J, hJ, U, hU, hUs⟩ := Filter.mem_pi.mp hs
    let A : I → Set P := fun i => {p | x p ∈ U i}
    have hA : ∀ i, (A i).Infinite := by
      intro i
      rw [← frequently_cofinite_iff_infinite]
      exact mapClusterPt_iff_frequently.mp (hx.2 (v i) (hv i (by simp))) (U i) (hU i)
    obtain ⟨f, hf, hfA⟩ := exists_injective_mem_of_forall_infinite A hA
    let i₀ : I := Classical.choice inferInstance
    let T : Set P := f '' {i | i ≠ i₀}
    have hT : T.Finite := (Set.toFinite {i | i ≠ i₀}).image f
    let B : Set P := A i₀ \ T
    have hB : B.Infinite := (hA i₀).sdiff hT
    let g : B → DistinctConfiguration P I := fun p =>
      ⟨Function.update f i₀ p.1, by
        intro i j hij
        by_cases hi : i = i₀
        · subst i
          by_cases hj : j = i₀
          · exact hj.symm
          · have hpj : p.1 = f j := by simpa [Function.update_self, Function.update_of_ne hj]
              using hij
            exact False.elim (p.2.2 ⟨j, hj, hpj.symm⟩)
        · by_cases hj : j = i₀
          · subst j
            have hip : f i = p.1 := by simpa [Function.update_self, Function.update_of_ne hi]
              using hij
            exact False.elim (p.2.2 ⟨i, hi, hip⟩)
          · apply hf
            simpa [Function.update_of_ne hi, Function.update_of_ne hj] using hij⟩
    have hg : Function.Injective g := by
      intro p q hpq
      apply Subtype.ext
      have hfun : Function.update f i₀ p.1 = Function.update f i₀ q.1 :=
        congrArg Subtype.val hpq
      exact Function.update_injective f i₀ hfun
    haveI : Infinite B := hB.to_subtype
    apply Set.infinite_of_injective_forall_mem hg
    intro p
    apply hUs
    intro i hi
    change x ((g p).1 i) ∈ U i
    by_cases hii : i = i₀
    · subst i
      simpa [g] using! p.2.1
    · simpa [g, Function.update_of_ne hii] using! hfA i

/-- **Maximal-independent/arbitrary-coupled joining dichotomy.** For every nonempty countable
subdirect relation `C`, one prime source has full local recurrent geometry; sampling all disjoint
finite prime configurations forces the maximal Cartesian constraint, while a selected cofinal
family of disjoint rows has recurrent constraint exactly `C`. -/
theorem exists_primeSource_independentMaximal_coupledArbitrary
    {I V : Type*} [Fintype I] [Nonempty I] [TopologicalSpace V]
    (C : Set (I → V)) [Nonempty C] [Countable C]
    (hC : IsSubdirectConstraint C) :
    ∃ (x : Nat.Primes → V)
      (a : ℕ → DistinctConfiguration Nat.Primes I),
      CofiniteTailDenseOn x Set.univ ∧
        CofiniteTailDenseOn (distinctConfigurationProfile x)
          (Set.univ.pi fun _ : I => Set.univ) ∧
        recurringValueSet (fun n => distinctConfigurationProfile x (a n)) = C := by
  obtain ⟨x, a, hxrec, hxcof, haC⟩ :=
    exists_primeSource_realizing_countable_subdirectConstraint C hC
  have hx : CofiniteTailDenseOn x Set.univ :=
    cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ x hxrec
  exact ⟨x, a, hx,
    cofiniteTailDenseOn_distinctConfigurationProfile x Set.univ hx, haC⟩

/-- Every continuous finite-configuration observable is tail-finitely supported precisely when it
vanishes on the forced Cartesian constraint. -/
theorem cofiniteTailDenseOn_distinctConfiguration_continuous_support_finite_iff
    {P I V : Type*} [Fintype I] [Nonempty I] [TopologicalSpace V]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (F : (I → V) → ℂ) (hF : Continuous F) :
    {a | F (distinctConfigurationProfile x a) ≠ 0}.Finite ↔
      ∀ v ∈ Set.univ.pi (fun _ : I => K), F v = 0 := by
  exact cofiniteTailDenseOn_continuous_support_finite_iff
    (distinctConfigurationProfile x) (Set.univ.pi fun _ : I => K)
    (cofiniteTailDenseOn_distinctConfigurationProfile x K hx) F hF

theorem cofiniteTailDenseOn_distinctPairProfile
    {P V : Type*} [TopologicalSpace V]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K) :
    CofiniteTailDenseOn (distinctPairProfile x) (K ×ˢ K) := by
  constructor
  · rintro _ ⟨pq, rfl⟩
    exact ⟨hx.1 ⟨pq.1.1, rfl⟩, hx.1 ⟨pq.1.2, rfl⟩⟩
  · rintro ⟨v, w⟩ ⟨hv, hw⟩
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rw [frequently_cofinite_iff_infinite]
    obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.mp hs
    have hAu : {p | x p ∈ u}.Infinite := by
      rw [← frequently_cofinite_iff_infinite]
      exact mapClusterPt_iff_frequently.mp (hx.2 v hv) u hu
    have hBt : {p | x p ∈ t}.Infinite := by
      rw [← frequently_cofinite_iff_infinite]
      exact mapClusterPt_iff_frequently.mp (hx.2 w hw) t ht
    obtain ⟨q, hq⟩ := hBt.nonempty
    let A : Set P := {p | x p ∈ u} \ {q}
    have hA : A.Infinite := hAu.sdiff (Set.finite_singleton q)
    let f : A → DistinctPair P := fun p =>
      ⟨(p.1, q), by
        intro hpq
        exact p.2.2 hpq⟩
    have hf : Function.Injective f := by
      intro p p' hpp'
      apply Subtype.ext
      exact congrArg (fun z : DistinctPair P => z.1.1) hpp'
    haveI : Infinite A := hA.to_subtype
    apply Set.infinite_of_injective_forall_mem hf
    intro p
    change distinctPairProfile x (f p) ∈ s
    apply hut
    exact ⟨p.2.1, hq⟩



end

end GaloisForLFunctions.HTGeometry
