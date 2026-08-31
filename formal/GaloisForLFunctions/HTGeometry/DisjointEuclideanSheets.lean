import GaloisForLFunctions.HTGeometry.InvarianceOfDomain

/-!
# Disjoint Euclidean sheets are countable

A continuous injection of a finite-dimensional Euclidean space into itself has open range, so a
family of such maps with pairwise disjoint ranges is a family of pairwise disjoint nonempty open
sets, and a separable space carries only countably many of those.

Consequently a product `X × E` admits no continuous injection into `E` unless `X` is countable:
each sheet `{x} × E` would be an open set, and the sheets are disjoint.  This is the obstruction
that rules out a transversally uncountable invariant set inside a surface — a minimal set whose
transversal is a Cantor set would produce uncountably many disjoint planes.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Invariance of domain, global form.**  A continuous injection of `E` into itself is open. -/
theorem isOpen_range_of_continuous_injective {f : E → E} (hcont : Continuous f)
    (hinj : Function.Injective f) : IsOpen (Set.range f) := by
  have h := invariance_of_domain_open_map f Set.univ isOpen_univ hcont.continuousOn
    (Set.injOn_of_injective hinj)
  rwa [Set.image_univ] at h

/-- **Disjoint sheets are countable.**  A family of continuous injections `E → E` with pairwise
disjoint ranges is indexed by a countable set. -/
theorem countable_of_pairwiseDisjoint_ranges {ι : Type*} {s : Set ι} {f : ι → E → E}
    (hcont : ∀ i ∈ s, Continuous (f i)) (hinj : ∀ i ∈ s, Function.Injective (f i))
    (hdisj : s.PairwiseDisjoint fun i => Set.range (f i)) : s.Countable :=
  hdisj.countable_of_isOpen
    (fun i hi => isOpen_range_of_continuous_injective (hcont i hi) (hinj i hi))
    (fun _ _ => Set.range_nonempty _)

/-- **A transversally uncountable product does not inject into `E`.**  If `F : X × E → E` is
injective and continuous in the second variable, then `X` is countable. -/
theorem countable_of_injective_prod {X : Type*} {F : X → E → E}
    (hcont : ∀ x, Continuous (F x)) (hinj : Function.Injective fun p : X × E => F p.1 p.2) :
    Countable X := by
  have hdisj : (Set.univ : Set X).PairwiseDisjoint fun x => Set.range (F x) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
    have hpair : ((b, v) : X × E) = (a, u) := hinj hv
    exact hab (congrArg Prod.fst hpair).symm
  have hcount : (Set.univ : Set X).Countable :=
    countable_of_pairwiseDisjoint_ranges (fun x _ => hcont x)
      (fun x _ u v huv => by
        have hpair : ((x, u) : X × E) = (x, v) := hinj huv
        exact congrArg Prod.snd hpair)
      hdisj
  exact Set.countable_univ_iff.mp hcount

/-- An uncountable transversal is impossible. -/
theorem not_injective_prod_of_uncountable {X : Type*} (hX : ¬ Countable X) {F : X → E → E}
    (hcont : ∀ x, Continuous (F x)) :
    ¬ Function.Injective fun p : X × E => F p.1 p.2 :=
  fun hinj => hX (countable_of_injective_prod hcont hinj)

end GaloisForLFunctions.HTGeometry
