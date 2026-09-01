import GaloisForLFunctions.HTGeometry.GradeQuotient
import GaloisForLFunctions.HTGeometry.AssociatedPrimeRegular
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Grade transfers along a ring map

```text
exists_mem_isSMulRegular_of_map   ** a regular element of the extended ideal can be replaced by one
                                     coming from the ideal itself **
exists_list_mem_isRegular_of_map  ** hence a whole regular sequence can be taken inside the base
                                     ideal **
```

The first is prime avoidance: the contractions of the finitely many associated primes of the module
are primes of the base ring, and the base ideal lies in none of them, because its extension is not
contained in any associated prime.

The second is the induction that turns one element into a sequence: after quotienting by the element
just produced, the grade of the extended ideal drops by at most one
(`hasGradeGE_quotSMulTop`), so the hypothesis is available again.

This is the form in which depth is compared across a finite ring map: a regular sequence for the
extension can always be chosen with entries in the base, which is what an argument over the base
ring — a projective-dimension count, say — needs.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open RingTheory.Sequence

universe u

variable {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]

/-- **A regular element of the extended ideal can be replaced by one coming from the ideal.** -/
theorem exists_mem_isSMulRegular_of_map [IsNoetherianRing D] (I : Ideal A)
    (N : Type u) [AddCommGroup N] [Module D N] [Module.Finite D N] {z : D}
    (hz : z ∈ Ideal.map (algebraMap A D) I) (hzreg : IsSMulRegular N z) :
    ∃ y ∈ I, IsSMulRegular N (algebraMap A D y) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Finset (Ideal D), (F : Set (Ideal D)) = associatedPrimes D N :=
    ⟨(associatedPrimes.finite D N).toFinset, by simp⟩
  set G : Finset (Ideal A) := F.image (Ideal.comap (algebraMap A D)) with hG
  have hprime : ∀ i ∈ G, ∀ _ : i ≠ (⊥ : Ideal A), ∀ _ : i ≠ (⊥ : Ideal A), i.IsPrime := by
    intro i hi _ _
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    have hqass : q ∈ associatedPrimes D N := by rw [← hF]; exact_mod_cast hq
    haveI : q.IsPrime := hqass.1
    exact Ideal.comap_isPrime _ _
  have hnotsub : ¬ ((I : Set A) ⊆ ⋃ i ∈ (G : Set (Ideal A)), (i : Set A)) := by
    rw [Ideal.subset_union_prime (f := fun i : Ideal A => i) (⊥ : Ideal A) (⊥ : Ideal A) hprime]
    rintro ⟨i, hi, hle⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    have hqass : q ∈ associatedPrimes D N := by rw [← hF]; exact_mod_cast hq
    have hmapq : Ideal.map (algebraMap A D) I ≤ q := by
      rw [Ideal.map_le_iff_le_comap]
      exact hle
    exact ((isSMulRegular_iff_forall_notMem_associatedPrimes D N).mp hzreg q hqass) (hmapq hz)
  obtain ⟨y, hyI, hynot⟩ := Set.not_subset.mp hnotsub
  refine ⟨y, hyI, ?_⟩
  rw [isSMulRegular_iff_forall_notMem_associatedPrimes]
  intro q hq hmem
  have hqG : Ideal.comap (algebraMap A D) q ∈ (G : Set (Ideal A)) := by
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, ?_, rfl⟩)
    rw [← hF] at hq
    exact_mod_cast hq
  exact hynot (Set.mem_iUnion₂_of_mem hqG hmem)

/-- **A regular sequence for the extended ideal can be taken inside the base ideal.** -/
theorem exists_list_mem_isRegular_of_map [IsNoetherianRing D] (I : Ideal A) :
    ∀ (n : ℕ) (N : ModuleCat.{u} D), Module.Finite D N →
      (Ideal.map (algebraMap A D) I) • (⊤ : Submodule D N) < ⊤ →
      HasGradeGE (Ideal.map (algebraMap A D) I) N n →
      ∃ rs : List A, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧
        RingTheory.Sequence.IsRegular N (rs.map (algebraMap A D)) := by
  intro n
  induction n with
  | zero =>
    intro N _ hlt _
    refine ⟨[], rfl, by simp, ⟨⟨fun i hi => absurd hi (by simp)⟩, ?_⟩⟩
    intro htop
    rw [List.map_nil,
      show (Ideal.ofList ([] : List D)) = ⊥ by simp [Ideal.ofList], Submodule.bot_smul] at htop
    have hbot : (⊤ : Submodule D N) ≤ Ideal.map (algebraMap A D) I • ⊤ := by
      rw [htop]
      exact bot_le
    exact absurd (le_antisymm hlt.le hbot) hlt.ne
  | succ n ih =>
    intro N hfin hlt hgrade
    haveI := hfin
    obtain ⟨rs, hlen, hmem, hreg⟩ := hgrade
    obtain ⟨z, t, rfl⟩ : ∃ z t, rs = z :: t := by
      cases rs with
      | nil => simp at hlen
      | cons z t => exact ⟨z, t, rfl⟩
    have hzreg : IsSMulRegular N z := ((isRegular_cons_iff N z t).mp hreg).1
    obtain ⟨y, hyI, hyreg⟩ :=
      exists_mem_isSMulRegular_of_map I N (hmem z (List.mem_cons_self ..)) hzreg
    set x : D := algebraMap A D y with hx
    have hxmem : x ∈ Ideal.map (algebraMap A D) I := Ideal.mem_map_of_mem _ hyI
    haveI hfinq : Module.Finite D ((ModuleCat.smulShortComplex N x).X₃) :=
      Module.Finite.of_surjective (Submodule.mkQ (x • (⊤ : Submodule D N)))
        (Submodule.mkQ_surjective _)
    have hxle : (x • (⊤ : Submodule D N)) ≤ (Ideal.map (algebraMap A D) I) • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mono_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxmem))
    have hltq : (Ideal.map (algebraMap A D) I) •
        (⊤ : Submodule D ((ModuleCat.smulShortComplex N x).X₃)) < ⊤ := by
      have hmapeq : (Ideal.map (algebraMap A D) I) •
          (⊤ : Submodule D ((ModuleCat.smulShortComplex N x).X₃))
          = Submodule.map (Submodule.mkQ (x • (⊤ : Submodule D N)))
            ((Ideal.map (algebraMap A D) I) • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      refine lt_of_le_of_ne le_top ?_
      intro hcon
      rw [hmapeq] at hcon
      have h2 := congrArg (Submodule.comap (Submodule.mkQ (x • (⊤ : Submodule D N)))) hcon
      rw [Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top] at h2
      rw [sup_eq_left.mpr hxle] at h2
      exact hlt.ne h2
    have hgq : HasGradeGE (Ideal.map (algebraMap A D) I)
        ((ModuleCat.smulShortComplex N x).X₃) n :=
      hasGradeGE_quotSMulTop N hyreg hlt hltq ⟨z :: t, hlen, hmem, hreg⟩
    obtain ⟨rs', hlen', hmem', hreg'⟩ := ih _ hfinq hltq hgq
    refine ⟨y :: rs', by simp [hlen'], ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with h | h
      · exact h ▸ hyI
      · exact hmem' r h
    · rw [List.map_cons]
      exact (isRegular_cons_iff N x _).mpr ⟨hyreg, hreg'⟩

end GaloisForLFunctions.HTGeometry
