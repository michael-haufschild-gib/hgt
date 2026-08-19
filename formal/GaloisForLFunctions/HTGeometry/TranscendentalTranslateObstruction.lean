import Mathlib

/-!
# A transcendental element of a finite-type algebra has non-invertible constant translates

If `R` is a nonzero algebra of finite type over a field `K` and `e ∈ R` is transcendental over `K`,
then `e - a` fails to be invertible for all but finitely many `a ∈ K`.  Equivalently, the image of
`Spec R → 𝔸¹_K = Spec K[e]` contains a nonempty open set.

The proof is Chevalley's theorem.  The image of `Spec R → Spec K[X]` is constructible, and it
contains the generic point because the nonzero polynomials in `e` form a multiplicative set missing
zero, so some prime of `R` avoids them.  A constructible set containing the generic point of the
spectrum of a domain contains a basic open `D(f)` with `f ≠ 0`; in `Spec K[X]` that misses only the
finitely many roots of `f`.

This is the geometric input to the no-new-constants theorem for Picard--Vessiot rings: it is what
makes a constant of a finitely generated `σ`-simple algebra algebraic over the base.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A constructible set containing the generic point contains a basic open.** -/
theorem exists_ne_zero_basicOpen_subset_of_isConstructible
    {A : Type*} [CommRing A] [IsDomain A] {s : Set (PrimeSpectrum A)}
    (hs : Topology.IsConstructible s)
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ s) :
    ∃ f : A, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ⊆ s := by
  classical
  obtain ⟨D, hD⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hs
  rw [← hD] at hgen ⊢
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion] at hgen
  obtain ⟨C, hCD, hCmem⟩ := hgen
  have hCmem' : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ C.toSet := hCmem
  rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff] at hCmem'
  obtain ⟨hzero, hnot⟩ := hCmem'
  have hgzero : ∀ i, C.g i = 0 := by
    intro i
    have := (PrimeSpectrum.mem_zeroLocus _ _).mp hzero (Set.mem_range_self i)
    simpa using this
  have hfne : C.f ≠ 0 := by
    intro hf
    apply hnot
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simp [hx, hf]
  refine ⟨C.f, hfne, ?_⟩
  intro x hx
  refine Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hCD, ?_⟩⟩
  rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff]
  constructor
  · rw [PrimeSpectrum.mem_zeroLocus]
    rintro y ⟨i, rfl⟩
    rw [hgzero i]
    exact x.asIdeal.zero_mem
  · intro hcon
    have hmem : C.f ∈ x.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp hcon (Set.mem_singleton _)
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hx hmem

/-- **The generic point is in the image of a dominant map.**  If the structure map from a domain is
injective, some prime of the target contracts to zero. -/
theorem genericPoint_mem_range_comap
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Nontrivial B]
    (f : A →+* B) (hf : Function.Injective f) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range (PrimeSpectrum.comap f) := by
  classical
  set M : Submonoid B := (nonZeroDivisors A).map (f : A →* B) with hM
  have hzero : (0 : B) ∉ M := by
    rintro ⟨x, hx, hfx⟩
    have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
    refine hx0 (hf ?_)
    rw [map_zero]
    exact hfx
  have hdisj : Disjoint ((⊥ : Ideal B) : Set B) (M : Set B) := by
    rw [Set.disjoint_left]
    intro y hy hyM
    rw [SetLike.mem_coe, Ideal.mem_bot] at hy
    exact hzero (hy ▸ hyM)
  obtain ⟨p, hp, -, hpdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal B) M hdisj
  refine ⟨⟨p, hp⟩, ?_⟩
  apply PrimeSpectrum.ext
  apply le_antisymm
  · intro x hx
    by_contra hx0
    have hxM : f x ∈ M := ⟨x, mem_nonZeroDivisors_of_ne_zero hx0, rfl⟩
    have hxp : f x ∈ p := hx
    exact Set.disjoint_left.mp hpdisj hxp hxM
  · exact bot_le

/-- **A transcendental element cannot have every constant translate invertible.**  If `R` is a
nonzero `K`-algebra of finite type and `e` is transcendental over `K`, then for every infinite set
of scalars some translate `e - a` is not a unit. -/
theorem exists_notMem_isUnit_sub_algebraMap
    {K R : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
    [Algebra.FiniteType K R] {e : R} (he : Transcendental K e)
    {S : Set K} (hS : S.Infinite) :
    ∃ a ∈ S, ¬ IsUnit (e - algebraMap K R a) := by
  classical
  letI : Algebra K[X] R := (Polynomial.aeval e).toRingHom.toAlgebra
  have halg : ∀ p : K[X], algebraMap K[X] R p = Polynomial.aeval e p := fun _ => rfl
  haveI : IsScalarTower K K[X] R := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [halg]
    simp
  haveI : Algebra.FiniteType K[X] R :=
    Algebra.FiniteType.of_restrictScalars_finiteType K K[X] R
  haveI : Algebra.FinitePresentation K[X] R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hfp : (algebraMap K[X] R).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hinj : Function.Injective (algebraMap K[X] R) := by
    intro p q hpq
    exact (transcendental_iff_injective.mp he) hpq
  have hconstr := PrimeSpectrum.isConstructible_range_comap hfp
  have hgen := genericPoint_mem_range_comap (algebraMap K[X] R) hinj
  obtain ⟨g, hgne, hsub⟩ :=
    exists_ne_zero_basicOpen_subset_of_isConstructible hconstr hgen
  obtain ⟨a, haS, hga⟩ : ∃ a ∈ S, ¬ g.IsRoot a := by
    by_contra hcon
    push Not at hcon
    have hinf : {x : K | g.IsRoot x}.Infinite := hS.mono (fun x hx => hcon x hx)
    exact hgne (Polynomial.eq_zero_of_infinite_isRoot g hinf)
  have hprime : (Ideal.span {X - C a}).IsPrime := by
    rw [Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero a)]
    exact Polynomial.prime_X_sub_C a
  have hmemOpen : (⟨Ideal.span {X - C a}, hprime⟩ : PrimeSpectrum K[X]) ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum K[X])) := by
    show (⟨Ideal.span {X - C a}, hprime⟩ : PrimeSpectrum K[X]) ∈ PrimeSpectrum.basicOpen g
    rw [PrimeSpectrum.mem_basicOpen]
    intro hcon
    exact hga ((Polynomial.dvd_iff_isRoot).mp (Ideal.mem_span_singleton.mp hcon))
  obtain ⟨P, hP⟩ := hsub hmemOpen
  refine ⟨a, haS, ?_⟩
  intro hunit
  have hmem : (X - C a) ∈ Ideal.comap (algebraMap K[X] R) P.asIdeal := by
    have : Ideal.comap (algebraMap K[X] R) P.asIdeal = Ideal.span {X - C a} :=
      congrArg PrimeSpectrum.asIdeal hP
    rw [this]
    exact Ideal.mem_span_singleton_self _
  have hval : algebraMap K[X] R (X - C a) = e - algebraMap K R a := by
    rw [halg]
    simp
  have hmemP : e - algebraMap K R a ∈ P.asIdeal := by
    rw [← hval]
    exact hmem
  exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem hmemP hunit)

end

end GaloisForLFunctions.HTGeometry
