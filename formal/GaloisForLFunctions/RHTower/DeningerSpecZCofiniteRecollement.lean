import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic

/-!
# The cofinite prime star of `Spec ℤ`

The Zariski space of `Spec ℤ` is a generic point together with the closed prime points, and its
topology is the cofinite topology relative to that generic point: a set is open exactly when it
is empty or contains the generic point and has finite complement.

* `deningerSpecZ_eq_generic_or_closed` classifies the points.
* `deningerSpecZGeneric_mem_of_isOpen` shows every nonempty open contains the generic point, and
  `deningerSpecZ_isOpen_iff` is the resulting classification of opens.
* `deningerSpecZ_compl_basicOpen`, `deningerSpecZ_basicOpen_inter`,
  `deningerSpecZ_basicOpen_mul_eq_lcm` and `deningerSpecZ_isTopologicalBasis` describe the
  principal arithmetic opens `D(N) = Spec ℤ[1/N]`.
* `deningerSpecZ_isClosed_of_finite`, `deningerSpecZ_isClosedEmbedding_of_finite` and
  `deningerSpecZ_isOpenEmbedding_compl` are the open–closed decomposition attached to a finite
  set of closed points.
* `deningerSpecZ_discreteTopology` and `deningerSpecZ_isClopen_singleton` show such a finite set
  is discrete, i.e. it is the coproduct of its points; this is the topological input to the
  finite direct sum decomposition of local cohomology with support in it.
-/

namespace RHTower

open PrimeSpectrum

section SpecZ

/-- The generic point of `Spec ℤ`. -/
def deningerSpecZGeneric : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩

@[simp] theorem deningerSpecZGeneric_asIdeal : deningerSpecZGeneric.asIdeal = ⊥ := rfl

/-- The closed point of `Spec ℤ` attached to a rational prime. -/
def deningerSpecZClosed (p : ℕ) (hp : p.Prime) : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Int.prime_iff_natAbs_prime.mpr (by simpa using hp)⟩

@[simp] theorem deningerSpecZClosed_asIdeal (p : ℕ) (hp : p.Prime) :
    (deningerSpecZClosed p hp).asIdeal = Ideal.span {(p : ℤ)} := rfl

/-- **Points of `Spec ℤ`.**  Every point is the generic point or a closed prime point. -/
theorem deningerSpecZ_eq_generic_or_closed (x : PrimeSpectrum ℤ) :
    x = deningerSpecZGeneric ∨ ∃ (p : ℕ) (hp : p.Prime), x = deningerSpecZClosed p hp := by
  by_cases h : x.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext h)
  · right
    have hprime : Prime (Submodule.IsPrincipal.generator x.asIdeal) :=
      Submodule.IsPrincipal.prime_generator_of_isPrime _ h
    refine ⟨(Submodule.IsPrincipal.generator x.asIdeal).natAbs,
      Int.prime_iff_natAbs_prime.mp hprime, PrimeSpectrum.ext ?_⟩
    rw [deningerSpecZClosed_asIdeal]
    conv_lhs => rw [← Ideal.span_singleton_generator x.asIdeal]
    exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs _)

/-- A closed prime point is not the generic point. -/
theorem deningerSpecZClosed_ne_generic (p : ℕ) (hp : p.Prime) :
    deningerSpecZClosed p hp ≠ deningerSpecZGeneric := by
  intro h
  have h' : Ideal.span {(p : ℤ)} = (⊥ : Ideal ℤ) := congrArg PrimeSpectrum.asIdeal h
  rw [Ideal.span_singleton_eq_bot] at h'
  exact hp.ne_zero (by exact_mod_cast h')

/-- **Generic point.**  Every nonempty open of `Spec ℤ` contains the generic point. -/
theorem deningerSpecZGeneric_mem_of_isOpen {U : Set (PrimeSpectrum ℤ)} (hU : IsOpen U)
    (hne : U.Nonempty) : deningerSpecZGeneric ∈ U := by
  rw [PrimeSpectrum.isOpen_iff] at hU
  obtain ⟨s, hs⟩ := hU
  by_contra hmem
  have hgen : s ⊆ (deningerSpecZGeneric.asIdeal : Set ℤ) := by
    have : deningerSpecZGeneric ∈ zeroLocus s := by rw [← hs]; exact hmem
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp this
  have huniv : ∀ x : PrimeSpectrum ℤ, x ∈ zeroLocus s := by
    intro x
    refine (PrimeSpectrum.mem_zeroLocus _ _).mpr fun a ha => ?_
    have hb : a ∈ (⊥ : Ideal ℤ) := hgen ha
    simp [Ideal.mem_bot.mp hb]
  obtain ⟨y, hy⟩ := hne
  exact (hs ▸ huniv y) hy

/-- The singleton of a closed prime point is closed. -/
theorem deningerSpecZ_isClosed_singleton_closed (p : ℕ) (hp : p.Prime) :
    IsClosed ({deningerSpecZClosed p hp} : Set (PrimeSpectrum ℤ)) := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  refine IsPrime.to_maximal_ideal ?_
  rw [deningerSpecZClosed_asIdeal, Ne, Ideal.span_singleton_eq_bot]
  exact fun h => hp.ne_zero (by exact_mod_cast h)

/-- The singleton of any non-generic point is closed. -/
theorem deningerSpecZ_isClosed_singleton {x : PrimeSpectrum ℤ} (hx : x ≠ deningerSpecZGeneric) :
    IsClosed ({x} : Set (PrimeSpectrum ℤ)) := by
  obtain h | ⟨p, hp, rfl⟩ := deningerSpecZ_eq_generic_or_closed x
  · exact absurd h hx
  · exact deningerSpecZ_isClosed_singleton_closed p hp

/-- **Finite closed sets.**  A finite set of non-generic points is closed. -/
theorem deningerSpecZ_isClosed_of_finite {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) : IsClosed P := by
  have hcover : P = ⋃ x ∈ P, ({x} : Set (PrimeSpectrum ℤ)) := by
    simp
  rw [hcover]
  refine hfin.isClosed_biUnion fun x hx => deningerSpecZ_isClosed_singleton ?_
  intro hxg
  exact hgen (hxg ▸ hx)

/-- The primes containing a fixed nonzero integer form a finite set. -/
theorem deningerSpecZ_finite_mem_asIdeal {N : ℤ} (hN : N ≠ 0) :
    {x : PrimeSpectrum ℤ | N ∈ x.asIdeal}.Finite := by
  classical
  set S : Set (PrimeSpectrum ℤ) := {x : PrimeSpectrum ℤ | N ∈ x.asIdeal} with hS
  set g : PrimeSpectrum ℤ → ℕ :=
    fun x => (Submodule.IsPrincipal.generator x.asIdeal).natAbs with hg
  have hdvd : ∀ x ∈ S, (Submodule.IsPrincipal.generator x.asIdeal) ∣ N := by
    intro x hx
    have : N ∈ x.asIdeal := hx
    rwa [← Ideal.span_singleton_generator x.asIdeal, Ideal.mem_span_singleton] at this
  have himage : g '' S ⊆ (N.natAbs.divisors : Set ℕ) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Nat.mem_divisors.mpr ⟨?_, Int.natAbs_ne_zero.mpr hN⟩
    exact Int.natAbs_dvd_natAbs.mpr (hdvd x hx)
  have hinj : Set.InjOn g S := by
    intro x hx y hy hxy
    refine PrimeSpectrum.ext ?_
    rw [← Ideal.span_singleton_generator x.asIdeal, ← Ideal.span_singleton_generator y.asIdeal]
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    refine (Int.associated_natAbs _).trans ?_
    rw [hg] at hxy
    simp only at hxy
    rw [hxy]
    exact (Int.associated_natAbs _).symm
  exact Set.Finite.of_finite_image
    (Set.Finite.subset (N.natAbs.divisors.finite_toSet) himage) hinj

/-- **Classification of opens.**  A subset of `Spec ℤ` is open exactly when it is empty, or it
contains the generic point and has finite complement. -/
theorem deningerSpecZ_isOpen_iff {U : Set (PrimeSpectrum ℤ)} :
    IsOpen U ↔ U = ∅ ∨ (deningerSpecZGeneric ∈ U ∧ Uᶜ.Finite) := by
  constructor
  · intro hU
    rcases Set.eq_empty_or_nonempty U with rfl | hne
    · exact Or.inl rfl
    refine Or.inr ⟨deningerSpecZGeneric_mem_of_isOpen hU hne, ?_⟩
    obtain ⟨s, hs⟩ := PrimeSpectrum.isOpen_iff U |>.mp hU
    have hgen : deningerSpecZGeneric ∈ U := deningerSpecZGeneric_mem_of_isOpen hU hne
    have hns : ¬ s ⊆ (deningerSpecZGeneric.asIdeal : Set ℤ) := by
      intro hsub
      have hc : deningerSpecZGeneric ∈ Uᶜ := by
        rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hsub
      exact hc hgen
    obtain ⟨N, hNs, hN0⟩ : ∃ N ∈ s, N ≠ 0 := by
      by_contra hcon
      refine hns fun a ha => ?_
      have ha0 : a = 0 := by
        by_contra hne0
        exact hcon ⟨a, ha, hne0⟩
      simp [ha0]
    refine Set.Finite.subset (deningerSpecZ_finite_mem_asIdeal hN0) ?_
    intro x hx
    rw [hs] at hx
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hx hNs
  · rintro (rfl | ⟨hgen, hfin⟩)
    · exact isOpen_empty
    · rw [← isClosed_compl_iff]
      exact deningerSpecZ_isClosed_of_finite hfin (by simpa using hgen)

/-- **Nonempty opens are cofinite prime stars.**  A nonempty subset is open exactly when it is
the complement of a finite set of closed points. -/
theorem deningerSpecZ_isOpen_iff_star {U : Set (PrimeSpectrum ℤ)} (hne : U.Nonempty) :
    IsOpen U ↔ ∃ P : Set (PrimeSpectrum ℤ), P.Finite ∧ deningerSpecZGeneric ∉ P ∧ U = Pᶜ := by
  constructor
  · intro hU
    obtain h | ⟨hgen, hfin⟩ := deningerSpecZ_isOpen_iff.mp hU
    · exact absurd h hne.ne_empty
    · exact ⟨Uᶜ, hfin, by simpa using hgen, by simp⟩
  · rintro ⟨P, hfin, hgen, rfl⟩
    exact (deningerSpecZ_isClosed_of_finite hfin hgen).isOpen_compl

/-- **Principal arithmetic opens.**  The complement of `D(N)` is the set of primes containing
`N`. -/
theorem deningerSpecZ_compl_basicOpen (N : ℤ) :
    ((PrimeSpectrum.basicOpen N : Set (PrimeSpectrum ℤ)))ᶜ = {x : PrimeSpectrum ℤ | N ∈ x.asIdeal}
    := by
  ext x
  simp

/-- Intersection of two principal opens. -/
theorem deningerSpecZ_basicOpen_inter (M N : ℤ) :
    ((PrimeSpectrum.basicOpen M : Set (PrimeSpectrum ℤ))) ∩ (PrimeSpectrum.basicOpen N) =
      (PrimeSpectrum.basicOpen (M * N) : Set (PrimeSpectrum ℤ)) := by
  ext x
  simp [x.isPrime.mul_mem_iff_mem_or_mem, not_or]

/-- A product and a least common multiple cut out the same principal open. -/
theorem deningerSpecZ_basicOpen_mul_eq_lcm (M N : ℤ) :
    (PrimeSpectrum.basicOpen (M * N) : Set (PrimeSpectrum ℤ)) =
      (PrimeSpectrum.basicOpen (lcm M N) : Set (PrimeSpectrum ℤ)) := by
  ext x
  simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  constructor
  · intro h hl
    exact h (x.asIdeal.mem_of_dvd (lcm_dvd (Dvd.intro N rfl) (Dvd.intro_left M rfl)) hl)
  · intro h hmn
    refine h ?_
    rcases x.isPrime.mul_mem_iff_mem_or_mem.mp hmn with hm | hn
    · exact x.asIdeal.mem_of_dvd (dvd_lcm_left M N) hm
    · exact x.asIdeal.mem_of_dvd (dvd_lcm_right M N) hn

/-- Intersection of two principal opens is the principal open of the least common multiple. -/
theorem deningerSpecZ_basicOpen_inter_eq_lcm (M N : ℤ) :
    ((PrimeSpectrum.basicOpen M : Set (PrimeSpectrum ℤ))) ∩ (PrimeSpectrum.basicOpen N) =
      (PrimeSpectrum.basicOpen (lcm M N) : Set (PrimeSpectrum ℤ)) :=
  (deningerSpecZ_basicOpen_inter M N).trans (deningerSpecZ_basicOpen_mul_eq_lcm M N)

/-- **The complement of a principal open is the finite set of primes dividing `N`.** -/
theorem deningerSpecZ_compl_basicOpen_eq_primes {N : ℤ} (hN : N ≠ 0) :
    ((PrimeSpectrum.basicOpen N : Set (PrimeSpectrum ℤ)))ᶜ
      = {x : PrimeSpectrum ℤ |
          ∃ (p : ℕ) (hp : p.Prime), (p : ℤ) ∣ N ∧ x = deningerSpecZClosed p hp} := by
  rw [deningerSpecZ_compl_basicOpen]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain h | ⟨p, hp, rfl⟩ := deningerSpecZ_eq_generic_or_closed x
    · rw [h] at hx
      exact absurd (Ideal.mem_bot.mp hx) hN
    · exact ⟨p, hp, Ideal.mem_span_singleton.mp hx, rfl⟩
  · rintro ⟨p, hp, hdvd, rfl⟩
    exact Ideal.mem_span_singleton.mpr hdvd

/-- `D(N) = Spec ℤ[1/N]`: the principal arithmetic open is the range of the induced map on
spectra of the localization away from `N`. -/
theorem deningerSpecZ_basicOpen_eq_range_localization (N : ℤ) :
    Set.range (PrimeSpectrum.comap (algebraMap ℤ (Localization.Away N)))
      = (PrimeSpectrum.basicOpen N : Set (PrimeSpectrum ℤ)) :=
  PrimeSpectrum.localization_away_comap_range _ N

/-- The principal arithmetic opens form a basis of `Spec ℤ`. -/
theorem deningerSpecZ_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun N : ℤ => (PrimeSpectrum.basicOpen N : Set (PrimeSpectrum ℤ))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens

/-- **Open–closed decomposition, closed part.** -/
theorem deningerSpecZ_isClosedEmbedding_of_finite {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) :
    Topology.IsClosedEmbedding ((↑) : P → PrimeSpectrum ℤ) :=
  (deningerSpecZ_isClosed_of_finite hfin hgen).isClosedEmbedding_subtypeVal

/-- **Open–closed decomposition, open part.** -/
theorem deningerSpecZ_isOpenEmbedding_compl {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) :
    Topology.IsOpenEmbedding ((↑) : (Pᶜ : Set (PrimeSpectrum ℤ)) → PrimeSpectrum ℤ) :=
  ((deningerSpecZ_isClosed_of_finite hfin hgen).isOpen_compl).isOpenEmbedding_subtypeVal

/-- The two parts of the decomposition are complementary. -/
theorem deningerSpecZ_range_compl (P : Set (PrimeSpectrum ℤ)) :
    Set.range ((↑) : P → PrimeSpectrum ℤ)
      = (Set.range ((↑) : (Pᶜ : Set (PrimeSpectrum ℤ)) → PrimeSpectrum ℤ))ᶜ := by
  ext x
  simp

/-- **Finite prime star is discrete.**  A finite set of closed points carries the discrete
topology, i.e. it is the coproduct of its points. -/
theorem deningerSpecZ_discreteTopology {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) : DiscreteTopology P := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hclosed : IsClosed (P \ {x.val}) :=
    deningerSpecZ_isClosed_of_finite hfin.sdiff fun h => hgen h.1
  have hpre : ({x} : Set P) = ((↑) : P → PrimeSpectrum ℤ) ⁻¹' (P \ {x.val})ᶜ := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff,
      not_and, not_not]
    constructor
    · rintro rfl; intro _; rfl
    · intro h
      exact Subtype.ext (h y.2)
  rw [hpre]
  exact hclosed.isOpen_compl.preimage continuous_subtype_val

/-- Each point of a finite prime star is clopen in it. -/
theorem deningerSpecZ_isClopen_singleton {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) (x : P) : IsClopen ({x} : Set P) := by
  haveI := deningerSpecZ_discreteTopology hfin hgen
  exact ⟨isClosed_discrete _, isOpen_discrete _⟩

/-- A finite prime star is a finite discrete space. -/
theorem deningerSpecZ_finite_star {P : Set (PrimeSpectrum ℤ)} (hfin : P.Finite)
    (hgen : deningerSpecZGeneric ∉ P) : Finite P ∧ DiscreteTopology P :=
  ⟨hfin, deningerSpecZ_discreteTopology hfin hgen⟩

end SpecZ

end RHTower
