import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Idempotents

/-!
# Idempotents over a connected prime spectrum

The basic open of an idempotent is clopen.  Consequently a commutative ring whose prime spectrum
is preconnected has no idempotents other than zero and one.  The proof is kept at the semialgebraic
prime-spectrum level so downstream character-lattice arguments need no reducedness or domain
hypothesis.
-/

open Set

namespace GaloisForLFunctions.HTGeometry
namespace ConnectedPrimeSpectrumIdempotent

/-- The complementary basic opens cut out by an idempotent. -/
theorem basicOpen_compl_of_isIdempotentElem
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))ᶜ =
      PrimeSpectrum.basicOpen (1 - e) := by
  ext P
  rw [Set.mem_compl_iff]
  change ¬(e ∉ P.asIdeal) ↔ (1 - e) ∉ P.asIdeal
  push Not
  constructor
  · intro heP hcompP
    have hone : (1 : R) ∈ P.asIdeal := by
      have : e + (1 - e) ∈ P.asIdeal := P.asIdeal.add_mem heP hcompP
      simpa using this
    exact ((Ideal.ne_top_iff_one P.asIdeal).mp P.isPrime.ne_top) hone
  · intro heP
    have hmul : e * (1 - e) ∈ P.asIdeal := by
      rw [mul_sub, mul_one, he.eq]
      simp
    exact (P.isPrime.mem_or_mem hmul).resolve_right heP

/-- An idempotent whose basic open is empty is zero. -/
theorem eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty
    {R : Type*} [CommRing R] [Nontrivial R] {e : R}
    (he : IsIdempotentElem e)
    (hempty : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = ∅) :
    e = 0 := by
  have hnilmem : e ∈ nilradical R := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    let x : PrimeSpectrum R := ⟨P, hP⟩
    by_contra heP
    have hx : x ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.mem_basicOpen e x).mpr heP
    rw [hempty] at hx
    exact hx
  obtain ⟨d, hd⟩ := mem_nilradical.mp hnilmem
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    simp at hd
  exact (he.pow_eq hd0).symm.trans hd

/-- A commutative ring with preconnected prime spectrum has only the two trivial idempotents. -/
theorem isIdempotentElem_eq_zero_or_one_of_preconnected_primeSpectrum
    {R : Type*} [CommRing R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum R)] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hopen : IsOpen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isOpen_basicOpen
  have hclosed : IsClosed (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
    rw [← isOpen_compl_iff, basicOpen_compl_of_isIdempotentElem he]
    exact PrimeSpectrum.isOpen_basicOpen
  have hcases : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = ∅ ∨
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = Set.univ :=
    isClopen_iff.mp ⟨hclosed, hopen⟩
  rcases hcases with hempty | huniv
  · exact Or.inl (eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty he hempty)
  · right
    have hcompEmpty :
        (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) = ∅ := by
      rw [← basicOpen_compl_of_isIdempotentElem he, huniv, Set.compl_univ]
    have hzero : 1 - e = 0 :=
      eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty he.one_sub hcompEmpty
    exact (sub_eq_zero.mp hzero).symm

end ConnectedPrimeSpectrumIdempotent
end GaloisForLFunctions.HTGeometry
