import GaloisForLFunctions.RHTower.DeningerGenericPointSheaf
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The points of the arithmetic curve

The prime spectrum of the integers has one point for each rational prime and one generic point.
The generic point lies in every nonempty open set, because a closed set missing any point misses a
nonzero integer and so cannot contain the zero ideal.  The closed points are pairwise distinct, so
the closed subschemes they cut out are disjoint.

* `deningerArithBase` : the arithmetic curve as a topological space.
* `deningerGenericPt`, `deningerClosedPt` : its points.
* `deningerArithPoint_cases` : every point is one of these.
* `deningerGenericPt_isGeneric` : the generic point lies in every nonempty open set.
-/

namespace RHTower

open TopologicalSpace

/-- The arithmetic curve: the prime spectrum of the integers. -/
def deningerArithBase : TopCat.{0} := TopCat.of (PrimeSpectrum ℤ)

/-- The generic point of the arithmetic curve. -/
def deningerGenericPt : deningerArithBase := ⟨⊥, Ideal.isPrime_bot⟩

theorem deningerClosedPt_isPrime (p : Nat.Primes) :
    (Ideal.span {((p : ℕ) : ℤ)}).IsPrime := by
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (p.2).ne_zero
  rw [Ideal.span_singleton_prime hp0, Int.prime_iff_natAbs_prime]
  simpa using p.2

/-- The closed point of the arithmetic curve attached to a rational prime. -/
def deningerClosedPt (p : Nat.Primes) : deningerArithBase :=
  ⟨Ideal.span {((p : ℕ) : ℤ)}, deningerClosedPt_isPrime p⟩

theorem deningerClosedPt_asIdeal (p : Nat.Primes) :
    (deningerClosedPt p).asIdeal = Ideal.span {((p : ℕ) : ℤ)} := rfl

theorem deningerGenericPt_asIdeal : (deningerGenericPt).asIdeal = ⊥ := rfl

/-- **The closed points are pairwise distinct**, so the divisors they cut out are disjoint. -/
theorem deningerClosedPt_injective : Function.Injective deningerClosedPt := by
  intro p q h
  have h' : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} :=
    congrArg PrimeSpectrum.asIdeal h
  have hmem : ((q : ℕ) : ℤ) ∈ Ideal.span {((p : ℕ) : ℤ)} := by
    rw [h']
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_span_singleton] at hmem
  have hdvd : (p : ℕ) ∣ (q : ℕ) := by exact_mod_cast Int.natCast_dvd_natCast.1 hmem
  exact (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).1 hdvd)).symm ▸ rfl

theorem deningerClosedPt_ne_generic (p : Nat.Primes) :
    deningerClosedPt p ≠ deningerGenericPt := by
  intro h
  have h' : Ideal.span {((p : ℕ) : ℤ)} = (⊥ : Ideal ℤ) := congrArg PrimeSpectrum.asIdeal h
  have hmem : ((p : ℕ) : ℤ) ∈ (⊥ : Ideal ℤ) := by
    rw [← h']
    exact Ideal.mem_span_singleton_self _
  have : ((p : ℕ) : ℤ) = 0 := by simpa using hmem
  exact (by exact_mod_cast (p.2).ne_zero : ((p : ℕ) : ℤ) ≠ 0) this

/-- **Every point of the arithmetic curve is the generic point or a closed point.** -/
theorem deningerArithPoint_cases (x : deningerArithBase) :
    x = deningerGenericPt ∨ ∃ p : Nat.Primes, x = deningerClosedPt p := by
  by_cases hx : x.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hx)
  · right
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal x.asIdeal).principal
    have hg0 : g ≠ 0 := by
      intro h
      rw [hg, h] at hx
      exact hx (Submodule.span_zero_singleton ℤ)
    have hgp : Prime g := by
      have := x.isPrime
      rw [hg] at this
      exact (Ideal.span_singleton_prime hg0).1 this
    have hnat : Nat.Prime g.natAbs := Int.prime_iff_natAbs_prime.1 hgp
    refine ⟨⟨g.natAbs, hnat⟩, PrimeSpectrum.ext ?_⟩
    rw [hg, deningerClosedPt_asIdeal]
    exact (Int.span_natAbs g).symm ▸ rfl

/-- **The generic point lies in every nonempty open set**: a closed set omitting some point omits a
nonzero integer, hence does not contain the zero ideal. -/
theorem deningerGenericPt_isGeneric :
    DeningerIsGenericPoint (X := deningerArithBase) deningerGenericPt := by
  intro U hU
  obtain ⟨x, hx⟩ := hU
  by_contra hgen
  have hclosed : IsClosed ((U : Set deningerArithBase)ᶜ) := (U.2).isClosed_compl
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).1 hclosed
  have hgmem : deningerGenericPt ∈ PrimeSpectrum.zeroLocus s := by
    rw [← hs]
    exact hgen
  have hsub : s ⊆ (deningerGenericPt).asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hgmem
  have hxnot : x ∉ PrimeSpectrum.zeroLocus s := by
    rw [← hs]
    exact fun h => h hx
  refine hxnot ((PrimeSpectrum.mem_zeroLocus _ _).2 fun f hf => ?_)
  have hf0 : f = 0 := by
    have := hsub hf
    simpa [deningerGenericPt_asIdeal] using this
  rw [hf0]
  exact Ideal.zero_mem _

end RHTower
