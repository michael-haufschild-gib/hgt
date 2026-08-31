import Mathlib

/-!
# The dimension of a quotient by a finite intersection of primes

If `I = ⋂_{i ∈ s} P i` with each `P i` prime, then a chain of primes above `I` has its bottom above
one of the `P i`, hence lies entirely above that one.  So

```text
ringKrullDim_quotient_le_of_inf_primes    dim (R ⧸ I) ≤ max_i dim (R ⧸ P i)
ringKrullDim_quotient_le_of_le            quotienting further cannot raise the dimension
ringKrullDim_quotient_inf_primes          ** dim (R ⧸ I) = max_i dim (R ⧸ P i) **
```

Neither statement is in mathlib.  The Stanley–Reisner ideal of a finite complex is exactly such an
intersection — the primes being the coordinate ideals complementary to the facets — so this
computes the dimension of the monomial degeneration of the Hankel secant ring from the largest face,
which `HankelChainFaces.lean` pins at `2r`.
-/

namespace GaloisForLFunctions.HTGeometry

open PrimeSpectrum

theorem ringKrullDim_eq_krullDim_zeroLocus {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (I : Set R)) :=
  Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)

/-- **The dimension of a quotient by a finite intersection of primes is bounded by the dimensions
of the pieces.**  A chain of primes above the intersection has its bottom above one of the primes,
hence lies entirely above that one. -/
theorem ringKrullDim_quotient_le_of_inf_primes {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {P : ι → Ideal R} {I : Ideal R} (hI : I = s.inf P) {d : WithBot ℕ∞}
    (hd : ∀ i ∈ s, ringKrullDim (R ⧸ P i) ≤ d) :
    ringKrullDim (R ⧸ I) ≤ d := by
  classical
  rw [ringKrullDim_eq_krullDim_zeroLocus, Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨i, hi, hle⟩ :=
    ((p.head : PrimeSpectrum R).2.inf_le' (s := s) (f := P)).mp
      (by
        have hmem := (p.head).2
        rw [PrimeSpectrum.mem_zeroLocus] at hmem
        rw [← hI]
        exact hmem)
  have hstep : ∀ k : Fin (p.length + 1),
      (P i : Set R) ⊆ ((p.toFun k : PrimeSpectrum R)).asIdeal := by
    intro k
    have hmono : (p.head : PrimeSpectrum R) ≤ (p.toFun k : PrimeSpectrum R) := by
      have := p.monotone (Fin.zero_le k)
      exact this
    exact fun z hz => hmono (hle hz)
  let q : LTSeries (PrimeSpectrum.zeroLocus (P i : Set R)) :=
    { length := p.length
      toFun := fun k => ⟨(p.toFun k : PrimeSpectrum R),
        PrimeSpectrum.mem_zeroLocus _ _ |>.mpr (hstep k)⟩
      step := fun k => p.step k }
  have h1 : (q.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (P i : Set R)) :=
    Order.LTSeries.length_le_krullDim q
  rw [← ringKrullDim_eq_krullDim_zeroLocus] at h1
  exact le_trans h1 (hd i hi)

/-- Quotienting further cannot raise the dimension. -/
theorem ringKrullDim_quotient_le_of_le {R : Type*} [CommRing R] {I J : Ideal R} (h : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) ?_
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk I y, rfl⟩

/-- **The dimension of a quotient by a finite intersection of primes is the largest of the
dimensions of the pieces.** -/
theorem ringKrullDim_quotient_inf_primes {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {P : ι → Ideal R} {I : Ideal R} (hI : I = s.inf P) {d : WithBot ℕ∞}
    (hd : ∀ i ∈ s, ringKrullDim (R ⧸ P i) ≤ d)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hlow : d ≤ ringKrullDim (R ⧸ P i₀)) :
    ringKrullDim (R ⧸ I) = d := by
  refine le_antisymm (ringKrullDim_quotient_le_of_inf_primes hI hd) ?_
  refine le_trans hlow (ringKrullDim_quotient_le_of_le ?_)
  rw [hI]
  exact Finset.inf_le hi₀


end GaloisForLFunctions.HTGeometry
