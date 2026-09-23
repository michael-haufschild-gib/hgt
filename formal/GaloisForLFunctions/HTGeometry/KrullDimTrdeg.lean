import GaloisForLFunctions.HTGeometry.RationalNormalCone
import GaloisForLFunctions.HTGeometry.HankelSecantDimension

/-!
# Krull dimension is at most the transcendence degree

Noether normalization (`exists_integral_inj_algHom_of_fg`) embeds a polynomial ring on `s` variables
integrally into a finitely generated algebra over a field.  Dimension does not grow along an
integral extension (`ringKrullDim_le_of_isIntegral_rationalNormalCone`), so the dimension is at most `s`; and `s` is at
most the transcendence degree because an injective algebra map cannot decrease it.

```text
ringKrullDim_le_of_trdeg_le              ** dim R ≤ trdeg R for a finitely generated algebra **
ringKrullDim_hankelSecantQuotient_le     ** dim of the Hankel secant quotient is at most 2r **
```

The first statement is not in mathlib.  The second closes the dimension side of the Hankel card:
with `trdeg_hankelSecantQuotient = 2r` it bounds the Krull dimension above, and
`length_le_ringKrullDim_of_isRingRegularSeq` bounds it below by the length of any ring-regular
sequence.  So a ring-regular sequence of length `2r` on the secant ring would immediately give
`IsCohenMacaulayRing`, with the dimension equality coming for free.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- **Krull dimension is at most the transcendence degree**, for a finitely generated algebra over a
field.  Noether normalization embeds a polynomial ring on `s` variables integrally, and `s` is at
most the transcendence degree; dimension does not grow along an integral extension. -/
theorem ringKrullDim_le_of_trdeg_le {k : Type u} {R : Type u} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (h : Algebra.trdeg k R ≤ (d : Cardinal)) :
    ringKrullDim R ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k R
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hgint⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (MvPolynomial (Fin s) k) :=
    ringKrullDim_le_of_isIntegral_rationalNormalCone
  have h2 : ringKrullDim (MvPolynomial (Fin s) k) = ((s : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k]
    simp
  have h3 : (s : Cardinal.{u}) ≤ (d : Cardinal.{u}) := by
    have hle := trdeg_le_of_injective g hginj
    rw [MvPolynomial.trdeg_of_isDomain] at hle
    simpa using le_trans hle h
  have h4 : s ≤ d := by exact_mod_cast h3
  rw [h2] at h1
  refine le_trans h1 ?_
  exact_mod_cast Nat.cast_le.mpr h4

/-- **The Hankel secant quotient has Krull dimension at most `2r`.**  Its transcendence degree is
exactly `2r`, and Krull dimension is bounded by transcendence degree.

Together with a ring-regular sequence of length `2r` — the one remaining input — this would give
`IsCohenMacaulayRing` for the secant ring, since `length_le_ringKrullDim_of_isRingRegularSeq`
supplies the reverse inequality automatically. -/
theorem ringKrullDim_hankelSecantQuotient_le (K : Type) [Field K] [CharZero K] {N r : ℕ}
    (hN : 2 * r ≤ N) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r)
      ≤ (((2 * r : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  classical
  haveI hprime : (RHTower.finiteHankelSecantIdeal K N r).IsPrime :=
    RHTower.finiteHankelSecantIdeal_isPrime K N r
  haveI : IsDomain (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) :=
    Ideal.Quotient.isDomain _
  haveI : Algebra.FiniteType K (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ K (RHTower.finiteHankelSecantIdeal K N r)) Ideal.Quotient.mk_surjective
  exact ringKrullDim_le_of_trdeg_le (le_of_eq (trdeg_hankelSecantQuotient K hN))


end GaloisForLFunctions.HTGeometry
