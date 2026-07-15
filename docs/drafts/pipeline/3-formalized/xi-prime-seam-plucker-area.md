# The Xi prime seam obstruction is a weighted Plucker area

- **ID:** `xi-prime-seam-plucker-area`
- **Stage:** 3-formalized
- **Type:** EXACT HIGHER-RANK GEOMETRY / UNIFIED-FIELD CORE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CLASSICAL IDENTITY, NEW SOURCE INTERPRETATION CANDIDATE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairVariance.lean`

## Theorem

Let `a_p` be any complex prime-indexed packet and put `mu_p=1/p`.  For a finite prime set `s`,
write

```text
M_s = sum_(p in s) mu_p,
S_s = sum_(p in s) mu_p |a_p|^2,
A_s = sum_(p in s) mu_p a_p.
```

Define the weighted Gram determinant of the constant section and `a` by

```text
Delta_s(a)=M_s S_s-|A_s|^2.                               (1)
```

Then the ordered reciprocal-prime pair energy satisfies

```text
E_s(a)=sum_(p,q in s) mu_p mu_q |a_p-a_q|^2
      =2 Delta_s(a).                                      (2)
```

In particular `Delta_s(a)>=0`.  For the canonical FE--Schwarz seam on every Xi fibre, the
formalized RH obstruction energy is exactly twice this determinant.

## Plucker meaning

In the finite weighted Hilbert packet, `(1)` is the Gram determinant of `1_s` and `a_s`, hence

```text
2 Delta_s(a)=||a_s tensor 1_s-1_s tensor a_s||^2.         (3)
```

Thus the obstruction is not an accumulation of unrelated prime scalars.  It is the squared
Plucker area of one source two-plane.  Pairwise coherence is precisely rank collapse of that
plane.  For the canonical seam, cofinal decay then turns a constant packet into the zero packet,
so the critical line is the zero-area locus.

## Proof

The already-formalized weighted variance identity gives

```text
E_s(a)=2 M_s S_s-2|A_s|^2.
```

Factoring `2` proves `(2)`.  Pair-energy nonnegativity proves nonnegativity of `(1)`.  Equation
`(3)` is the standard Gram/exterior-square identity and supplies the geometric interpretation of
the exact Lean equality.

## Why this changes the rigidity target

Every individual Xi seam charge tends to zero throughout the open strip, including off-line
fibres.  Hence each pointwise pair difference is bounded and ordinary fixed-point boundedness
cannot contradict it.  The non-RH theorem instead produces finite sets whose *whole Plucker area*
is arbitrarily large.  Any higher-rank group route must therefore construct one packet element
`g_s` satisfying

```text
||b(g_s)||^2=2 Delta_s(a),                                (4)
```

not merely represent each difference `a_p-a_q` separately.  This is the exact positive residue of
the failed pointwise property-`(T)` route.

## Lean declarations

```text
primePairPluckerGramDet
primePairDifferenceEnergy_eq_two_mul_pluckerGramDet
primePairPluckerGramDet_nonneg
orbitwisePrimeSeamPairEnergy_eq_two_mul_pluckerGramDet
```

## Verification

The existing module cache was present, so no build was run for this touched file.  The final
source check was serialized:

```text
lake env lean GaloisForLFunctions/RHTower/XiPrimeSeamPairVariance.lean
```

It completed without Lean diagnostics.  No full or concurrent Lean build was run.

## Novelty boundary

- Weighted variance, Gram determinants, Cauchy--Binet, and exterior-square norms are classical.
- The existing module already contained the scalar variance identity.
- Candidate new content is the exact identification of the canonical Xi obstruction as the
  Plucker area that must be packetized by the HT horizon `A2` action.
- This is structurally significant but not an RH proof: equation `(4)` remains open.
