# Four-leg relative-return-degree selection

- **ID:** ULF-FRRD-001
- **Stage:** 5-failed
- **Type:** FALSIFIED as a source-derived selection mechanism
- **Parent:** ULF-PHRD-001
- **Status:** `[FALSE/UNSUPPORTED PRODUCER] [POSITIVE SURVIVOR PROMOTED TO ULF-PHSR-001]`

## Proposed mechanism

The card proposed that the source mean return `7/4`, together with four Hodge polarizations,
canonically generates a relative completion determinant of degree `7`, and that every off-line
functional-equation quartet adds degree `4`.  Completion conservation would then give
`7=7+4k` and force `k=0`.

## Exact killing mechanism

The source colligation does not generate the proposed determinant degree.  Write its survival
shift as

```text
C=S R,
R e_n=sqrt((2n+3)/(2n+9)) e_n,
S e_n=e_(n+1).
```

Then

```text
sqrt((2n+3)/(2n+9))-1=-3/(2n)+O(n^-2).              (FRRD.1)
```

The singular values of `C-S` are the absolute values of these weights.  Therefore

```text
C-S is in S_2 but not S_1.                           (FRRD.2)
```

The natural regularized determinant at this perturbation depth is `det_2`.  But `C-S` is a
compact unilateral weighted shift with spectrum `{0}`; its regularized determinant
`det_2(I+z(C-S))` is identically one.  It has neither zeros nor winding and cannot produce degree
`7`.  More elaborate `det_2` products acquire the standard multiplicative anomaly, already
formalized in `HTGeometry/FredholmDeterminant` and audited in
`PrimeDepthBVWoldGradedDet2ScalarDescentBoundary` and
`PrimeDepthBVWoldSourceDaggerAtlasTransition`; the correction is continuous scalar data, not a
canonical integral source degree.

The Bourgain--Grünbaum--Velázquez--Wilkening return theorem does imply that *if* one replaces the
source by a finite-dimensional recurrent rational-inner model, its mean `7/4` forces dimensions
`4|d` and winding `7|K`, with minimal `(d,K)=(4,7)`.  ULF-PHRD-001 simultaneously proves that no
such finite model realizes the source history: rational-inner coefficients decay exponentially,
whereas the exact first-return law has a polynomial `n^-4` tail.  Thus the integer `7` belongs to
a deliberately lossy finite coarse model, not to the actual source operator.

Finally, no checked corpus theorem assigns `+4` determinant degree to an off-line quartet without
already inserting its divisor.  That proposed target law had no independent producer either.

## No-go closure

- **Exact killing theorem/mechanism:** `(FRRD.1)--(FRRD.2)` place the actual source in the
  Hilbert--Schmidt/non-trace-class regime, where its direct regularized determinant is zero-free;
  the only degree-seven object is the finite rational-inner coarse model already excluded by the
  full tail.
- **Strongest positive survivor:** the non-trace-class perturbation is not featureless.  Its
  positive elapsed-history defects `D_N=I-C*^N C^N` are measurable weak `S_1` with exact residue
  `3N`; every exit slice has residue `3`, and their marked normal readout reconstructs the
  prime-mixed integral nuclear `mathsf T`.  This is proved in ULF-PHSR-001.
- **New insight:** the intrinsic source invariant is a singular residue clock plus finite-part
  torsor, not a Fredholm return degree.  The number `7` remains an exact first-moment numerator but
  cannot be promoted to a completion index without new structure.
- **Status:** failure is paper-closed.  Positive survivor is dependency-closed in Stage 2.

## It cannot be this

RH selection cannot come from assigning the actual open source colligation the degree of a finite
recurrent observer.  Any future determinant/index proposal must be constructed directly in the
power-law infinite history and must survive the `S_2\S_1` anomaly; the equality `7=7+4k` may not
be used as its own producer.

## Log

- 2026-09-03 — retired after hostile source-determinant attack; residue-clock survivor promoted.

