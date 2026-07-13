# Prime Kasteleyn Harnack geometry does not localize the centered slice

- **ID:** `prime-kasteleyn-harnack-slice-localization`
- **Stage:** 5-failed
- **Type:** `[NO-GO] [LARGE OUTLANDISH DETOUR AUDIT] [POSITIVE STABILITY SUCCESSOR]`
- **Attempted statement:** Positive planar bipartite dimer weights make the Kasteleyn spectral curve
  Harnack; after evaluating its magnetic variables at centered prime characters, Harnack maximality
  forces all zeros onto the centered critical line.
- **Verdict:** false already for the one-cell honeycomb spectral curve.

## Exact finite counterexample

The positive-weight honeycomb dimer has a Kasteleyn spectral polynomial of trinomial form.  Take

```text
P(x,y)=1+x+3y.
```

This is a positive planar dimer spectral curve and hence is Harnack by the Kenyon--Okounkov--
Sheffield theorem.  On the diagonal magnetic slice `x=y=u`,

```text
P(u,u)=1+4u,
P(-1/4,-1/4)=0,
|-1/4|=1/4 != 1.
```

Thus even the simplest positive Harnack curve can meet a one-parameter magnetic slice away from
the unit torus.  Harnack maximality controls the topology and amoeba multiplicity of the full real
curve; it does not give the half-plane or polydisk nonvanishing needed for critical-line
localization.

A numerical prime-frequency check gives the same diagnosis without being used as proof: the
unweighted trinomial `1+2^(-iz)+3^(-iz)` has many nonreal centered zeros.  The exact diagonal
counterexample above is already decisive and avoids relying on that computation.

## Closed attempted chain

```text
positive prime-labelled planar dimer
  -> Kasteleyn determinant
  -> Harnack spectral curve                               [PARENT THEOREM]
  -/-> prime-frequency slice has only unit-torus zeros    [FALSE]
  -/-> RH.
```

No cofinal limit can repair a finite zero-location theorem that is false at one cell unless the
source family has an additional property absent from general positive dimers.

## Positive successor

The failure isolates the stronger finite datum exactly.  A surviving planar determinant must
satisfy at least one of:

1. multivariate half-plane or polydisk stability;
2. an explicit source-pure amoeba-line exclusion for the ray determined by the prime logarithms;
3. a Hermitian/PSD determinant-pencil representation whose one-variable sections are real-rooted.

The first and third options are pursued concretely in
`../1-in-progress/prime-kirchhoff-matroid-half-plane-rh.md` (HPP matroids, with Kirchhoff
determinants only where regularity permits) and
`../1-in-progress/prime-support-boundary-jet-stability-rh.md`.  If a Kasteleyn matrix also has one
of those properties, the proof comes from that additional stability, not from Harnack maximality.
The second option is a legitimate distinct successor only if prime--Gamma source relations prove
the amoeba avoidance before the Xi divisor is inspected.

The positive finite classification problem is therefore:

```text
which positive planar dimer Kasteleyn polynomials remain nonvanishing
on the common prime Cayley half-planes?
```

That subclass, rather than all Harnack dimers, is the reusable object left by the no-go.

## Parent result

- R. Kenyon, A. Okounkov, and S. Sheffield, *Dimers and amoebae*,
  <https://annals.math.princeton.edu/2006/163-3/p06>.

## Gates

- [x] positive planar dimer parent theorem checked
- [x] smallest diagonal magnetic slice attacked
- [x] explicit off-unit-torus zero exhibited
- [x] Harnack-only implication retired
- [x] positive half-plane/stable subclass isolated
