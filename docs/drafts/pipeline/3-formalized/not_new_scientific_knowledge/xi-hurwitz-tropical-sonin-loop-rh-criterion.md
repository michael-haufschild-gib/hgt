# Xi--Hurwitz tropical Sonin loop RH criterion

- **ID:** `xi-hurwitz-tropical-sonin-loop-rh-criterion`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`, `[FORMALIZATION]`, not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzTropicalSoninLoop.lean`
- **Route:** `../../1-in-progress/hurwitz-sonin-tropical-loop-rh.md`

## Statement

Let `alpha` be the supremal normalized principal Hurwitz phase, already proved equal to the sharp
rightmost Xi displacement.  Define

```text
m(alpha)=2+(1+alpha)^(-1)
```

and the closed Sonin scale path `3 -> m(alpha) -> 3`.  Then `1<m(alpha)<=3`, and
`m(alpha)=3` exactly when `alpha=0`.

The faithful Sonin finite-word normal form remembers the minimum scale visited.  Therefore Lean
proves, at every positive aperture `a`,

```text
RH <->
  operator(3 -> m(alpha) -> 3)
    = compactly
  directGram(3,3).
```

## Scope

The loop is defined from the target Xi phase.  The theorem does not construct a source-only
prime--Gamma/Hurwitz Gram word with this normal state or prove its endpoint absorption.  It is a
routine exact bridge between two already formalized criteria and is not new scientific knowledge.
