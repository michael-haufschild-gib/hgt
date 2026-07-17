# Xi analytic--monodromy source-circuit fracture criterion

- **ID:** `xi-source-circuit-fracture-rh`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `../../1-in-progress/joint-source-represented-matroid-transport-rh.md`
- **Statement:** Every Xi divisor point carries the fixed completed-density reflection relation;
  this relation fails to transport to the Hurwitz FE--Schwarz differential circuit exactly at an
  off-critical zero.  Hence global relation preservation and global fracture-freeness are each
  equivalent to RH.

## Theorem

For `rho` in the Xi divisor support put

```text
z_rho=(rho-1/2)(-i).
```

The completed-density components satisfy

```text
E(z_rho)+E#(z_rho)=4 z_rho^2 XiC(z_rho)=0.             (1)
```

Let `M(rho)` be differential dependence of the two continued-Hurwitz functions at exponents
`1-rho` and `conj(rho)`.  The existing exact Hurwitz circuit law gives

```text
M(rho) iff Re rho=1/2.                                  (2)
```

Define a source-circuit fracture at `rho` to mean that `(1)` holds and `M(rho)` fails.  Then

```text
fracture at rho iff Re rho != 1/2.                      (3)
```

Consequently

```text
every analytic relation transports to M
  iff no Xi divisor point is a fracture
  iff RH.                                               (4)
```

The derivative-drop source additionally supplies the unconditional orientation datum

```text
thetaCuspTailThirdDerivativeDropMass > 0.               (5)
```

Equation `(5)` orients the analytic odd boundary channel; it does not prove the comparison in
`(4)`.

## Why this is the positive residue of a no-go

The proposed statement that every off-critical zero is a circuit common to all natural
realizations is false already for the analytic and monodromy pair.  The analytic relation `(1)`
holds at every Xi zero, while the monodromy circuit `(2)` holds only on the critical line.  The
failure is therefore not absence of structure: it identifies the exact positive obstruction,
namely a coefficient-bearing relation-transport fracture.

The word `relation` in `(1)` is intentional.  The theorem does not assert that both analytic
coordinates are nonzero or that the support is minimal, so calling `(1)` a literal two-element
matroid circuit would overclaim.  This is one reason the source object must retain represented
relation vectors rather than only ordinary circuit supports.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.XiSourceMatroidCircuitFracture
```

Principal declarations:

```text
xiCompletedDensityReflectionRelationAt_all
xiHurwitzMonodromyCircuitAt_iff_re_eq_half
xiSourceCircuitFractureAt_iff_re_ne_half
xiSourceCircuitComparisonPreserving_iff_fractureFree
xiSourceCircuitComparisonPreserving_iff_riemannHypothesis
xiSourceCircuitFractureFree_iff_riemannHypothesis
xiSourceCircuitFractureOrientationLaw
```

Targeted foreground checks on 2026-07-17:

```text
lake env lean GaloisForLFunctions/RHTower/XiSourceMatroidCircuitFracture.lean
lake build GaloisForLFunctions.RHTower.XiSourceMatroidCircuitFracture
```

Both passed.  The module contains no hypotheses on the displayed theorems and no `sorry`,
`admit`, new axiom, `opaque`, or `unsafe` declaration.

## Anti-circularity and open producer

This theorem quantifies over the actual Xi divisor.  It is therefore an exact RH-equivalent
consumer/bridge, not an RH proof and not the missing source producer.  The open theorem is to
construct, without using Xi zeros, a strict cofinal comparison from the finite
Euler--Gamma--theta relation module to the analytic, monodromy, spectral, Hermitian, and integral
realizations and to prove that it preserves the coefficient vector in `(1)`.  That source theorem
would discharge the left side of `(4)` and hence prove RH.

## Gates

- [x] exact pointwise analytic relation
- [x] exact pointwise fracture law
- [x] global transport/fracture-free RH equivalence
- [x] positive derivative-drop orientation residue
- [x] unconditional Lean formalization and targeted module build
- [ ] source-pure construction of the five-realization comparison

