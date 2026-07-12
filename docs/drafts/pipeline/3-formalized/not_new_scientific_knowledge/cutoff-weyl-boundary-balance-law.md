# Cutoff Weyl boundary-balance law

- **ID:** `cutoff-weyl-boundary-balance-law`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CutoffWeylBoundary.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

Let `e` be an idempotent matrix cutoff and let `U,V` obey the global Weyl relation

```text
U V = zeta V U.
```

Write

```text
c_e(A) = e A e,
b_-(A) = (1-e) A e,
b_+(A) = e A (1-e).
```

Then

```text
c_e(U)c_e(V) - zeta c_e(V)c_e(U)
  = zeta b_+(V)b_-(U) - b_+(U)b_-(V).                    (1)
```

Consequently the compressed pair satisfies the same Weyl relation exactly if the two opposite
corner products obey the boundary-balance law

```text
zeta b_+(V)b_-(U) = b_+(U)b_-(V).                        (2)
```

If `U` commutes with the cutoff, both directed corners of `U` vanish, so `(2)` holds automatically.
This is the natural aperture situation for Euler multiplication.  The compressed translation still
need not be invertible; preservation of the projective equation and preservation of invertibility
are separate gates.

## Proof

The existing compression semicommutator theorem gives

```text
c_e(UV) = c_e(U)c_e(V) + b_+(U)b_-(V),
c_e(VU) = c_e(V)c_e(U) + b_+(V)b_-(U).
```

Compress `UV=zeta VU`, substitute both identities, and rearrange.  Equation `(2)` makes the
right side of `(1)` zero.

## Positive statement from the pinned no-go

`PrimeDyadicWeyl.lean` proves that the global translation generator has no fixed spectral point, so
literal descent to one pinned SEM germ is impossible.  Equation `(1)` identifies the surviving
mechanism rather than merely closing the route:

> a nonlocal cutoff descent preserves the dyadic Weyl phase exactly when its two directed boundary
> flows balance projectively.

This converts the open RH source theorem into a concrete boundary identity.  The next object is the
source-defined SEM annulus cutoff for the global prime translation--Euler pair, together with finite
reduced operators whose corner products can be compared by `(2)`.

## Formal surface

- `compression_weylBoundary`
- `compression_weylRelation_of_boundaryBalance`
- `compression_weylRelation_of_left_commutes_cutoff`
- `not_boundaryBalance_of_compression_weylDefect_ne_zero`

## Verification

`lake env lean GaloisForLFunctions/RHTower/CutoffWeylBoundary.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is the standard Toeplitz--Hankel semicommutator applied to a projective Weyl relation, so no
claim of new scientific knowledge is made.  Its significance is exact localization of the nonlocal
descent condition in the RH chain.

## Gates

- [x] 0 -> 1: compressed Weyl defect and corner data stated
- [x] 1 -> 2: exact boundary identity and balance criterion proved
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; source SEM cutoff realization remains open
