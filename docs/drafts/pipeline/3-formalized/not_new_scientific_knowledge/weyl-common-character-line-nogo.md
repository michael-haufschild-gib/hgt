# Weyl common-character-line no-go

- **ID:** `weyl-common-character-line-nogo`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeylCommonEigenspaceNoGo.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

Let `U,V` be finite complex matrices satisfying

```text
U V = zeta V U.
```

If a nonzero vector `x` is a common eigenvector

```text
U x = a x,
V x = b x
```

with `a,b` nonzero, then `zeta=1`.  Consequently, at every positive dyadic depth, a Weyl pair with
phase `Bottcher.dyadicRoot(k)` preserves no common character line.

## Proof

Applying the two sides of the Weyl equation to `x` gives

```text
ab x = zeta ab x.
```

One nonzero coordinate of `x` and the nonvanishing of `a,b` permit cancellation, giving
`zeta=1`.  The depth-`k` Böttcher phase has order `2^k>1`.

## Positive statement from the Hurwitz packet no-go

The rational Hurwitz packet has a canonical finite Fourier clock--shift action, but the scalar-zeta
component is one character line.  A projection that isolates that line necessarily breaks at least
one Weyl generator.  Therefore the packet cannot constrain the scalar-zeta multiplicity by simply
projecting the full determinant law.

The positive successor is exact:

> any arithmetic isolation theorem compatible with the Weyl action must retain a full nontrivial
> `2^k`-orbit (or control the complementary orbit's divisor independently); it cannot retain only
> a common one-dimensional character eigensector.

## Formal surface

- `phase_eq_one_of_weyl_common_eigenvector`
- `no_dyadicWeyl_common_eigenvector`

## Verification

`lake env lean GaloisForLFunctions/RHTower/WeylCommonEigenspaceNoGo.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is standard Weyl-pair representation theory.  No claim of new scientific knowledge is made.
It formalizes the exact obstruction to a trivial-character projection in the Hurwitz torsion
detour.

## Gates

- [x] 0 -> 1: common-character-line shortcut stated
- [x] 1 -> 2: phase-one obstruction proved
- [x] 2 -> 3: dyadic specialization formalized and checked
- [ ] 3 -> 4: not promoted; full-orbit arithmetic isolation remains open
