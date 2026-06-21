# C-2026-06-18-021 Proof Attempt: Hodge-Index Realization

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

Realize `Q_W = Omega - Pi` as a Hodge intersection form of a missing
`Spec Z x_{F1} Spec Z` object with a source-built complex/Kahler structure `J`,
so Hodge index forces the faithful negative index to vanish.

## Attempt

A Hodge-index proof would have this shape:

```text
source-built geometry X
primitive subspace P_X
comparison c: P_X -> test space of Q_W
Hodge-Riemann positivity on P_X
c^* Q_W = +/- intersection form on P_X.
```

Then the sign convention can be chosen so that Hodge-Riemann positivity gives
`Q_W >= 0`, and hence RH.

## Weakened Theorem

If such a comparison identifies `Q_W` with a positive Hodge-Riemann form on the
entire faithful carrier, then RH follows.

## Obstruction

The required absolute geometry does not currently exist as a mathematical
object in the corpus. Also Hodge index usually gives a signature theorem, not
automatic vanishing of all negative directions unless the correct primitive
piece and sign are identified.

## Missing

The F1/absolute space, its cohomology, the source-built `J`, the intersection
form, and the comparison with Weil's explicit-formula form.
