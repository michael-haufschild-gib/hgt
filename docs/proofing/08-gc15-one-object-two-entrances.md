# G-C15 Proof Attempt: One Object, Two Entrances

Source: `docs/consolidated/08-conjectures-required.md` appendix.

Claim status: `[CONJECTURE]`.

## Target Claim

The Jacobi-Loewner-Krein-Hodge route and the Jensen/Laguerre-Polya/Polya-Schur
route are two coordinate presentations of the same completed archimedean
polarized object.

## Attempt

Let `C` be a completed carrier. One entrance gives a faithful index
`kappa_-(C)`. The other gives all-level Jensen hyperbolicity. To prove they
are the same object one needs natural transformations:

```text
Jacobi/Krein(C) -> Jensen(C),
Jensen(C) -> Jacobi/Krein(C),
```

preserving fake-family behavior and negative-square count.

## Weakened Theorem

If both entrances compute the same faithful kernel `Q_W`, then their RH
criteria are equivalent.

## Obstruction

Equivalence of criteria is weaker than identity of objects. The current corpus
does not define a common universal carrier from which both presentations are
functorial shadows.

## Missing

Construct the common object and prove both presentations are faithful functors.
