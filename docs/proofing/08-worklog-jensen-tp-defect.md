# Jensen TP-Defect Proof Attempt

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

```text
# non-real Jensen roots -> 2 kappa_-,
= 0 for all (d,n) <=> Laguerre-Polya <=> RH.
```

## Attempt

The known scalar entrance is:

```text
xi in Laguerre-Polya <=> RH,
```

and Jensen polynomial hyperbolicity for all relevant degrees is equivalent to
Laguerre-Polya membership. Therefore absence of non-real Jensen roots at all
levels is equivalent to RH.

The stronger count `# non-real roots -> 2 kappa_-` needs a model-matching
theorem: each off-line conjugate pair must contribute exactly two non-real
Jensen roots in the limiting defect count, with no extra non-real roots from
finite-degree artifacts.

## Weakened Theorem

All-level Jensen hyperbolicity is equivalent to RH, assuming the standard
Jensen/Laguerre-Polya equivalence for `xi`.

## Obstruction

The exact defect count is not supplied by the equivalence alone. It requires
tracking multiplicities through the Jensen approximation regime and proving no
spurious non-real roots persist.

## Missing

A comparison theorem between Jensen root defects and the faithful carrier
index `kappa_-`.
