# B1 Proof Attempt: Source-Measure Bridge

Source: `docs/consolidated/08-conjectures-required.md` §2 and
`docs/consolidated/03-theorems-toward-rh.md` §1.

Claim status: `[CONJECTURE - hard arrow]`.

## Target Claim

The completed transport features force

```text
supp(mu_xi) subset {Re s = 1/2},
mu_xi = (1 / 2pi) Delta log |xi|.
```

Equivalently, all off-line contour charges of `d log xi` vanish.

## Proof Attempt

The bridge becomes exact if one can prove a contour-charge theorem. Let `R` be
a rectangle in the critical strip whose closure avoids the critical line and
whose boundary avoids zeros. By the argument principle,

```text
(1 / 2pi i) int_boundary(R) xi'(s)/xi(s) ds
```

is the number of zeros of `xi` in `R`, counted with multiplicity. Therefore:

```text
all such off-line contour integrals vanish
  => no zeros off the critical line
  => RH.
```

Conversely, RH implies the same vanishing for every such off-line rectangle.

So the transport bridge must prove that the listed transport features imply
the vanishing of these contour integrals. Any weaker statement about windowed
statistics, typical behavior, medians, or covariance is insufficient unless it
is shown to force every off-line contour integral to be zero.

## Weakened Theorem Proved Here

**Theorem B1-W.** The source-measure bridge is equivalent to an all-rectangle
contour-charge vanishing theorem:

```text
supp(mu_xi) subset {Re s = 1/2}
iff
int_boundary(R) d log xi = 0
```

for every rectangle `R` whose closure is disjoint from the critical line and
whose boundary avoids zeros.

Proof: `mu_xi` is the divisor measure of the entire function `xi`; the
argument principle identifies contour periods with zero count in each
rectangle. Rectangles disjoint from the critical line form a basis for testing
off-line support.

## Where The Full Proof Fails

The corpus has not shown that phase-weld cancellation, cross-lane association,
Berry equalization, survivor spines, reset occupation, volume covariance, or
two-clock seams imply contour-charge vanishing. Those are features of a
transport field; RH needs a statement about the support of its divisor current.

## Missing Input

1. A canonical map from transport features to a closed current or contour
   integral.
2. A theorem that nonzero off-line contour charge forces violation of at least
   one completed transport feature.
3. A fake-family separation theorem, because an FE-exact fake may reproduce
   transport features while retaining off-line zeros.
