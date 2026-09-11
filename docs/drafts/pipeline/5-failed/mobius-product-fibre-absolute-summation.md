# Möbius product fibres: internal cancellation and absolute summation fail

- **ID:** E-PRODUCT-FIBRE-001
- **Stage:** 5-failed for cancellation inside a product fibre or absolute summation of fibres.
- **Target:** a source-derived upper bound for the signed Gamma--Hankel covariance.
- **Status:** exact positive classification and variation theorems proved in Lean;
  cancellation between different products remains open.
- **Parent:** [literal renewal attack](../1-in-progress/route-e-literal-renewal-energy-attack.md).

## Frozen test and exact arithmetic consequence

[FAILED CANDIDATE MECHANISM; PAPER AND LEAN PROOFS] Group the original ordered pairs
by their product `q=m*n`, hoping common-divisor and coprime-factor variation
will provide cancellation within each group. Put

```
T_N(q;r) = sum_(1<=m,n<=N, m*n=q) mu(m)*mu(n)/(m+n)^r,
W_N(q;r) = sum_(1<=m,n<=N, m*n=q) mu(m)^2*mu(n)^2/(m+n)^r.
```

For every pair, `mu(m)*mu(n)=lambda(m*n)*mu(m)^2*mu(n)^2`.
This follows from `mu(n)=lambda(n)*mu(n)^2` and complete multiplicativity
of Liouville; it does not require coprimality. Consequently

```
T_N(q;r) = lambda(q)*W_N(q;r),
|T_N(q;r)| = W_N(q;r),
E_N(r) = Gamma(r)*sum_(1<=q<=N^2) lambda(q)*W_N(q;r).
```

All weights are nonnegative. Every nonzero term inside a fixed product
fibre has the same sign. Exact product conditioning therefore removes all
within-fibre cancellation; the desired cancellation must connect different
products. The squarefree cutoff restrictions remain in `W_N`.

## Quantitative test of absolute summation over fibres

The complete fibre variation is exactly the unsigned source pair sum:

```
sum_(1<=q<=N^2) |T_N(q;r)|
 = sum_(1<=m,n<=N) mu(m)^2*mu(n)^2/(m+n)^r.
```

The corpus theorem `quarter_le_card_squarefree` supplies at least `N/4`
squarefree integers in `[1,N]`. For `N>=1` and `r>=0`, every denominator
is at most `(2N)^r`, hence the displayed variation is at least

```
(N/4)^2/(2N)^r = (2^(-r)/16)*N^(2-r).
```

Thus for every `1<r<2`, taking absolute values after exact product grouping
still diverges along every sequence of cutoffs tending to infinity. The
positive survivor is the exact fibre-sign classification,
the source energy decomposition, and this explicit full variation lower
bound. This is not a lower bound for the signed covariance itself.

## Stronger positive survivor: the entire diagonal is identified

If `m,n` are squarefree and `m*n=k^2`, squarefreeness implies `m|k`
and `n|k`. Thus `m,n<=k`; their product equals `k^2`, forcing
`m=n=k`. Conversely `m=n` gives a square product. Therefore

```
D_N(r) = Gamma(r)*sum_(q<=N^2, q square) W_N(q;r),
C_N(r) = Gamma(r)*sum_(q<=N^2, q nonsquare) lambda(q)*W_N(q;r).
```

For `r>1`, the existing diagonal majorant has finite sum `B_r` and
`D_N(r)<=B_r`. Write `V_N` for full fibre variation and `V_N^cross`
for its nonsquare part. The exact identity

```
Gamma(r)*V_N(r) = D_N(r) + Gamma(r)*V_N^cross(r)
```

gives `V_N^cross >= V_N-B_r/Gamma(r)`. Consequently
`V_N^cross -> +infinity` for every `1<r<2`. Absolute summation fails
even after removing every diagonal contribution, not merely because the
diagonal was left in the estimate.

This does not exclude a signed upper ceiling, a bounded-return subsequence,
or a prime-induced comparison between distinct products. It requires those
comparisons to retain their changing cutoff weights.

## Surviving attack

Liouville sign reversal under multiplication by a prime connects different
products, but their complete cutoff weights differ. Test the resulting
retained-weight pairing before claiming a cancellation gain. A formal
change of variables alone would leave the original estimate open.

The parent card retains the next one-prime test, its exact boundary, and
the still-unproved collective estimate; this card retires only the two
mechanisms named in its title.

## Source and method audit

- Deep corpus searches for gcd pair cancellation and signed product fibres
  recovered complete multiplicativity of Liouville and the squarefree
  coefficient identity. Neither requires coprimality of the pair.
- `RHTower.quarter_le_card_squarefree` from `SquarefreeLowerDensity`
  supplies the actual uniform lower-density input used above.
  `MobiusCoprimeSquarefreeProductSignCount` instead retains an unknown
  signed imbalance; it supplies no independent balance estimate.
- The generated ingredient proposal using `finiteSignedCharge_product`
  and a finite modular shear norm was marked `not_verified`. Its Cartesian
  product and modular identities do not identify the coupled physical
  product fibres or bound their signed sum. Deep search coverage was partial;
  statements, method arguments, proof ideas and ingredient sets were inspected.
- Broad `coloring` search found [Zamir, July 2026](https://arxiv.org/html/2607.25973v1):
  the fixed-palette algorithm uses an actual low-degree structure or large
  vertex sets constrained to disjoint palettes. Neither structure has been
  derived for these arithmetic fibres. No algorithm was run.
- The same broad search found [Shi--Dong, July 2026](https://arxiv.org/html/2607.20752v1):
  digit-color restrictions control carries in progressions before a finite-field
  norm construction. No corresponding restriction on literal Möbius signs or
  weighted factor incidences is established here. These papers supplied no
  covariance estimate.

## Verification state

Paper proofs above are complete. The entire source passed
`lake env lean /tmp/route_e_product_fibre.lean` without diagnostics.
The positive survivor is in
`GaloisForLFunctions.RHTower.MobiusProductFibreVariation`, namespace
`RHTower.MobiusProductFibre`, with its umbrella import wired.
The final targeted command
`lake build GaloisForLFunctions.RHTower.MobiusProductFibreVariation` passed.
Existing dependencies replayed informational tactic suggestions; the new leaf
emitted no diagnostics. Generated indexes were refreshed; formal lint passed
with existing file-size warnings. No own Lean process remains.
No numerical experiment or evaluation is part of this attempt.
