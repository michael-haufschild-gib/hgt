# Exact weighted digit identities for geometric receiver rows

- **ID:** biarithmetic-weighted-digit-identities
- **Stage:** 3-formalized
- **Type:** CLASSICAL FINITE ALGEBRA
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** Evaluating ordinary base-five digits at a real parameter gives exact affine recursion, block concatenation, arbitrary-depth dilation defects, and a leading-digit lower bound.

## Proof

Write `D_a(n)=sum_l digit_l(n) a^l`, a finite polynomial. Splitting the least significant digit gives

`D_a(5n+r)=r+a D_a(n)` for `0<=r<5`.

Splitting after `r` digits gives, for `m<5^r`,

`D_a(5^r n+m)=a^r D_a(n)+D_a(m)`.

Equivalently, `a^r D_a(floor(n/5^r))=D_a(n)-D_a(n mod 5^r)`. These are polynomial identities for every real `a`. For `a>=0`, every digit contributes nonnegatively. If `5^r<=n<5^(r+1)`, the leading digit is at least one, so `D_a(n)>=a^r`.

The geometric receiver row is `V_a(n)=a/(5-a) D_a(n)` when `0<a<5`; proving its infinite fractional-part series representation is a separate analytic bridge. The identities here are exact finite foundations, not that bridge or an escape-module classification. Weighted digit sums are classical; no novelty is claimed for these identities.

## Verification

- [x] Complete finite paper proof.
- [x] Finite identities checked in scratch and direct repository leaf.
- [x] Repository leaf, axiom audit, and umbrella import.

The direct check of `WeightedBaseFiveDigits.lean` passed. Transitive audits of
`fiveDigitRow_affine`, `fiveDigitRow_concat`, `fiveDigitRow_split`, `fiveDigitRow_block_lower`,
and `fiveDigitRow_dilation_defect` report only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports the leaf; no umbrella build was run. Obsolete scratch files were removed.
