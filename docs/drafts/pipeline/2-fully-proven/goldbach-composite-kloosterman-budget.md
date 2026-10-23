# Composite Kloosterman budget for the finite product incidence

- **ID:** goldbach-composite-kloosterman-budget
- **Stage:** 2-fully-proven
- **Type:** Classical bridge; deliberately weaker than the Weil bound, no novelty claim
- **Parent:** [prime-dilation dispersion](../1-in-progress/goldbach-prime-dilation-dispersion.md)
- **Lean status:** Not formalized; no theorem stub or analytic premise added

## Exact statement

For every positive modulus M and residues a,b modulo M, put
g=gcd(M,gcd(a.val,b.val)). With the standard Kloosterman sum over units,

    |S(a,b;M)|³ ≤ 512 τ(M)³ M² g.                    (1)

This bound keeps the actual frequency gcd and has exponent 2/3 instead
of 1/2. That weaker exponent still gives a power saving after summing
the balanced product row moduli. The numerical constant pays the prime 2.
No conjectural cancellation estimate is an input.

## Paper proof

**Common-factor reduction.** Write M=gL and a=ga', b=gb' using integer
representatives. Reduction `(Z/M)× → (Z/L)×` is onto. Its fibres all have
size λ=φ(M)/φ(L), and λ≤g: reduction of the whole residue ring has exactly
g elements in each fibre. The phase factors through this reduction,
including the inverse coordinate. Thus

    S(a,b;M)=λ S(a',b';L).

The reduced pair satisfies gcd(a',b',L)=1. It suffices to prove the
primitive-pair bound with g=1, since τ(L)≤τ(M) and
g³L²=M²g. If L=1, the reduced sum consists of one term and the same
inequality follows directly.

**Prime powers.** At each prime power p^k dividing L, at least one
coefficient is a unit. Inversion of the summation unit interchanges
the two coefficients, so put the unit in the inverse coordinate.

For odd p and k=1, the checked prime Weil bound gives
`|S|³≤8p^(3/2)≤8p²=(k+1)³p^(2k)`.
For k≥2 put j=ceil(k/2), m=k−j. The checked stationary-phase identity
restricts the sum to unit x satisfying

    a x²=b (mod p^m).

If there is no solution, the sum vanishes. Otherwise choose a solution
x₀. The equation forces a to be a unit modulo p^m, and x/x₀ is a square
root of 1 there. For odd p there are at most two roots. Every root has
p^j lifts modulo p^k, so `|S|≤2p^j`. Since 3ceil(k/2)≤2k for k≥2,

    |S|³≤8p^(2k)≤(k+1)³p^(2k).

At p=2, the same argument needs at most eight roots of 1 modulo 2^m.
For m≤2 this follows from the size of the residue ring. For m>2,
`(x−1)(x+1)` is divisible by 2^m. At least one of x−1 and x+1 is
not divisible by 8, because their difference is 2. Cancelling its
2-adic valuation (at most 2) shows x≡1 or −1 modulo 2^(m−2).
Those two classes contain at most eight residues modulo 2^m.
Hence `|S|≤8·2^j`, giving

    |S|³≤512(k+1)³2^(2k).

At p=2,k=1 the unit group has one element, so this bound also holds.
The existing `HalfWeight.pm_classes` at n=1 supplies the same eight-root
estimate; its source has been inspected, but no new closure audit of it
is claimed here.

**CRT.** Twisted multiplicativity splits S over the prime-power factors
of L. The coefficient twists are units and preserve primitive pairs.
Multiply the cubed bounds. The prime 2 occurs at most once among the
prime-power factors, so 512 occurs at most once. Since
`τ(L)=∏_(p^k∥L)(k+1)`, the primitive-pair result is

    |S(a',b';L)|³≤512τ(L)³L².

Common-factor reduction now proves (1). Every ingredient is finite
arithmetic except the already checked prime Weil bound, whose full Lean
closure contains only the standard foundational axioms.

## Proof-source audit

- Prime Weil roots: `/tmp/hgt-goldbach-prime-dilation-source-audit.log`.
- CRT and odd-prime-power stationary phase:
  `/tmp/hgt-goldbach-composite-source-audit.log`.
- Each audit passed direct `lake --old env lean`, with only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Corpus supplies `ZMod.unitsMap_surjective` through the inspected finite
  Frobenius reduction source, and the square-root congruence classification
  in `RHTower/HalfWeightSquareRoots.lean`.

## Formalization obligations

Formalize (1) itself, with arbitrary actual residues and positive modulus.
Keep the common-factor phase identity, exact fibre multiplicity, the
two-adic root count and CRT induction inside its proof closure. Do not
replace any of these by a supplied bound or a `Prop` interface.

After (1), the finite modular-hyperbola completion and its zero-frequency
terms still require their own proof. Neither (1) nor the complete-residue
kernel is the centered Goldbach dispersion estimate.
