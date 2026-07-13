# Height-adaptive finite RH ladder

- **ID:** `height-adaptive-finite-rh-ladder`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN RH CHAIN / QUANTITATIVE MULTIPLICITY COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `XiZeroDensity`, `ModulusSlopeField`, `RHLadderTheory`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveFiniteLadder.lean`

## Statement

The complete cofinal RH ladder is stronger than necessary.  The corpus already proves an
unconditional constant `C>0` such that the total Xi multiplicity in `B(2,r)` obeys

\[
N_\Xi(r)\le C(1+r)\log(2+r),\qquad r\ge1.
\]

For each `r`, choose one finite depth `k(r)` satisfying

\[
2^{k(r)}>C(1+r)\log(2+r).
\]

If every right-half Xi zero inside `B(2,r)` has order divisible by `2^{k(r)}`, then the disc
contains no right-half zero.  Indeed, any such order is positive, at most `N_Xi(r)`, and divisible
by a strictly larger positive integer.  Exhausting the plane by these discs proves RH.

The regional root is itself stronger than necessary.  Let `boxOrderSum(n)` be the total Xi order in
the right-half upper box `1/2 < Re(s) < 1`, `0 <= Im(s) < n`, and let

\[
\operatorname{DISC}_{k}(n)=\texttt{discCensusH}(k,n)
  =\texttt{boxOrderSum}(n)\pmod {2^k}.
\]

It is enough, for each integer `n>=1`, to choose one `k_n` above the global disc envelope and prove
the single scalar relation

\[
\operatorname{DISC}_{k_n}(n)=0.
\]

The box mass is then simultaneously divisible by `2^{k_n}` and strictly smaller than it, hence is
zero.  This scalar census condition is the weakest formalized entrance; regional Kummer roots are
only one sufficient provider.

```text
unconditional Xi zero-count envelope
  + one sufficiently high vanishing scalar DISC census per integer height
  -> total right-half box mass is divisible by a larger positive integer
  -> every integer-height right-half box is empty
  -> RH.
```

The source-facing condition is explicit.  On

\[
U_r=\{\Re s>1/2\}\cap B(2,r+1)
\]

construct one analytic function `g_r` with

\[
g_r^{2^{k(r)}}=\xi,
\qquad
2^{k(r)}>C(1+r)\log(2+r).
\]

Lean proves that this regional root supplies the disc rung and hence the capstone.  No global root
branch or compatibility with every higher Kummer depth is assumed.

Integer discs are cofinal, so the premise can be made countable.  It is enough to construct

\[
g_n^{2^{k_n}}=\xi
\quad\hbox{on}\quad
\{\Re s>1/2\}\cap B(2,n+1),
\qquad n=1,2,\ldots,
\]

with `2^{k_n}` above the same envelope at `n`.  Lean formalizes this as
`XiNatHeightAdaptiveDiscKummerRoots` and proves the resulting RH capstone.

## Attack and non-circularity

This does not assume the local order and then choose a larger power of two.  The depth is fixed
uniformly for the complete disc from the unconditional Jensen/growth envelope before selecting any
zero.  It is therefore stronger than the tautology that every finite integer is smaller than some
power of two, and weaker than demanding every ladder rung at every point.

The route dies if `k(r)` is chosen after reading the largest zero multiplicity rather than from the
source-independent counting envelope.  It also dies if the regional root is defined only after
deleting the zeros it is meant to constrain.

## Open core

`[OPEN CORE]` Prove from the completed prime--Gamma/SEM boundary source that, for each integer
height `n`, one scalar census `discCensusH k_n n` vanishes at a modulus above the explicit global
zero-count envelope.  No pointwise zero-order divisibility, analytic root, global branch, or
compatibility between different heights is required.

A regional degree-`2^{k_n}` analytic Kummer root is a sufficient but unnecessarily strong provider
of the census relation.  The preferred attack is a direct boundary congruence for the total box
winding/order.

Since `N_Xi(r)=O(r log r)`, the required depth is logarithmic in `r`; this asymptotic depth estimate
is a paper observation, not yet a separate Lean theorem.

## Gates

- [x] unconditional disc zero-count envelope
- [x] prove one local order is bounded by the total disc divisor mass
- [x] formalize regional finite ladder and the exhaustion theorem
- [x] formalize the regional analytic-root entrance to the disc ladder
- [x] reduce the regional-root family to countably many integer windows
- [x] weaken the regional roots to one scalar DISC census relation per integer height
- [x] verify the exact Lean dependency and axiom surface
- [ ] construct the height-adaptive regional roots/congruences
- [ ] RH

## Formal verification

Lean proves `xiOrderToNat_le_xiBallOrderSum`, the regional predicate `XiDiscRHLadder`, the
height-adaptive predicate `XiHeightAdaptiveDiscLadder`, and the capstone
`riemannHypothesis_of_xiHeightAdaptiveDiscLadder`.  The constant
`xiZeroCountEnvelopeConstant` is selected from the already proved unconditional
`xi_zeroCount_growth` theorem.  The named module build passes in the repository toolchain.  The
source-facing chain is formalized by `XiDiscKummerRoot`,
`xiDiscRHLadder_of_kummerRoot`, and
`riemannHypothesis_of_xiHeightAdaptiveDiscKummerRoots`.  Its countable refinement is
`XiNatHeightAdaptiveDiscKummerRoots` with capstone
`riemannHypothesis_of_xiNatHeightAdaptiveDiscKummerRoots`.  The strictly weaker scalar interface is
`XiNatHeightAdaptiveBoxCensus`, with capstone
`riemannHypothesis_of_xiNatHeightAdaptiveBoxCensus`.  The capstones use only `propext`,
`Classical.choice`, and `Quot.sound`.
