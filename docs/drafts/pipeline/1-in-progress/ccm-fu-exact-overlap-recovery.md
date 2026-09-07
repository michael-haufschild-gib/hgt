# CCM-FU: recover actual mergers beyond the geometric certificate

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], direct source comparison
- **Goal:** Complete signed Abel bound and RH remain open.
- **Parent:** [first-prime certificate obstruction](../5-failed/ccm-fu-universal-first-prime-certificate.md).

## Proof target

At M=12p the geometric first-prime certificate fails for every sufficiently
large prime p, although its actual energy contracts. Attack the stronger
positive statement that every second prime q still gives `Q_{p,q}<=B` in
this entire family. Retain every four-cofactor block and its actual signs;
do not infer this from the failed geometric allowance.

The intended source estimate is `K_d(M)<=3sqrt(M)/5` at every cutoff and
dilation. The smooth remainder has increasing differences between consecutive
squares. Its transition to a square is upward by the harmonic half-bound.
Thus its maximum is controlled by square endpoints. Stirling's global
ceiling and the harmonic lower twelfth-square correction bound each square
by `7/6-gamma-1/(2s)+1/(12s^2)<3/5`. Centered time cancellation and exact
clipped homothety transfer this ceiling to every K_d.

For the quotient-twelve child, analytic endpoint estimates aim at
`K_d(12)<=0.104sqrt(12)` for all d>0. The exact mean gives a parent floor
`K_r(12p)>=0.09sqrt(12p)` uniformly over r<=12 once p is large.
For q>12 the joint child vanishes. The bounds b<=0.104sqrt(M),
c<=0.6sqrt(M), a>=0.09sqrt(M) imply `bc<=a(b+c)`, because
`0.104*0.6<0.09*(0.104+0.6)`.

For q<=12, the two large-parent channels approach the same coefficient
uniformly on these finitely bounded cofactor scales. Their difference can
be made at most0.001sqrt(M), while the difference of the two nonnegative
small-child profiles is at most0.104sqrt(M). Their complete alternating
square is then paid by the two parent squares alone. Cofactors r>12 have
both p-children zero and contract directly.

These are source-level proof obligations, not numerical predictions or
assumed inputs. No computation is planned. Even if closed, this proves two
initial mergers in the stated family; complete adaptive iteration and RH
remain separate obligations.
