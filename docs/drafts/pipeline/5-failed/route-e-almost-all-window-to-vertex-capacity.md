# Route E almost-all window-to-vertex capacity

- **ID:** `ROUTE-E-ALMOST-ALL-WINDOW-VERTEX-CAPACITY-001`
- **Stage:** 5-failed
- **Type:** SOURCE-MECHANISM NO-GO / DEFECT-CURRENT SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact optimum “unused capacity = signed imbalance” already formalized by
  `completeBipartiteProportionalConductance_exact_unused` and
  `completeBipartiteProportionalConductance_attains_signedImbalance` in
  `MobiusBoundaryOppositeSignTransport.lean`

## Proposed mechanism

Partition a block scale into short windows \(B_j\) of length \(h\).  Use an almost-all
short-interval Möbius theorem to declare the few windows outside its error tolerance
“exceptional,” cover those windows with cofactor-amplified \(E_3\) tokens, and treat every
ordinary window as locally balanced.

This incorrectly identifies exceptional windows with unmatched Möbius vertices.

## Killing defect identity

Inside \(B_j\), let \(P_j\) and \(N_j\) be the positive and negative squarefree counts, and put

\[
d_j=P_j-N_j=\sum_{n\in B_j}\mu(n).
\tag{1}
\]

Even with complete bipartite opposite-sign incidence inside the window, the exact minimum unused
capacity is

\[
\boxed{|d_j|.}
\tag{2}
\]

This is not a weakness of a matching algorithm.  Every opposite-sign edge consumes equal mass
from the two signs, so at least the imbalance remains; proportional complete-bipartite transport
attains `(2)`.  The cited Lean theorems prove both statements.

An almost-all theorem at fixed tolerance \(\delta>0\) gives, on ordinary windows, only

\[
|d_j|\le\delta h.
\tag{3}
\]

Summing `(3)` gives the proof-level bound

\[
\sum_{j\ {\rm ordinary}}|d_j|\le\delta U,
\tag{4}
\]

which is linear for fixed \(\delta\), not strict-half.  A power-saving number of exceptional
windows does not change `(4)`.

The information loss is genuine.  An abstract sign sequence may have block defects
\(+\delta h\) throughout the first half of the scale and \(-\delta h\) throughout the second.
It has no exceptional windows and zero total unweighted mean, yet its exponentially weighted
sum is \(\asymp\delta U\), because the two halves receive different Gibbs weights.  Thus even
adding a PNT-level global mean does not recover Route E from `(3)`.

Menon's 2026 mean-square estimate improves the average tolerance to a negative logarithmic
power, but the corresponding total defect remains \(U/(\log U)^{O(1)}\), still far above
\(U^{1/2+\varepsilon}\).

## Strongest positive survivor

Almost-all input produces an exact two-part source decomposition:

1. **hard-window incidence:** exceptional windows, for which cofactor-amplified \(E_3\) supply
   can meet global cardinality and strict-half displacement;
2. **ordinary defect current:** the signed sequence \(d_j\) left by optimal local transport.

A valid hybrid must prove one of:

\[
\delta\le U^{-1/2+o(1)},
\tag{5}
\]

or the genuinely signed estimate

\[
\left|\sum_j d_j e^{-x\,\xi_j}\right|
\le U^{1/2+o(1)}
\tag{6}
\]

for suitable window locations \(\xi_j\), including its sectorwise co-moving boundary form.
Equation `(6)` is a renormalized Möbius source law; it cannot be replaced by
\(\sum|d_j|\le\delta U\).

The cofactor and interval-Hall theorems remain valid, but they solve only the first component.
`MOBIUS-EXCEPTIONAL-CARLESON` is therefore necessary for fallback capacity, not sufficient for
Route E.

## Hostile audit

- “Every ordinary center has an opposite-sign neighbor” is weaker than capacity; a single target
  can serve many rows but carries unit physical load.
- “Every ordinary window has both signs” is weaker than `(2)` by its full signed imbalance.
- Tensoring windows does not erase `(4)` without a signed law for the defect sequence.
- Calling \(d_j\) random or independent adds an unproved source assumption.
- The local optimum `(2)` is classical; standalone novelty is not claimed.  The new Route E
  insight is the exact separation of fallback Hall capacity from the surviving ordinary defect
  current.

## Status

`RETIRED`.  Published almost-all window estimates do not furnish a power-saving unmatched vertex
set.  Cofactor fallback remains a conditional survivor; the ordinary defect current `(6)` and
co-moving seam flux remain `OPEN-SOURCE-001`.
