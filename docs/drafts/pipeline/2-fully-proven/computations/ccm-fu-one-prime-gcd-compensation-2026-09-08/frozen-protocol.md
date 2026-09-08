# CCM-FU: one-prime compensation between exact gcd groups

- Status: frozen diagnostic; no universal inequality proved.
- Type: `[BRIDGE]` candidate, not a new universal-law conjecture.
- Full chain: actual divisor source → uniform O(M) complete signed Abel head → CCM-FU → RH.
- Frontier map remains read only.

## Frozen mathematical question

Keep the literal coefficients C_d(M), diagonal D(M)=sum_d C_d(M)^2,
and complete ordered off-diagonal gcd groups G_r(M). The existing exact
identity is S(M)^2=D(M)+sum_r G_r(M). The previous positive-part budget
discarded essential compensation and failed numerically at M=115.

At each M, put positive groups on the left and negative groups on the
right. Connect r and s precisely when r/s or s/r is an integer prime.
Allow nonnegative fractional transfer along these edges, with row
capacity G_r and column capacity -G_s. Let U(M) be total positive mass
minus the largest transferable mass. The frozen candidate is

```text
                         U(M) <= D(M), for every M.
```

Equivalently, every subset A of positive groups must satisfy
sum_(r in A) G_r - sum_(s in negative neighbors of A) (-G_s) <= D.
Any such transport leaves sum G <= U, hence S^2 <= 2D. The existing
quadratic diagonal bound would then supply the required O(M) head.
This implication does not establish the arithmetic capacity inequality.

The question is not whether arbitrary opposite signs can be paired:
unrestricted fractional matching is already classified in the corpus
as a reformulation of signed imbalance. Prime adjacency is fixed before
execution. It need not reverse the sign of G; only opposite-sign edges
are admitted. No graph changes or fitted constants follow a failure.

## Broad corpus search and applicability

Single-concept, unrestricted searches used `compensated`, `commutator`,
`summation`, `matching`, `flow`, `transport`, `Hall`, and `capacity`.
The last two return 651 declarations in 78 modules and 2463 declarations
in 353 modules respectively; these are index coverage, not proofs read.
No multiword AND query or module restriction selected these results.

- `BipartiteHallGluing`: overlap compensation is exact, but expansion
  remains an input; this is not a source capacity theorem.
- `ForwardWindowHallMatching`: ordinary equal-window Hall inequalities
  reduce to intervals. The prime-divisibility graph has no such interval
  neighborhood identification, so that reduction cannot be imported.
- `Sieve.BalancedHallCapacity`: distinct-product capacity requires its
  explicit cardinality and moment inputs; it does not compare these G weights.
- `MobiusBoundaryOppositeSignTransport`: conductance cancellation,
  weighted neighbor-cut obstruction, and optimal unrestricted transport
  are already formal. Do not re-formalize their generic consumer.
- `MobiusBoundaryFixedArityLocalHallMassNoGo`: forbids specified local
  common-spectator transport for Gibbs boundary atoms. Here vertices are
  full quadratic gcd groups, and no displacement window is imposed.
  It warns against assuming local capacity, but does not decide this test.
- `DiscreteEnergyBootstrap`, `TruncatedConvolutionCommutator`, and
  `ChainShellCommutator` expose cancellation mechanisms without an
  identification satisfying their hypotheses for the literal Abel source.

## Why this computation can change the proof search

Saved data show large positive small-gcd groups coexisting with larger
negative mass. Their distribution among prime neighbors is unknown.
The full zero-residual claim is already predictably false: at M=115,
G_6>0 has no negative prime neighbor. The diagonal allowance is therefore
essential. The isolated mass does not decide the proposed inequality.

The experiment records the maximizing deficient cut and the residual
source labels of one deterministic optimum. This distinguishes a small
boundary defect from an obstruction involving interacting small gcds.
Residual allocation can depend on the optimum; cut deficit is the
invariant. Neither finite success nor a bounded-looking quotient range
will be promoted to a theorem.

## Frozen execution protocol

1. Use only saved actual-source arrays from
   `../2-fully-proven/computations/ccm-fu-positive-gcd-budget-2026-09-08`.
   Cutoffs: every M=101,...,256 and 512,1024,2048,4096,8192 (161 total).
   No larger confirmation run or new source screen.
2. Execute on the supplied RunPod, four independent workers, one BLAS
   thread, a 90-second hard screen deadline. Normalize capacities by D.
   Include all signed groups; retain negligible residuals in the budget.
3. Use deterministic augmenting flow on the literal prime graph. Check
   row and column capacities, edge support, total transfer, and the
   residual reachable cut. Independently enumerate prime adjacency by
   trial division for every M<=112. Check flow/cut equality to 1e-10 D.
4. Candidate failure threshold: U-D>1e-9 D. Record every cutoff and every
   flow edge, maximal-deficit cut, isolated positive mass, and residual
   positive support; do not screen only favorable groups.
5. Independently audit the first tested failure; if none fails, audit the
   largest U/D among M<=256. Use 80 digits and a separate 90-second
   deadline. Reconstruct source from log-factorial and literal divisor
   sums; use original time sums and every channel pair when M<=256,
   otherwise clipped sums and complete divisor inversion. Independently
   solve the selected graph at 80 digits and compare its cut and mass.
6. Archive scripts, input hashes, all output, precision checks and elapsed
   time under `2-fully-proven/computations`; verify downloaded hashes and
   remove owned remote scratch. Numerical output is never a Lean premise.

## Proof obligation after the diagnostic

The missing theorem is uniform control of every actual weighted prime
neighbor cut. Cardinality, non-isolation, a feasible flow on a finite
sample, or the abstract max-flow identity does not prove it. If the test
fails, inspect the exact obstructing arithmetic sector and its positive
survivor before abandoning this specific candidate. Keep RH and CCM-FU
open unless their full source bound is proved.
