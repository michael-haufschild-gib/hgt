# CCM-FU: one-prime compensation between exact gcd groups

- Status: frozen diagnostic completed; candidate survives all 161 tested cutoffs;
  no universal inequality proved.
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

## Result and mathematical interpretation

All 161 frozen cutoffs satisfy U<=D numerically. The largest U/D is
0.25122246490521869 at M=223. The 80-digit independent source reconstruction
and Edmonds–Karp solver give

```text
D = 59.99466979756561086838399783306600645...
U = 15.07200882771911030020962237392457469...
A = {6,10}
negative neighbors(A) = {5,30,42,70}.
```

Neither source vertex is isolated. The obstruction is their combined
demand on the available neighbor union. Isolated-vertex estimates alone
do not measure this defect. At M=4096 the maximizing cut contains 17
positive groups, starts at gcd 30, and has U/D approximately 0.21932424;
its isolated mass is only approximately 0.00567569 D. At M=8192 the cut
starts at gcd 42. These are finite observations, not bounded-quotient
or growing-cutoff theorems. No numerical universal constant is inferred.

The failed positive-part test is materially different: at M=1024 its
P/D is about 2.74156, while the one-prime residual is about 0.0140471 D.
The graph retains compensation that was discarded by that positive majorant.

### Direct proof attempt and remaining gap

At the channel-pair level, if p divides both squarefree labels d and e,
replacing d by d/p changes the exact gcd from r to r/p and reverses
the Möbius product. If p divides d but not e, replacing e by pe changes
the gcd from r to pr and reverses the product, provided the new label is
active. This explains literal one-prime transport without identifying
the sign of an entire G group with Möbius parity of its label.

These moves do not construct a capacity-respecting flow. Their positive
weights can differ, multiple source pairs can land at one target, and
copying a prime can cross the cutoff. `DivisorUnsignedGlobalEnvelope`
bounds individual channels and proves eventual factor-two comparisons;
it supplies neither the summed incoming load nor every weighted cut.
`MobiusDivisorLocalizedInteractions` retains a processed-cardinality
factor, so its bound cannot be used as a uniform complete compensation
estimate. The resulting gap is quantitative arithmetic load control,
not an absent graph definition or a missing max-flow wrapper.

Further broad searches (`submodular`, `involution`, `load`, and explicit
OR searches for lattice/cut and log-concavity variants) exposed additional
possible mechanisms, but none supplied that input. The inspected
`MobiusGibbsCardinalityBoundary` is a different exponential carrier;
`RouteEWeightedHallANOVA` retains its physical normalization factor;
`MobiusReciprocalAllocationColumnBound` requires a forward token law and
an inverse-interval incoming-class count not established here; and
`Sieve.RouteERamareIncidenceConditionalNegative` retains the noncentered
scalar mode, precisely where a signed source bound is still required.

No new universal arithmetic inequality has a closed paper proof here.
No new Lean theorem, numerical axiom, generic consumer, or formal no-go
was added. This specific candidate remains open; RH remains open.

## Reproducibility and cleanup

[Complete computation archive](../2-fully-proven/computations/ccm-fu-one-prime-gcd-compensation-2026-09-08/README.md)
contains the pre-execution protocol, scripts, all 161 inputs and flow
outputs, summary, and independent 80-digit audit. All 327 remote
source/result/input file hashes were verified after download. The screen
used four workers and took 0.05636 seconds; the audit used four workers
and took 0.09786 seconds. Both had separate 90-second deadlines.
Source/group discrepancies are below 1.9e-15 and the audited normalized
flow/cut discrepancy is below 1.1e-81. These are precision checks, not
interval certificates. Owned remote scratch and local transfer archives
were removed after confirming no owned experiment process remained.
No Lean build was started and no frontier-map edit was made.

## Arithmetic parity charge: an additional obstruction

Every nonzero G_r has squarefree r, since a nonsquarefree common divisor
forces both Möbius channel coefficients to vanish. An edge r↔pr between
nonzero groups therefore has mu(pr)=-mu(r). Cancellation of opposite
group signs by equal mass preserves both L=sum G and

```text
                         J = sum_r mu(r)*abs(G_r).
```

Indeed both absolute masses decrease equally while their Möbius parities
are opposite. The graph separates into two invariant classes indexed by
mu(r)*sign(G_r). Their net signed masses are (L+J)/2 and (L-J)/2.
Every allowed flow therefore leaves positive mass at least

```text
             U_colour = max((L+J)/2,0) + max((L-J)/2,0).
```

This lower bound is attained if every opposite-sign pair in each class
is allowed, by the existing complete-bipartite proportional construction.
The actual prime graph can have further neighbor-cut obstructions.

If a prime flow leaves positive mass U and negative mass V, then
U-V=L=S^2-D and |J|<=U+V. Consequently

```text
                       S^2 + |J| <= D + 2U.
```

The proposed U<=D thus requires S^2+|J|<=3D in addition to S^2<=2D.
This is a necessary condition for the specific graph, not an independently
proved source ceiling or a claimed necessary condition for every RH proof.
The cancellation and two-class optimality arguments are applications of
the already formal conductance and complete-bipartite laws cited above;
the uniform arithmetic estimate is still missing.

### Frozen parity-charge diagnostic

Before execution, freeze this distinct question: does the new necessary
bound S^2+|J|<=3D fail on the saved actual source, and how much of each
already-computed prime-flow deficit is forced by the two invariant classes?
This evaluates a new obstruction; it does not extend the prime-flow screen.

Use all 165 previously saved source cutoffs (101,...,256 and powers of two
512,...,131072), including their saved Möbius array. No new source screen
or max-flow solve. Four RunPod workers, one BLAS thread, 60-second deadline.
Retain every group. Compute L,J,S,D and U_colour in long double; independently
sum the signed masses in the two classes and verify both formulas. Compare
with the 161 existing prime-flow outputs where available. A numerical
failure requires S^2+|J|-3D>1e-9 D.

Independently reconstruct the first failure if it is at M<=1024; otherwise
reconstruct the largest (S^2+|J|)/D among M<=256. Use the existing independent
80-digit defining-source/all-pairs audit code, then evaluate J independently
from its saved groups using direct integer factorization. Separate 90-second
deadline, four workers for the source reconstruction. Larger unaudited
failures, if any, remain explicitly screen evidence only. Archive all input
hashes, output, source audit and elapsed time, verify downloads and clean
owned remote scratch. Do not change the graph or fit a replacement constant.

### Parity-charge result and next proof obligation

All 165 saved cutoffs have both invariant class balances strictly negative
in the screen. Consequently U_colour=0 throughout the tested range.
The maximum (S^2+|J|)/D is approximately 0.9544291021 at M=223, below
the frozen necessary ceiling 3 and also below 1. This observation does
not establish a new uniform ceiling or alter the frozen candidate.

The independent 80-digit M=223 audit gives

```text
J       =  52.83946163643150092399176833740165891...
(L+J)/2 =  -1.36700548663954088739468917625305938...
(L-J)/2 = -54.20646712307104181138645751365471829...
```

Yet its previously audited prime-graph residual is 15.0720088277... .
Thus neither an imbalance between the two invariant classes nor isolated
vertices accounts for that residual: negative capacity is available in
the same class but outside the deficient source set's prime neighbors.
Every positive prime-flow deficit in the saved 161-flow dataset exceeds
the zero class deficit. This directs the proof search to the arithmetic
location of shared negative capacity; a parity-only estimate cannot
control the observed prime-neighborhood loss. Complete pairing inside
each class removes the loss numerically, but using that construction
uniformly still requires proving the actual class balances.

Additional unrestricted searches used `cancellation`, `bilinear`,
`incidence`, `parity`, and `component`, with exploration hits retained.
The inspected `CoprimeFiberStabilization` classifies a different two-source
deletion count; `DivisorStationaryKernelMellinSymbol` retains its zeta
factors and convergence hypotheses; `Sieve.HilbertBilinear` requires an
actual bounded-symbol kernel; and `IncidenceDesignBound` requires its
design identity and centered input. None identifies the present signed
gcd cut with a form satisfying those hypotheses. The existing retained
coordinate parity-energy theorem is distinct from this gcd-group charge:
its source defects arise during prime processing, and its gain estimate
does not prove a uniform bound on the new class balances or prime cuts.

[Parity-charge archive](../2-fully-proven/computations/ccm-fu-gcd-parity-charge-2026-09-08/README.md):
four-worker screen 0.04899 seconds; independent four-worker source audit
0.04075 seconds; 80-digit charge evaluation 0.00215 seconds. All 499
remote source/result/input hashes were verified after download. The
normalized audit difference from the screen is below 8.7e-19. All owned
remote scratch and local transfer archives were removed after checking
that no owned process remained. No new source or max-flow screen, Lean
build, axiom audit, graph modification, or frontier-map edit was made.
No unconditional RH proof or new uniform arithmetic bound was obtained.
