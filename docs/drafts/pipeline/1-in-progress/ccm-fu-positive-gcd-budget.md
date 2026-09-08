# CCM-FU: positive gcd budget

- Type: source-bound candidate and frozen discriminating experiment.
- Status: unproved; experiment not yet run.
- Full chain: actual divisor source → O(M) complete signed Abel head → CCM-FU → RH.
- Frontier map read only.

## Candidate

Let C_d(M) be the literal signed divisor Abel channel, D(M)=sum_d C_d(M)^2,
and G_r(M) its exact ordered off-diagonal component with gcd r. The corpus
proves S(M)^2=D(M)+sum_r G_r(M), and D(M) has an unconditional quadratic
ceiling. Individual G_r and even fixed binary packets can be positive.

The frozen sufficient candidate is

`sum_(1<=r<=M) max(G_r(M),0) <= D(M)` for every M.

It allows positive groups and preserves every cancellation within a group.
If true, S(M)^2<=2D(M), giving the desired O(M) bound. This is a candidate
arithmetic estimate, not an assumed input and not a new universal law.
Existing bounded-order experiments do not decide it: the signed sum of gcd
groups can be small even when their positive part exceeds the diagonal.
No fitted constant or regrouping will replace the claim after the screen.

## Broader corpus search and applicability

Unrestricted single-concept searches used `cancellation`, `renewal`,
`discrepancy`, `compensation`, `balancing`, and `dissipation`, with additional
pages for cancellation and discrepancy. No module filter or multi-term AND
was used in these searches. The respective searches cover 899, 44, 167, 96,
42, and 62 matching modules; these are search coverage counts, not claims
that every proof was read.

- `HTGeometry.TernaryVoronoiAntisymmetry`: odd resonant kernels cancel under
  symmetric weights. The actual quadratic pairing has no established odd
  kernel representation; its symmetric part cannot be discarded.
- `HTGeometry.RenewalOccupationPotential`: monotone discounted occupation
  contracts once a positive stochastic kernel and strict discount are
  supplied. Those data and a uniformly affordable source comparison are
  not established for the literal divisor channels.
- `ChronologicalArithmeticAveraging`: exact Abel averaging retains the
  terminal residual and prices earlier errors. It does not supply a bound
  on the raw errors being averaged.
- `HTGeometry.BipartiteHallGluing`: overlap compensation glues rank bounds
  after the forward and reverse expansions are established. It supplies
  neither weighted cancellation nor the necessary arithmetic matching.
- `GibbsSignedCovarianceAccumulation`: signed forcing and energy dissipation
  must retain their exact normalization. A rewritten endpoint inequality
  is not an independent producer.
- `CoprimeFiberStabilization`: complete product-fibre cancellation can have
  an exact divisor-count classification without a new arithmetic bound.

These checks motivate testing a one-sided budget on the complete actual
quadratic groups rather than assuming local signs or importing a generic
contraction. The preceding coprime-column transport supplies exact source
provenance for G_1; it supplies no bound for this candidate.

## Frozen computation protocol

Run only on the supplied RunPod, four worker processes, BLAS threads one,
90-second whole-screen deadline. No Lean computation or numerical premise.
New cutoffs: every M=101,...,256 and powers of two 512,...,131072. Retain
every channel and every gcd group at each cutoff, not selected pairs.

Construct channels from the defining log-factorial/divisor defect and exact
clipped square-root weights. Use long-double arithmetic. For each r form

`B_r=(sum_(r|d) C_d)^2-sum_(r|d) C_d^2=sum_(r|g) G_g`,

then invert by descending divisor subtraction. At every cutoff check the
complete reconstruction against S^2-D. Independently check all pairs at
each M=101,...,112 and the original time-sum channel formula at M=101,...,104.

Record positive mass, negative mass, absolute mass, ratios to D and M^2,
all positive groups, reconstruction errors and source hashes. Failure
threshold is `1e-10*max(1,D)` above the proposed diagonal budget.

Independently reconstruct at 80 digits the first failing cutoff, if one
exists; otherwise audit the largest positive-mass/diagonal ratio among
tested cutoffs at most 1024. The audit has its own 90-second deadline and
uses four workers. It is numerical evidence, not an interval certificate.
Download scripts and complete outputs. Do not enlarge the range to confirm
a pass. A pass leaves the universal source estimate open; a failure rejects
this particular constant-one producer without refuting RH.
