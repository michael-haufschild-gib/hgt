# Exact single-test image via a regular separated-packet limit

Status: FORMALIZED, 2026-10-10. Exact single-test image and fixed distinct-node
surjectivity are discharged. All owned verification processes are terminal.

## Target

For every finite support s, `finiteWeilGramCoefficientVector s` is surjective.
Strengthen the existing dense-range theorem to exact realization by one actual
test. By the node-coalescing receiver, the realizing test can have distinct nodes.
No RH, arithmetic-domain, positivity-producer, or model hypotheses are allowed.

Stronger target exposed by the proof: for each s there exist a single finite N
and an injective x:Fin N→R such that
`u ↦ finiteWeilGramCoefficientVector s ⟨N,x,u,1⟩` is surjective.
Choose N and x before the requested vector; only amplitudes vary.

## Local evidence and preliminary attack

- `WeilLogShiftGramImageDensity.lean:17` proves only dense range.
- `WeilLogShiftGramImage.lean:69` gives exact NNReal scaling; line 101 gives
  separated-sum convergence using mixed kernels tending to zero.
- `WeilLogShiftGramCoordinates.lean` constructs a minimal dictionary with
  positive balance, zero balanced sum, and representations of every functional.
- `WeilLogShiftDomainBoundary.lean:23` proves strictly positive paired kernels.
  Thus a putative zero-form singleton anchor fails; do not use that shortcut.
- Installed `InverseFunctionTheorem/FDeriv.lean:85` provides
  `HasStrictFDerivAt.map_nhds_eq_of_surj`: a strict derivative with full range
  maps the source neighborhood filter onto the target neighborhood filter.
- Search `/tmp/hgt-weil-gram-exact-image-search.json`: cached lexical, 114
  matches total, first 20 inspected. Follow-up
  `/tmp/hgt-weil-exact-image-prior-search.json` returned 14 matches, all inspected.
  Exhaustive source search finds coefficient-vector usages in just six leaves:
  Image, ImageDensity, MinimalCardinality, CostInflation, FiberCost,
  NodeCoalescing. All usages checked; no exact-image result. MinimalCardinality
  only uses density to approximate simplex vertices. No external sources or
  novelty claim.

Density alone is insufficient. The proposed added mechanism is a regular zero
at the block-diagonal limit and stability under varying ALL finitely many
kernel entries. Local audit found no prior exact-image result. External novelty
is unassessed; only local Lean mathematical evidence is authorized.

## Paper argument

Write E=R^s. Use the existing unconditional dictionary, indexed by finite J,
with actual tests (N_j,x_j,u_j,b_j), coefficient vectors v_j in E, and
positive balance a_j. Thus sum_j a_j v_j=0, and the linear span of v_j is E.
The latter follows directly by applying the representation theorem to the
linear functional c↦sum_k y_k c_k, for arbitrary y in E, and evaluating on
coordinate basis vectors.

Flatten node indices to finite I=Sigma j,Fin N_j. Assign distinct real labels
ell_j. For T→+infinity, node (j,i) is T*ell_j+x_ji. Its amplitude is
t_j*sqrt(a_j*b_j)*u_ji, with variable t in R^J; outer test scale is 1.
No variable square roots or nonnegative-variable constraints occur.

Let P=R^(I×I×s) be the finite space of kernel entries. Define polynomial
Q(K,t)_k = -sum_(j,i),(h,l)
  t_j*t_h*sqrt(a_j*b_j)*u_ji*sqrt(a_h*b_h)*u_hl*K((j,i),(h,l),k).
For actual separated nodes, K=K_T contains the pairedLogKernel entries, so
Q(K_T,t) is exactly the coefficient vector of this one actual test.

Let K_0 keep entries within each packet and set all cross-packet entries to 0.
Then K_T→K_0, since different real labels give affine differences escaping
every compact set and the corpus proves paired kernels vanish cocompactly.
At the constant amplitude vector 1, Q(K_0,1)=sum_j a_j*v_j=0.
The derivative in t at this point sends h to sum_j 2*a_j*h_j*v_j. It is
surjective: represent any y as sum_j c_j*v_j and choose h_j=c_j/(2*a_j).

Consider H:P×R^J→P×E, H(K,t)=(K,Q(K,t)). It is a polynomial, hence has a
strict derivative at (K_0,1). This derivative is surjective: to obtain (dK,y),
fix parameter derivative dK and solve the amplitude derivative for
y - (derivative_K Q)(dK), using the preceding surjectivity. All spaces are
finite-dimensional real normed spaces, hence complete.

The cited local-surjection theorem says range(H) contains a neighborhood of
(K_0,0). A product neighborhood U×V is contained in that range, with
K_0 in U and 0 in V. Choose a finite T with K_T in U. For every y in V,
membership (K_T,y) in range(H) gives parameters (K,t) with K=K_T and
Q(K_T,t)=y. Thus one FIXED finite node configuration realizes a whole
neighborhood of zero by varying only its real amplitudes.

Every vector y in E has a positive scalar multiple epsilon*y in V. Realize
epsilon*y as above, then use the exact NNReal outer-scale law with 1/epsilon.
This realizes y by one actual test. E=0 is immediate (or covered by the same
argument). Coalescing preserves its full coefficient vector and ensures
distinct nodes.

The stronger structural survivor is a fixed finite node configuration whose
amplitude quadratic map has zero in the interior of its range. Positive
homogeneity then makes that same amplitude quadratic map surjective; outer
rescaling can alternatively be absorbed into all amplitudes by sqrt.
Apply the proved fiber regrouping to this fixed configuration: its node-image
type and node positions are fixed independently of amplitudes. Aggregating
amplitudes is a linear map, so the resulting distinct-node amplitude map remains
surjective. This proves the stronger fixed-node target on paper as well.

## Proof obligations / plan

Implementation refinement: use the smaller parameter space J→J→E, whose
entry is the complete mixed-packet coefficient vector (including its fixed
amplitudes and negative sign). The quadratic map is sum_ij t_i*t_j*K_ij;
its diagonal limit is K_ii=a_i*v_i. This is the linear aggregation of the
larger entrywise parameter space in the paper argument and preserves every
step. The vertical derivative can be identified from the diagonal identity,
without expanding the entire parameter derivative.

Four leaves written: `WeilLogShiftQuadraticSurjection.lean`,
`WeilLogShiftGramBalancedVectors.lean`, `WeilLogShiftGramPacketKernel.lean`,
and `WeilLogShiftGramExactImage.lean`. Generic local-surjection leaf now passes
cleanly after replacing deprecated `ContinuousLinearMap.sum_apply` with root
`sum_apply`. Actual balanced-vector producer passed cleanly on its first native
build. Packet and exact-image leaves now also pass cleanly. The unconditional
fixed-node receiver has passed native Lean verification; its final public axiom
audit has passed.
Nineteen core derivative/topology API terms verified in scratch. Installed API
uses `HasFDerivAt.unique` after `.hasFDerivAt`; no `HasStrictFDerivAt.unique`.
Thirty-five derivative, topology, reindexing, and cast API terms now passed
scratch checks. Prepared final audit covers all 17 authored public declarations.
Generic proof needed explicit reductions for locally abbreviated function
spaces, not additional assumptions. All derivative and neighborhood arguments
have passed. Packet API verification and the final public audit both passed.

Packet normalization exposed a Lean dependent-index issue: destructing the
expression `w j` after creating node-index aliases leaves finite-type instance
arguments tied to the old expression. A standalone coefficient-expansion lemma
destructs a genuine test variable before these aliases exist. That lemma now
supplies the diagonal identity. Mixed-kernel convergence and the full packet
coefficient calculation required no mathematical changes. Current native packet
rebuild passed (exit 0). Its only diagnostic was an unused finite-type parameter
on the diagonal identity; omitting it also exposed the same redundant parameter
on kernel convergence. Both are now omitted. Packet leaf passed cleanly (exit 0,
empty log). Exact-image receiver passed on its first native build, also clean.
All four source/olean freshness checks and exactly-once umbrella imports passed.
Index refresh passed. Final scratch audit covers all 17 public declarations
and 35 API terms and passed (exit 0). Source-to-audit coverage is complete; all
17 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`,
with no diagnostics. Exact indexed search finds the stronger receiver at
`WeilLogShiftGramExactImage.lean:52`; basic surjectivity is at line 82.
No partial compilation is counted as a passed leaf.

Global lint ran: no diagnostics for these leaves, nine unrelated umbrella gaps
in the shared tree. Log `/tmp/hgt-weil-exact-image-lint.log`. Do not call global
lint clean or change unrelated modules to clear this research increment's gate.
The nine gaps, all under `GaloisForLFunctions`, are:
`RHTower.GaussianPrimeSumCeilingReceiver`,
`RHTower.PhotonicLosslessTemporalStackRealZeros`,
`RHTower.XiTaylorCoefficientsLogConcave`,
`HTGeometry.PaperMoebiusEulerFactor`, `HTGeometry.PaperMoebiusPrimeClock`,
`HTGeometry.PaperMoebiusPrimeSlice`, `HTGeometry.PaperMoebiusPrimeTransport`,
`HTGeometry.PaperPrimeConstantProjection`,
`HTGeometry.QKrawtchoukCompanionTriangular`.

- [x] Complete exact local prior-art search.
- [x] Verify the 35 new derivative/topology/reindexing/cast API terms in scratch.
- [x] Formalize finite polynomial parameter family and its strict derivative.
- [x] Prove derivative surjectivity from actual coordinate-record fields.
- [x] Prove all finite mixed kernel entries converge to block diagonal.
- [x] Use parameter-preserving local surjection to get an actual neighborhood.
- [x] Discharge all helpers in unconditional exact-image receiver, with
  distinct-node corollary; audit native leaves, axioms, wiring, index, lint.

No external literature audit is authorized. No claim of total-cost efficiency
follows: making packets distant can substantially increase their tail cost.

## New corpus insight and remaining frontier

The earlier dense image is now the entire finite coefficient space. A single
fixed finite node configuration suffices for every target, with distinct nodes
and outer normalization one; only real amplitudes vary. The actual positive
dictionary produces a regular zero in the block-diagonal limit, and the local
surjection theorem transfers full quadratic surjectivity to actual finite
packet separation. No new analytic or arithmetic producer premise remains.

This closes finite-dimensional realizability in this branch. It does not control
the cost of the realizers as support grows. The next research target is exact
realization cost, compared with the existing positive-mixture native gauge and
the unconditional cutoff cost lower bounds. No external priority claim is made.

Follow-up (2026-10-10): [uniform realization cost](finite-weil-uniform-realization-cost.md)
is now formalized. For each finite support, fixed distinct nodes and C>0 realize
every target y with native unit cost <= C||y||. Growth of C with the support and
optimal cost remain open. The next paper-proved step is
[coordinate isolation cost](finite-weil-coordinate-isolation-cost.md), now formalized.
