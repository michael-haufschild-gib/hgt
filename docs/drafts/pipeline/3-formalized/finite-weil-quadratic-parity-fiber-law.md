# The whole quadratic-start fiber has a parity-conditioned binomial model

Status: FORMALIZED. Signed distortion, exact parity reading, probability-model normalization and metric, finite approximation, and unrestricted offset/mixture-sequence convergence pass native Lean and complete axiom audit.
Date: 2026-10-10. Internal verdict: BRIDGE. Local Lean corpus only; no external novelty assertion.

Target: n=r+1, b_i=finiteWeilBinomialDual r i=(-1)^(n-i)*choose(n,i), k_r=2n^2+t(r). For every t : Nat -> Nat and every a : Nat -> Set.Icc (0:Real) 1, the l1 distance between finiteWeilCanonicalMixture r k_r (a r) and

    i |-> (choose(n,i)+(2*a(r)-1)*b_i)/2^n

tends to zero. Finite stronger statement: the distance is at most 4*sqrt((n+1)/2)/n for all quadratic-width starts and all a in [0,1]. No regularity or growth premise on either sequence.

Prior-corpus search: lexical `binomial profile` in WeilLogShift returned exactly the arithmetic absolute-profile formula and the newly drafted midpoint-profile l1 error; both inspected. MomentRatios already gives adjacent sign alternation and positivity at the last node. CanonicalQuadrature transfers these to the actual canonical profile and proves endpoint disjointness. LogNodalDistortion currently states only the absolute raw-weight identity. Its product proof exposes the following signed strengthening.

Dependency-closed proof:
1. For any positive injective finite node family x, set a_i=product_{j!=i} L(x_i,x_j), with the already-proved positive logarithmic mean. The exact signed nodal-weight identity is
   W(log x)_i=a_i*W(x)_i.
   Indeed, each factor satisfies (log x_i-log x_j)^(-1)=L(x_i,x_j)*(x_i-x_j)^(-1). Both differences are nonzero by injectivity and the proved injectivity of log on positives. Multiply over erased indices using the actual Lagrange nodal-weight definition. This strengthens the existing absolute identity without a new analytic assumption.
2. Translation of arithmetic nodes and subtraction of the common logarithmic center preserve every gap. Therefore the same signed identity holds for the canonical and arithmetic raw weights. All distortion factors, factorial scales, and normalizing norms are positive. The exact arithmetic signed-binomial formula then gives
   c_i=sigma_i*abs(c_i), sigma_i=(-1)^(n-i), for c=finiteWeilCanonicalCluster r k, with abs(sigma_i)=1.
3. Let p_i be the existing canonical midpoint probability and beta_i=choose(n,i)/2^n. Existing positive/negative profile definitions are (abs(c_i)+/-c_i)/S. Hence
   canonicalMixture(a)_i=(1+(2a-1)*sigma_i)*p_i.
   The displayed binomial model is exactly (1+(2a-1)*sigma_i)*beta_i. For a in [0,1], the common multiplier lies in [0,2]. Thus the whole-fiber l1 error is at most twice the midpoint l1 error, which is bounded by 2*sqrt((n+1)/2)/n in the preceding midpoint proof.
4. The finite error bound tends to zero. Quadratic width is automatic for arbitrary natural offsets. This proves the fully quantified target.

Exact survivor: the parity observable satisfies sum_i sigma_i*canonicalMixture(a)_i=2a-1 for every finite order, since the two endpoint probabilities occupy opposite signs and each has total mass one. The binomial model retains this same observable exactly. The mixing coordinate persists in parity even as the midpoint profile approaches a common binomial envelope.

Failure audit: claiming every fiber element approaches the unconditioned binomial law in total variation would be false at the endpoints. At a=1 and a=0, the correct models are the two disjoint parity-conditioned binomial laws. No Gaussian limit or optimal Gram-cost constant is claimed here.

Completed: signed raw distortion identity; canonical sign/binomial identity; exact parity reading; model positivity, mass one, and exact l1 metric; finite full-fiber approximation; unconditional varying-mixture/offset limit. Native and axiom audits are complete.

Model audit before Lean implementation: beta_i=choose(n,i)/2^n has total mass one, and sum sigma_i*beta_i=0 by the existing zeroth alternating-binomial moment. Thus the explicit binomial mixture has mass one for every real a and nonnegative entries for a in [0,1]. Its parity reading is exactly 2a-1 by sigma_i^2=1. It also retains the exact fiber metric: the difference at parameters a,b is 2(a-b)*sigma_i*beta_i, so its l1 norm is 2*abs(a-b). In particular its endpoints have distance two. These are elementary consequences of the already-verified arithmetic binomial producer, not an external probabilistic assumption.

Implementation started: signed raw-weight and canonical parity leaves plus the exact parity-reading leaf are drafted. Actual toolchain confirms Lagrange.nodalWeight is a product of inverse gaps, so the signed proof retains that product form rather than collapsing it to an inverse product. Native validation is serialized after API checks.

Six leaves are drafted: SignedDistortion, CanonicalParity, ParityMixture, BinomialMixture, ParityBinomialBound, ParityBinomialLimit. SignedDistortion passed its first native check in the sequential session80169; CanonicalParity is now checking. The exact parity-reading proof uses one controlled pointwise rewrite, avoiding a recursive simplification of the midpoint by its own parity-factor identity. Later leaves are not yet claimed verified.

Final audit, 2026-10-10:
- Six leaves, 23 public declarations, 15 explicit API terms. First native sequence80169 exit0 (API and SignedDistortion/CanonicalParity/ParityMixture); second sequence82045 exit0 (BinomialMixture/ParityBinomialBound/ParityBinomialLimit). All six final native logs empty. Final scratch audit61617 exit0, standard axioms only: propext, Classical.choice, Quot.sound.
- Unconditional root: `tendsto_finiteWeilCanonicalMixture_binomial` in WeilLogShiftParityBinomialLimit.lean:19. Inputs t : Nat -> Nat and a : Nat -> Set.Icc (0:Real) 1 impose no analytic growth or regularity premise. Explicit finite error is at most 4*sqrt((n+1)/2)/n.
- Exact survivors include signed logarithmic raw weights, canonical coefficient parity, parity reading 2a-1 at every finite r,k, and the binomial model's l1 distance 2*abs(a-b). The model has total mass one for all real a and is nonnegative for a in [0,1].
- `/tmp/hgt-parity-metadata.py`: declarations=23, api_terms=15, issues=[]. Own and direct dependency oleans fresh; six umbrella imports exactly once; exhaustive incoming scope only intended chain/umbrella. Root appears in refreshed local lexical search with one eligible hit and no markers. Forbidden declarations and source whitespace clear.
- Authoritative lint85547 exit1: eleven unrelated missing umbrella imports: RHTower.JointAncestryClusterPhase, JointAncestryLogWeightBernoulli, JointAncestryLogWeightExpansion, JointAncestryLogWeightPrimeSum, JointAncestryQuasiRHAmplification, JointAncestryQuasiRHCore, JointAncestryQuasiRHParameters, JointAncestryZeroTailBound, LiSignIntersective, XiSliceMixedClassDetection; HTGeometry.QKrawtchoukCompanionTriangular. None belongs to this increment.
- Internal assessment: the entire existing moment fiber now has a probability model with the correct parity coordinate and metric, uniformly in arbitrary varying mixture parameters. This strengthens the midpoint/scalar frontier without identifying disjoint endpoints. No external novelty assertion, web search, external paper, numerical experiment, full build, or raised heartbeat.
- Next stronger target: exact adjacent optimal transport for all ordered nodal fibers, at every start and order, in ../2-fully-proven/finite-weil-adjacent-nodal-transport.md. A deletion recurrence proves alternating prefix signs; this produces adjacent edge masses summing to one and a matching dual certificate. Lean implementation pending. Goal remains active; no owned Lean process is live.
