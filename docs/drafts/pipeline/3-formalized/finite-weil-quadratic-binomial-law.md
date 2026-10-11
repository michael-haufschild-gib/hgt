# Quadratic-start midpoint profiles converge to the binomial law

Status: FORMALIZED. Exact midpoint identification, generic normalization inequality, finite l1 bound, and unconditional arbitrary-offset limit pass native Lean and full axiom audit.
Date: 2026-10-10. Local Lean corpus and installed dependencies only.
Internal verdict: BRIDGE. No external novelty claim.

Exact target: for every t : Nat -> Nat, set k_r=2(r+1)^2+t(r). The sum over i : Fin(r+2) of
abs(finiteWeilCanonicalMixture r k_r (1/2) i - choose(r+1,i)/2^(r+1))
tends to zero. Stronger finite target at every k+2 >= 2(r+1)^2:

    sum_i abs(midpoint_i - choose(n,i)/2^n) <= 2*sqrt((n+1)/2)/n,

where n=r+1. This is an l1 distance; total variation is half of this quantity. It concerns the actual existing midpoint of the canonical probability moment fiber, not a newly postulated measure.

Prior-corpus audit: lexical `binomial probability` restricted to WeilLogShift returned zero hits. Broadened `probability` returned three hits, all inspected: canonical profile sensitivity, the exact moment-fiber mass pairing, and the unique-mixture classification. Read the existing midpoint definition and positive/negative profile definitions. They give midpoint_i=abs(c_i)/sum_j abs(c_j) by cancellation. A separate `sqrt cost` search returned four hits, all inspected; two were existing cost receivers and two were reverse-Minkowski cost geometry. Merely inserting the asymptotic mass constant into an existential unspecified cost constant would add little, so that is not the next research target.

Proof:
1. Use q_i=finiteWeilArithmeticAbsProfile r i, G=sum_i q_i, f_i=finiteWeilCanonicalMassProfile r k i, F=sum_i f_i. All entries and both sums are positive. The exact common-scalar raw-weight identity proves midpoint_i=f_i/F. The arithmetic binomial formula gives q_i/G=choose(n,i)/2^n.
2. Let D=sum_i abs(f_i-q_i). The already established pointwise distortion and arithmetic weighted first-moment estimate give D <= G*e, where e=sqrt((n+1)/2)/n. This is the summed absolute error, before the triangle inequality used in the existing sum-error theorem.
3. For arbitrary positive finite profiles, write
   f_i/F-q_i/G=(f_i-q_i)/G + f_i*(G-F)/(F*G).
   Triangle inequality, sum_i f_i=F, and F,G>0 imply
   sum_i abs(f_i/F-q_i/G) <= D/G + abs(G-F)/G <= 2D/G.
   Hence the finite target follows. Crucially, the normalization factor F cancels; no eventual lower bound for F/G and no maximal-coefficient estimate is needed.
4. e^2=(1+1/n)/(2n) tends to zero by the natural reciprocal limit. Thus e tends to zero. The quadratic width is automatic for every offset sequence t, giving the unconditional target by squeezing.

Failure audit: the claim is only for the midpoint. The two endpoint profiles remain disjoint and have l1 distance exactly 2, as the corpus already proves. No endpoint convergence in total variation to the same binomial law is claimed. The midpoint law adds distributional information absent from the scalar mass limit and transports every uniformly bounded observable by the same l1 error bound.

Completed: exact midpoint/raw-profile identity, generic positive-profile normalization inequality, finite binomial-distance estimate, and unconditional offset-sequence limit. All analytic input is discharged. Full-fiber follow-up now formalized: finite-weil-quadratic-parity-fiber-law.md.

Implementation progress: four leaves drafted (ProfileNormalization, MidpointProfile, MidpointBinomialBound, MidpointBinomialLimit); native checks pending. The general normalization proof exposes a stronger helper: q need not be entrywise nonnegative, provided its total sum is positive. Only f must be entrywise nonnegative with positive total. The same algebra proves this extension; the final midpoint theorem remains unconditional for arbitrary natural offsets. Focused `normalization profile` corpus search returned two C0-profile receiver statements; both inspected and unrelated. Installed normed-group search found a quotient-norm triangle inequality, also inspected and not a finite probability-normalization producer. Current native sequence runs API validation first, then the four leaves serially, stopping at the first failure.

Native progress: API validation passed with all 19 initial explicit terms; general normalization inequality and all four exact midpoint/binomial-profile identities now have passed builds in the sequential session75860. Their logs are empty. Distance and limit leaves remain under validation. Added a twentieth API term for the precise additive-order step. The full-fiber continuation has a separate complete paper proof in finite-weil-quadratic-parity-fiber-law.md; it retains the parity mixing coordinate and does not assert endpoint convergence to the unconditioned law.

Final audit, 2026-10-10:
- Four leaves: WeilLogShiftProfileNormalization, WeilLogShiftMidpointProfile, WeilLogShiftMidpointBinomialBound, WeilLogShiftMidpointBinomialLimit. Sequential native builds session75860 exit0; all four final logs empty. Final native scratch API/axiom audit session96481 exit0: nine public declarations, twenty explicit API terms, standard axioms only (propext, Classical.choice, Quot.sound).
- Finite root: `finiteWeilCanonicalMixture_midpoint_binomial_bound` in WeilLogShiftMidpointBinomialBound.lean:27. Unconditional asymptotic root: `tendsto_finiteWeilCanonicalMixture_midpoint_binomial` in WeilLogShiftMidpointBinomialLimit.lean:22, for arbitrary t : Nat -> Nat, with no analytic premises.
- `/tmp/hgt-midpoint-metadata.py`: declarations=9, api_terms=20, issues=[]. Own and direct dependency oleans fresh. Each of four umbrella imports occurs exactly once. Exhaustive incoming scope is the intended leaf chain plus umbrella. Refreshed local lexical index returns the exact root, one eligible hit and no markers. Whitespace and forbidden-declaration checks clear.
- Authoritative lint session40242 exit1: eleven unrelated missing umbrella imports: RHTower.JointAncestryClusterPhase, JointAncestryLogWeightBernoulli, JointAncestryLogWeightExpansion, JointAncestryLogWeightPrimeSum, JointAncestryQuasiRHAmplification, JointAncestryQuasiRHCore, JointAncestryZeroTailBound, LiUpperQuadraticCriterion, XiCosineShiftCriticalScaleDefectCount, XiGaussianHeatTraceCompleteMonotonicity; HTGeometry.QKrawtchoukCompanionTriangular. None is part of this increment.
- Assessment: the scalar mass frontier now has a distributional bridge for the actual existing midpoint probability, with an explicit finite rate and arbitrary offset sequence. Generic normalization algebra is support machinery, not the research claim. No external novelty claim, external paper, web search, numerical experiment, full build, or raised heartbeat.
- Follow-up complete: the whole-fiber parity-conditioned binomial law is formalized in finite-weil-quadratic-parity-fiber-law.md. Exact adjacent optimal transport is next, in ../2-fully-proven/finite-weil-adjacent-nodal-transport.md. The signed raw-weight identity and exact parity reading expose how the mixture coordinate persists. Goal remains active; no owned Lean process remains live.
