# BAG C28.56x — complete damped arithmetic cubic trace audited

Goal ACTIVE/unbudgeted: unconditional Lean RH proof/falsification, BAG only. No subagents, numerical computations/experiments, added axioms/sorry/admit, heartbeat raises, commits/push, full/umbrella builds. Corpus search before conjectures/code. One owned foreground Lean at a time. Final leaf audit lake --old env lean; #print axioms via /tmp. Do not mark blocked for math difficulty or complete absent RH. Every turn state route, hard gaps and prior contribution.

Previous references: mem:rh/bag-full-signed-trace-2026-10-04-01a0 (C28.56w, no hard closure) and mem:rh/bag-joint-cubic-packet-checkpoint-2026-10-03-01a0 (C28.56v, audited actual prime packets prove quadratic mixing cannot generically imply cubic cancellation).

NEW production formal/GaloisForLFunctions/RHTower/ChiRamanujanCompleteCubicTrace.lean, 433 lines, namespace RHTower.BAGTrace. All27 public theorems audited. At p, z=p^(-sigma), coefficient c(i)=1 for i>=0, c(-1)=-z/(1-z)=-1/(p^sigma-1), c(i)=0 for i<-1. localTriple=c(i)c(j)c(i+j)z^(i+j).
Full local HasSum=(1-z)^-2; full absolute HasSum=(1+4z)/(1-z)^2. Proof retains positive quadrant, both positive corners, both negative strips. Finite-product HasSum over ALL integer valuation assignments. For sigma>1 and directed finite prime sets P:
- complete_signed_trace_zeta: trace sigma P -> riemannZeta(sigma).re^2.
- complete_absolute_trace_limit: absoluteTrace sigma P -> zeta(sigma).re^2 * prod_p(1+4p^-sigma).
- complete_offAxes_trace_zeta: literal masked sum excluding either zero valuation vector -> 1-zeta(sigma).re^2.
offAxesTrace_eq proves exact mask = trace-axis-axis+origin, not just a definition of subtraction. Each axis is evaluated. zetaSeries_eq connects actual mathlib riemannZeta to real Dirichlet series. Prime coefficient identity proven even for all real sigma.

Important scope: theorem is complete directed prime-coordinate resonance trace. Reindexing as ONE unordered positive-rational double tsum is not yet formalized. Fixed-shift rational-dilation orthogonality remains paper. Frequency axes a=1,b=1 are NOT yet identified with literal physical prime diagonals p=r,q=r. Their weighted 1/epsilon pole must match the actual logN contraction scale. Neither full prime cubic nor RH is proved.

AUDITS all TERMINAL:
- final clean production29462 exit0/no diagnostics; log /tmp/bag-rational-trace-final-01a0.log.
- axiom75944 exit0, ALL27 use only propext, Classical.choice, Quot.sound; log /tmp/bag-rational-trace-axioms-01a0.log.
- umbrella import wired immediately after ChiPrimePacketConnectedCubicSeparation; no umbrella build.
- index4755 exit0; log /tmp/bag-rational-trace-index-01a0.log; overview/API/gaps plus search index refreshed.
- lint37951 exit1:18 unrelated unreachable modules only, no new leaf/proof-debt/generated-file error; /tmp/bag-rational-trace-lint-01a0.log.
- whitespace check passed. Three owned /tmp Lean probes removed; only intended production .olean exists, no owned part files. No live tool processes.
Finite Pi proof needed explicit f/g and reindexing-function arguments to avoid expanding Finset.prod >200k heartbeats. No heartbeat changes. Removed redundant coarse local mass bound after exact absolute product gave convergence.

Docs:
P3 docs/drafts/pipeline/3-formalized/bag-complete-damped-cubic-trace.md.
P1 docs/drafts/pipeline/1-in-progress/bag-rational-product-trace-euler-cancellation.md contains next HARD paper argument.
Frontier map BAG row C28.56x added.
Working log bagchi-quantitative-sparse-recurrence-working-log.md appended full result/evaluation/audits.

NEXT HARD CONJECTURE (paper, NOT Lean):
For sigma=1+epsilon, m_sigma(a)=mu(den a)/prod_(p|den a)(p^sigma-1).
Complete local two-Mellin factor with x=p^-s,y=p^-t:
E=1/((1-x)(1-y)) + z^2/(1-z)^2*(1/x+1/y)
  - z/(1-z)*(y/(x*(1-y))+x/(y*(1-x))).
Algebraic factorization E=(1-z)^-2*[1+(x-z)(y-z)*(x+y-xy)/(xy(1-x)(1-y))].
For s=sigma+iu,t=sigma+iv global Z_sigma =
|zeta(sigma+iu)|^2 |zeta(sigma+iv)|^2 / |zeta(sigma+i(u-v))|^2 * H_sigma(u,v).
H=product of local E times four inverse zeta factors divided by two cross factors.
After first-order cancellation H_p-1 and fixed derivatives O_k(p^-2sigma log^k p), uniform real u,v and sigma>=1. H(u,0)=H(0,v)=1 EXACT.
Single axis D_sigma(u)=|zeta(sigma+iu)|^2 K_sigma(u),
K=prod_p[1-z^2*(1-exp(iu logp))^2/(1-z)^2]. K(0)=1,K'(0)=0.

Set J_sigma(u)=(epsilon^2+u^2)|zeta(sigma+iu)|^2, a=J_sigma(0);
A(u,v)=J(u)J(v)H(u,v)/J(u-v); B=(A-a)/(uv);
M(u)=(J(u)K(u)-a)/u^2, smooth extended axes.
At epsilon=0 J_1(0)=1 means pole-removed LIMIT, NOT mathlib's junk zeta value at1.
Z-D(u)-D(v)+1 exact rational-kernel decomposition predicts compact-frequency distribution limit:
-pi^2 delta_(0,0) -2 PV(1/u) tensor PV(1/v)
+v B_1 PV(1/u)+u B_1 PV(1/v)-2B_1-M_1(u)-M_1(v)+1.
Do not drop intersection point mass! a->1; epsilon^2uv/denproducts ->0, epsilon^2/denproducts ->pi^2delta; u/den ->PV; u^2/den ->1.
Source pole/nonvanishing inputs checked: riemannZeta_residue_one; HTGeometry.RiemannZetaMeromorphic analyticAt_riemannZeta/meromorphicOn; mathlib LSeries/Nonvanishing riemannZeta_ne_zero_of_one_le_re. Need prove full Mellin/Euler identity, uniform remainder derivative bounds, actual distributional action and its growth for moving V/W; then finite-height near-resonance and coupled-limit transfer.

Do NOT conflate absolute convergence of GROUPED Ramanujan expansion with absolute convergence after every frequency is separated (fails small epsilon). Keep finite grouped cutoffs. No physical Poisson/prime major arc asymptotic has been proved. Corpus sharp-edge transfer exists but scale-dependent smooth derivatives remain.

All current searches TERMINAL; evidence /tmp/bag-...-01a0.json: product-trace-next nonpartial, abel-rational-trace-source nonpartial (65286 inventory), rational-allpass deep nonpartial; rational-connected-trace deep PARTIAL (65305 inventoried, mostly compiler pending/source-only); zeta-boundary lexical analytic/meromorphic hits only then rg verified nonvanishing. All declaration/candidate/source/proof/ingredient sections inspected. Do not repeat broad searches returning unrelated operator/algebra identities.

Assessment: this turn closes a complete infinite signed arithmetic aggregate with absolute convergence and literal axis removal. Full physical signed cubic/zero trace, growing moments, moving cofactors, positive common-height self-return and RH all remain OPEN. Continue actual weighted trace and physical transfer; no easier quadratic wrappers, no speculative RH claim.
