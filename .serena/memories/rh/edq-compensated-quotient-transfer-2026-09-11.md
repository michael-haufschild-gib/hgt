# EDQ compensated quotient transfer — no stronger bound

Latest user instruction: stop #print axioms. Do not run it again; this overrides earlier audit instructions. No computations. Frontier map remains read-only. Goal remains active and unachieved.

Current proof chain: Euler deletion -> cofinal subpower control of complete signed source/current -> off-line exclusion -> RH.

Updated only docs/drafts/pipeline/1-in-progress/edq-compensated-log-renewal.md, section at line 261. Added 120 lines of paper transfer tests, no Lean theorem/build/audit/index/lint. git diff --check passed. Do not describe this as improvement to the hard arithmetic bound.

Exact compensation is ALREADY formalized in RHTower.DeletionCounterterm.hasSum_mertensIncrement_mass and error_eq_compensated_quotient_mass (EulerDeletionCountertermRigidity). Re-formalizing the continuous version would duplicate existing content.

For positive u, phi_n(u)=fract(u/n)/u; R_N=sum_(n<=N) mu(n)phi_n; G_N=R_N-H_N phi_1; e(u)=1_(u>=1)/u. Define h_N(v)=1_(v>N)(M(floor v)-M(N))/v and P h(u)=sum_j h(u/j)/j - integral h(v)dv/v.
Existing arbitrary-log Mertens rates imply weighted L1 norm h_N=O_q(log(N)^(1-q)), q>1. Exact weighted mean=-H_N. Finite divisor regrouping gives P h_N=R_N+e=G_N+H_N phi_1+e. Correction uniformly bounded in physical L2(du); no bound on G_N gained.

Generic L1(dv/v)->L2(du) bound false even zero mean: h=1_[1,2)/v -2*1_[2,4)/v has mean0, weighted absolute integral1, and nonzero L2 output. For h_a(v)=h(v/a), weighted norm unchanged, P h_a(u)=P h(u/a), output norm squared multiplied by a. Interval counting proves P h=O(1/u); no numerical calculation. This is a paper transfer failure, not a closed no-go, and does not disprove desired estimate for arithmetic h_N.

Actual compactification: L>N integers, k_N,L(v)=1_(v<L)h_N(v); Delta=M(L)-M(N). With h_N,L(v)=sum_(N<n<=L)mu(n)1_(v>=n)/v, get k=h_N,L-Delta*1_(v>=L)/v, P h_N,L=R_N-R_L, P(1_(v>=L)/v)=-phi_L. Therefore P k=R_N-R_L+Delta phi_L, and P k-P h_N=-(R_L+e)+Delta phi_L. Exact boundary norm squared=norm(phi_1)^2 Delta^2/L. Log estimates do not make it small. DO NOT call this a lower bound on complete defect: interaction with R_L+e is retained. Weighted input convergence does not justify strong output convergence.

Inspected BurnolCoPoissonSeedL2Recovery through theorem seed_memLp_two: RHTower.BurnolCoPoissonSource.seed_memLp_two requires compact source support and an existing L2 output vector. Finite inverse cutoff grows with support ratio. Inspected BurnolCoPoissonSourceDilation through215: intertwining exact, aperture changes and membership hypotheses retained. No uniform arithmetic norm control. Also inspected Sieve/AlmostOrthogonality: requires actual Schur row bound. Ordinary normalized dilations are log shifts whose pairwise operator norms do not decay. Uncompensated operator norm lower bounds do NOT exclude compensation. First interval N<u<2N in P h_N has only one active quotient; existing EulerDeletionFirstTailMertens obstacle remains.

Four broad deep/method searches (shared coefficients/renewal, Cotlar/dilation/autocorrelation, scale orthogonality, Muntz/coPoisson) completed, all partial. Generations872700,872742,872793,872903. All lanes inspected; source_only candidates not Lean verified. Two inventories complete56809, most compilerpending, unavailable semantic retrieval/deadline. All4 owned terminal jobs exited0 and their exact /tmp/edq-*-root-20260911m.json files removed. No owned Lean process started; foreign processes untouched.

Broad newest-first arXiv memory search found Ellis et al. 2609.11383v1, 10Sept2026, delay-engineered non-Markovian spin oscillator. Read exact linear characteristic equation appendix IV.3: delay phase and gain both matter, negative feedback coefficient alone insufficient. No EDQ bound transferred; no simulation.

No RH proof/falsification, stronger arithmetic source bound, or completed no-go. Next work must attack actual signed arithmetic cancellation; do not repeat compensation, generic weighted-L1 continuity, compact seed regularity, or old axiom audits.
