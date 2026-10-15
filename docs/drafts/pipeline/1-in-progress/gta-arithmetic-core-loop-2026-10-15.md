# GTA arithmetic core research

Status: IN PROGRESS. Goal: unconditional Lean proof of RH through GTA.

## Constraints

Use hgtl7 conjecture/attack/proof/formalization loop. Corpus-only evidence; no external literature or numerical experiments. Keep GTA fixed. Do not substitute new equivalences, estimate optimization, or another route for the missing arithmetic theorem. Preserve unrelated worktree edits.

## Plan

1. Inspect actual theta kernel and existing GTA no-go theorems.
2. State an exact arithmetic mechanism excluding persistent nonreal source modes; attack it against existing Lean results.
3. Complete a dependency-closed mathematical proof before adding Lean.
4. Check new leaves individually with `lake --old env lean`, audit axioms in `/tmp`, wire umbrella, run formal lint.
5. Continue until RH itself is proved without an unproved premise.

## Verified source frontier

- `HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean`: uniform quartic-charge decay over all actual theta-stage Schur packets is equivalent to RH.
- `PaperThetaSchurIdealClassification.lean`: compactness of the full stage/mode operator is equivalent to the same endpoint. This does not supply arithmetic decay.
- `HedenmalmThetaSkewAdjointDefectFloorNoGo.lean`: ordinary anti-Hermitian energy has a strictly positive limit. The fixed coordinate vector detects a negative imaginary expectation. Therefore ordinary asymptotic Hermiticity cannot supply GTA decay.
- `HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion.lean`: finite stages approach the fixed negative theta kernel in Hilbert--Schmidt norm with exact zero trace; ordinary determinants converge locally uniformly to normalized Xi.

## Current question

What arithmetic identity of the theta source forces real spectrum despite persistent ordinary skew-adjoint energy and indefinite Green boundary? Need a source-selected mechanism, not positivity imposed on all source vectors.

External novelty status: not audited, per user instruction. No claim of new scientific knowledge or RH proof.

## Cycle 1: extend the opposite-frequency metric

Conjecture: the already constructed positive `pairedBlockMetric` also symmetrizes the full theta quotient operator, including cross-frequency interactions. Verdict: FALSE by an exact two-scale argument, without numerical experiments.

Let a=Phi(1), b=Phi(2), c=Phi(3), r=(b-a)/a, s=(Phi(4)-b)/b. Existing source theorems give a>0 and 0<r,s<1. The literal quotient Fourier entries are D(m,n)=(Phi(m)-Phi(n-m))/(2*pi*n). The metric maps e_(+/-n) to e_(+/-n)+r_(n)e_(-/+n).

Pair its adjoint defect against (e_1,e_2) and (e_1,e_-2). After multiplication by 4*pi, these two real entries are

E1=(-r+2*s)*(c-a)-2*a*r*(1+s),
E2=3*(c-a)-2*a*r*(1+s).

Hence 3*E1+(r-2*s)*E2=-2*a*r*(1+s)*(3+r-2*s)<0. Thus both entries cannot vanish. This proves the conjecture false and removes Phi(3) entirely; failure is forced by the exact dyadic source inequalities.

Positive survivor (strengthened on paper): replace 1,2,3,4 by n,2n,3n,4n for every n>=1. Multiplying the same two entries by 4*pi*n gives the same exact negative functional. Consequently any self-adjoint symmetrizer Q must disagree with the paired metric on at least one of e_n,e_(2n),e_(-2n), for every n. A correction supported on finitely many Fourier frequencies cannot repair this metric. More generally its defect functional must cancel the explicit negative value at every dyadic scale. This is a constraint on the missing full source form, not a replacement RH criterion. Formalization pending.

Next core conjecture remains existence/construction of a positive, source-derived form retaining all cross-frequency couplings. The paired metric is a failed ansatz for that same GTA obstacle, not a reason to leave GTA.

## Anti-theatre / anti-laziness checkpoint

- No RH proof and no source decay producer yet. Do not count the existing equivalences as progress on that producer.
- The paired-metric extension was an exact falsifiable ansatz for the core, not an estimate improvement. Its all-scale obstruction was derived from actual source coefficients and searched against the corpus.
- External novelty is unassessed. Formalization alone does not establish novelty.
- Next work must construct the coupled positive form or directly force transverse spectral-charge decay. Positivity of isolated blocks and tail-smallness of the cross-frequency operator are insufficient; the latter carries the leading spectral mass.
- No computational experiments, new axioms, heartbeat changes, full builds, or unrelated source edits.

## Cycle 2: allow arbitrary positive weights on each frequency pair

Stronger conjecture: replace the particular paired metric by arbitrary positive reflection-invariant blocks [[a_n,b_n],[b_n,a_n]], with a_n>|b_n|, and recover symmetry of the full source operator. Attack on paper: still FALSE, by divergence of the actual CDF action, not by quantitative perturbation bounds.

For fixed positive m and n>m, the cross-pair symmetry equations imply

 m*(a_m+b_m)*(2*Phi(m)-Phi(n-m)-Phi(n+m))
   = n*(a_n-b_n)*(Phi(n+m)-Phi(n-m)).

Since Phi(j) tends to infinity, the left side is eventually strictly negative. Both scalar coefficients outside parentheses are positive. Hence Phi(n+m)<Phi(n-m) eventually. On any residue class modulo 2m this makes Phi eventually decreasing and bounded above, contradicting Phi(j) tending to infinity.

This attacks arbitrary positive weights in the pair-local ansatz; the particular normalization of Cycle 1 is irrelevant. A surviving metric must include cross-pair correlations. The paper argument has not been formalized. Broader search then located `ThetaCdfFiniteRangeSymmetrizerNoGo.lean`, which already proves no bounded uniformly coercive symmetrizer of any finite absolute-frequency range. Accordingly the bounded/coercive version of this conjecture is REDISCOVERED and is not being promoted as a new result.

## Cycle 1 formal survivor

`formal/GaloisForLFunctions/RHTower/ThetaQuotientDyadicMetricDefect.lean` now contains the exact dyadic functional, its strictly negative evaluation on the actual paired metric, the exact compensating charge required of a repair, and impossibility of agreement with that metric outside finitely many frequencies. The distinguishing content is the exact source identity at every dyadic scale, not another claim that finite-range coercive metrics fail.

- Final leaf check: `lake --old env lean GaloisForLFunctions/RHTower/ThetaQuotientDyadicMetricDefect.lean`, exit 0, no output.
- Wired once into `RHTower.lean` next to the existing paired-metric import. No full umbrella build.
- `scripts/formal_tools.py index`: exit 0; new source indexed.
- Global `scripts/formal_tools.py lint`: exit 1; unreachable concurrent modules `EvenSectorAbelAveraging`, `EvenSectorAbelLaplace`, `EvenSectorAbelPinning`, `EvenSectorFarBumpPoleFreeCombination`; no error in the GTA leaf. Preserve concurrent work.
- Axiom audit: `lake --old env lean /tmp/gta-dyadic-axioms.lean`, exit 0. All 9 public declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or extra axiom. Log `/tmp/gta-dyadic-axioms.log`. Audit source verified identical to the final leaf, SHA256 `7c6dcc2ecb423d8da9fd61d5fbea0e18fbcd585f89c7eda5018d47ef3fdeb792`.
- Exact module lexical search finds the new dyadic declarations; final `git diff --check` passes. Removed owned probe/working scratch files; retained axiom witness and research evidence. No adjacent `.olean`/`.ilean` files.

## Current core and rejected over-strengthening

Read `HedenmalmThetaDerivativeJordan.lean`, `HedenmalmThetaDerivativeHistorySpectrum.lean`, `HedenmalmThetaDerivativeHistoryQuotient.lean`, and `HedenmalmThetaDerivativeHistoryRiesz.lean`. Both full and constant-centered source operators have actual infinite zero-Jordan chains. The closed derivative-history restriction is quasinilpotent, and the literal history quotient preserves every nonzero Xi spectral value with full algebraic multiplicity.

Therefore a bounded injective metric on the full or merely constant-centered source is an impossible target, and a positive definite symmetrizer on the history quotient may impose semisimplicity beyond RH. Keep the original GTA quartic-decay endpoint, which allows multiplicities and nonnormal finite stages.

Next exact source ansatz under investigation: start with the nonlocal Gram form B* M B, where B is the literal theta inverse and M is reciprocal quantile speed. Its adjoint defect is B*(M B-B* M)B=i B* C B, with C the already-proved rank-two pinned boundary. Positivity of this Gram form alone does not remove the boundary. A valid repair must retain all nonzero source divisor data, handle the closed zero-history, and cancel the boundary without assuming real zeros or semisimplicity. No such repair has been proved.

## Cycle 3: faithful index-one boundary realization

Conjecture tested: the existing hyperbolic boundary augmentation supplies a faithful index-one spectral realization of the source pencil. Corpus search and Lean inspection found the exact augmentation already implemented in `HedenmalmThetaSourceDifferentialGreen.lean`; no new realization was constructed here.

Write S for `thetaCenteredSourceInverse`, J_z k = k + z(S k - mean(S k) 1), m(k)=mean(S k), d(k)=dipole(k), and E=sqrt(M). The existing augmented readout is A_z k=(E J_z k, (i z/2)(m(k),d(k))). Its Green identity holds, but its zero set must be checked independently.

Dependency-closed paper proof of the obstruction and positive survivor:

1. On ker J_z, m is injective: if J_z k=0 and m(k)=0 then the injective shifted range map k+z S k vanishes, hence k=0. Apply this to a difference for full injectivity.
2. A_z k=0 implies J_z k=0 because E is injective. If z=0 then J_0 k=k. Otherwise the first port gives m(k)=0. Thus A_z has trivial kernel for every z, including every Xi zero. Ordinary augmented kernels cannot represent the divisor.
3. Every nonzero source kernel vector has m(k) != 0 and admits unique normalization m(k)=1. Therefore Xi(z)=0 iff there exists a unique k with J_z k=0 and m(k)=1. This is a source-defined boundary response, not a spectral realness assertion.
4. At that normalized response, A_z k=(0,(i z/2, i z d(k)/2)). The divisor survives as a nonzero boundary-only output, not as an augmented zero. This preserves the zero set; no algebraic-multiplicity claim is made.

Status: paper proof closed and formalized in `HedenmalmThetaAugmentedReadoutDivisorBoundary.lean`. Final `lake --old env lean` leaf check passed, and `/tmp/gta-boundary-axioms.log` audits all six theorems with only propext, Classical.choice, Quot.sound. Leaf SHA256: `61d7b4d3caaee238dfb0cc319a46aee4642e8478dfde2991d640b2256b518e1d`. Import wired once into RHTower. This rejects one proposed faithful completion, not GTA. The arithmetic quartic-decay producer remains unproved; the user's subsequent steering below supersedes index-one construction as the active target.

## User steering: nonnormal transverse coupling

User explicitly sets the hard problem: **nonnormal transverse coupling, rather than self-adjoint spectral placement, must distinguish the critical wall**. GTA remains fixed. The selfadjoint/index-one construction is no longer the active producer. Complete only the already-started boundary-fidelity audit; do not build more selfadjoint placement interfaces.

Existing Lean mechanism: `FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect.lean` proves exactly

`HS(M)^2 - Re tr(M^2) = NonnormalEnergy(S) + 2 sum_i Im(S.T_ii)^2`.

The full defect need not vanish and must not be made the target. The nonnormal coupling must account for the full source defect, leaving asymptotically zero transverse remainder. This is the producer problem; merely renaming the remainder or adding a conditional RH bridge is not a solution.

Candidate rejected before implementation: transverse diagonal conjugation can create a strictly convex, reflection-symmetric Hilbert--Schmidt energy with unique minimum at the wall. But similarity preserves the divisor, and generic reflection-balanced operators have the same convexity. Such a minimum alone cannot select actual Xi modes. No code or RH claim from that candidate.

Next research target: an arithmetic identity for the literal nonnormal source coupling which saturates the quadratic defect (or directly cancels its quartic transverse reporter), retaining the cross-frequency interaction and full source divisor. No such identity has yet been proved.

## Cycle 4: parity Gram blocks and singular directed feedback

This is the active mechanism after the user's steering, within GTA. Internal search: `/tmp/gta-parity-feedback-search.json` (inspect Lean hits before formalizing). Exact starting point is `inner_unitFourierBasis_thetaQuotientOperator`, not an abstract spectrum surrogate.

Paper derivation for a finite set of distinct positive frequencies m,n. Put Phi_n=`cdfAction n`, theta_n(x)=2 pi n F(x), where F is the literal theta CDF. Define the two real Gram matrices

- S_mn = integral sin(theta_m(x)) sin(theta_n(x)) dx = (Phi_(m+n)-Phi_(m-n))/2.
- C_mn = integral (1-cos(theta_m(x)))(1-cos(theta_n(x))) dx = Phi_m+Phi_n-(Phi_(m+n)+Phi_(m-n))/2.

All these integrals exist: sin(theta_n)^2 <= 2(1-cos(theta_n)); the latter is integrable by `integrable_cdfAction_integrand`. Products follow by Cauchy--Schwarz, or elementary square domination. Thus S and C are positive semidefinite. For distinct positive frequencies S is positive definite: a zero quadratic form forces a sine polynomial to vanish on the full CDF image (0,1), hence every coefficient vanishes. This is a paper proof, not yet Lean checked here.

The literal +/- frequency matrix is [[A,B],[-B,-A]], with
A_mn=(Phi_m-Phi_(n-m))/(2 pi n), B_mn=(Phi_(m+n)-Phi_m)/(2 pi n).
The even/odd change of basis gives [[0,A-B],[A+B,0]], where

`A+B = S N^(-1)/pi`, `A-B = (C - 1 Phi^T) N^(-1)/pi`.

After the finite diagonal similarity by N^(-1/2), write K=N^(-1/2) S N^(-1/2), H=N^(-1/2) C N^(-1/2), u_n=1/sqrt(n), v_n=Phi_n/sqrt(n). The matrix is exactly

`(1/pi) [[0, H-u v^T], [K, 0]]`.

The squared lower parity block is similar to

`(1/pi^2) [K^(1/2) H K^(1/2) - (K^(1/2)u)(K^(1/2)v)^T]`.

This localizes all nonsymmetry to a directed rank-one feedback coupling of two distinct source boundary vectors. It does NOT make the full operator selfadjoint, and positivity of H and K does not settle the feedback's spectral effect. In particular, a positive Gram block minus an arbitrary nonsymmetric rank-one term need not have real spectrum.

Infinite-limit warning is structural, not an optional technical estimate: u is not in l2 because sum 1/n diverges; v is not in l2 because Phi_n tends to infinity. The bounded compact source operator therefore cannot be analyzed by independently extending these finite feedback vectors as bounded l2 vectors. Cancellation between Gram and feedback terms must be retained. Do not infer a bounded rank-one perturbation or a finite negative index from this finite formula.

Conjecture to investigate, not proved: the theta-specific directed feedback has a renormalized cross-spectral positivity/conservation law which consumes the transverse part of the GTA defect. Prove this from the literal theta source, including the singular limit, rather than assuming positivity of a quotient metric or real divisor. First audit the finite decomposition in Lean and search for existing source feedback laws; then attack this arithmetic sign/cancellation law. Generic CDF Gram positivity alone cannot be advertised as that law.

Falsification check on generic Gram-plus-feedback positivity: H=[[2,3/2],[3/2,3]], K=I, u=(1,1), v=(1,2) have H positive definite and u,v strictly positive. Nevertheless H-u v^T=[[1,-1/2],[1/2,1]] has eigenvalues 1 +/- i/2. Thus entrywise positivity of boundary vectors and positivity of both Gram blocks are insufficient. The source-specific relation between C, S, u, v is essential. This algebraic counterexample has a paper proof; it is not another task to prioritize over the actual theta feedback.

Cycle 3 closeout: index refresh passed (two changed files at snapshot); `git diff --check` passed. Global formal lint exited 1 for concurrent unreachable EvenSectorAbelAveraging, EvenSectorAbelLaplace, EvenSectorAbelPinning, EvenSectorAbelRigidity, EvenSectorFarBumpPoleFreeCombination, with existing large-file warnings. No failure named the new GTA leaf. Scratch probe removed after successful leaf and axiom audits; audit source/log retained in /tmp. All owned command handles terminal. Goal remains active; RH is unproved.

## Cycle 4 continuation: exact stochastic normalization of the feedback

New corpus evidence: `ThetaQuantileResistanceNetwork.lean` already supplies positive theta conductances a_n, unit capacity `2 sum a_n Phi_n=1`, and for every m!=0 the exact Green law `sum a_n (2 Phi_m-Phi_(m-n)-Phi_(m+n))=0`. These are source laws, not spectral-realness premises.

Combining them with the cosine Gram formula gives the dependency-closed paper identity

`sum_(n>=1) 2 a_n C_mn = 1` for m>=1.

Thus `P_mn=2 a_n C_mn` is a nonnegative row-stochastic kernel. It obeys detailed balance `a_m P_mn=a_n P_nm`. The literal feedback distribution `r_n=2 a_n Phi_n` is also nonnegative with total mass one. The even-to-odd parity channel is precisely

`P_mn-r_n = 2 pi n a_n [D_mn-D_m,-n]`.

This identifies the nonsymmetric source feedback as centering a reversible positive Gram transition by a distinct source probability distribution. Its full row cancellation is exact and uses every frequency. It is not a vanishing assertion about Schur transverse charge. Multiplication by frequency/conductance weights and coupling to the sine Gram sector remain essential; do not discard them or claim that realness of an isolated Markov quotient settles GTA.

Formal audit underway in `/tmp/gta-parity-probe.lean`: source sine/cosine Gram integral formulas, finite Gram positivity, exact parity coefficient formulas. First probe exposed only rewriting/type-annotation issues; second probe running. Next append the exact stochastic normalization above, then audit and promote the resulting source-coupling leaf. No numerical experiments.

### Cycle 4 audited result and dependency check

Promoted `formal/GaloisForLFunctions/RHTower/ThetaQuotientParityFeedback.lean` with 22 public definitions/theorems. The leaf proves the two source Gram integral formulas and finite positive semidefiniteness, literal Fourier parity pairing, and all stochastic identities above. It does not formalize the square-root matrix similarity or strict positive definiteness claimed separately on paper.

- Final leaf audit: `lake --old env lean GaloisForLFunctions/RHTower/ThetaQuotientParityFeedback.lean`, exit 0; `/tmp/gta-parity-leaf-audit.log` empty.
- All 22 public declarations audited from a copy of the exact leaf in `/tmp/gta-parity-axioms.lean`, exit 0. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or added axiom. Evidence `/tmp/gta-parity-axioms.log`.
- SHA256 `c71ff5a4f9929b7d3810ee35d5e674993c0459abcdb10be66dfbdc87d437c4bc`. Wired once into `RHTower.lean`; no umbrella build.
- Index exit 0. Global lint exit 1: concurrent `EvenSectorNegPartAbelRigidity` is unreachable from its umbrella; no error names the new GTA module. Do not alter unrelated work to hide this failure.

Stronger dependency audit: `ThetaQuantileScoreProjection.lean` already proves `D s=0` and `ker D intersect H0 = C s`, for the actual score vector. The stochastic row cancellation is compatible with this existing zero mode. Also `ThetaQuantileKronReduction.lean` already gives a singular boundary feedback formula and proves the clock functional unbounded in its energy. Do not represent the new parity coordinates as a new proof of boundary cancellation or removal of the full zero history.

Verdict: BRIDGE. Source-normalized nonnormal coupling has been identified exactly, but no arithmetic vanishing law for transverse charge has been proved. External novelty remains unassessed by user instruction. Formalization is not evidence of scientific novelty or RH progress by itself.

### Next attack: a relation between the two parity channels

Keep the actual coupled operator, not just its stochastic channel. In finite formal notation write A=diag(a_n), N=diag(n), P=2 C A, r_n=2 a_n Phi_n. The squared even channel is

`D_even^2 = (P - 1 r^T) A^(-1) N^(-1) S N^(-1)/(2 pi^2)`.

Thus Markov reversibility of P does not remove the directed centering or the frequency-weighted sine channel. On the quotient by constants P-1r induces P, but the second factor need not descend to that quotient. Deleting this coupling would be an invalid argument. Any infinite realization must justify its weighted domains, not apply an unbounded similarity as though it preserved spectrum.

Candidate source property being tested, not established: positive Hankel forms of the literal theta conductances, `sum_(m,n in F) c_m c_n a_(m+n) >= 0` for all finite positive frequency sets F. A stronger possible producer is a Hausdorff-moment representation of a_n. These are all-order statements about the source profile, not RH or a real-spectrum assumption. Their proposed role is to control the difference between the even and odd restrictions of the same jump generator, which is a Hankel coupling. Neither this property for theta nor a sufficient implication to GTA charge decay has yet been proved; both must be attacked before further formalization. Existing positivity of individual a_n and concavity of the profile do not establish Hankel positivity.

Exact meaning of the proposed coupling: with real coefficients c_m, theta profile h, and A(t)=sum c_m cos(2 pi m t), B(t)=sum c_m sin(2 pi m t), the Hankel form equals `integral_0^1 h(t) (B(t)^2-A(t)^2) dt`, by the cosine addition law and a_n=-hhat(n). Therefore the missing sign is an order relation between parity energies of the same Hardy polynomial. Each parity energy separately being positive says nothing about this difference.

Falsification audit for a possible generic proof, on paper only: h_e(t)=t(1-t)-e t^2(1-t)^2, 0<e<=1, is positive inside, zero at endpoints, symmetric, strictly concave. Its conductances are exactly `a_n=1/(2 pi^2 n^2)-3 e/(2 pi^4 n^4)>0`. They admit the signed Laplace density `w_e(x)=x/(2 pi^2)-e x^3/(4 pi^4)`. For coefficients of z(1-z)^N, the Hankel form is `integral_0^infty exp(-2x)(1-exp(-x))^(2N) w_e(x) dx`. The positive part is bounded by an exponential in -N on the fixed interval where w_e>=0; the negative part on [log N,log N+1] has magnitude bounded below by a positive multiple of (log N)^3/N^2 for sufficiently large N. Thus the form is eventually negative. For e<=0 the displayed density is nonnegative and every such Hankel form is nonnegative. This sharply separates the all-order condition from concavity and individual conductance positivity; it does not disprove the theta-specific conjecture. No numerical experiment used. This model classification has not been Lean-audited and is not a finished no-go theorem or a reason to retire GTA.

Research priority remains the actual nonnormal two-channel problem. Do not spend another cycle formalizing generic scalar/matrix wrappers or this model classification before establishing that the proposed theta Hankel condition controls the physical coupled operator and its singular limit. An unproved connection to the GTA producer would make even a true Hankel theorem insufficient.

Search evidence: `/tmp/gta-parity-coupling-search.json` partial at reranking; `/tmp/gta-conductance-hankel-search.json` partial at query/deadline/filter stages. Neither supplied an applicable theta conductance Hankel theorem. Exact lexical `thetaConductance` found only its definition and positivity theorem. This is bounded corpus evidence, not an assertion that no such theorem exists elsewhere.

Final working audit: `git diff --check` passes; axiom source begins with byte-identical final leaf; all 22 declarations reported; no adjacent olean/ilean files. Removed owned `/tmp/gta-parity-probe.lean`, retained audit/search evidence. All owned job handles terminal. No full build, numerical work, added axiom, heartbeat increase, commit, or push.

## Cycle 5: test whether conductance Hankel positivity can control the coupled source

Previous turn: PROGRESS (audited source identity and explicit unresolved dependency). Mission unchanged. The Hankel candidate is being tested for sufficiency before trying to prove it for theta. Direct modulus-squared coupling is already in the corpus: `ThetaCuspShellIncompleteGammaCoordinate.lean` 9601 onward gives product-fibre Hermitian energies, their convergent sum equal to normSq Xi, and their transverse derivative equal to the actual Hedenmalm current. `HedenmalmGaussianHankelApertureWidthSpectrum.lean` makes full current positivity equivalent to the divisor-width bound. Rewriting that sign again would not produce it.

### New source family and paper proof of the stronger obstruction

For delta>0, r(t)=sin(pi t), 0<t<1, set

`h_delta(t)=r(t) [1+delta log(1+1/r(t))]`, `Q_delta(t)=integral_(1/2)^t 1/h_delta(s) ds`.

Define T_delta=Q_delta^(-1), k_delta(x)=h_delta(T_delta(x)), and F_delta(z)=integral_0^1 exp(i z Q_delta(t)) dt. This is an actual quantile source, not an arbitrary finite matrix. The following chain is a paper derivation; formalization is in progress, and no complete Lean no-go theorem is claimed yet.

1. Put f_delta(r)=r+delta r log(1+1/r). On r>0,
   f'_delta=1+delta[log(1+1/r)-1/(1+r)]>0,
   f''_delta=-delta/[r(1+r)^2]<0.
   The strict inequality log(1+u)>u/(1+u) follows by integrating its positive derivative u/(1+u)^2 from zero. Therefore h_delta>0, symmetric, strictly concave on (0,1), and tends to zero at both endpoints. The induced density is smooth, even, positive on all R, integrates to one, and `(log k_delta)''=h_delta h_delta''<0`.
2. For 0<t<=1/2, 2t<=r(t)<=pi t. These bounds give h_delta(t)<=pi t[1+delta log(1/t)] and, for sufficiently small t, h_delta(t)>=2 delta t log(1/(pi t)). Hence Q_delta tends to both infinities but |Q_delta(t)| is at most C_delta+(1/(2delta))log log(1/(pi t)) near zero. All exponential moments exist. Integrating exp(R|Q_delta|), and bounding u^p exp(-u/2) by its maximum, gives `|F_delta(z)|<=exp(K_delta(1+|z|)log(2+|z|))`. Thus F_delta is even entire of order at most one in the corpus's explicit growth sense. Also integral q_delta(t)^2 t(1-t) dt is finite (endpoint integral dt/[t log^2 t]); the literal pinned inverse is Hilbert--Schmidt.
3. Exact positive mixture, y>0:
   `sqrt(y)[1+delta log(1+1/sqrt(y))] = integral_0^infty y/(y+s) [1+(delta/2)log(1+1/s)]/(pi sqrt(s)) ds`.
   Derivation: sqrt(y)/(sqrt(y)+v) has density v/[pi sqrt(s)(s+v^2)]; verify by s=u^2 and elementary partial fractions/arctan integrals. Integrate v from 0 to 1, using r log(1+1/r)=integral_0^1 r/(r+v) dv. All integrands are nonnegative, so Tonelli applies. The sqrt(y) part uses its elementary Stieltjes integral.
4. In the elementary profile y/(y+s), y=sin^2(pi t), set R=(sqrt(s+1)-sqrt(s))^2. Its nth negative cosine coefficient is `(1-R)/(1+R) R^n`, n>=1, by the absolutely convergent Poisson series. Substituting s=(1-R)^2/(4R) in step 3 yields the exact conductances
   `a_n(delta)=1/(2pi) integral_0^1 R^(n-3/2)(1-R)[1+delta log((1+R)/(1-R))] dR`.
   Thus a_(n+1) is a Hausdorff-moment sequence of the positive finite density `R^(-1/2)(1-R)[1+delta log((1+R)/(1-R))]/(2pi)`. Every finite shifted Hankel form is positive, indeed strictly positive for independent monomials, and every alternating finite difference is positive. Individual conductances, jump-profile Green law, capacity law and the exact coupled parity normalization all survive.
5. As delta decreases to zero, Q_delta(t) tends pointwise to `Q_0(t)=log(tan(pi t/2))/pi`, with |Q_delta|<=|Q_0|. The limiting density is sech(pi x), whose characteristic function is sech(z/2); `SechComplexFourierTransform.lean` supplies the transform identity. Its second and fourth moments are 1/4 and 5/16. Dominated convergence gives `mu_4(delta)-3 mu_2(delta)^2 -> 1/8>0`.
6. An even entire real function of the stated order-one growth, F(0)=1, with only real zeros is Laguerre--Polya (`OrderOneEvenLaguerrePolya.lean`). Its fourth logarithmic derivative at zero is nonpositive: for each real-rooted polynomial approximant it is -6 times the sum of reciprocal fourth powers of roots; local uniform derivative convergence passes the inequality to F. At an even characteristic function this derivative is mu_4-3mu_2^2. Hence all sufficiently small delta>0 in this family have a nonreal zero. Imaginary-axis zeros are impossible because the moment generating integral is strictly positive.
7. The nonreal zero gives an actual pinned-inverse eigenvector, not merely an unrelated transform counterexample. If F_delta(z)=0, set `g(t)=-exp(-i z Q_delta(t)) integral_0^t exp(i z Q_delta(s)) ds`, `f(t)=-i z q_delta(t) g(t)`. Then g'=f-1, both endpoint values of g are zero, integral f=1, and `V f=g`. Endpoint log-log bounds give g=O(t) at zero and O(1-t) at one, so f=O(1/log(1/t)) at zero and the reflected bound at one; in particular f is L2 and nonzero. Therefore `(i M_q V)f=(-1/z)f`. The g=O(t) bound follows by integrating the power of log(1/s)/log(1/t) arising from exp(i z(Q(s)-Q(t))); after s=t exp(-u), its integral is bounded by integral_0^infty exp(-u)(1+u)^C du. This retains the literal nonnormal source construction.

Consequently even all-order positive conductance moments, strict log-concavity, full support, entire order-one transform, theta-like double-exponential tails, and a Hilbert--Schmidt pinned inverse cannot by themselves force the critical wall. This attacks the proposed producer inside GTA; it does not disprove that theta itself has positive Hankel conductances, nor retire GTA. The positive survivor is the explicit source-profile/moment-measure correspondence and regularization family retaining these structures while changing spectral phase. Formalize that exact construction and obstruction, not only an abstract negative slogan.

Scope audit: the family has not been shown to satisfy theta's Euler product or its narrow zero strip together with its central zero-free gap. The fourth-cumulant witness specifically exploits a property theta does not share. Therefore this refutes sufficiency of the listed profile conditions alone; it does not refute a proposed theorem that also uses those arithmetic constraints. Do not silently discard the latter when returning to the actual theta operator.

Alternative paper proof of step 6, with existing corpus support and no fourth-derivative algebra: `LaguerrePolyaImaginaryAxisBounds.lean` proves the real-rooted polynomial Gaussian bound, and `EvenRealRootedGaussianBounds.lean` / `RiemannKernelLaguerrePolyaSymbol.lean` pass such bounds through coefficient limits. For a normalized even LP characteristic function, `|F(iY)|^2 <= exp(mu_2 Y^2)`. Here mu_2(delta)<=mu_2(0)=1/4, but for any Y>pi the positive integral F_delta(iY) tends to infinity as delta decreases to zero, since the limiting sech density has no exponential moment at Y. Fatou or monotone convergence proves divergence. Thus all sufficiently small positive delta violate the uniform Gaussian bound. This may be the shorter formal nonreal-zero proof; it still requires the source integral, moment bound, and order-one growth to be audited.

Formal plan: (1) literal log-sine profile calculus and endpoint/source control; (2) exact positive conductance moment representation; (3) quantile moment limit and order-one nonreal-zero conclusion; (4) reconnect to the original GTA source and identify the genuinely arithmetic relation absent from this family. No numerical experiments. Do not mark the no-go closed until the full chain and positive survivor are audited.

### Cycle 5 formal checkpoint

`LogSineQuantileProfile.lean` now proves the scalar lift and its exact two derivatives, positivity, reflection, continuous zero endpoints, strict profile concavity, and the two endpoint inequalities in step 2. It contains 24 public declarations (4 definitions and 20 theorems). The source-transform, conductance, Hilbert--Schmidt and nonreal-zero conclusions are not claimed in this leaf.

- Final leaf `lake --old env lean GaloisForLFunctions/RHTower/LogSineQuantileProfile.lean`: exit 0, empty `/tmp/gta-logsin-leaf-audit.log`.
- Exact-copy axiom audit `/tmp/gta-logsin-axioms.lean`: exit 0; all 24 declarations use only `propext`, `Classical.choice`, `Quot.sound`. SHA256 `dbf1c08be6bf33f6bcb056285946a237eb63178ec3f5d3a55bd47b895ebc863a` and exact source prefix verified.
- Wired once into RHTower, index exit 0. Global lint exit 1: concurrent `PrimitiveHyperplaneBlindPositivity` unreachable from umbrella, no error names the new leaf. `git diff --check` passed.
- Owned scratch `/tmp/gta-logsin-profile.lean` and `/tmp/gta-logsin-api.lean` removed after audits; retained proof evidence and search logs. No adjacent olean/ilean, full build, numerical experiment, heartbeat increase, commit or push. All owned command handles terminal.

Anti-theatre / anti-laziness: this turn produced a concrete source-level falsification construction for the proposed coupling condition, with its first constituent formally checked. It did not prove the theta arithmetic sign or finish the counterexample. The initial general semantic searches mostly returned irrelevant hits; further work should use exact discovered theorem names and the explicit integral kernel. External novelty is unassessed per user instruction. No effort-based deferral occurred. Next action is the actual Fourier coefficient / positive moment identity for this same profile, followed by the transform argument; do not drift into unrelated no-go wrappers or call the hard GTA obstacle solved.

Completion audit: unconditional RH is still unproved; the user goal remains ACTIVE. Neither the new exact obstruction nor existing equivalent criteria meet the goal.

### Cycle 5 exact positive mixture checkpoint

`LogSineStieltjesRepresentation.lean` proves the explicit density
`rho_delta(s)=[1+(delta/2)log(1+1/s)]/(pi sqrt(s))`, its positivity for delta>=0,
the literal scalar and profile Stieltjes identities, absolute joint integrability
on `(0,1) x (0,infinity)`, and the exact cosine-coefficient Fubini identity.
The auxiliary integral is proved by partial fractions of the corpus's
`integral_Ioi_one_div_add_mul_sqrt`; the exceptional auxiliary parameter v=r is
removed as a null singleton. No divergent integral or formal interchange is used.

Direct final leaf command `lake --old env lean GaloisForLFunctions/RHTower/LogSineStieltjesRepresentation.lean`
exited 0 with empty `/tmp/gta-stieltjes-leaf-audit.log`. Seven public declarations;
SHA256 `c5d00d4a16a4a46abd1d1257918b7def1b62972e0b96331db57de609943b7904`.
Wired once into RHTower. Exact-copy axiom audit prepared, not yet run at this checkpoint.
The preceding profile was compiled only as a needed import, into the normal build tree.

Next proof in progress: exact elementary coefficient
`-integral sin^2(pi t)/(sin^2(pi t)+s) cos(2pi n t) dt
 = [(1-R)/(1+R)] R^n`, where `R=(sqrt(s+1)-sqrt(s))^2`.
Corpus search `/tmp/gta-poisson-conductance-search.json` returned useful existing
Poisson Fourier moments with partial coverage; those are now being matched to the
literal interval profile. Full conductance moment theorem, nonreal zero and actual
theta arithmetic coupling remain unfinished. The user goal is ACTIVE.

### Cycle 5 conductance theorem audited

`LogSineConductanceMoments.lean` now proves the exact elementary Poisson/cosine
identity and, for every delta>=0 and n>=0,
`a_(n+1)(delta)=integral_0^infinity W_delta(s) R(s)^n ds`,
where `R(s)=(sqrt(s+1)-sqrt(s))^2` lies strictly between 0 and 1 and
`W_delta(s)=rho_delta(s) [(1-R(s))/(1+R(s))] R(s)>0`.
The weight is integrable, dominated by `rho_delta(s)/(1+s)`. This is an explicit
finite Hausdorff mixing measure, represented by its pushforward from `(0,infinity)`;
the optional change of variables to the paper's density on `(0,1)` is not yet formalized.
Every power moment is integrable, every a_(n+1)>0, and every finite shifted Hankel
form equals `integral W_delta(s) R(s)^shift [sum c_m R(s)^m]^2 ds >= 0`.
Thus the original proposed all-order source positivity is proved for this literal
family, with no spectral-placement premise. Nonreal spectrum is not yet formalized.

Audits:
- `lake --old env lean GaloisForLFunctions/RHTower/LogSineConductanceMoments.lean`: exit 0,
  empty `/tmp/gta-moments-leaf-audit.log`. Fifteen public declarations.
  SHA256 `5ad652a1ee7fbec4503f9ad9b5f4ceac5fbce879cbe50e85d95b3e0c50218c4e`.
- Both exact-copy axiom audits exited 0: `/tmp/gta-stieltjes-axioms.lean` (7 declarations)
  and `/tmp/gta-moments-axioms.lean` (15); only propext, Classical.choice, Quot.sound.
- Both leaves wired once into RHTower; index exited 0. Global lint exited 1 only for
  foreign unreachable NormalSeriesStrictFDeriv, AnchorLevelGraph, JointAnchorContinuity,
  JointAnchorRegularity. Preserve those concurrent edits; neither new leaf is named.

Next source proof has a simpler paper route than exact sech moments. Define
`Q_delta(t)=integral_(1/2)^t 1/h_delta` and `F_delta(z)=integral_0^1 exp(i z Q_delta(t)) dt`.
For 0<t<=1/2 and delta>=0, h_delta>=sin(pi t)>=2t gives
`0<=-Q_delta(t)<= (1/2)log(1/(2t))`. Reflection gives `integral Q_delta^2<=1/2`
using the symbolic identity integral_0^1 log(u)^2 du=2. No exact sech Fourier
transform, fourth cumulant, or exact variance is necessary for the obstruction.
On every compact subinterval of (0,1), Q_delta tends to Q_0 as delta decreases to0.
Since sin(pi t)<=pi t, `-Q_0(t)>=(1/pi)log(1/(2t))`; at Y=2pi the lower-half
integrand exp(-Y Q_0(t)) is at least (2t)^(-2), whose integral diverges. Hence
F_delta(iY) tends to infinity, by monotone convergence or by taking finite lower
cutoffs and then their limit. A normalized LP characteristic function with this
uniform second-moment bound obeys `|F(iY)|^2<=exp(Y^2/2)`. The polynomial imaginary
Gaussian inequality and the audited `tendsto_lagRatio` provide this limit theorem;
even polynomial approximants are unnecessary on the imaginary axis.
After proving F_delta entire with the previously derived order-one envelope for
delta>0, the existing real-zeros-to-LP theorem yields nonreal zeros for every
sufficiently small positive delta. Then formalize the literal pinned-inverse mode.
This is the next concrete source theorem, not a claim already established in Lean.

Corpus search `/tmp/gta-quantile-endpoint-search.json` completed with snapshot
coverage. It found the forward PositiveDensitySource/quantile normal form, but no
ready constructor from this reciprocal profile. Existing proofs of the LP Gaussian
bounds were inspected in Lean. No web or numerical experiments were used.

Anti-theatre: actual progress is the exact all-order conductance theorem and its
positive source measure. The no-go remains open until the same family's nonreal
zero and pinned mode are formalized. Theta arithmetic and RH remain unresolved;
GTA remains fixed and the goal remains ACTIVE.

### Cycle 5 clock coordinate refinement

Previous turn: PROGRESS (exact literal conductance moments, all shifted Hankel forms and audits).
Keep the same source family. Use the exact coordinate t0(u)=2 arctan(exp u)/pi.
Then t0'(u)=1/(pi cosh u), sin(pi t0(u))=1/cosh u, and
`Q_delta(t0(u))=P_delta(u)/pi`, where
`P_delta(u)=integral_0^u [1+delta log(1+cosh v)]^(-1)dv`.
Both sides vanish at u=0 and have the same derivative; this proves the identity
without changing the source. The transformed probability density is sech(u)/pi.

Elementary bounds `|u|/2<=log(1+cosh u)<=|u|+log 2` imply, for delta>0,
`|P_delta(u)| <= (2/delta)log(1+delta|u|/2)` and a logarithmic lower bound from
integrating 1/[1+delta log2+delta|u|]. Thus P_delta is odd, strictly increasing,
onto R and tends to u as delta decreases to0, while |P_delta(u)|<=|u|.
This makes the previously closed paper nonreal-zero proof simpler: the measure is
fixed and exponentially decaying; all transformed exponential moments for positive
delta become ordinary polynomial moments, whereas at delta0 an exponential moment
diverges. No fourth cumulant, exact variance or numerical evidence is required.

Paper growth estimate: for p>=0 and x>=0, tangent-line concavity of log at a=1+2p
implies `p log(1+x)-x <= p log(1+2p)-x/2`. This supplies an integrable exponential
envelope and the required O(R log R) entire growth after the clock bound.
The coordinate identities, then these literal source estimates, are the next Lean
work. This is a representation change within GTA, not a different source or route.

### Exact pole obstruction replaces the variance calculation

The corpus already proves compactness from one nonvanishing real window for LP
functions: `RHTower.IntervalLaguerrePolya.exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window`
in `XiIntervalLaguerrePolyaRH.lean`. Its hypotheses are uniform convergence on
[-epsilon,epsilon] to a continuous nowhere-zero real-window function. Its output
is an entire limit g of reflected products, with g(t)=G(t)G(-t) on that window.
This gives an exact pole obstruction for the present family and avoids any need
to formalize variance or fourth cumulants.

Use the unnormalized, unscaled clock transform
`H_delta(z)=integral_R exp(i z P_delta(u))/cosh(u) du`.
The original quantile transform equals H_delta(z/pi)/pi by the fixed coordinate
change. H_delta(0)=pi, H_delta is even, and positive delta gives an entire
order-one envelope. At delta0, H_0(x)=pi/cosh(pi x/2) on the real axis, by the
corpus's exact sech Fourier transform.

Uniform convergence on any bounded real window follows from
`|H_delta(x)-H_0(x)| <= |x| integral |P_delta(u)-u|/cosh(u) du`.
The scalar phase inequality follows by factoring the difference into a unit
complex exponential times exp(i x(P_delta-u))-1 and using the existing
`Complex.norm_exp_I_mul_ofReal_sub_one_le`. The integral tends to zero by DCT:
pointwise clock convergence is proved and its integrand is bounded by
`2|u|/cosh(u)<=4|u|exp(-|u|)`, which is integrable in the corpus.

Suppose there are arbitrarily small positive delta for which every H_delta zero
is real. Choose such delta_n with 0<delta_n<1/(n+1); then delta_n tends to0.
Order-one real-zero classification makes every H_delta_n LP. Apply the existing
window theorem, with any fixed positive epsilon, to obtain entire g with
`g(x)=pi^2/cosh(pi x/2)^2` on the real window. The entire identity theorem then
forces `g(z) cosh(pi z/2)^2=pi^2` everywhere. At z=i, cosh(pi i/2)=0, contradicting
pi!=0. Hence every sufficiently small positive delta has a nonreal zero.
This proof retains the literal source and the original all-order Hankel positivity;
no numerical estimate or new real-spectrum premise replaces the open conclusion.
The source's literal pinned-inverse eigenvector still needs formalization afterward.

### Cycle 5 clock and entire-transform formal checkpoint

`LogSineQuantileClock.lean` (299 lines, 27 public declarations) now proves the
fixed arctan-exp coordinate, its exact derivative and sine identity, literal
profile substitution, exact reciprocal-profile clock identity, strict monotonicity,
oddness, contraction, logarithmic growth and parameter-zero convergence. Direct
`lake --old env lean GaloisForLFunctions/RHTower/LogSineQuantileClock.lean` exited0;
`/tmp/gta-clock-leaf-audit.log` empty. SHA256
`613a18e39f0d92f33704774967aa2c71d98844768263d12e82f5f75dfb5ab509`.
The exact-copy 27-declaration axiom audit exited0 with only propext, Classical.choice,
Quot.sound. The leaf was compiled into normal build output solely as a needed import.

`LogSineClockTransform.lean` (348 lines, 16 public declarations) now proves the
fixed sech exponential bound and every polynomial moment, an explicit integrable
exponential envelope for each positive regularization, the complete real
exponential-integrability set, the exact MGF identity, entire analyticity,
evenness, value pi at zero, and the global order-one envelope. Direct final leaf
command exited0 with empty `/tmp/gta-transform-leaf-audit.log`. SHA256
`05626e5329189cf329f9f2264d510eb4c3892d635766d7f84a4740ee4064dff8`.
Its exact-copy axiom audit is running at this checkpoint. Both leaves are wired
once into RHTower; index exited0. No numerical experiment or increased heartbeat.

Workflow correction: one final-audit launch briefly overlapped the preceding
scratch Lean process. The newer audit was terminated by its owned PIDs, exit143
confirmed and PIDs absent; after the earlier process exited0, the final leaf was
rerun alone. Do not claim uninterrupted single-process discipline for this turn.
A prior audit command launched from repo root failed before opening its leaf;
it was rerun from formal/. No full build or foreign process was touched.

Next exact target is the pole obstruction above, with no variance calculation:
1. Uniform real-window convergence H_delta -> H_0 from the weighted L1 clock
   difference. Use the newly exported `integrable_logSineSech_abs_pow` at n=1.
   The phase inequality is `Real.norm_exp_I_mul_ofReal_sub_one_le` (namespace Real,
   not Complex); factor two phases to reduce to it.
2. Base real-axis identity H_0(x)=pi/cosh(pi x/2), using the existing sech transform
   at parameter -x and cosh evenness. Actual transform is unnormalized and unscaled;
   the original F(z)=H(z/pi)/pi. The whole-line integral change-of-variables for F
   still needs a formal theorem; the clock composition identity is already proved.
3. If nonreal zeros fail to occur for arbitrarily small positive delta, choose
   bad delta_n<1/(n+1). `tendsto_one_div_add_atTop_nhds_zero_nat` supplies the upper
   sequence. Apply order-one real-zero classification to each H_delta_n and the
   existing LP-window compactness theorem. The latter yields entire g agreeing
   with pi^2/cosh(pi z/2)^2 on a real window. Apply
   `GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval`
   to g(z)cosh(pi z/2)^2-pi^2, then evaluate at i.
4. Real-zero classification also asks finite analytic order everywhere. This
   follows from nonzero value at0 and mathlib `analyticOrderAt_eq_top_iff_eq_zero`
   for globally analytic functions; do not add it as an assumption.
5. Then formalize the original-transform identity and literal pinned-inverse mode.

Searches: `/tmp/gta-sech-clock-search.json` completed; `/tmp/gta-clock-entire-search.json`
and `/tmp/gta-meromorphic-window-search.json` partial. The MGF API was found through
`EntireExponentialMomentPolynomialDensity.lean` and checked in the installed
`Mathlib/Probability/Moments/ComplexMGF.lean`; the LP-window theorem was inspected
at its exact Lean statement. No external novelty claim is made.

Anti-theatre/anti-laziness: these are checked dependencies of a concrete proposed
falsification, not a theta sign producer or a completed no-go. No work was deferred
because of difficulty. The next action is the exact pole contradiction, not more
generic estimate improvements. The hard arithmetic coupling for theta and RH
remain unresolved; GTA and the full goal remain ACTIVE.

Final checkpoint completion: both exact-source axiom audits exited0; all27+16
public declarations reported only propext, Classical.choice, Quot.sound. Prefix,
count, hashes and single umbrella imports verified. Global lint exit1 solely for
foreign unreachable `CHMDStage1MultiplicativeResolventAndClampedBeam`; neither new
leaf is named. Diffcheck passed. Removed owned logcosh/clock-exponential API and
proof scratches; retained audits and search evidence. No adjacent olean/ilean.
All owned jobs terminal. Goal remains ACTIVE, with no RH or complete counterexample
claim. Latest continuation memory: `research/gta-log-sine-clock-pole-test-2026-10-15`.

### Cycle 6: the exact pole obstruction closes

The complete pole-contradiction scratch exited0 (`/tmp/gta-pole-proof.log`). It proves
`exists_nonreal_zero_logSineClockTransform`: one eta>0 exists such that every
0<delta<eta has a nonreal zero. The hypothesis that all zeros are real appears
only inside the contradiction proof; analyticity, finite order, evenness, nonzero
value at0, growth and convergence are all derived from the literal family.
The weighted-L1 clock convergence and uniform real-window convergence are proved.
The limiting sech transform forces an impossible entire continuation at z=i.
No experiment, approximate zero location, or variance/cumulant computation is used.

The separate exact-substitution scratch `/tmp/gta-quantile-transform.lean` also
exited0. It proves the base coordinate is injective with image exactly (0,1),
and the whole-line Jacobian identity F_delta(z)=H_delta(z/pi)/pi for the literal
reciprocal-profile quantile transform. Its proof uses no integrability assumption.

These proofs are being consolidated into `LogSineQuantileNonrealZeros.lean` with
an unconditional final theorem combining the nonreal zero, strict concavity,
strictly positive conductances and all finite shifted Hankel inequalities.
Final leaf and axiom audits remain to be run at this checkpoint. The existing
conductance leaf is being built only as the new leaf's required import.

The positive survivor of this obstruction is the already-proved exact positive
Stieltjes/Hausdorff moment representation of every conductance and every Hankel
square. This is stronger than isolated coefficient inequalities. It does not
control the spectrum of the singular pinned inverse. The next genuine source
obligation is constructing its nonreal eigenmode in L2, and the next GTA rigidity
obligation must use information beyond these moment inequalities. No theta
Euler-product, narrow-strip or large central-gap property has been supplied for
this test family. Do not claim this refutes theta arithmetic coupling.

Cycle6 final audit: `lake --old env lean
GaloisForLFunctions/RHTower/LogSineQuantileNonrealZeros.lean` exited0. The leaf has
351 lines and9 public declarations. SHA256
`d1c414c1c604d9c593811dcebe79390a666b95e954f44b801a8536fb9fead9df`.
Exact-copy `/tmp/gta-nonreal-axioms.lean` exited0; all9 public declarations report
only propext, Classical.choice, Quot.sound. Both audit logs contain an informational
ring-normalization suggestion, with no error or warning. Exact source prefix,
single umbrella import and absence of adjacent olean/ilean verified. Global lint
exited1 for foreign unreachable module
`GaloisForLFunctions.RHTower.CHMDStage2KleinGordonTransmutationAndTContourBochner`;
no owned leaf was flagged. All Lean jobs in this turn were sequential.
The new leaf supersedes the briefly created, never-built name
`LogSineClockNonrealZeros.lean`; only `LogSineQuantileNonrealZeros.lean` remains/wires.

### Cycle7 exact next target: literal pinned quantile eigenmode

Use the direct quantile operator with q_delta=1/h_delta; constructing an auxiliary
inverse-clock density is not necessary for this operator statement. This is the
same profile and pinned Volterra operator, not a replacement source.
For a zero z of the now-formalized F_delta, set on0<t<1
  J(t)=integral_0^t exp(i z Q_delta(s)) ds,
  g(t)=-exp(-i z Q_delta(t))*J(t),
  f(t)=-i z q_delta(t)*g(t).
Then g'=f-1 in the interior. Define g=f=0 at the endpoints. The intended theorem
constructs a nonzero f in complex L2(0,1) with mean1 and
  i q_delta C f=(-1/z) f,
where C is the literal pinned primitive. z!=0 follows from F_delta(0)=1.

Closed paper endpoint argument (formalization still required):
1. The existing lower profile bound gives t*q_delta(t)->0 as t->0+, and symmetry
   gives (1-t)*q_delta(t)->0 as t->1-. Positivity and interior continuity are proved.
2. Fix epsilon=1/(2*(1+|Im z|)). Choose a>0 such that q_delta(v)<=epsilon/v on
   0<v<=a. For0<s<=t<=a, integration gives
     0<=Q(t)-Q(s)<=epsilon*log(t/s).
   Therefore |exp(i z (Q(s)-Q(t)))|<=(t/s)^(1/2). The exact integral of this
   upper bound on0<s<t is2t, so |g(t)|<=2t. The argument also proves phase
   integrability at0. At1 use F_delta(z)=0 to replace the prefix J by minus the
   suffix integral and repeat with the symmetric endpoint. Thus |g(t)|<=2(1-t).
3. Consequently |f(t)|<=2|z|t*q_delta(t)->0 at0, and similarly at1. Both f and g
   extend continuously to[0,1]; g vanishes at the endpoints. Interior FTC plus
   the continuous endpoint derivative f-1 gives integral_0^1 f=1 and C f=g.
   f lies in L2 by continuity on a compact interval; mean1 proves nonzero.
   Algebra now gives the literal eigen-equation and a nonreal eigenvalue -1/z.
4. To construct a bounded compact operator rather than just its L2 eigen-equation,
   the kernel i*q_delta(t)*(1_{s<=t}-t) has squared L2 norm
     integral_0^1 q_delta(t)^2*t*(1-t) dt.
   Near0 the profile lower bound dominates this by a constant times
     1/[t*log(1/(pi*t))^2],
   whose integral converges (primitive1/log(1/(pi*t))). Reflection handles1;
   interior continuity handles the middle. This gives a genuine Hilbert–Schmidt
   pinned inverse, with no boundedness assumption on q itself.

This directly addresses the singular domain seam. Avoid reopening generic
self-adjoint spectral placement, variance estimates, or a density-factory detour.
Existing corpus `HedenmalmPinnedVolterraBoundaryDefect.lean` supplies C on L2 and
its exact pinned prefix. `HedenmalmCompactSourceEigenmode.lean` supplies an analogous
mode-to-operator bridge for PositiveDensitySource, but using it would require an
unnecessary source factory. Prefer reusing its Hilbert–Schmidt machinery with the
literal q, and prove the source's own endpoint data.

Anti-theatre/anti-laziness: this turn proves an exact counterexample to the bare
positive-Hankel criterion, not a theorem forcing theta onto the critical wall.
No external novelty assessment was performed, as instructed; no novelty relative
to literature is claimed. Existing LP classification/compactness is reused rather
than presented as new mathematics. The positive survivor is the exact conductance
moment representation. The harder theta-specific nonnormal coupling remains open.
No step was deferred for difficulty; next cycle closes the singular eigenmode
seam and then returns to the missing arithmetic constraint. GTA and RH goal stay ACTIVE.

Index refresh exited0; final diffcheck passed. Owned proof scratches removed;
audit/source-search evidence retained. All owned jobs terminal. Continuation memory:
`research/gta-log-sine-nonreal-zeros-2026-10-15` (supersedes clock-pole checkpoint).

Cycle7 in progress: created/wired `LogSineQuantileEndpoint.lean` (169lines).
Its needed-import build exited0, empty `/tmp/gta-mode-endpoint-dependency.log`;
final no-o leaf audit and exact-copy axiom audit still outstanding. It proves
literal q positivity/reflection/interior continuity, interval integrability,
clock difference/derivative/reflection, arbitrarily small tq near0, tq->0,
logarithmic clock-difference bound, and actual phase-difference half-power bound.
No heartbeat increase. `LogSineQuantileNonrealZeros.olean` built as needed import.

Scratch `/tmp/gta-mode-phase.lean` imports both leaves and now contains phase
integrability from the exact Jacobian, endpoint primitive bound, actual mode,
ODE derivative, zero-endpoint limits, reflection at a transform zero, compact
interval continuity, mean1 and pinned-prefix identity. Current compile runs under
handle85844 at this checkpoint; poll it to terminal before any next Lean job.
Earlier runs verified phase integrability and the endpoint norm bound after two
small corrections: intervalIntegral.intervalIntegrable_rpow' is namespaced;
IntervalIntegrable.congr uses uIoc, whereas integral_congr uses uIcc. Latest changes
use convert! for the complex derivative instance diamond and using! plus Pi.mul_apply
for the real limit instance diamond. No spectrum or RH claim from this scratch yet.

Cycle7 mode checkpoint: `LogSineQuantileEigenmode.lean` now exists and is wired.
Its final direct leaf audit exited0 with empty `/tmp/gta-eigenmode-leaf-audit.log`.
The actual vector in H=Lp complex2 unitIntervalMeasure has mean1, is nonzero, and
satisfies i*q*C f=(-1/z)f almost everywhere. The unconditional final theorem pairs
nonreal lambda with strict concavity, strictly positive conductances and every
finite shifted conductance Hankel inequality for all sufficiently small delta>0.
This closes the singular L2-domain obligation. Endpoint final no-o audit and
combined exact-source eigenmode/imported-endpoint axiom audit are still pending.

Next global operator closure: avoid logarithmic improper endpoint integrals by
using the already-proved exact base coordinate t0. Its universal sine inequality
implies cosh(u)*t0(u)*(1-t0(u))<=1/2. The Jacobian transforms the squared kernel
energy into cosh(u)*t0(u)*(1-t0(u))/(pi*D_delta(u)^2). Since D_delta(u)>=
1+delta*|u|/2>=min(1,delta/2)*(1+|u|), this is bounded by a constant times
(1+|u|)^(-2), integrable by the corpus's integrable_one_add_norm. This yields the
full Hilbert–Schmidt operator without pretending q itself is bounded. Reuse
pinnedSliceVec/continuous_pinnedSliceVec/norm_sq_pinnedSliceVec and kernelOperator
from HedenmalmHilbertSchmidtNorm and SoninTimeBandHilbertSchmidt.

Cycle7 audits complete: endpoint direct no-o audit exited0 with empty log, SHA256
4d05868eafa5088866782a8f23f54f0e9b425cf043811a0ebfc987a8a018d538 (169lines,13public).
Eigenmode direct no-o audit exited0 with empty log, SHA256
26fcd640e780dc158848bb8279335a74acf0c88aad86d70ad7ddfb6fe5903e57 (461lines,30public).
Combined `/tmp/gta-eigenmode-axioms.lean` has an exact eigenmode source prefix and
prints all30 eigenmode plus13 imported endpoint declarations. Exit0; all43 only
propext, Classical.choice, Quot.sound. Endpoint olean was built from the same
unchanged source and its final direct source audit passed. Global lint exit1 only
for foreign unreachable EvenSectorPolarRigidity, EvenSectorPolarStripCeiling,
EvenSectorPoleFreeNodeTests. No owned leaf flagged. No final index refresh yet.

The next full-operator scratch is `/tmp/gta-mode-energy.lean` (~250lines). The
kernel-energy proof already elaborates except one missing local positivity witness
and two redundant rings; those are now fixed. Its new operator section is untested.
The eigenmode leaf is being built into normal olean solely as this scratch's needed
import. Poll that build before compiling the energy/operator scratch. The latter
constructs the actual q-dependent field, L2 kernel, bounded Hilbert–Schmidt inverse,
pointwise pinned formula and true compact-operator nonreal eigenvectors.

Cycle7 COMPLETE at compact-operator level. `LogSinePinnedInverseCounterexample.lean`
(252 lines, 10 public declarations) constructs the literal bounded Hilbert–Schmidt
operator B_delta=i*M_q*C on L2(0,1), proves compactness, exact pinned-history action,
and actual nonreal eigenvectors. Every sufficiently small positive delta satisfies
strict concavity, positive conductances, all shifted Hankel forms, and nonreal
compact spectrum. No kernel energy or eigenmode-domain premise remains. This is
an unconditional counterexample to the bare conductance-Hankel spectral criterion;
it is not a theta counterexample. Positive survivor: exact positive conductance
moment representation remains valid but cannot determine directed coupling.

Final direct no-o leaf audit exited0, empty log at
/tmp/gta-counterexample-leaf-audit.log. Exact-source axiom audit exited0;
all10 public declarations use only propext, Classical.choice, Quot.sound.
Index and global lint both exited0 after the new leaf was wired. Earlier foreign
unreachable-module errors have disappeared. No full build or heartbeat increase.
The endpoint/eigenmode/compact trio has 53 audited public declarations.

Cycle8 OPEN: examine theta-specific mixed spectral feedback, not additional bare
profile inequalities. For a positive-frequency finite head N, set J=diag(n),
H=J^(-1/2) C J^(-1/2), K=J^(-1/2) S J^(-1/2),
u=J^(-1/2)1, v=J^(-1/2)Phi. The literal parity matrix is similar to
(1/pi)[[0,H-u v^T],[K,0]]. With T=K^(1/2) H K^(1/2),
a=K^(1/2)u, b=K^(1/2)v, the squared channel is T-a b^T.
Candidate (unproved): b^T p(T)^2 a>=0 for every real polynomial p and
actual theta finite head. This controls cross residues of the full boundary
feedback rather than conductance moments. If valid, the secular equation yields
real squared eigenvalues; finite physical spectra lie on real/imaginary axes.
Compact compression convergence plus the literal positive imaginary-axis
transform would exclude nonzero imaginary limits. Neither this theta sign nor
its finite-head universality is established. Need attack before conditional
formalization; generic Gram positivity and positive u,v do not suffice.

Corpus searches theta nonnormal feedback cross spectral residues / theta quotient
finite Fourier nonreal compression had complete source snapshots but no relevant
producer; many compiler statuses source_only. Read exact ThetaQuotientParityFeedback
source and confirmed both parity formulas, PSD Grams, stochastic centered row,
and retained rank-one feedback. No external search or numerical experiment.

Cycle8 algebra audit (paper, no new Lean theorem asserted): K is positive definite
for distinct positive frequencies by sine-function independence against the
strictly positive source density. For the normalized parity head and a nonzero
physical eigenvalue lambda, w=pi^2*lambda^2 lies in the spectrum of T-a*b^T.
For every distinct real eigenvalue t of symmetric T, the relevant signed residue
is r_t=b^T*E_t*a (spectral projection, not an arbitrary individual eigenvector
weight in a repeated eigenspace). The all-polynomial condition is equivalent to
r_t>=0 by finite Lagrange interpolation. If w is nonreal, the determinant lemma
implies 1+sum_t r_t/(w-t)=0, whose imaginary part gives
sum_t r_t/abs(w-t)^2=0. Nonnegative residues force every residue zero; the real
part then contradicts 1=0. Hence the finite physical eigenvalues lie on the real
or imaginary axis. Negative real squared eigenvalues need not be ruled out at
finite stages: positivity of the literal theta transform on the imaginary axis
can remove nonzero imaginary limiting eigenvalues. This avoids adding a needless
feedback-gain bound b^T*T^-1*a<=1.

Only finite similarities are used. Their constants may diverge with N; compact
convergence must concern the physical Fourier compressions, not a fictitious
bounded infinite H-u*v^T operator. Infinite u,v are not in l2. The existing exact
nonzero generalized eigenspace transfer in ThetaQuantileFourierQuotient.lean
was checked at lines395-497; it identifies actual quotient eigenvalues with
-1/z for XiC zeros and preserves algebraic multiplicity. This is infrastructure,
not the missing arithmetic sign producer.

A weaker sufficient local target is strict positivity of the signed resolvent
form b^T*((T-x)^2+y^2)^-1*a at relevant w=x+i*y, y!=0. At a transverse eigenvalue
this form is exactly zero. This is recorded as an alternative test of the same
directed coupling, not a proved assertion or a replacement of the GTA goal.
The sign must be derived from the actual theta source; generic Gram positivity,
conductance moment positivity, and a newly named passivity premise cannot supply it.
Deep search /tmp/gta-cross-residue-theory-search.json exited0, complete snapshot,
no applicable theta producer. It returned mostly unrelated spectral/rank-one
lemmas, rejected. No new formal conditional wrapper added.

Cycle8 new attack: the reference core may itself have infinitely many diverging
spectral levels. Let U_N,V_N synthesize sin(2*pi*n*F(x))/sqrt(n) and
(1-cos(2*pi*n*F(x)))/sqrt(n), n=1..N, into L2(dx) of source coordinate.
Then U_N^*U_N=K_N, V_N^*V_N=H_N and nonzero squared singular values of
A_N=V_N U_N^* are eigenvalues of T_N=K_N^(1/2)H_N K_N^(1/2).
On x,y<0 (CDF in(0,1/2)), its limiting kernel is
sum_n (1-cos(2*pi*n*F(x)))*sin(2*pi*n*F(y))/n
=pi/2 * 1_{y<x}. This follows from the sine sawtooth series; diagonal value
irrelevant. On each fixed finite interval[-L,0], bounded partial sine sums
and dominated convergence should give HS convergence to pi/2 times Volterra.
Thus each fixed singular value of A_N tends to infinity as N->infinity,
by first choosing a sufficiently long interval, then passing N->infinity.

If proved, nonnegative cross residues are IMPOSSIBLE for all sufficiently large
actual theta heads: positive residues interlace the spectrum of T_N-a_N b_N^T
with T_N, forcing a physical squared eigenvalue beyond its uniform norm bound
once the second reference eigenvalue diverges. Stronger survivor: above the
physical spectral bound, reference eigenvalues must be simple and their
residues alternate signs. Indeed p_M(t)>0 for real t beyond the entire physical
spectrum, r_j=p_M(t_j)/p_T'(t_j), and descending ordered t_j give alternating
signs. Repeated reference eigenvalues would persist under rank one and violate
the physical bound. Consequently number of negative cross residues diverges.
This is a PAPER CANDIDATE ATTACK, not yet verified; finish Fourier-kernel and
singular-value dependencies before declaring FALSE. No theta/RH conclusion.
Positive survivor would be compulsory infinite signed compensation inside the
nonnormal coupling, not a generic numerical countermodel. GTA stays fixed.

Cycle8 dependency-closed paper proof, replacing the unneeded global partial-sum
bound by Hilbert-basis convergence:
1. On H=L2(0,1), normalized sine modes s_n=sqrt(2)*sin(2*pi*n*t)
are an orthonormal basis of the reflection-odd subspace. If P_N is their first-N
projection, C*s_n=sqrt(2)*(1-cos(2*pi*n*t))/(2*pi*n). Hence the finite kernel
sum c_n(t)sin_n(s)/n is exactly pi*C*P_N. C is Hilbert–Schmidt, so
pi*C*P_N converges in operator norm to pi*C*P_odd (basis tail identity).
2. For I=[-L,0], R_I:H->L2(I,dx), R_I f=f(F(x)), is bounded because q is
bounded on F(I), a compact subinterval of(0,1). Its adjoint is
R_I^*g(t)=1_{F(I)} q(t)g(Q(t)); this follows from the exact CDF Jacobian.
Thus the source compression of A_N=V_N U_N^* equals R_I*(pi*C*P_N)*R_I^*.
Reflection sends F(I) to the opposite half. For x in I, the reflected input
contributes nothing to the prefix and the odd input has zero mean. Therefore
R_I*(pi*C*P_odd)*R_I^* g(x)=(pi/2)*integral_{-L}^x g(y)dy.
3. Split I into k adjacent intervals of common length ell=L/k. On each take the
normalized Haar function (+1 then -1)/sqrt(ell). These inputs are orthonormal;
their Volterra images are disjoint tents with squared norm ell^2/12. The limiting
compression expands their k-dimensional span by pi*ell/(2*sqrt(12)). Norm
convergence subtracts an arbitrarily small error. Extension by zero is isometric,
restriction contractive, so the same lower bound holds for the global A_N.
The dimension lemma for approximation numbers yields, for each fixed k>=1,
a_{k-1}(A_N)->infinity. This is a full limit, not just unboundedness: choose L
first to beat any target, then all N beyond the norm-convergence threshold work.
4. U_N,V_N are genuine maps into L2(dx): source sine/cosine-defect Gram formulas
prove the finite vectors square integrable. Their Gram matrices are K_N,H_N.
Polar decomposition (or finite AB/BA nonzero-spectrum identity) shows that
squared singular values of A_N are precisely eigenvalues of T_N. Their order
and multiplicities are preserved. Thus every fixed largest eigenvalue of T_N
diverges.
5. M_N=T_N-a_N b_N^T has the squared nonzero spectrum of pi*D_N. The original
finite Fourier compression D_N satisfies norm(D_N)<=norm(D), D compact/bounded.
Hence every eigenvalue of M_N has modulus<=R=pi^2*norm(D)^2, uniformly inN.
For real t>R, p_M(t)>0: real roots contribute positive factors, complex conjugate
pairs contribute positive squared moduli. Rank-one determinant identity gives
p_M(w)=p_T(w)*(1+sum_t r_t/(w-t)), with r_t=b^T E_t a.
A multiple eigenvalue t>R would persist in p_M, impossible. So each such t is
simple. In descending order t_1>...>t_j>R, p_T'(t_j) has sign(-1)^(j-1).
Evaluating the polynomial identity at t_j proves
(-1)^(j-1)*r_{t_j}>0. In particular the second large level has negative residue;
indeed the number of strictly negative residues tends to infinity.

Paper verdict for Cycle8 all-nonnegative-residue conjecture: FALSE. Positive
survivor: every fixed reference spectral level diverges, and exterior residues
are forced to alternate, with an unbounded number of negative residues. This
uses the actual theta CDF and physical compact inverse, without any zero-placement
premise. It does not prove RH. Generic Fourier, Volterra and rank-one tools are
parent theory; the actual singular-core/physical-feedback comparison is the new
internal conclusion. External novelty audit omitted by explicit user instruction.
Formalization now begins with the exact source Volterra kernel limit; full
spectral-divergence/alternation formalization remains required before closure.

Formalization checkpoint: scratch /tmp/gta-reference-kernel.lean defines finite
paritySinePartial, parityReferenceKernel, thetaParityReferenceKernel and proves
candidate exact left-half-plane Volterra step limit, including pi/4 on diagonal.
It imports existing SawtoothFourierSeries; source has exact conditional partial
sum convergence, NOT a uniform bound on partial sums (its similarly named bound
controls the LIMIT only). Do not confuse these. Lean run handle48678 is still
live at this checkpoint; log empty. Never start a second Lean before terminal.

Implementation refinement: for spectral lower bounds only finitely many packet
matrix entries are needed. Strong Fourier projection convergence plus continuity
of C suffices; no new operator-norm/HS convergence theorem or global uniform
sawtooth partial-sum bound is needed. Pull back compactly supported source input
and output packets with q weights; inner products against pi*C*P_N converge by
HilbertBasis.hasSum_repr. Disjoint mean-zero Haar inputs have disjoint primitive
tents. Finite entry convergence is uniform on their fixed finite-dimensional
span, giving the same approximation-number lower bound. This removes an
unnecessary technical dependency while preserving the full theorem.

Kernel scratch passed (handle56718 terminal0, empty /tmp/gta-reference-kernel.log).
Corrections: Finset.sum_div rewrites a divided sum forward; explicit ht.1/ht.2
for linear arithmetic; avoid convert on the entire Tendsto proposition and
rewrite the scalar limit instead. No heartbeat changes. The needed normal olean
for ThetaQuotientParityFeedback was built, exit0 empty log.

Current scratch /tmp/gta-reference-core.lean extends the kernel proof with actual
L2(dx) sine and cosine-defect vectors, their exact S/C Gram identities, and the
finite rank-one sum thetaParityReferenceOperator with full bilinear readout.
Its compile has just started; poll its owned handle before any next Lean.
The new file is not yet in the tree or umbrella. Full divergence/alternation
formal proof remains outstanding; do not report the no-go as Lean-complete.

Paper-proof simplification: strict positive definiteness of K_N is NOT required.
Use finite AB/BA characteristic identities. M=K^(1/2)(H-u v^T)K^(1/2)
has the same characteristic polynomial as (H-u v^T)K, including zero roots;
nonzero square roots give eigenvalues of the physical parity block. Similarly
A_N A_N^*=V_N K_N V_N^* has exactly T_N's positive eigenvalues through
S=V_N K_N^(1/2), SS^* and S^*S. PSD Gram matrices suffice. Avoid implementing
an unnecessary independence/inverse theorem.

An easier packet family for the formal lower bound: each source packet consists
of three consecutive intervals of length ell. Input is (+1 on first, -1 on third)
/sqrt(2*ell); output is 1 on middle/sqrt(ell). Input/output families separately
orthonormal; each input has zero integral. The Volterra primitive on the middle
is sqrt(ell/2), and every other packet contributes zero. Thus the finite readout
matrix tends to (pi*ell/(2*sqrt(2))) times identity. Use Bessel to turn this into
uniform expansion, then approximation-number dimension bound. No tent-square
integral or explicit Volterra singular functions needed. Target unchanged.

`ThetaParityReferenceCore.lean` is now written and wired (225 lines,26 public
names including the type abbreviation). Final direct no-o leaf audit exited0,
empty /tmp/gta-reference-core-leaf-audit.log. Exact-source axiom audit exited0;
26 reports, no axioms outside propext/Classical.choice/Quot.sound.
SHA256 f5be6fc5eedcfc17113dd5c42f411517ca29a1a7a1abd372c08f41d9c1546de3.
One umbrella import, no adjacent olean/ilean artifacts. Index/lint running.
Actual declared operator on unweighted L2(dx) retains all finite sine/cosine
features, with exact S/C Gram identities. No spectral-divergence declaration yet.

Current next scratch /tmp/gta-reference-fourier.lean (not yet verified) defines
parityPrimitive=(pi/2)*C*(1-R), its symmetric Fourier truncations, strong and
bilinear convergence, reflection on Fourier modes, and exact literal-source
Fourier readout of quantileUnitary. Compile handle52882. Poll to terminal before
next Lean. Remaining work: identify the finite source bilinear sum with these
truncations; prove exact three-interval packet response; obtain uniform
finite-dimensional expansion and every approximation-number divergence; then
finite square-core/characteristic comparison and exterior residue alternation.
SourceSpace thetaSource=L2(k^-1 dx) has integrable_sourceSpace for every vector;
its quantileUnitary and integral_quantileTransform supply the needed CDF change
of variables. Indicator packets belong to this weighted space because k is
positive continuous on their compact supports. L2.inner_indicatorConstLp_indicatorConstLp
and the source measure's compact finiteness are useful, already located.

Formalization simplification: existing ThetaQuantileFlatNormalForm already supplies
flatLp f=normalized(x)*f(F(x)) in unweighted L2 and preFlat for every bounded
compactly supported measurable source field. This gives the cleaner exact identity
<flatLp g,A_(N+1) flatLp f>=<g,parityFourierTruncation N f>, without introducing
weighted SourceSpace packets or new CDF-pullback operators. Scratch now proves
paired Fourier modes and attempts this identity; its first full run had four
local elaboration issues, now corrected. Full reference divergence and alternating
residues are still paper-only. Needed core olean built successfully. Search
/tmp/gta-packet-volterra-search.json complete snapshot; returned unrelated Volterra
upper bounds and unrelated source packets, no missing spectral lower-bound producer.

Fourier scratch now passes with empty log (37352 exit0). Written and wired
ThetaParityReferenceFourier.lean, 222lines/21public, SHA256
38b50ce981028c84dcecf3afd5c4cf63abebf4fb719e50ee817a1f61bc85d02a.
Needed-import olean build36434 exit0. Final no-o/axiom audits still pending.
Packet scratch now proves the exact source primitive pairing, negative-support
Volterra limit, and attempts the full arbitrary-i,j three-interval matrix limit.
Latest compile49432; poll terminal before next Lean. No full spectral result yet.

Further lower-bound simplification (paper): orthonormal packet Gram calculations
are unnecessary. The existing eventually_quadForm_sub_diagonal_le and
sq_pi_norm_le_sum_sq apply to the finite packet matrix converging to
c*identity, c=pi*l^2/2. They yield Re<Vx,A_N Ux> >= c/2*||x||_sup^2.
Individual interval norms give ||Ux||<=2*k*sqrt(l)*||x||_sup and
||Vx||<=k*sqrt(l)*||x||_sup. Thus A_N expands range(U) by
pi*l/(8*k^2) for all sufficiently large N. The same positive form proves U
injective, so range(U) has dimension k; no independent sine independence or
packet orthogonality proof is needed. The existing approximation-number
dimension lemma now gives every fixed approximation number diverging by choosing
l arbitrarily large. Constants deliberately unoptimized. Search
/tmp/gta-packet-minmax-search.json found the needed finite-form stability theorem;
read EventualNegDefFromEntrywise and DiagonalNegativeMargin sources directly.

Packet scratch passed, including norm bounds (98540 exit0, empty log).
ThetaParityReferencePackets.lean written/wired, 362lines/29public, SHA256
ba98927731ee03769bcf53cfbee427bfa4100a36d8acd12a0808b1946e27f410.
Needed-import build98322 is live; poll before next Lean. Its main theorem
`tendsto_thetaParityPacket_matrix` proves the literal arbitrary-i,j source matrix
limit pi*l^2/2 times Kronecker delta. The input bound is 2*sqrt(l), output norm
exactly sqrt(l). Final no-o and exact-source axiom audits pending for both new
Fourier/packet modules. `/tmp/gta-reference-divergence.lean` now contains the
complete attempted proof of all fixed approximation-number divergence, not yet
compiled. It imports the packet module plus existing finite-form stability and
approximation-number dimension bound. Do not claim divergence as Lean proved yet.

ANALYTIC DIVERGENCE NOW PROVED IN LEAN. Scratch20589 exited0; only an unused
simp argument remained, removed in the written module. New wired
ThetaParityReferenceDivergence.lean,184lines/2public,SHA256
ea06a340989ff5c64e5fdfbce7ed68df024a67cbba651feb5da0d5bf43f50496.
The unconditional theorem `tendsto_thetaParityReference_approxNumber_atTop (n)`
proves every fixed approximation number of actual A_(N+1) tends to infinity.
No zero-placement, residue-sign, packet-rank, or source-regularity premise remains.
Direct no-o source audit65808 live. Combined exact-source audit prepared at
/tmp/gta-reference-divergence-axioms.lean: source prefix is divergence leaf,
prints all78 public declarations in Core/Fourier/Packets/Divergence. Still need
final direct Fourier/Packets audits and combined axiom run after65808 terminal.
Index78669 exited0; lint started. Source diffcheck clean.

Hard next dependency stays actual finite spectral feedback comparison, then
strict exterior residue alternation and unbounded negative-residue count. These
remain dependency-closed paper results, not yet Lean claims. Divergence alone is
not critical-wall selection and not RH. It makes the singular-reference side of
the nonnormal cancellation obstruction unconditional. The parent Fourier,
finite-form stability, and dimension arguments are existing mathematics; external
novelty remains unassessed by user instruction. No pivot from GTA.

FINAL ANALYTIC AUDITS COMPLETE. Direct `lake --old env lean <leaf>` no-o audits
for all four Core/Fourier/Packets/Divergence modules exited0 with empty logs.
Combined exact-source axiom audit exited0: exactly78 expected public names, only
propext/Classical.choice/Quot.sound. Exact source prefix, source hashes, one
umbrella import each, and absence of adjacent olean/ilean verified. Index exit0;
lint exit1 only two foreign unwired modules:
CHMDStage7HyperbolicCoshFactorizationAndEvenSubblindDecomposition and
OddSectorAnyPoleWeightJointRigidity. No owned GTA leaf flagged. Diffcheck clean.
Obsolete owned proof scratches and redundant unrun axiom files removed; retained
/tmp/gta-reference-divergence-axioms.lean and all audit logs. No live owned jobs.

Next finite comparison can use normalized physical parity modes
(e_n+e_-n)/sqrt(2), (e_n-e_-n)/sqrt(2). Their block matrix is
(1/pi)[[0,(C-1*Phi^T)J^-1],[S J^-1,0]]. Diagonal finite similarity by J^(1/2)
gives [[0,H-u*v^T],[K,0]]/pi. AB/BA gives the square-core characteristic identity
without any inverse of K. Positive reference spectrum comes from S=V*K^(1/2),
SS*=A_N A_N*, S*S=T_N. Preserve multiplicities and finite indexing; no bounded
infinite similarity is claimed.

For exterior determinant positivity, complex-root factorization is unnecessary:
real p_M(t) has no zeros for t>R, is continuous, and is eventually positive by
its monic leading coefficient. Intermediate value theorem gives positivity on
the whole exterior interval. Rank-one characteristic identity can be derived
for invertible wI-T then extended as a polynomial identity; evaluate at exterior
reference roots. Repeated roots would persist after rank one, contradiction.
Simple descending roots give alternating derivative signs and thus residues.
These are next exact formal obligations, not hypotheses to wrap the RH goal in.

Honesty/anti-theatre audit: actual analytic frontier moved unconditionally. Parent
Fourier/Volterra/finite-form/min-max theory was reused, not claimed novel. External
novelty audit omitted by explicit user instruction. No numeric experiments or
estimate tuning. Remaining critical-wall selector is unproved; this result closes
an analytic dependency of compulsory directed cancellation, not RH. GTA and the
long-term goal remain active. Current turn classification: progress.

Continuation after verified divergence: previous turn classified PROGRESS.
Objective attachment and hgtl7 reread; architecture/testing docs absent. GTA fixed.
Search /tmp/gta-finite-square-search.json complete snapshot; mostly unrelated
root-block/rank-one candidates, no ready actual finite square-core comparison.
Search /tmp/gta-compression-bound-search.json partial but usable snapshot; found
standard compression norm machinery, no directed theta sign producer.

First finite target: actual parity head matrix has eigenvalues bounded uniformly
by ||thetaQuotientOperator||. Use unnormalized physical parity vectors
v_(+,n)=e_n+e_-n, v_(-,n)=e_n-e_-n with Gram2I; no square-root normalization or
finite basis inversion is needed. Their operator matrix pairings equal twice
B_N=(1/pi)[[0,(C-1Phi^T)J^-1],[S J^-1,0]]. For B_N x=lambda*x, synthesize f=sum x_i*v_i.
Gram2I proves f nonzero and <f,Df>=lambda*<f,f>. Cauchy–Schwarz and boundedness
of D imply |lambda|<=||D||. This is a dependency-closed paper proof of the actual
finite head bound, not a new spectral-placement assumption. Next transfer through
finite diagonal similarity and Matrix.charpoly_mul_comm (verified in source)
to the normalized rank-one square core. CFC.sqrt with MatrixOrder supplies the
PSD square root; strict K positivity is still unnecessary.

Finite proof refinement: residue alternation only needs absence of positive real
roots of p_M above R, not a full complex-root modulus theorem for M. Keep K,H,Q,
T,M real. From a real exterior root t>R>=0, AB/BA gives a real eigenvector of
F*K (F=H-u*v^T). With z=sqrt(t)>0, (v,Kv/z) is an eigenvector of the real block
[[0,F],[K,0]] with eigenvalue z. Multiplying by the positive finite diagonal
sqrt(J), then complexifying coordinates, gives an eigenvector of the literal
physical head with eigenvalue z/pi. Its already-targeted uniform bound yields
t<=pi^2||D||^2, contradiction. This proves exactly the exterior exclusion needed
for positivity and alternation, avoiding unnecessary complexification of the
square-core characteristic polynomial. Full survivor unchanged.

Current scratch /tmp/gta-parity-head.lean: definitions of literal complex parity
head/modes; Gram2I; exact operator pairings; a private finite-compression Rayleigh
bound; actual head eigenvalue and characteristic-root bounds. Not compiled yet.
Name/API scratch /tmp/gta-parity-check.lean first run caught unconstrained
universe levels in @have checks and a nonexistent mulVec_vecMulVec name. Fixed
have universes explicitly and removed the unused nonexistent name. Corrected
check build6887 live; poll terminal before first head proof compile.

Finite-head checkpoint: /tmp/gta-parity-head.lean run95488 terminal exit0,
empty log. Actual Gram2I, quotient-operator pairings, uniform eigenvalue/root
bounds all compiled. Promoted to ThetaParityFiniteHead.lean and wired once.
Needed import olean next; final direct/axiom audits still pending.
Rank-one sign deep search complete snapshot but no applicable determinant lemma;
lexical det/vecMulVec query used next.

Directed-square checkpoint: /tmp/gta-parity-square.lean run21825 terminal exit0,
empty log. Actual normalized Gram cores K,H, PSD square root Q, T=QHQ,
M=T-ab^T=Q(H-uv^T)Q; AB/BA charpoly identity; finite weighted eigenvector
transport; no positive real charpoly root above R=pi^2||D||^2; p_M(t)>0 for
all t>R. All compiled without K inverse, residue sign premises, or added axioms.
Promoted ThetaParityFeedbackSquare.lean, wired once. Needed import build and
final source/axiom audits pending.

Next scratch /tmp/gta-parity-residues.lean uses corpus singular determinant lemma
bgv_det_diagonal_add_vecMulVec from HTGeometry/BorisovGabberVasiuDeterminant.lean.
Target exact secular expansion in the real reference eigenframe, exterior
simplicity and strict sign (-1)^#{higher eigenvalues} r_i>0. Not compiled yet.
Reference spectrum search complete snapshot: approxNumber_eq_singVal available;
no actual A_N/T_N comparison found. A possible finite transfer is A A*=S S*,
S*S=T, S=V Q. Positive energy eigenvector e with A*A e=mu e maps to
w=S*A e with T w=mu w and ||w||=mu||e||. This preserves multiplicity via
inner products, avoids K inverse, and can transfer arbitrary finite divergent
energy eigenspaces to T. That comparison remains unformalized.

## User correction: selector only

User explicitly rejects further constraints, side no-go formalization, and
auxiliary milestones as next deliverables. Goal resumed ACTIVE. Sole accepted
next mathematical deliverable is the actual unconditional GTA critical-wall
selector with complete proof and Lean verification. Residue-alternation and
reference-level transfer work is PARKED, not completed or retired. Build73807
for ThetaParityFeedbackSquare exited0; no owned Lean process remains. New head
and square module final audits remain pending; no additional Lean is launched
until a dependency-closed selector proof is available.

Selector context: literal transverse quadratic remainder is
HS(D)^2-Re tr(D^2)-nonnormalSchurEnergy. Existing exact Fourier-current coordinate
is J(a,b)=2Re(xi'(1/2+a+ib)*conj(xi(1/2+a+ib))). Corpus already identifies
nonnegativity for all 0<a<1/2,b real with RH. This equivalence is not a producer.
Direct source expression is 16 integral_(u,t>0) u sinh(2au)
phi(u+t)phi(u-t) cos(2bt). Actual source prime-Gamma-pole Ward equation and
all-product-fibre summation are available. Individual completed fibre positivity
is already false; theta source equation alone gives no signed-energy sign.
Target now an actual source proof of J>=0 (or equally strong direct transverse
mode exclusion), not another named hypothesis or necessary condition.

## Cross-route corpus search requested by user

Selector remains sole mathematical deliverable. User requested corpus search for
unconventional reuse of other routes. No new conditional Lean module was added.
Deep searches covered transverse selection, Fourier positivity, Doob cancellation,
odd supersolutions, positive extension, deletion-current closure, positive
commutators, and prime-harmonic admission. Exact lexical searches supplemented
them. Results are `/tmp/gta-crossroute-*-search.json` and
`/tmp/gta-crossroute-*-lexical.json`. Initial two deep requests completed; most
subsequent deep requests reported partial coverage. Index reports source snapshot,
background refresh, and many source-only compiler records. Proposed ingredient
sets are not proofs; several incorrectly connect positivity or vanishing of
different quantities. Actual source statements were checked instead.

Useful imports, with exact applicability:

1. `WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean:689` proves the full
   source identity `markovEnergy(Phi*v) = E_Gamma(v) + E_prime(v) -
   integral Phi(x)*cosh(x/2)*v(x)^2 dx`, for compact C2 real v. Both jump energies
   are nonnegative. Unlike the earlier GTA diagonal Ward energy, this includes
   the actual nonlocal Gamma cross terms. `XiSliceHusimiHeatDictionary.lean:37`
   proves Phi is exactly thetaCuspFullSource. The sharp pole-mass domination on
   all odd tests is still RH-equivalent, not established by this identity.

2. `EulerDeletionMixedCurrentGram.lean:342,383` proves strict signed current for
   every nonzero finite complex mixture at an off-wall actual zero, retaining all
   cross terms. Current vanishes iff the zero is critical or every coefficient
   is zero. This is a usable transverse detector. The attempted shortcut from
   zero landing fails: `EulerDeletionReflectedChronologicalCurrent.lean:176`
   annihilates only the imaginary current; the real current is a surviving
   chronological remainder. No GTA identity forcing that real current to zero
   was found. Also ordinary theta prime deletion has multiplier (1-p^-s), whereas
   pole-clearing Dirichlet deletion has (1-p^(1-s)); they cannot be silently
   identified. A translated theta source Phi-sqrt(p)*Phi(.+log p) has the latter
   bilateral Laplace multiplier by the existing translation formula; this
   algebraic observation does not identify their quadratic currents.

3. `HedenmalmGammaSewnRouteRKreinGaugeBridge.lean:180` proves the actual signed
   marked prime sequence is summable iff centered grade t=0. At t!=0 its charge
   is -sign(t)/p modulo l1; the Route R/Hedenmalm charges differ by the bounded
   invertible Fisher gauge p^2/(p+1)^2. Potential selector mechanism: derive this
   precise summability from GTA eigenmode admission. No such derivation found.
   Compactness alone supplies none. The positive marked energy diverges even at
   t=0, so retain the signed difference. Product-continuous linear landing is
   already excluded by XiShiftedHankelBoundaryCoronaLandingNoGo.

4. `HTGeometry/PrimeHarmonicEulerFormationTangent.lean:595` supplies an actual
   Euler Haar-frame trichotomy: neutral tilt -> nonzero Haar frame; positive tilt
   -> zero trace norm; negative tilt -> divergent end-window norm. This is a
   route-independent dynamic selection mechanism, but a GTA mode-to-frame
   comparison preserving its normalization is not supplied by the theorem.

Rejected ready-made handoffs: CCM real Fourier zeros require a simple odd ground
with specific frequency and eta, not arbitrary GTA eigenmodes; Sonin positive
all-prime operators still require their all-moment source weld; Deninger Hodge
purity assumes positive flow-compatible Hodge data and Xi inclusion. FZZ positive
Gram feedback is blind on its coupling kernel. None is an unconditional GTA
selector, and no further no-go formalization is authorized as next deliverable.

Verification: `/tmp/gta-crossroute-candidate-audit.lean`, run with
`lake --old env lean` (no output object), exited 0. Six exact imported declarations
checked, each #print axioms only propext/Classical.choice/Quot.sound: Doob full
identity; mixed-current strict sign and nullspace classification; Route R/Fisher
charge equality and summability iff; CCM finite odd-ground real-zero theorem.
Log `/tmp/gta-crossroute-candidate-audit.log`. This checks reusable imports,
not a new selector proof. No owned Lean process remains.

Assessment: useful existing knowledge recovered; no new mathematical theorem or
critical-wall selector established. Continue with actual source coupling using
these identities; do not resume parked residue-alternation work or replace the
missing construction by a named positivity/admission hypothesis.

## Actual-mode transfer audit after cross-route search

Continuation classification: progress on the requested corpus investigation and
verification; no new selector proof or new mathematical theorem. Goal stays
ACTIVE. No external-input blocker. User's selector-only restriction still holds.

Completed deep searches (all returned partial=false):
`/tmp/gta-mode-prime-intertwiner-search.json`,
`/tmp/gta-anomaly-cyclicity-search.json`,
`/tmp/gta-coupled-positive-commutator-search.json`, and
`/tmp/gta-formation-strictness-search.json`. Coverage is a source snapshot with
many pending compiler records; generated ingredient sets sometimes combine
unrelated algebraic declarations and are not proofs. All search jobs terminated.

Tested the literal mode-to-prime-frame handoff rather than assuming its tilt.
The actual source mode satisfies
`f_z' + i*z*f_z = i*z*phi`, `integral f_z = M` at a Xi divisor, and
`(B+1/z) T_p f_z = r_p`. Here `T_p f(x)=p^(-1/2) f(x+log p)` and
`r_p(x)=i*p^(-1/2)*integral_[x,x+log p] phi` is nonzero and identical for the
two reflected divisor modes. On Haar L2, change of variables gives
`||T_p f_z||^2 = p^(-1)||f_z||^2`: this marginal has no transverse tilt.
The frame theorem uses clock log(log p)-L, whereas literal translation uses
log p. Neither the required clock comparison nor a phase-sensitive grade
identification follows from the norm formula. This does not exclude other
coupled transfers; it invalidates treating the literal marginal as that transfer.

Existing source code settles the relevant carrier facts: the anomaly leaves
the original reciprocal-theta compact fibre but belongs to Haar L1 and L2;
its complete real-translation orbit is Haar-L2 cyclic. The exponential
critical rigging makes all strip evaluations continuous and integer shifts
contractive, yet its normalized character energy already exceeds one at z=i/4.
That example is not asserted to be a Xi zero. Thus ambient contractivity does
not itself prove the needed half-density inequality for actual divisor modes.
No new carrier/no-go module was added.

Additional exact cross-route coupling recovered:
`HedenmalmThetaXiMassConnectionGreenCompensation.lean` identifies the phase-linear
sum of the polarized theta Green packet and ordered half-density prime
connection with archimedean terms minus prime-square/higher-power terms.
This sum is unconditionally bounded on positive vertical time lines.
`HedenmalmThetaXiMassCompensatedAsymptoticCarrier.lean` gives its exact two-residue
future carrier. `XiHeatCassiniWoldThetaGreenCompensation.lean` proves that removing
the finite Euler trace leaves the same carrier. These are genuine GTA/arithmetic
identities, but a bounded sum permits cancellation of unbounded summands;
they do not supply the separate current bound that selects the wall.

`DirectSubunitEscapeCapacityFusion.lean` does not close that gap: its own exact
formation-relative law includes a non-summable completion companion. The
remaining primitive source sequence is summable only after subtracting that
companion. `IntegralCurvedTateCoherentPrimitiveIndex.lean` identifies coherent
primitive existence with RH, rather than constructing the primitive. Do not
promote either statement into an unconditional selector.

Verification: `/tmp/gta-coupled-transfer-audit.lean` imported four existing
modules and checked seven exact declarations with `#print axioms`.
`lake --old env lean /tmp/gta-coupled-transfer-audit.lean` exited 0; log
`/tmp/gta-coupled-transfer-audit.log`. Every printed axiom list was exactly
propext/Classical.choice/Quot.sound. Objects existed and were newer than sources;
this was an import audit, not a rebuild of all source dependencies. No owned
Lean process remains; no Lean source or umbrella was changed in this continuation.

Next live mathematical attack: evaluate the full Gamma/prime/pole quadratic
identity on the actual paired divided-source modes, with cutoff removal proved,
and compare it to the strict mixed Euler-deletion current. The target is an
actual identity forcing the real transverse current to vanish, not another
assumed positivity, boundedness, or completion property. No such identity has
yet been derived. Keep the common forcing and every mixed term throughout;
zero imaginary current, unit reciprocal charge, and bounded compensated current
do not give zero real transverse current.
