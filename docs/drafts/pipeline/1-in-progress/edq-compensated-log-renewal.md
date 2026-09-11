# EDQ: compensated logarithmic renewal

Status: the exact renewal and positive linear forcing-energy bounds are
[formalized in Lean](../3-formalized/edq-log-prime-forcing.md). The further
relative-cancellation limits below are paper consequences. RH and the complete signed upper
bound remain open. This card tests the proposed estimate that the harmonic
correction in prime-dilation feedback is negligible. It does not retire EDQ.

## Actual source and hard target

On the positive ray put

```
phi_n(u) = fract(u/n)/u,
b_n(u) = phi_n(u)-phi_1(u)/n,
G_N = sum_(n<=N) mu(n)*b_n,
H_N = sum_(n<=N) mu(n)/n,
J_N = sum_(n<=N) mu(n)*log(n)*b_n,
D_q f(u) = f(u/q)/q.
```

The b_n vanish below 1 and have the original compensated physical norm.
Their exact dilation law is `D_q b_n=b_(qn)-b_q/n`. Consequently

```
J_N = -A_N-B_N,
A_N = sum_(2<=q<=N) Lambda(q)*D_q G_floor(N/q),
B_N = sum_(2<=q<=N) Lambda(q)*H_floor(N/q)*b_q.
```

This follows from `mu*Lambda=-mu*log` by finite hyperbola interchange.
The correction involves all earlier H-values; small H_N does not bound it.
The exact logarithmic history equation for G_N retains A_N+B_N together.
The open estimate is a cofinal subpower bound for its resulting complete
signed Gram sum, equivalently a sufficient ceiling for the original source.

## Conjecture tested: B_N has subpower energy

The following formalized argument instead gives constants c,C>0 with
`c*N <= ||B_N||^2 <= C*N` eventually. These inequalities concern B_N,
not G_N. The Lean statement retains its literal coefficients and physical norm.

Write `a_N(q)=Lambda(q)*H_floor(N/q)`. The elementary bound `|H_m|<=2`
follows by applying the complete residue-sum bound at the initial endpoint:
`|m*H_m-1|<=m` for m>=1; H_0=0. With `psi(x)<=Cpsi*x`, this gives

```
sum_(q<=K) |a_N(q)| <= 2*Cpsi*K,
R_N := sum_(q<=N) q*|a_N(q)| <= 2*Cpsi*N^2.
```

Finite Abel summation then bounds
`sum_(q<=N) |a_N(q)|/sqrt(q) <= 4*Cpsi*sqrt(N)`.
The existing generator bound `||b_q||^2<=2/q` gives the upper energy bound.

For the lower bound retain the literal periodic cell mean

```
m_N = (S_N-T_N)/2,
S_N = sum_(q<=N) Lambda(q)*H_floor(N/q)
    = sum_(d<=N) mu(d)/d * psi(N/d),
T_N = sum_(q<=N) Lambda(q)/q * H_floor(N/q).
```

PNT gives `psi(N/d)/N -> 1/d` for each fixed positive d. The hyperbola
summands divided by N are bounded absolutely by `Cpsi/d^2`, so dominated
series convergence gives `S_N/N -> c2=sum_(d>=1) mu(d)/d^2`.
This constant is positive without a numerical evaluation: retaining d=1,2
and bounding all d>=3 by `1/[d(d-1)]` gives `c2>=1/4`.
Also finite Abel summation gives
`|T_N|<=2*Cpsi*harmonic(N)<=2*Cpsi*(1+log(N))`.
Thus `m_N/N -> c2/2>0`.

The existing, physical-weight-preserving window theorem states
`|m_N|^3 <= 8*R_N*||B_N||^2`. Together with the preceding estimates it
gives the claimed positive linear lower bound. No period average replaces
the physical norm; the mean is used only through that proved inequality.

## Consequence for the attack

Discarding B_N or estimating it as a subpower error cannot prove the
compensated feedback inequality. The remaining attempt must estimate the
joint signed contribution of A_N and B_N. Its upper bound is not obtained
by the preceding size theorem, and no RH proof is claimed.

There is a further positive consequence on paper, using the already
formalized bound `primitiveEnergy_factorial_rate` with logarithmic order
six. It gives `||G_k||<=C*sqrt(k)/(log(k))^3` for all sufficiently large k.
After enlarging C there is also a global bound `||G_k||<=C*sqrt(k)`.
Finite vector-valued Abel summation gives the exact identity

```
J_N = log(N)*G_N
    - sum_(1<=k<N) log((k+1)/k)*G_k.
```

Since `log((k+1)/k)<=1/k`, splitting the sum at sqrt(N) bounds its
first part by `2*C*N^(1/4)` and its second by
`16*C*sqrt(N)/(log(N))^3`, up to harmless endpoint constants.
The first term is at most `C*sqrt(N)/(log(N))^2`. Thus
`||J_N||/sqrt(N)->0`. With the lower bound for B_N and the exact renewal,

```
||A_N+B_N||/||B_N|| -> 0,
||A_N||/||B_N|| -> 1.
```

These relative limits are paper consequences, not additional Lean
theorems in the current module. They identify compulsory leading
cancellation. They do not improve the power of N in the known estimate
for G_N or control the residual signed history at the RH threshold.

## Search and transfer audit

Five broad OR-matched deep/method searches covered logarithmic cutoff
history, prime-dilation adjoints, signed Tauberian energy, recurrence
bootstrap, and Mangoldt harmonic convolution. Each used a 120-second
budget, two rounds, all retrieval views, and no per-module cap. All were
partial at generation 823349 with pending coverage; retrieval or judging
was interrupted or timed out. The history search also reported unavailable
Qdrant. Candidate metadata was predominantly `source_only`; the history
lane included a stale source, and the compensation lane included a stale
compiler snapshot. Proof-idea and ingredient sets were empty. These results
are not an exhaustive absence certificate. The ingredients used in the
proof are checked in the actual Lean scratch file.

Bernstein--Szego contraction candidates require terminal-vector
orthogonality that has not been established for the actual Mobius source.
Cayley energy candidates concern a constructed dissipative orbit, without
an identification with the cutoff sequence. The signed hyperbola/Tannery
mechanism does apply to the literal coefficients above and supplies their
nonzero mean limit.

A broad newest-first arXiv search for `avalanche` led to
[Janssens--Moll--Schindler, arXiv:2609.08666v1, 8 September 2026](https://arxiv.org/html/2609.08666v1).
Its analytic majorization argument assumes positive charge weights and
independent uniform cluster positions; it reduces a sum of squared
normalized weights. The signed physical Mobius Gram has neither premise.
No source-energy upper bound follows from that argument. Searches for
`majorization` and `dissipation` supplied no applicable transfer; the direct
arXiv majorization endpoint was rate-limited.

The earlier frozen logarithmic gcd protocol concerns its stated
compensated Gram identity, not the uncorrected raw prime-feedback identity.
It was never executed. The user's subsequent **no computations** instruction
excludes executing it; experimental execution is no longer pending work.

## Signed-history and first-tail estimate audit

**No new arithmetic ceiling.** The following paper attempts do not improve
the known exponent, close RH, or retire EDQ. They identify the exact terms
left by three proposed estimate mechanisms. No new Lean module is claimed.

**Convex history → retained forcing.** For N>1 finite Abel summation gives

```
w_k = log((k+1)/k),
Gbar_N = sum_(1<=k<N) w_k*G_k/log(N),
G_N = Gbar_N + J_N/log(N) = Gbar_N-(A_N+B_N)/log(N).
```

The history weights are positive and sum to one. This suggests importing
the history-plus-resolvent estimate in
[Fritz, Threshold dynamics for subdiffusive grain growth, 7 September 2026](https://arxiv.org/pdf/2609.07938).
Propositions 3.2--3.4 use a convex Caputo history and the actual Helmholtz
equation `(a I-Delta)u=a fbar`; testing that equation against u gives its
L2 contraction. The EDQ Abel identity supplies neither that operator
equation nor its accretivity. Its source term is the exact joint packet
`-(A_N+B_N)/log(N)`. The already proved linear size of B_N cannot be
charged as a subpower forcing allowance. This transfer leaves the joint
signed estimate open; it does not exclude a different eventual dissipative
construction derived from the actual source.

**Zero-mass Green form → terminal energy retained.** Put
`u_n=mu(n)*b_n`, `t_n=log(n)`, `T=log(N)`, and `E(k)=||G_k||^2`.
The complete logarithmic Gram is exactly

```
L(N) = sum_(m,n<=N) max(t_m,t_n)*<u_m,u_n>
     = T*E(N)-sum_(1<=k<N) w_k*E(k).
```

Indeed, replace each maximum by T minus the sum of w_k over
`max(m,n)<=k<N`, then interchange the finite sums.
[Hossein et al., Clustering versus sorting, 30 August 2026, section 5.1](https://arxiv.org/html/2608.29679v1)
uses a Neumann Green form that is negative on zero-total-mass competition
modes. That sign suggests adjoining the vector `-G_N` at terminal location T.
The enlarged EDQ source then has total vector mass zero, but its quadratic is

```
Q_aug = L(N)-T*E(N) = -sum_(1<=k<N) w_k*E(k).
```

Both terminal cross terms and the terminal self term have been included.
Thus the nonpositive augmented form returns the existing history identity;
recovering the original source restores the unknown `T*E(N)`. No upper
bound for that term has been obtained from Green negativity.

**Complete first-tail correlations → an unpaid quantitative estimate.**
The existing `DeletionFirstTail.error_eq_harmonic_add_mertens_increment`
identifies the actual error on `N<n<=2N` as
`n*H_N+M(n)-M(N)`. The same module proves that its increment energy I_N is
at most six times the full error energy. For N>=1, expanding this literal
increment energy and telescoping its physical weights gives

```
I_N = sum_(N<a,b<=2N) mu(a)*mu(b)
        * (1/max(a,b)-1/(2*N+1))
    = D_N + 2*O_N,
D_N = sum_(N<a<=2N) mu(a)^2*(1/a-1/(2*N+1)),
O_N = sum_(1<=h<N) sum_(N<a<=2*N-h)
        mu(a)*mu(a+h)*(1/(a+h)-1/(2*N+1)).
```

All denominators here are real. To verify the first equality, a pair a,b
occurs in precisely the squared prefixes with `max(a,b)<=n<=2N`, whose
weights sum to `1/max(a,b)-1/(2*N+1)`. The second equality separates equal
indices and writes the strict half as b=a+h. In particular
`0<=D_N<=sum_(N<a<=2N)1/a<=log(2)`; the final inequality follows by
integrating 1/x on each preceding unit interval.

The candidate bound is a one-sided subpower estimate for O_N, retaining
all shifts h<N and their moving endpoints. No such estimate was proved.
`Sieve.AveragedChowlaInterface.MRBilinear_moebius_of_averagedChowla`
explicitly assumes `AveragedChowlaUniform` for the Mobius sequence; its
proof does not discharge that input. Moreover, that interface specifies
an `o(H*Y)` correlation budget, not the required subpower weighted budget.
Even a transfer with an ideal factor 1/N at H,Y of order N would leave an
`o(N)` allowance, without the needed power rate. This is a normalization
comparison, not an assertion that the moving-endpoint transfer is proved.
Controlling I_N would still leave the harmonic interaction and the complete
later tail in the original source. The finite expansion above is a paper
audit of that necessary local estimate, not an additional Lean receiver.

The reciprocity follow-up also inspected
`Sieve.KloostermanPhysicalResidueModulusBilinear`: it retains the signed
modulus kernel exactly, while its available operator estimate still has
the modulus factor and two residue-vector norms. No identification and
improved estimate for O_N or the full EDQ Gram follows from that statement.

Six further broad OR-matched deep/method searches covered gcd-log
cancellation, resolvents, coarea, zero-mass Green forms, divisor-tail
reciprocity, and Mertens increments. Each used 120 seconds, two rounds,
all retrieval views, no refresh and no per-module cap. All were partial
at generation 823353, with pending coverage and unfinished judging.
All returned 20 declarations; five returned 20 candidate lemmas and 20
source arguments, while the Green query returned neither lane. All
proof-idea and ingredient sets were empty. The candidate/source lanes
were `source_only`, with no compiler metadata; they were not accepted as
Lean-verified proof ingredients. Relevant source statements were read.
Retrieval was interrupted or timed out; some searches also reported an
unavailable Qdrant service. These results cannot certify corpus absence.

Additional broad newest-first arXiv searches used `screening`, `rigidity`
and `reflection`; the latter two endpoints failed. The screening search led
to [Solomons et al., geometric quantum state preparation, 9 September 2026](https://arxiv.org/html/2609.10282v1).
Its section II.1 represents a linear-system solution up to a magnitude
factor. Such state preparation does not supply the missing norm bound for
the unnormalized EDQ source. No algorithm or numerical experiment was run.

## Compensated quotient transfer: the input norm and truncation boundary

The co-Poisson transfer attempt gives no stronger source bound. In
particular, exact compensation is already formalized in
DeletionCounterterm.error_eq_compensated_quotient_mass and
DeletionCounterterm.hasSum_mertensIncrement_mass, in
EulerDeletionCountertermRigidity. Repackaging those identities is not new
arithmetic progress.

Here is the continuous normalization used to test the transfer. All
functions below are on the positive ray, and N is a positive integer:

\[
 \phi_n(u)=\frac{\{u/n\}}u,\quad
 R_N=\sum_{n\le N}\mu(n)\phi_n,\quad
 G_N=R_N-H_N\phi_1,\quad
 e(u)=\frac{1_{u\ge1}}u,
\]
\[
 h_N(v)=\frac{1_{v>N}(M(\lfloor v\rfloor)-M(N))}{v},\qquad
 Ph(u)=\sum_{j\ge1}\frac{h(u/j)}j-\int_0^\infty h(v)\frac{dv}{v}.
\]

The corpus's arbitrary logarithmic Mertens bound implies
\(\int|h_N(v)|\,dv/v=O_q((\log N)^{1-q})\) for each integer q>1,
by integrating \(|M(\lfloor v\rfloor)|/v^2\) above N and adding
\(|M(N)|/N\). Cellwise integration of the existing increment-mass
identity gives \(\int h_N(v)\,dv/v=-H_N\). Finite divisor regrouping,
using \(\sum_{n\le u}\mu(n)\lfloor u/n\rfloor=1_{u\ge1}\), therefore gives

\[
                  Ph_N=R_N+e=G_N+H_N\phi_1+e.                 \tag{Q1}
\]

Each quotient sum is finite at a fixed u. Since \(|H_N|\le2\),
\(\|\phi_1\|_2\le\sqrt2\), and \(\|e\|_2=1\), the correction between
Ph_N and G_N is uniformly bounded in \(L^2(du)\). Thus (Q1) retains
the physical energy target; it does not estimate it.

**The weighted input norm does not control output energy.** For
\(h_a(v)=h(v/a)\), a>0, substitution gives
\[
 \|h_a\|_{L^1(dv/v)}=\|h\|_{L^1(dv/v)},\qquad
 Ph_a(u)=Ph(u/a),\qquad \|Ph_a\|_2^2=a\|Ph\|_2^2.            \tag{Q2}
\]
Even zero weighted mean does not fix this mismatch. Take
\(h(v)=1_{[1,2)}(v)/v-2\,1_{[2,4)}(v)/v\).
Its weighted mean is zero and its weighted absolute integral is one.
For 1<u<2, Ph(u)=1/u. For large u, the two integer interval counts
have cancelling linear parts and bounded errors, so Ph(u)=O(1/u);
hence \(0<\|Ph\|_2<\infty\). Equation (Q2) rules out a uniform
\(L^1(dv/v)\)-to-\(L^2(du)\) bound on these compact zero-mean seeds.
This generic transfer failure says nothing negative about the desired
bound for the particular arithmetic h_N.

**Actual arithmetic truncation keeps a boundary.** For integers L>N,
let \(k_{N,L}(v)=1_{v<L}h_N(v)\), and set
\[
 h_{N,L}(v)=\frac1v\sum_{N<n\le L}\mu(n)1_{v\ge n},
 \qquad \Delta_{N,L}=M(L)-M(N).
\]
Then
\[
 k_{N,L}=h_{N,L}-\Delta_{N,L}\frac{1_{v\ge L}}v,\qquad
 Ph_{N,L}=R_N-R_L,\qquad
 P(1_{v\ge L}/v)=-\phi_L.
\]
The last two identities follow directly by counting the admitted
quotients and subtracting their weighted integrals. Consequently
\[
 Pk_{N,L}=R_N-R_L+\Delta_{N,L}\phi_L,\qquad
 Pk_{N,L}-Ph_N=-(R_L+e)+\Delta_{N,L}\phi_L.                 \tag{Q3}
\]
The boundary has the exact squared norm
\[
 \|\Delta_{N,L}\phi_L\|_2^2
   =\|\phi_1\|_2^2\,\frac{(M(L)-M(N))^2}{L}.
\]
The available logarithmic estimates do not make this term small.
Nor may it be declared a lower bound for the complete defect in (Q3):
the interaction with R_L+e must remain. Weighted input convergence does
not justify strong output convergence.

RHTower.BurnolCoPoissonSource.seed_memLp_two, in
BurnolCoPoissonSeedL2Recovery, assumes a literal source with compact
multiplicative support and an existing L2 output vector.
Its finite inverse uses a cutoff at least the support ratio. Neither
this theorem nor the dilation membership theorems supplies a uniform
estimate for (Q3). The first interval N<u<2N also has only one active
quotient in (Q1); its signed Mertens increment is the existing
EulerDeletionFirstTailMertens obstacle. Later disjoint time intervals
cannot cancel a positive energy already integrated on this interval.
This does not preclude cancellation between quotient terms at the same u.

Four broad deep/method searches tested shared coefficients and renewal,
Cotlar dilation autocorrelation, almost orthogonality across scales,
and Muntz/co-Poisson compensation. All used OR matching, all retrieval
views, two rounds, no module cap, cached content and 120-second budgets.
All were partial. Generations were 872700, 872742, 872793 and 872903;
the second and fourth reported complete source inventories of 56,809
files, with most compiler states pending. All returned 20 declarations.
The second and fourth also returned 20 candidate and 20 source entries;
the third returned 20 candidates. No proof ideas were returned. The two
ingredient sets covered autocorrelation Fourier identities and dilation
bookkeeping. Source statements were inspected; no candidate was accepted
as compiler-verified. Retrieval interruptions, an unavailable semantic
service and a reranking deadline limit the search conclusions.

A broad newest-first arXiv search for memory led to
[Ellis et al., delay-engineered spin dynamics, 10 September 2026](https://arxiv.org/html/2609.11383v1).
Its exact linear characteristic equation retains the delay phase as
well as gain; a negative feedback coefficient alone does not prove
stability. The inspected result supplies no estimate of the EDQ source.
No simulation was run.

Equations (Q1)–(Q3) are paper normalizations and transfer tests, not new
Lean theorems or a completed no-go. The source energy estimate remains
open. No computations, Lean builds, or frontier-map changes accompany
this section.
