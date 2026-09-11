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

The earlier frozen logarithmic gcd experiment still tests its stated
compensated Gram identity. It is not a numerical test of the uncorrected
raw prime-feedback identity. RunPod remains unavailable; no computation
has been performed for this card.
