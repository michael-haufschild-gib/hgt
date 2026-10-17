# Finite-train topology and diffuse packet escape

## Source domain and corpus boundary [PAPER PROOF]

Fix an actual compact C² real source f with R=h_f(0)>0 and correlation radius
D>0. Let c_i be a nonzero finite real coefficient vector, and let t_i be distinct
integers. For S>0 define

    G(u)=sum_i c_i f(u-t_i S),  Q=sum_i c_i²>0,
    A_k=sum_(i,j:t_j-t_i=k) c_i c_j,
    L=max({0} union {|A_k|/Q : k!=0 is a realized difference}).

Every G is an actual compact C² source, smooth if f is smooth. The old copyTrain
is the special case t_i=i. Arbitrary integer sites permit sparse growing trains
without introducing an analytic separation interface. The existing finite-source
correlation expansion groups as

    h_G(x)=sum_k A_k h_f(x-kS).

Injectivity gives A_0=Q, swapping indices gives A_(-k)=A_k, and all realized
differences lie in a finite set containing zero. Distinct integer differences
are separated by at least one. These are finite algebraic facts, not assumptions
on source correlations. Existing grouped copy algebra and energy-tail comparison
are inputs; they are not counted anew.

Deep discovery used a 90-second budget and returned partial source-only candidates,
pending coverage, no proof ideas or ingredient sets, and no applicable replacement
for the source identities inspected directly. Lexical fallback logs from the
candidate card identify the exact earlier train and signed-compactness APIs.
No exhaustive external priority claim is made.

## 1. Exact correlation peak [PAPER PROOF]

Assume S>2D. Distinct packets h_f(x-kS) and h_f(x-lS) cannot both be nonzero:
their centers are separated by at least S, while their support radii sum to 2D.
At x=0 only the zero packet survives, so R_G=QR>0. Consequently

    H_G(x)=sum_k (A_k/Q) H_f(x-kS),
    H_G(x)-H_f(x)=sum_(k!=0) (A_k/Q) H_f(x-kS).

At most one term of the last sum is nonzero. Since |H_f|<=1, its absolute value
is at most L. If L>0, a maximizing nonzero lag k exists. At x=kS, the seed and
every other packet vanish, while H_f(0)=1. Thus H_G(kS)=A_k/Q and

    ||H_G-H_f||_infinity=L.

When L=0 the same identity follows from the upper bound and norm nonnegativity.
This covers single-packet data and exact interior cancellations.

## 2. Count-independent energy convergence [PAPER PROOF]

For |x|<=S/2 and S>2D, every nonzero packet vanishes, because
|x-kS|>=S-|x|>=S/2>D. Thus H_G=H_f on this entire window. The already proved
local normalized energy comparison gives

    |E(G)-E(f)| <= 2 integral_(S/2,infinity) w_arch(x) dx.

For S>=2D+2 the right side is bounded by 2 integral_(1,infinity) w_arch. This
integral is finite and nonnegative. Every train, with any count or coefficients,
therefore belongs to one actual source class with ceiling

    K=E(f)+2 integral_(1,infinity) w_arch >=0.

If S_n tends to infinity, the integrable tails tend to zero. Hence E(G_n)->E(f)
uniformly over all finite counts, integer sites and nonzero coefficient vectors.
No coefficient-size or packet-count bound enters this estimate.

## 3. Complete variable-count compactness criterion [PAPER PROOF]

Let the finite data vary arbitrarily with n and let S_n>=2D+2 tend to infinity.
The following conditions are equivalent:

1. L_n tends to zero.
2. H_Gn tends globally uniformly to H_f.
3. The correlations H_Gn have compact closure in the global supremum norm.
4. Their signed logarithmic traces decay uniformly over the family.

Sections 1 and 2 prove 1 iff 2 and place every source under one ceiling K.
Uniform convergence gives compact closure of the range. Conversely, compact
closure gives uniform continuum tails by the signed compactness theorem. For
each n with L_n>0 choose a maximizing nonzero integer lag k_n. Its center has
|k_n S_n|>=S_n, and |H_Gn(k_n S_n)|=L_n. Uniform tails therefore force L_n->0;
indices with L_n=0 already satisfy every positive bound. The earlier signed-grid
criterion gives 3 iff 4. Its general signed node values are retained throughout.

## 4. Exact polar symbol and continuity scale [PAPER PROOF]

Put B(z)=sum_i c_i exp(z t_i S). Compact support makes both source moments
and every polar integral finite. Translation and finite linearity give

    M_+(G)=B(1/2) M_+(f), M_-(G)=B(-1/2) M_-(f).

The actual half-line moment product identity and R_G=QR yield

    P(G)=B(1/2) B(-1/2) P(f)/Q.

If P(f)!=0, P(G_n)->P(f) holds exactly when B_n(1/2)B_n(-1/2)/Q_n->1.
Solve for the multiplier by dividing P(G_n) by the fixed nonzero P(f) for
necessity; scalar continuity proves sufficiency. This classifies the additional
polar requirement even when global correlations and energies converge.

## 5. Explicit diffuse producer with diverging polar moment [PAPER PROOF]

Take a concrete nonnegative C-infinity bump supported in [-1,1], nonzero at zero.
Its mass and both half-exponential source moments are positive; hence P(f)>0.
Its correlation radius is D=2. For q>=2 use q coefficients c_i=1 at integer
sites t_i=3^i, 0<=i<q. Their positive differences are distinct. Indeed, if
a<b and c<d and b>d, then

    3^b-3^a >= 2*3^(b-1) >= 2*3^d > 3^d-3^c.

Equality of the differences therefore forces b=d, then a=c. Negative differences
reduce to positive differences by swapping the endpoints. Thus every nonzero
realized lag has coefficient exactly one, Q=q, and L=1/q. The first two sites
give a nonzero lag, so this maximum is attained. Each coefficient contributes
the fraction 1/q of the diagonal source mass: no packet dominates.

Choose q_n=n+2 and S_n=2D+2+q_n. Then S_n>=2D+2, S_n->infinity and L_n->0.
The actual smooth trains have one energy ceiling, globally convergent normalized
correlations, convergent energies, compact correlation closure, and uniform signed
logarithmic trace decay.

Nevertheless their polar moments tend to positive infinity. All terms in
B(1/2)B(-1/2)=sum_(i,j) exp((t_i-t_j)S/2) are positive. The first two sites
differ by exactly two, so their term is exp(S), for every real S. The product
is therefore at least exp(S). Since the chosen spacing has S>=q,
and exp(q/2)>=q/2, it is at least q²/4. Therefore

    P(G_q) >= (q/4) P(f) -> infinity.

This explicit source family supplies unconditional error and growth bounds.
It assumes no Chebyshev estimate, positivity receiver, or unproved moment
vanishing. No floor-sum counterterm manipulation is used. In accordance with
Trap 10, an actual producer and its proved bounds are the sharpness endpoint.
No exact full-grid blindness is claimed for this family.

## Insight and formal status

Correlation compactness can arise from dilution across many equally weighted
packets, not merely from suppressing a fixed collection of copy amplitudes.
The surviving invariant is the largest grouped normalized lag coefficient.
The polar symbol detects exponentially amplified interactions that this unweighted
invariant and the decaying energy tail cannot control.

Certified as connected package 13 of 100. All eight direct Lean leaves pass
without diagnostics; all 77 public declarations (61 theorems, 15 definitions,
one structure) have only the standard `propext`, `Classical.choice`, `Quot.sound`
dependencies. All eight imports and 77 exact API entries are verified.

The global formal lint snapshot remains blocked by four unrelated unwired
modules and a foreign `sorry` in `HighFrequencyLaplaceEnergyMeanValue.lean:292`.
No error concerns this package; repository-wide green is not claimed. Full
certificate: `docs/drafts/pipeline/3-formalized/finite-train-topology-and-diffuse-escape-2026-10-17.md`.

The next paper result, `NyquistPolarIntegrableResidual.md`, constructs a stable
all-tail Nyquist residual with an explicit 1/sqrt(N) error bound. It is uncounted
and awaits Lean formalization.
