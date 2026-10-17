# Continuous factorial producer preserving the arithmetic grid

Status: dependency-closed paper proof; Lean verification in progress. One package,
not separate counts for interpolation, cancellation, or norm estimates.

For N≥1 put ε=1/(4N), A=1+ε and

qε(t)=min(1,max(0,(A−t)/ε)),
Uε,K(x)=exp(x/2) Σ_{j=1}^K qε(j exp(x)/K),
S_N=(Uε,4N−4Uε,2N+4Uε,N)/sqrt(N).

All divisions inside qε are real divisions. These formulas define the functions
on the entire real line, without an indicator extension.

## Continuity, support, exact arithmetic values

Each summand is continuous. If x≤0 and j≤K, then j exp(x)/K≤1, so qε=1.
Consequently Uε,K(x)=K exp(x/2), and the stencil vanishes. If
x≥log(4N+1), then j exp(x)/K≥A for K=N,2N,4N, so every ramp vanishes.
Thus S_N is continuous and supported in [0,log(4N+1)].

For integer n≥1, qε(jn/K)=1 when jn≤K. When jn>K, integrality gives
jn≥K+1≥K+εK, since K≤4N; therefore qε(jn/K)=0. This includes equality
at the ramp's upper endpoint. Hence Uε,K(log n)=R_K(log n), where R_K
is the real-ratio factorial lift, and S_N(log n)=W_N(log n) exactly.
The actual von Mangoldt atomic sum is therefore unchanged. In particular
S_N(0)=0 and S_N(log(4N))=2. The family is not an autocorrelation family.

## Polar integral and unconditional pairing

For a=K/j≥1 set L0=log a and L1=log(aA). The ramp qε(exp(x)/a)
equals 1 on [0,L0], equals (A−exp(x)/a)/ε on [L0,L1], and vanishes
above L1. Since 2cosh(x/2) exp(x/2)=exp(x)+1, direct integration gives

∫₀∞ (exp(x)+1) qε(exp(x)/a) dx
=a−1+log a+εa/2+ρ(ε),
ρ(ε)=(A log A−ε)/ε.

For a direct FTC certificate on the second interval use the primitive
[(A−1/a)exp(x)+Ax−exp(2x)/(2a)]/ε. Its derivative is exactly the
tail integrand. Evaluation uses exp(L0)=a, exp(L1)=aA and log(aA)=log a+log A.
No exchange of two improper integrals is needed.

Finite summation yields
∫₀∞ polarDensity(x) Uε,K(x) dx
=(1+ε/2)K H_K−K+K log K−T(K)+Kρ(ε).
The atomic sum is T(K). The stencil cancels K, K log K and Kρ(ε).
Writing B_N=T(4N)−4T(2N)+4T(N) and
C_N=4N(H_(4N)−2H_(2N)+H_N), the full signed pairing is

ν(S_N)=[2B_N−(1+1/(8N))C_N]/sqrt(N).

The verified predecessor bounds |B_N|≤5log(4N+1)+1 and 0≤C_N≤1 give

|ν(S_N)|≤[10log(4N+1)+3+1/(8N)]/sqrt(N).

There is no Chebyshev-discrepancy assumption and no discrete linear counterterm
inside a floor sum. Both exponential branches of the polar density remain present.

## Uniform, nonvanishing squared L² norm

For any antitone f:ℕ→[0,1], put
E_M(f)=Σ_{k=0}^{M−1}(f(2k+1)−f(2k+2)). Each summand is nonnegative.
Inserting the nonnegative gaps f(2k+2)−f(2k+3) shows
0≤E_M(f)≤f(1)−f(2M+1)≤1. Splitting a finite sum into successive pairs gives

Σ_{j=1}^{4N}f(j)−4Σ_{j=1}^{2N}f(2j)+4Σ_{j=1}^N f(4j)
=E_(2N)(f)−2E_N(f∘(2·)) ∈[−2,1].

Apply this to f(j)=qε(j exp(x)/(4N)). It follows that
|S_N(x)|≤2exp(x/2)/sqrt(N). On its support, integration gives
∫ℝ S_N²≤(4/N)(4N+1−1)=16. The looser public bound 20 is also valid.
(Using exp(L) instead of exp(L)−1 gives 16+4/N≤20.)

For log(2N+1)<x≤log(4N), only j=1 in Uε,4N survives, with ramp value 1.
Indeed j≥2 gives j exp(x)/(4N)>(4N+2)/(4N)>A, and already
exp(x)/(2N)>(2N+1)/(2N)>A kills both smaller lifts. Thus
S_N(x)=exp(x/2)/sqrt(N) throughout this interval. Nonnegativity of its
square and interval integration imply
∫ℝ S_N²≥(4N−(2N+1))/N=2−1/N≥1.

The pairing therefore tends to zero for a concrete compact continuous family
whose L² size cannot vanish. This is a scalar producer, not a uniform bound on
arbitrary correlations or on a source-packet operator.

## Prior-work audit

The existing factorial lift supplies the exact actual-weight atomic calculation
and harmonic correction. `LogarithmicGridSource` and
`SmoothLogarithmicGridSource` impose vanishing autocorrelations at grid nodes;
they do not supply this nonzero grid-preserving interpolation. The current
construction is therefore not a restriction to the grid-blind subspace.

Search `/tmp/spp9-search.json` returned a complete file inventory but partial
deep reasoning and mostly source-only compiler metadata. Its candidates and
source arguments were inspected; continuity and finite-integral tools are
reusable, while the proposed coprime-grid ingredient set is inapplicable.
