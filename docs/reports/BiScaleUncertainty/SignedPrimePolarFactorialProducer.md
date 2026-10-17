# A factorial producer for the actual signed prime–polar measure

For K≥1 define the concrete compact test

R_K(x)=exp(x/2) Σ_{j=1}^K 1_[0,log(K/j)](x),

where K/j is real division. Let ν be the actual half-line measure
Σ_{n≥2} Λ(n)/sqrt(n) δ_log(n) − 2cosh(x/2) dx.
All tests below are bounded measurable functions with compact support, hence
their polar integrals exist. Their atomic sequences have finite support.

## Exact evaluation [PROVED HERE]

For n≥1, the jth rectangle contains log n exactly when nj≤K. Therefore
R_K(log n)=sqrt(n) floor(K/n), and it vanishes for n>K.
Since Λ(1)=0, the actual atomic pairing is
Σ_{n=1}^K Λ(n) floor(K/n)=Σ_{m=1}^K log m=:T(K).
The equality uses Σ_{d|m}Λ(d)=log m, already formalized in the factorial producer.

For each j≤K, L=log(K/j)≥0 and

∫_0^L 2cosh(x/2)exp(x/2) dx
=∫_0^L(exp x+1)dx=K/j−1+log(K/j).

Finite summation gives the polar integral
K H_K−K+K log K−T(K), where H_K=Σ_{j=1}^K 1/j.
Consequently ν(R_K)=2T(K)−K log K−K H_K+K.
Both polar exponential branches are retained; the second is the log(K/j) term.

## Harmonic cancellation [PROVED HERE]

Pair even and odd summands to obtain
H_(2m)−H_m=Σ_{k=1}^m[1/(2k−1)−1/(2k)]. Thus

H_(4N)−2H_(2N)+H_N
=Σ_{k=N+1}^{2N}1/[2k(2k−1)].

Every summand is nonnegative and at most 1/(4N²) for N≥1.
There are exactly N terms. Hence
0≤4N(H_(4N)−2H_(2N)+H_N)≤1.

## Unconditional normalized producer [PROVED HERE]

Define W_N=(R_(4N)−4R_(2N)+4R_N)/sqrt(N), N≥1.
This is supported in [0,log(4N)], with literal finite atomic support and an
integrable polar term. Linearity is justified by those domain facts.
The dilation stencil cancels K log K and K exactly. Thus

ν(W_N)=[2 B_N−C_N]/sqrt(N),
B_N=T(4N)−4T(2N)+4T(N),
C_N=4N(H_(4N)−2H_(2N)+H_N)∈[0,1].

The existing unconditional factorial producer theorem gives
|B_N|≤5 log(4N+1)+1. The triangle inequality now yields

|ν(W_N)|≤[10 log(4N+1)+3]/sqrt(N).

Taking N=n+1 gives a public endpoint with only n:ℕ as input.
This explicit arithmetic cancellation uses actual Λ weights and no conjectural
Chebyshev discrepancy bound. It proves a quantitative scalar producer statement;
it does not control all signed correlations, packet norms, or Weil positivity.

The test retains fixed amplitude: W_N(0)=0 and W_N(log(4N))=2. The first identity
uses R_K(0)=K; the second uses R_(4N)(log(4N))=sqrt(4N) while the two smaller
rectangles vanish. Thus this is not merely an arbitrary test scaled uniformly to
zero. It also cannot be a nonzero real-source autocorrelation: zero origin energy
would force that autocorrelation to vanish everywhere.

## Trap 10 and proof boundary

The continuum endpoint log(K/j) is never replaced by log floor(K/j).
The arithmetic floor appears only from counting actual prime atoms inside the
real-ratio rectangles. The stencil is applied to the already-summed factorial T,
without subtracting a discrete linear counterterm before floor summation.

Lean certification pending. The result is one package, including construction,
domain admission, exact evaluation and bound; helpers are not separate counts.
