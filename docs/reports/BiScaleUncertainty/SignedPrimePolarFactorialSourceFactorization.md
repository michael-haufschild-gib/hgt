# Actual source factorization and its linear energy cost

Status: dependency-closed paper proof; Lean verification in progress. This is one
candidate package, uncounted until the actual-source endpoint is verified.

## Explicit parameters and sources

Fix N≥1. Put A=1+1/(4N), δ=log(A)/3, E=exp(δ), ε=E−1. Then
E³=A, 0<δ≤1/(12N), δ≥1/(15N), ε≥δ, and E⁴≤2.
Indeed log A≤A−1 gives the upper bound for δ; log A≥1−1/A=1/(4N+1)
gives the lower bound. Also 1≤A≤5/4 and E⁴≤E⁶=A²<2.

Use the already verified clamped ramp qε(t)=min(1,max(0,(1+ε−t)/ε)) and set

Uε,K(x)=exp(x/2) Σ_{j=1}^K qε(j exp(x)/K),
R_N(x)=[Uε,4N(x)−4Uε,2N(x)+4Uε,N(x)]/sqrt(N).

The same finite antitone pairing as in the continuous factorial producer gives
|R_N(x)|≤2exp(x/2)/sqrt(N). The stencil is zero for x≤0 and for
x≥log(4NE). Since E≤A, its squared L² norm is at most 16.

Define the continuous tent τδ(t)=max(0,min(t,2δ−t)) and the density

ρ_N(t)=exp(t) τδ(t)/ε².

Finally define the actual compact continuous sources

F_N(u)=R_N(−u),
G_N(u)=exp(u/2)ρ_N(u),
P_N=F_N+G_N, M_N=F_N−G_N.

F_N vanishes on the positive half-line; G_N vanishes off [0,2δ]. Both vanish
at zero, so F_N(u)G_N(u)=0 for every u. No unproved regularity interface occurs:
continuity follows from finite min/max formulas, and support is explicit.

## Tent moments

For a≠0, direct FTC on [0,δ] and [δ,2δ] gives

∫₀²δ exp(at)τδ(t)dt=[(exp(aδ)−1)/a]².

Primitives on the two intervals are respectively
exp(at)(at−1)/a² and exp(at)(a(2δ−t)+1)/a².
Their derivatives are t exp(at) and (2δ−t)exp(at). Evaluation and
exp(2aδ)=exp(aδ)² give the displayed identity. Thus

∫ρ_N=1, ∫exp(t)ρ_N(t)dt=[(E+1)/2]².

All integrals are literal finite integrals of continuous compact functions.

## Actual mixed correlation and exact grid preservation

Let H_N(x)=∫F_N(u)G_N(u+x)du. A translation of Lebesgue integration yields

H_N(x)=∫₀²δ ρ_N(t)exp(t/2)R_N(x−t)dt.

This is continuous by parameter integration on a fixed compact interval. It
vanishes for x≤0 and x≥log(4N+1). For the upper tail, t≤2δ implies
exp(x−t)≥(4N+1)/E²=4NE, which kills the ramp stencil.

For integer n≥1 and t∈[0,2δ], every term with jn≤K has ramp value one.
For jn>K, integer separation gives jn≥K+1≥KA≥KE³≥KE exp(t), since K≤4N.
Thus qε(jn exp(−t)/K)=0. The exponential factors cancel, so

exp(t/2)R_N(log n−t)=W_N(log n),
H_N(log n)=W_N(log n).

This includes n=1, where all finite constant sums cancel. The actual von Mangoldt
atom sequence is exactly the verified factorial sequence, not a grid-blind one.
Its atomic sum is B_N/sqrt(N), where B_N=T(4N)−4T(2N)+4T(N).

## Both polar branches and unconditional pairing

For a≥1, one additional single-ramp FTC calculation gives

∫₀∞ exp(x)qε(exp(x)/a)dx=a−1+εa/2.

On the collar use the primitive [(1+ε)exp(x)−exp(x)²/(2a)]/ε.
Subtracting this from the verified full single-ramp polar formula gives the
constant-branch integral log a+ρ(ε), with
ρ(ε)=((1+ε)log(1+ε)−ε)/ε. Finite summation and the factorial stencil therefore give

∫exp(x/2)R_N(x)dx=(1+ε/2)C_N/sqrt(N),
∫exp(−x/2)R_N(x)dx=−B_N/sqrt(N),
C_N=4N(H_(4N)−2H_(2N)+H_N)∈[0,1].

Integrate the compact mixed-correlation formula in either order. Every integrand
is continuous with support in a fixed finite rectangle, so finite Fubini applies.
A translation x=y+t multiplies the positive polar branch by exp(t) and leaves
the negative branch unchanged, after the source factor exp(t/2) is included.
Using the two tent moments gives

ν(H_N)=[2B_N−a_N C_N]/sqrt(N), a_N=[(1+E)/2]³.

Since 1≤a_N≤E³=A and |B_N|≤5log(4N+1)+1,

|ν(H_N)|≤[10log(4N+1)+3+1/(4N)]/sqrt(N).

This uses actual prime weights and continuum polar moments. No discrepancy
estimate or pre-floor linear counterterm is inserted.

## Nonvanishing test size and an autocorrelation contrast

The density is nonnegative with integral one. The pointwise ramp bound gives
|H_N(x)|≤2exp(x/2)/sqrt(N); its support gives ∫H_N²≤16.
If log(2N+1)≤x≤log(4N) and 0≤t≤2δ, then
exp(x−t)≥(2N+1)/E²>2NE and exp(x−t)≤4N. Thus only the j=1 rectangle
of the largest lift survives, with value one. Consequently
H_N(x)=exp(x/2)/sqrt(N) on this full interval, and ∫H_N²≥2−1/N≥1.

Expanding the two actual source autocorrelations gives

J_N(x):=[h_(P_N)(x)−h_(M_N)(x)]/2=H_N(x)+H_N(−x).

The reflected term is zero for x≥0. Hence J_N preserves the same arithmetic
grid and has the same full signed pairing as H_N. The disjoint half-line supports
also give J_N²=H_N²+H_N(−·)² pointwise, so 2≤∫J_N²≤32.
In particular J_N(0)=0 and J_N(log(4N))=2. This is an actual autocorrelation
difference; it is not itself an autocorrelation or a positivity certificate.

## The source-energy cost is linear, not hidden

The product F_NG_N vanishes pointwise. Therefore

h_(P_N)(0)=h_(M_N)(0)=∫F_N²+∫G_N².

For the upper bound, 0≤τδ≤δ and ε≥δ give, on [0,2δ],
ρ_N≤δE²/ε² and G_N²=exp(t)ρ_N²≤δE⁴ρ_N/ε².
Thus ∫G_N²≤E⁴/δ≤2/δ≤30N. Since ∫F_N²≤16≤16N,
both source origin energies are at most 46N.

For the lower bound, integrate the nonnegative square
(ρ_N−1/(2δ))² on [0,2δ]. Its expansion, ∫ρ_N=1 and interval length 2δ imply
∫ρ_N²≥1/(2δ). Since exp(t)≥1 there, ∫G_N²≥1/(2δ)≥6N.
Therefore the exact equal source energies satisfy

6N≤h_(P_N)(0)=h_(M_N)(0)≤46N.

The same explicit family combines nonvanishing contrast size and a vanishing
scalar pairing bound with a provably growing source-energy cost. It supplies
actual source admission while keeping that cost visible; it does not establish
uniform control of arbitrary signed source packets.

## Prior-work boundary

`FiniteSourceEnergyScalarization.lean` separates sources to kill both local cross
terms and preserve summed local data. Here the mixed correlation is deliberately
retained and evaluated. The existing coprime factorial producer supplies a different
discontinuous scalar stencil. Neither inspected result gives these continuous
sources, exact arithmetic preservation and two-sided source-energy cost together.
The partial convolution search supplied no applicable complete factorization;
the proof instead uses direct continuous profiles, finite parameter integration,
translation and elementary FTC. The further tent search retrieved
`HTGeometry.integral_tiltedTentFullProfile`; the Lean tent moment reuses that
bilateral transform by translation. Its classical moment calculation is an
ingredient, not a separate contribution. No external novelty claim is inferred.
