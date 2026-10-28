# Spectral exhaustion by torsion-adjunction energies

- **ID:** full-prime-spectrum-adjunction-exhaustion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Ramanujan full-matrix quasimodes; harmonic rough-number tensorization; prime-defect Dirichlet form
- **Statement:** Every bounded energy window of `log(N) I-P_N` converges, with multiplicity, to the simple energies `gamma+log(m)+tameDifferent(m)`.
- **Count:** uncounted infrastructure due previously recorded concurrent overlap; formalization and integration complete

## Goal

The actual renormalized prime matrix has the exact eventual arithmetic spectral
count below every threshold outside the adjunction energies. Each positive conductor
has an isolating window containing one eventual simple eigenline, whose projection
captures its normalized Ramanujan profile. Uniform approximation of every bounded-mass,
bounded-defect vector by a fixed finite Ramanujan span supplies the compactness input.
No full Weil positivity or RH implication is asserted.

## Gates

- Existing uncounted decision retained. No further novelty audit, as instructed.
- [x] Dependency-closed paper proof of compactness, exact spectral counts, and simple eigenlines.
- [x] Exact Lean realization, sixteen final direct source checks, eighteen transitive axiom reports, umbrella wiring.

## Dependency-closed proof [PROVED HERE]

All sixteen modules, including both spectral endpoints, are formalized and
individually source-checked. Write `P_N` for the literal prime matrix, `A_N=log(N)I-P_N`,
`E(m)=gamma+log(m)+tameDifferent(m)`, and
`v_(m,N)=c_m(n)/sqrt(phi(m)*n*log(N))` for positive conductors and N>=2.
For every T outside `{E(m):m>=1}`, the theorem is

`#{eigenvalues of A_N below T, with multiplicity} = #{m>=1:E(m)<T}`

for all sufficiently large N. Each E(m) additionally has a fixed isolating
window containing one simple actual eigenvalue eventually. That eigenvalue
tends to E(m), and its spectral projection captures v_(m,N) in squared norm.

### 1. The actual arithmetic compactness estimate

For a real horizon vector x, extend by zero and put

`D_N(x)=sum_(u<=N)sum_(t<=N/u) Lambda(t)*(x(ut)-x(u)/sqrt(t))^2`.

The existing sharp counterterm, with epsilon=1/2, gives eventually and
uniformly in x

`<x,A_N x> >= (gamma-1/2)||x||^2 + D_N(x)/2`.

Consequently unit vectors of energy at most T satisfy
`D_N(x)<=K_T=max(0,2(T-gamma+1))`.
The exact double-sum/Euclidean-form identity is part of the energy adapter.

The inspected prime-peeling proof bounds every rough harmonic variance by
`K exp(Psi(Q,X)) G_(Q,X)`, where Psi<=0 for X>=2; for X<2 the variance
vanishes. Thus one constant C>0 works for every roughness threshold Q and
horizon X. On a Q-rough interval with Q>=2, every prime ladder has weight
log(p)>=log(Q). Bound each ladder variance by its edges from the valuation-zero
base. Distinct pairs (prime, positive exponent) give distinct prime powers,
so these edges inject into the literal defect. Therefore

`Var_(Q,X)(sqrt(k)*z(k)) <= C/log(Q) * D^rough_(Q,X)(z)`.

Here only the bottom vertex is restricted to the rough interval; the edge
multiplier t remains unrestricted. This precise restriction matters in the
following partition.

Write every n uniquely as d*k with d Q-smooth and k Q-rough. On the fibre d,
the quotient horizon is X=N/d. Apply the last inequality to
`z_d(k)=sqrt(d)*x(d*k)`. Its pole gauge is exactly `sqrt(d*k)*x(d*k)`.
The harmonic conditional mean h of this gauge, divided by sqrt(n), satisfies

`||x-h||^2 = sum_d Var_(Q,N/d)(sqrt(d*k)*x(d*k))/d`.

The same rescaling multiplies each edge square by d. Dividing by d and
partitioning bottom vertices by their unique smooth/rough factors therefore
gives exactly `sum_d D^rough_(Q,N/d)(z_d)/d=D_N(x)`. Hence

`||x-h||^2 <= C*D_N(x)/log(Q)`.

Large retained valuations are controlled separately. For any prime p, apply
`a^2 <= 2(a-b)^2+2b^2` on every downward p-power edge. Reindexing by the
upper vertex counts exactly v_p(n) edges at n. The bottom term is bounded
by the geometric series `sum_(j>=1)p^(-j)=1/(p-1)`. This proves

`log(p)*sum_n v_p(n)*x(n)^2 <= 2D_N(x)+2log(p)/(p-1)*||x||^2`.

Let `B_Q=sum_(p<Q)(2/log(p)+2/(p-1))`. Outside the box v_p(n)<L for every
p<Q, at least one retained valuation is at least L. Summing the preceding
moment bounds gives

`mass_outside_box <= B_Q*(D_N(x)+||x||^2)/L`.

Set z=h inside the box and z=0 outside. Pointwise,
`|x-z|^2 <= |x-h|^2+1_outside*|x|^2`; thus no projection contraction
assumption is needed. For ||x||^2<=1 and D_N(x)<=K, first choose Q>=2 with
`log(Q)>2C(K+1)/eta`, then L>0 with `L>2B_Q(K+1)/eta`. The resulting
squared error is at most eta, uniformly in N and x.

This approximation lies in one explicit finite Ramanujan span. Set
`M=product_(p<Q)p^L`. The gcd with M replaces every retained valuation by
min(v_p(n),L). It preserves box membership, and inside the box equals the
full Q-smooth part. Thus the truncated conditional mean is `F(gcd(n,M))/sqrt(n)`
for a real function F depending on N and x. Finite Möbius inversion expands
F(gcd(n,M)) in indicators 1_(d divides n), d dividing M. The already proved
identity `sum_(q divides d)c_q(n)=d*1_(d divides n)` expands these indicators
in the normalized Ramanujan modes with q dividing M. The conductor set
`S=M.divisors` depends only on K and eta, not on N or x.

### 2. A uniform positive coordinate certificate

The quasimode theorem gives `Gram(v_(m,N),v_(l,N))->[m=l]` on each fixed
finite positive conductor set. If its entries differ from identity by at most
`1/(2(|S|+1))`, then for every coefficient vector a,

`||sum_(m in S)a_m v_(m,N)||^2 >= (sum_(m in S)a_m^2)/2`.

Indeed the Gram error is bounded by the entrywise error times
`(sum|a_m|)^2 <= |S| sum a_m^2`.

Use the compactness estimate with eta=1/4 and K=K_T. For each unit vector x
of energy at most T, choose z in that fixed span with ||x-z||<=1/2. Then
||z||<=3/2, so its synthesis coefficients satisfy sum a_m^2<=9/2. Also
`<x,z>=1-<x,x-z>>=1/2`. Cauchy--Schwarz in the finite coefficient space
therefore yields

`sum_(m in S)|<x,v_(m,N)>|^2 >= 1/18`.

The constant is only a positive witness. It is uniform over the entire
bounded-energy unit sublevel and all sufficiently large horizons.

### 3. Exact multiplicity-sensitive spectral count

The tame different is nonnegative, so E(m)>=gamma+log(m). Hence
`S_T={m>=1:E(m)<T}` is finite. The finite-packet theorem and the positive
minimum of T-E(m) on S_T give at least |S_T| actual eigenvalues below T,
counting multiplicity, for all sufficiently large N.

For the upper count, suppose the actual subspace below T had dimension greater
than |S_T|. The linear map recording its coordinates against the profiles with
m in S_T has a nontrivial kernel. Normalize a nonzero kernel vector x. Its
energy is at most T and all its S_T coordinates vanish.

For any m with E(m)>T, expansion in the actual Hermitian eigenbasis and
Cauchy--Schwarz give

`|<x,v_(m,N)>|^2 <= ||(A_N-E(m))v_(m,N)||^2/(E(m)-T)^2`.

This estimate holds for every unit vector supported in the entire low spectral
subspace, not merely for a single eigenvector. One direct proof restricts the
Parseval sum for v to that subspace: every residual weight there is at least
(E(m)-T)^2. The remaining coefficient sum for x is one.

Apply this estimate to the fixed finite detecting set from Section 2. A conductor
in S_T contributes zero; every other detecting conductor has E(m)>T because
T is not an arithmetic energy. Its actual residual tends to zero by the
quasimode theorem. Thus the total detecting coordinate mass is bounded by a
fixed finite sum tending to zero, contradicting 1/18. The actual low dimension
is at most |S_T|. Combined with the lower count, this proves the exact assertion.

### 4. Isolation and convergence of the actual eigenline

Fix m>=1. Properness makes the set E(l)<E(m)+1 finite; energy injectivity
separates its members. Choose delta>0 so that |E(l)-E(m)|<2delta implies l=m.
The thresholds E(m)-delta and E(m)+delta are outside the arithmetic energy set,
and their arithmetic counts differ by exactly one. The proved actual counts
therefore imply that the half-open window [E(m)-delta,E(m)+delta) contains
exactly one spectral index eventually. This includes multiplicity and hence
gives a simple eigenvalue.

For any epsilon>0, the existing conductor-m quasimode puts an actual spectral
point within min(epsilon,delta/2) of E(m). It lies in that window and must be
the unique point there. Thus its energy tends to E(m).

Let Pi_N be the literal orthogonal projection onto that window. Every excluded
actual eigenvalue is at distance at least delta from E(m). Parseval gives

`delta^2*||(I-Pi_N)v_(m,N)||^2 <= ||(A_N-E(m))v_(m,N)||^2 -> 0`.

The normalized profile has squared norm tending to one, so this captures its
nonzero limiting line in the unique actual eigenspace. All projections and
residuals here belong to the actual finite matrix; no abstract limiting
operator or assumed spectral compactness enters the argument.

## Lean realization and verification

`RAPT` denotes `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`.

| Owner | Module |
|---|---|
| RAPT | `TheRoughHarmonicMeasureTensorizesUniformly` |
| RAPT | `PrimeDefectControlsValuationMoments` |
| RAPT | `TheRoughPrimeDefectControlsVariance` |
| RAPT | `TheHorizonSplitsIntoSmoothRoughFibres` |
| RAPT | `TheSmoothRoughMeanApproximatesBoundedDefect` |
| RAPT | `GcdProfilesHaveFiniteRamanujanExpansions` |
| RAPT | `ValuationBoxesAreFiniteRamanujanSpans` |
| RAPT | `PrimeValuationBoxesCaptureBoundedDefect` |
| RAPT | `BoundedPrimeDefectHasFiniteRamanujanApproximation` |
| HTGeometry | `FiniteGramApproximationCertificate` |
| RAPT | `TheRenormalizedPrimeEnergyControlsTheDefect` |
| RAPT | `BoundedPrimeEnergyHasFiniteRamanujanCoordinates` |
| RAPT | `TheAdjunctionEnergyHasFiniteSublevels` |
| HTGeometry | `HermitianSpectralWindowBounds` |
| RAPT | `TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum` |
| RAPT | `TheSimplePrimeEigenlinesConvergeToRamanujanLines` |

All sixteen final direct source checks passed with empty diagnostics. Eighteen
retained transitive endpoint reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. No prohibited proof mechanisms or raised limits occur in these
sources. Evidence:

- `logs/full-prime-spectrum-exhaustion-source-audit-2026-10-28.log`
- `logs/full-prime-spectrum-exhaustion-axioms-2026-10-28.log`

All modules are wired into their mathematical-owner umbrellas; umbrellas were
not compiled. Foundational RAPT documentation records uniform finite Ramanujan
approximation, exact spectral counts, and simple eigenline convergence. Owned
scratch/check/search files were removed after retaining these logs.

The previously recorded concurrent-overlap decision is unchanged: this package
is retained as uncounted infrastructure. No additional novelty audit or web search
was performed for completion.
