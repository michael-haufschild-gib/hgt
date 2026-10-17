# Local packet bounds for the actual factorial sources

Status: paper argument; Lean certification in progress. Uncounted until the
actual-source endpoint and dependency audits pass.

## Statement

Put N=n+1, r=sqrt(N), s=sqrt(r), δ=log(1+1/(4N))/3,
ε=exp(δ)−1, L=log(4N+1), and J=[−3δ,L]. Let R be the existing
`sourceFactorialRamp N` and G=`exponentialTentSource δ`. Reflect the two
balanced sources:

V±(u)=s R(u) ± s⁻¹G(−u).

For the literal signed translation packet

Q_K f(u)=Σ_{1≤m≤K+2} Λ(m)/sqrt(m) f(u+log m)
          −∫₀^{log(K+2)} 2cosh(t/2)f(u+t)dt,

the proposed certificate is

∫_J |Q_(10N)V±|² ≤ 300000 sqrt(N).

Every source and cutoff is explicit. No Chebyshev discrepancy or packet-budget
hypothesis occurs. The packet stabilizes on J for K≥10N. Its full real-line
norm is not asserted to stabilize or satisfy this bound.

## Arithmetic cancellation at real scales

Write T(k)=Σ_{m=1}^k log m. This is exactly the Chebyshev floor summatory;
no discrete linear counterterm is subtracted inside that summation.
For v≥0, set A(v)=T(floor(4v))−4T(floor(2v))+4T(floor(v)).
If k=floor(v), then floor(4v)−4k≤3 and floor(2v)−2k≤1.
For integers a≤b and b≤X, monotonicity of log gives

0≤T(b)−T(a)≤(b−a)log(X+1).

The integer stencil already satisfies |A(k)|≤5log(4k+1)+1, also at k=0.
The two carry errors therefore give

|A(v)|≤12log(4v+1)+1.                                      (1)

We next use finite-sum sandwiches, avoiding any regularity assumption on a
real-scale factorial step function. For K∈{N,2N,4N}, u∈J, let v_K=K exp(−u).
After multiplying by exp(−u/2), the actual atomic translate of the K-th
smoothed factorial lift is

S_K(u)=Σ_{1≤m≤10N+2} Λ(m)
             Σ_{1≤j≤K} qε(jm/v_K),

where qε(t)=min(1,max(0,(1+ε−t)/ε)).
For m≥2, exp(−u)≤exp(3δ)≤5/4 implies v_K/m<K, so the finite j cap
does not remove any term from the lower sharp count. The upper count may
always be enlarged. Terms with m=1 vanish since Λ(1)=0. Also
(1+ε)v_K≤K exp(4δ)≤2K≤8N<10N+2, so the m cap contains every
nonzero sharp term. The identity ΣΛ(m)floor(B/m)=T(B) gives

T(floor(v_K))≤S_K(u)≤T(floor((1+ε)v_K)).                   (2)

Since ε(4N)≤1 and exp(−u)≤5/4, the two floor indices in (2) differ by
at most two. Put v=N exp(−u), U=(1+ε)v, and H=log(4U+1).
Each smoothing correction E_K=S_K−T(floor(v_K)) lies in [0,2H].
Consequently |E_(4N)−4E_(2N)+4E_N|≤10H. Combining with (1),

|atomicSource R (10N) u|≤exp(u/2)/r · (22H+1).

Because ε≤1 and exp(u)≤4N+1≤5N, we have 4U+1≤13N exp(−u).
With B=1+log(13N), this proves the convenient envelope

|atomicSource R (10N) u|≤22 exp(u/2)/r · (B−u).            (3)

This is an explicit estimate for the constructed arithmetic packet, not a
restatement of an assumed discrepancy estimate.

## Polar branch and the broad packet

The established ramp facts are R=0 outside [0,L], |R(x)|≤2exp(x/2)/r,

M₊=∫ exp(x/2)R(x)dx=(1+ε/2)C_N/r,  0≤C_N≤1,
M₋=∫ exp(−x/2)R(x)dx=−A(N)/r.

In particular |M₊|≤2/r and |M₋|≤(5L+1)/r. The cutoff contains the
entire relevant translate because L+3δ<log(10N+2).
For 0≤u≤L, use the full M₊ minus its initial segment. Its contribution
to the polar packet is at most

exp(−u/2)[2/r+2(exp(u)−1)/r]=2exp(u/2)/r.

The other branch is at most 2exp(u/2)(L−u)/r. For −3δ≤u≤0, use both
full moments directly; exp(−u)≤5/4 makes the coefficient at most
5(1+L). In both cases,

|polarSource R (10N) u|≤5 exp(u/2)/r · (B−u).

Together with (3), the actual signed packet satisfies

|Q_(10N)R(u)|≤27 exp(u/2)/r · (B−u).                      (4)

The prime and polar terms are combined in Q before its energy is taken.
The bound uses triangle inequality after arithmetic cancellation within (3);
it makes no claim to optimize their mixed term.

The primitive of exp(u)(B−u)² is
exp(u)[(B−u)²+2(B−u)+2]. The lower endpoint value is nonnegative.
At u=L, exp(L)/N≤5 and 1≤B−L≤4, hence

∫_J exp(u)/N · (B−u)² du≤130.

Equation (4) gives ∫_J |Q_(10N)R|²≤94770≤100000.

## Narrow source and balancing

Let H(u)=G(−u), supported on [−2δ,0]. Every prime translate vanishes
on J: for m≥2, u+log m>0 since exp(3δ)≤5/4<2, and the m=1 weight
vanishes. Its polar packet is zero for u≥0. For −3δ≤u≤0 only
0≤t≤−u≤3δ contributes. Here 2cosh(t/2)≤3, while ∫|G|≤2.
Therefore |QH|≤6 and

∫_J |QH|²≤108δ≤9/N.

Linearity and (a±b)²≤2a²+2b² now give

∫_J |QV±|²≤200000r+18/(rN)≤200018r≤300000r.

Reflection preserves autocorrelation, so the previously certified common
origin energy satisfies 6r≤h_(V±)(0)≤46r. In particular the local packet
energy divided by source origin energy is at most 50000.

## Stabilization and the pairing consequence

For u∈J and t≥log(10N+2), u+t>L, so both sources vanish. The same
support argument removes all later atoms. Thus Q_KV±=Q_(10N)V± on J
for every K≥10N, and Q_KV± vanishes for u≥L.

The exact source-packet identity and Cauchy–Schwarz localized to J yield

|pairing(K,h_(V±))|²≤300000r h_(V±)(0)≤50000 h_(V±)(0)².

For |y|≤δ, the source chord V±(u−y)−V±(u) vanishes below −3δ.
The packet vanishes above L. Its whole-line squared chord norm is exactly
2(h_(V±)(0)−h_(V±)(y)). Hence the literal increment pairing satisfies

|pairing(K,t↦h_(V±)(t+y)−h_(V±)(t))|²
  ≤600000r (h_(V±)(0)−h_(V±)(y)).

These consequences use the instantiated packet budget proved above. They do
not introduce a new receiver premise.
