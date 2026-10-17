# Actual rough Markov clamp, exact local splitting and graph rigidity

Let q be any physical L² velocity, G(t)=c+primitive q(t), and f(x)=G(exp x).
Set T(a)=min(max(a,0),1), R(a)=a−T(a). Define actual L² velocities

    q_T = (modulusVelocity q c − modulusVelocity q (c−1))/2,
    q_R = q−q_T.

No derivative, integrability or graph-admission premise is assumed. All compact
source conclusions allow zero/disconnected sources and arbitrary nonnegative
arithmetic coefficients.

## Constructed states and exact additive energy

The scalar identity T(a)=(|a|−|a−1|+1)/2 and linearity of the interval integral,
together with the previously constructed modulus primitive, give for every t

    T(c)+primitive q_T(t)=T(G(t)),
    R(c)+primitive q_R(t)=R(G(t)).

Both states are therefore locally absolutely continuous, with actual derivatives
q_T and q_R a.e. The modulus derivative formula and zero-level derivative law
at levels 0 and 1 give

    q_T=q 1_{0<G<1},    q_R=q 1_{G≤0 or G≥1}    a.e.

At either threshold q vanishes a.e.; the choice of open/closed endpoint does
not create unproved level-set assumptions. Thus q_T q_R=0 and
q²=q_T²+q_R² a.e. Integrating gives, for every oriented interval,

    E(q;a,b)=E(q_T;a,b)+E(q_R;a,b).

Transporting by t=exp x gives the identical exact split for the actual weighted
logarithmic derivative energies. For ordered intervals both terms are nonnegative,
so clamping contracts local additive energy. Every finite edge path budget splits
exactly; Tonelli gives the same addition identity for total congestion, even when
total energies are infinite.

## Firm jump contraction and admitted form

T is increasing and 1-Lipschitz. For a≤b,
0≤T(b)−T(a)≤b−a, hence R(b)−R(a)≥0. Reversing endpoints gives
ΔT ΔR≥0 in all cases. Expanding Δa=ΔT+ΔR yields

    (ΔT)²+(ΔR)² ≤ (Δa)².

Apply this to every actual graph edge and integrate the nonnegative terms over
the complete constructed diffuse/countable-line measure:

    J(q_T)+J(q_R) ≤ J(q).

The same scalar inequality with b=0 (T(0)=R(0)=0) proves
Mψ(Tf)+Mψ(Rf)≤Mψ(f). Therefore the full admitted source-mass-plus-jump form
contracts, with the removed state's form bounded by the loss. Compact-source
admission makes each term finite. Its existing variance floor gives

    Vψ(Rf) ≤ sinh(2B) [J(q)−J(q_T)].

This is a quantitative control on the portion removed by clamping. Additive
derivative orthogonality does not imply orthogonality of nonlocal jump increments;
the jump split is an inequality and retains a nonnegative interaction term.

## Complete graph equality classification

If J(q_T)=J(q), finite cancellation in the firm inequality gives J(q_R)=0.
Existing compact-graph rigidity says R(f) is constant on every nonzero source
point. Conversely J(q_R)=0 makes its squared jump zero a.e. for the actual edge
measure. The exact residual primitive then makes original and clamped jumps
equal a.e., hence their energies agree.

Every nonzero fiber of R is a singleton: R(a)<0 forces a<0 and R(a)=a;
R(a)>0 forces a>1 and R(a)=a−1. Its zero fiber is [0,1]. Hence sourcewise
constancy of R(f) is equivalent to the following disjunction:

    f is constant throughout {ψ≠0}, OR f(x)∈[0,1] whenever ψ(x)≠0.

If the source set is empty, both conditions are vacuous. If a source value lies
outside [0,1], its nonzero residual fiber forces all source values to equal it.
This proves the classifier without connectedness or positive-mass assumptions.
It concerns graph energy; source-mass equality has a different condition.

## Evidence and scope

Focused corpus search found actual modulus, rough primitive, admission and variance
building blocks, but no matching clamp realization. All returned candidate lemmas
and source arguments were inspected; incomplete freshness and unmeasured semantic
coverage limit absence claims. The classical normal-contraction notion is described
in [Brigati–Hartarsky](https://arxiv.org/abs/2205.02928) and in
[Baudoin's Dirichlet-form lecture](https://fabricebaudoin.blog/2019/02/11/lecture-5-dirichlet-forms/).
Those sources provide background, not premises for the proof above. No external
novelty, dense closed-form identification, self-adjoint generator or unitary affine
action is claimed. Markov clamping inside the constructed rough domain is one
connected contribution; its supporting lemmas are not separate contributions.

## Formal evidence

`RoughSobolevClamp.lean` has 25 public theorems and 3 definitions;
`RoughClampGraphControl.lean` has 11 public theorems. Both final serial direct
`lake --old env lean -o <normal-output> <leaf>` checks passed without diagnostics;
output timestamps postdate final sources. Both imports and all public names
are indexed. Global formal lint passed with existing large-file warnings only.
No full/umbrella build, numerical experiment or heartbeat increase was used.
All 39 public declarations passed axiom audit with exact name coverage and only
`propext`, `Classical.choice`, `Quot.sound`. Ten main signatures were inspected;
none contains an extra analytic admission premise. Whitespace checks passed.
All owned processes are terminal. This connected package is contribution **8/100**.

Evidence: `/tmp/rough-sobolev-clamp-build.log`, `/tmp/rough-clamp-graph-build.log`,
`/tmp/rough_clamp_axioms.lean`, `/tmp/rough-clamp-axioms.log`,
`/tmp/rough-clamp-index.log`, `/tmp/rough-clamp-lint.log`.
