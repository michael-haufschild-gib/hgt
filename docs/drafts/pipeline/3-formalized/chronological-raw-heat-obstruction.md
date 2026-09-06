# Raw chronological heat repair fails; persistent correction is necessary

**Status: [F] proved on paper and formalized.** Two leaf builds, all 20 new
public declarations' axiom audits, and authoritative lint passed. Only
propext, Classical.choice and Quot.sound occur. Both umbrella imports are wired;
no umbrella or full build ran. No computation or numerical zero entered a proof.

For h(t)=1/t−1/(exp(t)−1) and
R_N(t)=exp(−t)+Σ_(k≤N)μ(k)h(kt),

**||R_N||₂ does not tend to zero.** Consequently the geometric-response
coefficients b_(n,ε)=Σ_(d|n)μ(n/d)(−ε)^(d−1) cannot solve the approximation
problem along any ε_N∈[0,1/2] tending to zero. The original uniformly bounded
arbitrary-array target [R] remains unchanged and open. RH is not proved.

## Dependency-closed paper proof

1. Put g(v)=1/(exp(v)+1) and K(r)=∫₀¹g(ru)du. The exact dyadic identity is
   g(v)=2h(2v)−h(v) for v>0. For each u∈[0,1],
   exp(r)g(ru)=1/(exp(−r(1−u))+exp(−r)) is increasing in r.
   Thus w(r)=1/(exp(r)K(r)) is positive and decreasing on r≥0, with w(0)=2,
   and K(r)w(r)=exp(−r). Also 0<K(r)≤1/2. No asymptotic expansion is needed.

2. Define F_n(t)=Σ_(k≤n)μ(k)K(kt). Integrate the dyadic identity on u∈(0,1].
   Cauchy–Schwarz and exact L² scaling give
   |∫₀¹R_n(du)du|≤||R_n||₂/sqrt(d); exponential integrals are at most one.
   Hence |F_n(t)|≤3||R_n||₂/sqrt(t)+3. Independently, |F_n(t)|≤n/2.
   If ||R_n||₂≤δ for every n≥M, then all n satisfy
   |F_n(t)|≤B=3δ/sqrt(t)+3+M/2.

3. Finite Abel summation with weights w(kt) writes the exponential sum as
   weighted partial sums F_n(t), with nonnegative weights of total at most two.
   The final boundary term is included. Therefore, for every finite cutoff,
   |Σμ(k)exp(−kt)|≤2B. Absolute convergence at t>0 passes this bound to the
   genuine Möbius–Laplace transform L_μ(t):
   **sqrt(t)|L_μ(t)|≤6δ+(6+M)sqrt(t).**
   If ||R_n||₂→0, first choose its δ-tail, then let t↓0 and δ↓0. This forces
   the critical profile exp(−y/2)L_μ(exp(−y)) to tend to zero as y→∞.

4. The corpus's closed critical-boundary theorem excludes that profile limit.
   Its mechanism is the Abel final-value estimate ε Mellin(L_μ)(ρ+ε)→0.
   The pole-cleared identity Mellin(L_μ)(s)·zetaResidueUnit(s)=Γ(s)(s−1)
   and differentiability of zetaResidueUnit at a critical zero would then give
   Γ(ρ)(ρ−1)=0, which is impossible. `exists_riemannZeta_line_zero_dyadic`
   supplies an actual critical zero without RH or a numerical ordinate.
   No simple-zero hypothesis is needed. This proves [F].

5. Existing chronological damping rigidity equates damped convergence and raw
   convergence for every admissible vanishing schedule. Thus [A] is excluded.

## Positive survivor

There is c>0 such that ||R_N||₂≥c at arbitrarily large N. More strongly,
there is one c'>0 such that **every** successful arithmetic array a satisfies

||r_N(a)−R_N||₂≥c' at arbitrarily large N.

Choose c'=c/2 and use ||R_N||₂≤||r_N(a)||₂+||r_N(a)−R_N||₂ once the first
term is below c/2. No coefficient bound is needed for this necessary condition.
Convergence of each fixed coefficient toward μ, if established separately,
would therefore coexist with a correction whose full norm does not vanish.
The theorem does not yet localize that correction to a growing tail.

## Exact Lean map and audit

Namespace `RHTower`, directory `formal/GaloisForLFunctions/RHTower`.

- `ChronologicalPositiveAbelTransfer`: K, positive decreasing weights, exact
  norm scaling, the dyadic pairing, and the finite source-specific Abel estimate.
- `ChronologicalRawHeatObstruction.chronologicalRawHeat_not_convergent`:
  closed raw nonconvergence.
- `chronologicalRawHeat_frequent_floor`: the cofinal positive floor.
- `chronologicalDampedHeat_no_vanishing_schedule`: closed exclusion of [A].
- `chronologicalSuccessfulRepair_requires_persistent_correction`: the stronger
  necessary condition on every successful array.

Each source passed `lake env lean /tmp/<module>.lean`. Final audits were
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.<module>`
for each leaf separately. Existing dependency messages were replayed; only the
requested leaf compiled in each invocation. Private lemmas are audited through
all public declarations. Scratch audit artifacts are
`/tmp/chronological_raw_heat_{manifest.json,axioms.lean,axioms.txt,axiom_summary.json,lint.txt}`.
Lint passed with existing size warnings.

Related unsmoothed raw-approximation failures occur in
[Báez-Duarte's arithmetical Nyman–Beurling analysis](https://arxiv.org/abs/math/0011254).
The current heat result is proved directly by positive Abel transfer; no
inverse-smoothing inference is made. No novelty or priority claim is made for
this classical boundary-pole mechanism. The initial weighted-Mellin test proof
remains a paper cross-check; the certificate uses the shorter transfer above.
