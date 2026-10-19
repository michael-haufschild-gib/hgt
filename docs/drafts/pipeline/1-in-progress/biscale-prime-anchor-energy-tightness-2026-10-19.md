# Prime anchors, complete graph error, and prime-clock tightness

- **ID:** BSU-REVIEW-1910
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-1910/astra.md, §4 (U1–U3)
- **Statement:** Determine prime-anchored recovery for actual Möbius tapers, transfer its error to the complete source graph, and distinguish tight prime-clock families from escaping ones.

## Scope and gates

- [x] Read review and audit source-stratum restriction.
- [ ] U1: exact mixed-observation fibres, inverse exponent, explicit anchor and horizon losses; specialize to Möbius and Barban–Vehov coefficients, including taper zeros.
- [ ] U2: complete mass-plus-edge and signed-energy error estimates for the actual finite clock synthesis, with every coefficient and normalization cost retained.
- [ ] U3: construct an actual-prime escaping sequence with bounded complete graph norm and vanishing diagonal cost; prove an arithmetic-parameter restriction that restores compactness.
- [ ] Complete dependency-closed paper proofs before respective Lean implementations.
- [ ] Check each leaf with `lake --old env lean`; wire imports without umbrella builds; audit axioms and formal lint.

## Internal frontier and candidate attack

`SieveArithmeticSourceAnchors` proves the terminal-prime coordinate is
`-w(p)/p` and the BV anchor survives iff `p<X`. Highest-dyadic recovery
does not apply to squarefree rows when `N≥4`.

Use the mixed quadratic row `M_p(c)(q)=Y_c(p)Y_c(q)`, including `q=p`.
At a nonzero anchor, its only possible global ambiguity is simultaneous sign;
the arithmetic negative-anchor branch removes it. At a zero anchor the entire
row vanishes. Recovery must retain the inverse anchor cost and cannot be
advertised as horizon-uniform. This observation model is richer than diagonal
Selberg data and must be stated explicitly.

The corpus already proves
`|E(P)-E(Q)| ≤ ‖P-Q‖²+2‖P-Q‖‖Q‖` in the full source graph.
The new obligation is to bound `‖P-Q‖` from the specified observations for
literal finite arithmetic-clock synthesis, using finite Möbius inversion.
An arbitrary unspecified bounded synthesis operator would not discharge U2.

`exists_cutoff_eventually_criticalPrimeGraphClock_realization` approximates
every full graph vector by actual positive prime-clock sums with arbitrarily
small diagonal norm cost. `CHMDEscape.exists_primitive_escape` supplies a
bounded, mass-orthogonal sequence with complete energy tending to zero.
Their quantitative combination should give actual-prime noncompactness.
Positive survivor: a fixed cutoff, compact log-center interval, and bounded
total clock amplitude place all packets in a compact convex hull in the
complete graph norm. This controls singular prime edges, not only source mass.

**Preliminary verdict:** BRIDGE. These are source-specific quantitative
connections between established tools, not a new cancellation estimate or
an external novelty claim. User's persistent corpus-only restriction excludes
an external literature audit. No numerical experiments.

## Open proof obligations

- `[OPEN CORE U1]` Quantitative mixed-row inverse with variable anchor.
- `[OPEN CORE U2]` Explicit finite Möbius-inversion graph synthesis cost.
- `[OPEN CORE U3]` Actual-prime escape and compact center/amplitude survivor.

## Paper proof: mixed prime row (U1)

Write `y_q=Y_c(q)`, `z_q=Y_b(q)`, `a=y_p`, `b=z_p`, and
`e_q=|a y_q-b z_q|`. Include every `1≤q≤N` and the anchor square `q=p`.
If `b≠0`, equality of observations first gives `a²=b²`, hence `a=b`
or `a=-b`. The remaining products then give `y=z` or `y=-z` on the
whole active range. Finite multiples inversion gives the corresponding
coefficient equality. Conversely either simultaneous sign gives the same
quadratic row. If `b=0`, the zero row is equivalent to `a=0`; its fibre
is the entire anchor hyperplane. These statements apply on the squarefree
subspace as well, without introducing a highest-dyadic coordinate.

The identity `a(y_q-z_q)=(a y_q-b z_q)+(b-a)z_q` and triangle inequality give
`|a| |y_q-z_q| ≤ e_q+|a-b||z_q|`. Multiply by `|a+b|` and use
`|a-b||a+b|=|a²-b²|=e_p` to obtain the unconditional estimate

`|a||a+b||y_q-z_q| ≤ |a+b|e_q+|z_q|e_p`.

For two nonnegative Möbius tapers at a terminal prime,
`a=-w(p)/p`, `b=-v(p)/p`. Positive taper values select the same negative
branch, with denominator `D=w(p)(w(p)+v(p))/p²>0`. Thus the inverse is
Lipschitz, with fully displayed loss `1/D`; its coefficientwise numerator
is the displayed linear expression in observation errors. If the anchor
is held fixed, `e_p=0`, and the exact coordinate loss is `p/w(p)`.

Perturb only coefficient 1 by `t`. The anchor stays fixed because `p>1`;
only `Y(1)` changes, by `t`. Consequently only mixed coordinate 1 changes,
by `a t`. This remains a squarefree-supported Möbius taper when its first
taper is adjusted nonnegatively. The inverse cost `p/w(p)` is attained.
The nonconstant affine observation dependence also rules out any local
inverse exponent above 1. For BV the anchor amplitude is
`log(X/p)/p` for `p<X`, and zero otherwise. Its loss diverges as that
amplitude shrinks; a prime in the terminal interval is insufficient.

**U1 proof status:** dependency-closed paper proof; Lean implementation pending.

## Paper proof: full finite clock energy (U2)

Fix the canonical cutoff `k`, horizon `N`, and use the existing literal atoms
`A_d=canonicalPrimeGraphClockAtom k N d` (the definition also admits composite
positive divisors). Define `F(c)=Σ_{1≤d≤N} c(d) A_d`. This is a specified
finite arithmetic clock family in the original full source graph. No claim
identifies it with a completed RH receiver without a further limit theorem.

Finite multiples inversion gives, for every active divisor,

`c(d)-b(d)=d Σ_{1≤m≤N/d} μ(m)(Y_c(dm)-Y_b(dm))`.

For any nonnegative coordinate-error majorant `r`, therefore,

`‖F(c)-F(b)‖ ≤ K(r)` where

`K(r)=Σ_{d=1}^N d ‖A_d‖ Σ_{m=1}^{⌊N/d⌋}|μ(m)| r(dm)`.

There is no unspecified operator norm: `‖A_d‖=(√N/d)‖Q_k(log(N/d))‖`,
where `Q_k` is the existing full graph-valued cutoff clock. The weights
include mass, archimedean edges, and every prime-power edge. All product
cutoffs and the normalization `√N/d` remain visible.

For live same-sign anchors, put
`D=|a||a+b|` and `r(q)=(|a+b|e_q+|Y_b(q)|e_p)/D`.
U1 proves this majorant pointwise. Hence, with this exact `K`,

`|E(F(c))-E(F(b))| ≤ K²+2K‖F(b)‖`.

This is a linear observation-error estimate on bounded-error sets: if
`e_q≤η≤1`, let `L=K((|a+b|+|Y_b(q)|)/D)`; then
`|ΔE|≤(L²+2L‖F(b)‖)η`. A joint limit must pay `Lη→0` and
`Lη‖F(b)‖→0`. In particular, recovering coefficients with an unpriced
shrinking prime anchor cannot be substituted for this estimate.

**U2 proof status:** dependency-closed paper proof; Lean implementation pending.

## Paper proof: escape and compactness survivor (U3)

Take the existing primitive escape `u_n`, with orthogonal unit mass
projections and `‖u_n‖≤2`. At tolerance `ε_n=1/(16(n+1))`, actual-prime
synthesis produces `P_n=Σ_{p∈S_n}A_{k_n,N_n,p}` with `N_n≥n`, every
`p>√N_n`, every log-center above `n`, `‖P_n-u_n‖<ε_n`, and diagonal
cost below `ε_n`. Thus `‖P_n‖<3` and `E(P_n)→0` by full graph continuity.
For distinct indices, the original mass distance is `√2`; graph distance
is at least this. Two approximation errors sum to at most `1/8`, giving
`‖P_n-P_m‖>1`. No subsequence is Cauchy. All singular prime costs have
already been included in each norm. Bounded complete energy and vanishing
diagonal cost therefore do not provide prime-clock tightness.

For the positive survivor fix `k`, `T`, `R`, and `C≥0`. Restrict actual-prime
packets to log-centers in `[T,R]` and total amplitude
`Σ_{p∈S}√N/p≤C`. The curve `Q_k` is continuous in the complete graph
norm, so `K={0}∪Q_k([T,R])` is compact. Every packet belongs to
`C·conv(K)` (for `C=0` every amplitude vanishes). The closure of the
convex hull of a totally bounded subset of a complete normed space is
compact. Hence these packets are relatively compact in the full graph.
This is an explicit center/amplitude restriction, not an assumed energy
tail bound. The escape construction demonstrates why restrictions beyond
diagonal smallness are necessary; it does not claim this sufficient
restriction is necessary for every family.

**U3 proof status:** dependency-closed paper proof; Lean implementation pending.

## Stronger positive survivor: center bounds are unnecessary

The literal Abel log profile vanishes for nonpositive arguments and tends to
zero at positive infinity (`MobiusDivisorCriticalLogProfileTail`, using its
velocity-tail identity). For fixed canonical cutoff `χ_k`, compact support
therefore makes `χ_k(x) f(t-x)` tend uniformly to zero as `t→±∞`.
`criticalClockCutoff_variation_bound` is uniform in `t`.
`tendsto_bvLift_zero_of_uniform` upgrades this convergence to the **full**
graph norm. Thus `Q_k(t)→0` at both ends.

Consequently `{0}∪Q_k(ℝ)` is compact, and its closed convex hull is compact.
The preceding center/amplitude proof works for **all centers** once `k` is
fixed and total amplitude is bounded. This is stronger than the initially
proposed compact-center survivor; no extra analytic premise is required.
For packets whose minimum center tends to infinity, the same bounded-amplitude
condition gives convergence to zero in full graph norm. Hence nonzero deep
synthesis at a fixed cutoff forces amplitude growth. The obstruction is
not the mere increase of the prime indices.

**Verdict:** SURVIVES PRELIMINARY INTERNAL ATTACK. Complete paper proof uses
the literal source tail and existing BV admission, rather than a generic
finite-profile assumption. External priority remains unaudited.

## Verification constraints

One owned foreground Lean process at a time; no full builds, numerical
experiments, new axioms, proof holes, or heartbeat increases. Preserve other
agents' work. Keep discoveries/failures in `logs/biscale-review1910-facts.md`.
