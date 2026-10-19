# Prime anchors, complete graph error, and prime-clock tightness

- **ID:** BSU-REVIEW-1910
- **Stage:** 3-formalized
- **Type:** BRIDGE
- **Source:** ../../../reports/review-1910/astra.md, §4 (U1–U3)
- **Statement:** Determine prime-anchored recovery for actual Möbius tapers, transfer its error to the complete source graph, and distinguish tight prime-clock families from escaping ones.

## Scope and verification

- [x] Read review and audit source-stratum restriction.
- [x] U1: exact mixed-observation fibres, inverse exponent, explicit anchor and horizon losses; specialize to Möbius and Barban–Vehov coefficients, including taper zeros.
- [x] U2: complete mass-plus-edge and signed-energy error estimates for the actual finite clock synthesis, with every coefficient and normalization cost retained.
- [x] U3: construct an actual-prime escaping sequence with bounded complete graph norm and vanishing diagonal cost; prove an arithmetic-parameter restriction that restores compactness.
- [x] Complete dependency-closed paper proofs before respective Lean implementations.
- [x] Check each leaf with `lake --old env lean`; wire imports without umbrella builds; audit axioms; run formal lint and record repository-wide blockers.

## Internal frontier and proof mechanism

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
Their quantitative combination gives actual-prime noncompactness.
Positive survivor: a fixed cutoff and bounded total clock amplitude place all
packets in a compact convex hull in the complete graph norm. The full clock
curve vanishes at both ends, so no center restriction is needed. This controls
singular prime edges as well as source mass.

**Internal verdict:** BRIDGE. These are source-specific quantitative
connections between established tools, not a new cancellation estimate or
an external novelty claim. User's persistent corpus-only restriction excludes
an external literature audit. No numerical experiments.

## Formal verification

Every leaf below passed its original-source `lake --old env lean` export check
with zero diagnostics. All seven are imported exactly once by the area umbrella.
The final scratch audit checked all 77 public declarations and printed every
axiom dependency: the union is exactly `propext`, `Classical.choice`, and
`Quot.sound`. Source fingerprints remained unchanged through that audit; every
compiled artifact was newer than its source. No full or umbrella build was run.

**Repository lint:** `scripts/formal_tools.py lint --check-generated` was run
after index regeneration. Generated files are current. The global gate remains
blocked by three concurrent leaves outside this card; it reports no violation
in these seven leaves:

- `BiScaleUncertainty.PrimeBlockLevelSetAndRamareHalaszEnergy`
- `BezoutValuationIncidence.KloostermanTerminalBlockAndGlobalFrequencyCollision`
- `BezoutValuationIncidence.LinearBandVaughanTypeIIBilinearEstimate`

Each blocker is an absent theorem-area umbrella import. Their source and
integration work belong to other active tasks. The full lint output is retained
in `/tmp/bsu-review1910-lint-final.log`.

| Leaf | Formalized result |
|---|---|
| `PrimeAnchorMixedRecovery` | Exact mixed-row fibres, arithmetic phase, taper zeros, attained anchor loss. |
| `PrimeAnchorMixedSharpness` | Polarization and exclusion of every inverse exponent above one. |
| `PrimeAnchorCompleteGraphError` | Literal finite synthesis, full graph and signed-energy error bounds; Möbius/BV specializations. |
| `PrimeClockGraphCompactness` | Exact atom normalization and bounded-center convex compactness. |
| `PrimeClockGraphTailTightness` | Full graph decay, compactness for all centers, and vanishing deep bounded-amplitude packets. |
| `PrimeClockGraphEscape` | Actual-prime packets with vanishing diagonal cost and energy, yet no Cauchy subsequence. |
| `PrimeAnchorHorizonBounds` | Explicit harmonic horizon costs and arithmetic reference-norm bounds. |

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

**U1 proof status:** dependency-closed paper proof; recovery, sharpness, and horizon estimates formalized.

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

**U2 proof status:** dependency-closed paper proof; complete graph estimates and arithmetic specializations formalized.

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

**U3 proof status:** dependency-closed paper proof; escape and compactness survivor formalized.

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

**Verdict:** PROVED AND FORMALIZED. The proof uses
the literal source tail and existing BV admission, rather than a generic
finite-profile assumption. External priority remains unaudited.

## Verification constraints

One owned foreground Lean process at a time; no full builds, numerical
experiments, new axioms, proof holes, or heartbeat increases. Preserve other
agents' work. Keep discoveries/failures in `logs/biscale-review1910-facts.md`.

## Paper proof: explicit horizon loss

For fixed cutoff `k`, compactness of `{0}∪Q_k(ℝ)` supplies one finite
`B_k>0` with `‖Q_k(t)‖≤B_k` for all real centers. Write
`H_N=Σ_{d=1}^N 1/d`. The literal atom identity gives

`‖F(c)‖≤B_k√N Σ_{d=1}^N |c(d)|/d`.

Since `|μ(m)|≤1`, the inversion budget at unit error satisfies

`K(1)≤B_k√N Σ_{d=1}^N⌊N/d⌋≤B_k N√N H_N`.

Thus on a fixed anchor slice of magnitude `a`, mixed-row error at most `η`
gives full graph error at most `B_k N√N H_N η/a`. For the literal Möbius
row the reference norm is at most `B_k√N H_N`; for BV it is at most
`B_k√N H_N log X` when `X≥1`. Substitution in the full quadratic
continuity bound specifies both the linear and quadratic error terms.
These are fixed-cutoff growing-horizon estimates; varying `k` retains the
original exact graph-weight budget. They do not assume a cancellation saving.

## No-go closure and scope

- **Rejected claim:** bounded complete prime-clock graph norm and vanishing
  diagonal cost imply relative compactness. The constructed actual-prime
  packets remain pairwise more than one apart while signed energies tend to zero.
- **Positive survivor:** at each fixed cutoff, bounded literal total amplitude
  gives relative compactness for all centers. Cofinal centers then force graph
  convergence to zero. Nonzero deep synthesis cannot keep amplitude bounded.
- **Arithmetic distinction:** diagonal cost is a sum of squared atom norms;
  total amplitude is `Σ√N/p`. Their behavior is not interchangeable.
- **Remaining RH obligation:** these results neither sign the complete odd form
  nor supply a cofinal small-damping Möbius cancellation estimate. The graph
  synthesis is the explicitly defined finite divisor-clock family; no unproved
  identification with a completed RH receiver is used.
- **Novelty:** source-specific bridges and an internally checked tightness
  boundary; external literature priority is not certified under corpus-only scope.
