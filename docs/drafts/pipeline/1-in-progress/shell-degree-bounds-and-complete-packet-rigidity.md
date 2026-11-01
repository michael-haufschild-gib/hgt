# Shell degree and complete packet rigidity

- **ID:** shell-degree-bounds-and-complete-packet-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A8.
- **Target:** Bound the literal shell degree and compare successor–dilation
  rigidity with complete Weil packet energy.

## Shell bound

For a nonnegative `C²` profile supported in `[0,1]` with positive square mass,
`0<c≤N`, and `1≤n≤N`, the proposed bound is

`0 ≤ n·d_n ≤ 2(log 4+4)e^(5/2)c + 2e^(3/2)c(n/N)(log n+1)`.

Expand the non-ratio entry as its finite upward and downward prime-lag sums.
Each autocorrelation is at most the atom mass times its window indicator.
The weighted row `Σ_m √(n/m) NR_nm` equals `n·d_n`; the two directed row
bounds give the displayed constants. This retains the position dependence
needed to distinguish a fixed prefix from the terminal horizon.

## Prime successor comparison

A candidate lower bound uses pairs `(n,pn+1)` with primes `p>Q` and
`N/2≤pn<N`. Multiplication by `p` preserves every Ramanujan mode of
conductor at most `Q`; the affine difference therefore samples the
successor difference. The prime is recoverable from the pair, so these
edges are distinct. For large enough fixed overlap, their normalized
autocorrelations have a common positive lower bound.

Restricting `p≤N/(16Q²)` makes the quadratic-horizon sampling error a
fixed fraction of the interval mass. A precise candidate is

`½ affineDirichlet ≥ (1/64) [primePoleScale(⌊N/(16Q²)⌋)−primePoleScale(Q)]
 · nonconstantPacketMass`,

for every `Q≥2` and overlap above a profile-dependent constant. Here
`primePoleScale(X)=Σ_(p≤X) log p/p`; its formalized bounded-error Mertens
law gives the scale `log N−3 log Q−C`. Continuity of autocorrelation at
zero supplies a normalized lower bound `1/2` on a sufficiently small lag
interval. The successor gap for the same packet is at least its
nonconstant mass. This comparison is unproved; the shell payment remains
in the complete energy identity.

The successor gap follows from the exact period identity
`mean (F(n+1)−F(n))² = Σ_m 2(φ(m)−μ(m))a_m²`.
The constant mode contributes zero, parity contributes `4a_2²`, and
`|μ(m)/φ(m)|≤1/2` for `m≥3` gives at least `φ(m)a_m²`.
If `gcd(p,Q!)=1`, dilation preserves each Ramanujan mode and permutes
residues modulo `Q!`. Thus the same gap holds for `F(pn+1)−F(n)`.
The existing relative affine-window bound then gives
`Σ_(A<n≤A+K) (F(pn+1)−F(n))² ≥ (K−Q(Q−1))·nonconstantPacketMass`
when `K≥Q(Q−1)`. No prime-distribution input is needed for this step.

## Remaining obligations

- Formalize the pointwise degree bound and its packet-weighted consequence.
- Combine the exact complete packet identity with CSAR rigidity, retaining
  shell, pole, and archimedean terms at fixed and growing overlap.
- Direct leaf checks and transitive axiom audits.
