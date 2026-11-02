# Shell degree and complete packet rigidity

- **ID:** shell-degree-bounds-and-complete-packet-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A8.
- **Target:** Bound the literal shell degree and compare successor–dilation
  rigidity with complete Weil packet energy.

## Shell bound

For a nonnegative `C²` profile supported in `[0,1]` with positive square mass,
`0<c≤N`, and `1≤n≤N`, the formalized bound is

`0 ≤ n·d_n ≤ 2(log 4+4)e^(5/2)c + 2e^(3/2)c(n/N)(log n+1)`.

Expand the non-ratio entry as its finite upward and downward prime-lag sums.
Each autocorrelation is at most the atom mass times its window indicator.
The weighted row `Σ_m √(n/m) NR_nm` equals `n·d_n`; the two directed row
bounds give the displayed constants. This retains the position dependence
needed to distinguish a fixed prefix from the terminal horizon.

`ArithmeticCouplingTheory/TheShellDegreeHasAnExplicitRowBound.lean` proves
`nat_mul_shellDegree_le_explicit`, `shellDegree_nonneg`, and
`shellDegree_packet_payment_le`. The latter bounds `Σ_n d_n F(n)²` by the
corresponding harmonic and terminal logarithmic masses. Direct leaf and
transitive axiom audits pass; only `propext`, `Classical.choice`, and
`Quot.sound` occur. The umbrella includes the leaf.

## Prime successor comparison

For every nonnegative nonzero `C²` profile supported in `[0,1]`, some fixed
profile-dependent overlap threshold gives, for all `N≥1`, `Q≥2` and coefficient families,

`½ affineDirichlet ≥ (1/64) [primePoleScale(⌊N/(16Q²)⌋)−primePoleScale(Q)]
 · nonconstantPacketMass`.

The actual edges `(n,pn+1)`, with `Q<p≤N/(16Q²)` prime and
`N/(2p)<n≤N/(2p)+N/(4p)`, have weight at least `log p/(2N)`.
Their interval mass is at least `N/(16p)` times the nonconstant packet mass,
by the coprime-successor window gap. Distinct `(p,n)` give distinct ordered
edges, so their contributions sum inside the literal affine Dirichlet energy.
No prime-distribution estimate is needed.

The kernel-checked comparison and its paper proof are recorded in
[Prime successor edges pay nonconstant packet mass](../3-formalized/prime-successor-edges-pay-packet-mass.md).

## Remaining obligations

- Combine the exact complete packet identity with CSAR rigidity, retaining
  shell, pole, and archimedean terms at fixed and growing overlap.
