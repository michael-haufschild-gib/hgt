# Literal Euler-deletion covariance

**Status:** Lean-proved standard bridge. Not an RH producer.

**Checked source:** `CoprimeBlockCarryTransgression.blockDeletionCoefficient`,
`EulerDeletionQuasiShuffleScaling`, `EulerDeletionQuasiShuffleConvergence`.
Full-corpus searches checked deletion covariance, divisibility expectations,
Dirichlet Gram/LCM kernels, and reusable infinite-sum reindexing. The latter
exists privately in CCM for a different Schwartz carrier. Concurrent signature
files are outside this card's write scope.

**Exact surviving edge:** evaluate the quadratic accounting of the literal
infinite deletion source before Xi selection. This does not discharge the
unproved replication/dilation coherence or any RH order gate.

For `a_p(n)=1-p[p|n]`, `alpha>1`, and `Z(alpha)=sum_{n>=1} n^(-alpha)`,

`sum a_p(n)a_q(n)n^(-alpha)`
`= Z(alpha) [1-p p^(-alpha)-q q^(-alpha)+p q lcm(p,q)^(-alpha)]`.

All sums converge absolutely. For coprime moduli, subtracting the product
of normalized means leaves zero covariance; the uncentered cross term is
`Z(alpha)(1-p p^(-alpha))(1-q q^(-alpha))`, not zero. On the diagonal,
the centered variance is `Z(alpha) p^2 p^(-alpha)(1-p^(-alpha))`, strictly
positive for `p>1`. Thus arithmetic independence removes centered cross terms
but does not remove the source's positive diagonal energy.

**Proof:** expand both deletion coefficients. Multiples of `d` contribute
`d^(-alpha) Z(alpha)` by the bijection `k -> d k`; their intersection is the
set of multiples of `lcm(p,q)`. Absolute convergence follows by domination
with a constant times the convergent positive Dirichlet series. Coprime
factorization and the diagonal formula are algebraic consequences.

**Classification:** elementary zeta-distribution/divisibility covariance,
not a novelty claim. Its purpose is to prevent confusing centering with
annihilation in the live chronological-signature source comparison. No
numerical experiment is needed; no RunPod job is launched.

## Formal result

`RHTower/EulerDeletionDirichletGram.lean` proves the complete complex-source
identity for `u_p(s,n)=a_p(n)n^(-s)`, `Re s>1/2`:

`sum u_p(s,n) conjugate(u_q(s,n))`
`= zeta(2 Re s) [1-p p^(-2 Re s)-q q^(-2 Re s)+p q lcm(p,q)^(-2 Re s)]`.

The full complex pairing, not merely its real part, is identified and is
absolutely summable. The source at index zero vanishes; positive integer
coefficients and modulus labels are unchanged. The Gram intentionally loses
the common Mellin phase: no phase-faithful inverse recovery or Xi divisor
multiplicity transport is asserted.

Principal declarations (namespace `RHTower`):

- `tsum_deletionMellinSource_pair`: literal complex-source formula.
- `summable_norm_deletionMellinSource_pair`: absolute admission.
- `deletionDirichletMass_eq_riemannZeta`: actual zeta normalization.
- `tsum_deletionCenteredCoefficient_pair`: exact centered LCM covariance.
- `tsum_deletionCenteredCoefficient_pair_of_coprime`: centered orthogonality.
- `tsum_deletionCenteredCoefficient_sq_pos`: retained positive diagonal.

Scratch and published leaf checks pass without warnings. Nine principal axiom
audits report only `propext`, `Classical.choice`, `Quot.sound`. The module is
wired into RHTower; no umbrella build ran. Global lint's sole error at audit
time was the concurrently added, unrelated unwired
`HTGeometry.DispersivePDE.BrizardElasticaTravelingMomentum`.

**Open:** an independent source law identifying chronological replication with
Euler dilation. This covariance calculation neither supplies that law nor
changes the arithmetic cubic route's open off-line zero-charge problem.
