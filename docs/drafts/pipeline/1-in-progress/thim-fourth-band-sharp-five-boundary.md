# Complete fourth band and sharp universal five-horizon boundary

- **ID:** thim-fourth-band-sharp-five-boundary
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Scope:** Prove the full 5N damped response envelope and its radical/power defect
  consequences; classify the largest universal linear endpoint range.

## Plan and gates

1. [x] Read objective, current README, memories; search corpus and inspect building blocks.
2. [x] Dependency-closed paper proof of the 5N envelope and symbolic sharpness mechanism.
3. [ ] Formalize actual source; audit all declaration closures.
4. [ ] Wire umbrella; index/lint; audit artifacts; update ledger/memory; clean scratch.

`update_plan` unavailable; this card tracks work. README is read-only.

## Paper proof [PROVED HERE]

For `BN<k≤(B+1)N`, complementary-divisor splitting gives
`s_N(c,k)=Σ_{d∣k}c(d)−Σ_{q∈[1,B],q∣k}c(k/q)`.
Indeed q≤B and q∣k force k/q>N. This is a uniform finite-band normal form.

For the fourth band 4N<k≤5N and c=c_ε, ε≥0:

- If 4∣k, write k=4u. All-horizon squarefree divisor absorption gives
  `s_N(c,4u)=s_N(c,2u)`, with 2≤2u≤4N. The proved 4N envelope applies.
- Otherwise quotient 4 vanishes, leaving quotients 1,2,3. If either prime is
  absent, the terminal or one-prime contraction applies. If both divide k,
  write k=6u; the fourth-band inequalities imply u≥2, and the already proved
  two-prime convex identity gives the unit envelope.

Combining with the previous initial range yields `|s_N(c_ε,k)|≤1` for every
2≤k≤5N. Radical invariance transports this to all positive powers and all
endpoints with horizon-radical representative≤5N. Discrete polarization gives
`2D≤-E≤0` for prefixes and rough-start short windows with such endpoints.

For every prime p>5, set N=6p−1 and k=30p. Then 5N<k≤6N and the visible
complementary quotients are exactly 1,2,3,5. The four distinct primes 2,3,5,p
give μ(k)=1 and μ(k/2)=μ(k/3)=μ(k/5)=−1; the complete divisor sum is zero.
Thus `s_{6p−1,μ}(30p)=2` and `k=5N+5`. Unbounded primes yield unbounded
horizons, with k/N=5+5/N tending to5 from above. Consequently, for every real C,
the universal unit-envelope property on 2≤k≤CN holds iff C≤5, both for literal
Möbius weights and for the entire nonnegatively damped family.

## Classical baseline and limits

Baseline: multiplicativity/Möbius divisor cancellation, complementary-divisor
splitting, squarefree radical invariance, and discrete polarization. Exact
classical formulation is the displayed truncated Möbius divisor-sum envelope
and explicit four-prime counterfamily. Classification: **New formulation**;
no external novelty claim. Compare the finite divisor/shifted-correlation
frameworks [TH10](https://arxiv.org/abs/1009.5281) and
[CMS16](https://arxiv.org/abs/1612.03136).

The sharpness theorem obstructs a universal endpoint-unit-envelope argument
beyond 5N. It does NOT prove positive renormalized defects there: Dirichlet
energy may still dominate the larger endpoint. The positive survivor is the
exact 5N band and its unbounded radical/power certificates.

No numerical experiments, unproved mathematical premises, added axioms,
heartbeat changes, full builds, README edits, commits, or pushes.
