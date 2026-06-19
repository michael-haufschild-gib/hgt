# Finite-free convolution flow ⟹ RH-stability

- **ID:** finite-free-convolution-flow
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md · 00-status row #104
- **Statement:** RH = stability of the finite-free CLT fixed point under the additive arithmetic
  cumulant drift `κ_k = Σ_p κ_k(p)`.

## Goal
The degree-`d` Jensen/secular section of `Ξ` evolves by the finite free convolution `⊞_d`
(Marcus–Spielman–Srivastava), which preserves real-rootedness. Finite-free cumulants **add** under
`⊞_d`, so the criterion becomes a single additive cumulant sequence staying in the real-rooted cone —
replacing the open analytic LP-limit with an additive limit. Source-pure: built from the primes via the
per-prime kernel `K_d(p)`, not from the zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, has a runnable test, Door sketch (uses the `σ_p`
  multiplier / per-prime kernel structure)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Runnable first step: compute the finite-free cumulants of the degree-`d` section `J^{d,n}` of `Ξ` and
compare against `Σ_p κ_k(p)`. If they agree, state and attempt the additive-cumulant real-rootedness
criterion; import MSS interlacing / the finite `R`-transform as tools.

## Log
- 2026-06-19 — created in 0-backlog
