# The erosion threshold: ½ as the marginal-variance locus (G19)

- **ID:** erosion-threshold
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-time-and-non-holonomic-time.md · 00-status row #59
- **Statement:** The critical line is the marginal-variance locus of the infinite-frequency Euler
  cocycle: the Euler weight gives variance `Σ_p p^{-2σ}`, which diverges (`~loglog`) at `σ=½` and
  converges for `σ>½`.

## Goal
An intrinsic, non-circular meaning for `Re = ½`: it is where the infinite-frequency prime cocycle is
critically tuned (more frequencies average out hyperbolicity, so the generic `∞`-frequency cocycle is
integrable; `½` is the unique marginal coupling). Does not assume RH. The marginal regime's analytics
(Selberg's CLT, Ingham, Keating–Snaith) are already theorems.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure (prime weights only), attack idea, Door sketch
  (the `𝕋^∞` boundary flow of the `σ_p` family)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Write the variance/erosion criterion explicitly; show `σ>½ ⟹ L=0` (Bohr–Jessen zero-free) and `σ=½`
marginal; connect the marginal cocycle to Selberg's CLT (the zeros as its degenerations). Target: a
clean statement that the half-line is the erosion threshold, with the cocycle inputs cited.

## Log
- 2026-06-19 — created in 0-backlog
