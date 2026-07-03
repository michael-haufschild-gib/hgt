# RH tower/obstruction language: ξ-Kummer tower, RH_{2^k} ladder, root equivalence

- **ID:** rh-tower-lang
- **Stage:** 0-backlog
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/00-approach.md §3 (Arc A of 01-research-plan.md)
- **Statement:** For Ω = {Re s > 1/2} and ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s): (i) generic
  root⟺divisibility lemma (∃ analytic n-th root on simply connected Ω ↔ n divides every zero
  order); (ii) `RiemannHypothesis` ↔ coherent ℤ₂-Kummer tower of ξ on Ω; (iii) ladder
  RH_{2^k} := "2^k ∣ m(ρ) for all zeros in Ω" satisfies RH_{2^k} ↔ ∃ analytic 2^k-th root,
  and RH ↔ ∀k RH_{2^k}.

## Goal
Banks the branch-native language for the MWM lane (docs/drafts/rh-monodromy-weight-mismatch):
RH stated as a branching/tower obstruction, graded by multiplicity parity. Level 1 of the
ladder ("no odd-multiplicity — in particular no simple — off-line zeros") is the lane's first
open target; this card only builds the certified scaffolding. Non-circularity: (i)–(iii) are
elementary complex analysis over mathlib's `completedRiemannZeta`; no RH-strength input.

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `rh_iff_tower` + `rh_ladder_root` + `rh_iff_forall_ladder`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Reuse banked machinery: `exists_analyticOnNhd_pow_eq` (U0/U0KummerBranch.lean:100),
`analyticOnNhd_of_continuousOn_exp_eq` (:40), coherent-tower pattern
`u0_coherent_kummer_tower` (:224). Mathlib names probed 2026-07-03 on this toolchain:
`riemannZeta`, `completedRiemannZeta(₀)`, `completedRiemannZeta_one_sub`,
`RiemannHypothesis`, `riemannZeta_eulerProduct_tprod/_hasProd`,
`riemannZeta_ne_zero_of_one_lt_re` all exist; `riemannXi` does NOT — define ξ locally,
clear the poles with the s(s−1)/2 factor. Root⟸divisibility direction: path log on Ω∖Z,
single-valuedness from divisibility, removable singularity via |g| = |ξ|^{1/n} → 0.
Probe order-of-vanishing API (`analyticOrderAt`) and removable-singularity API in /tmp first.

## Log
- 2026-07-03 — created in 0-backlog (MWM lane opening; see rh-monodromy-weight-mismatch/)
