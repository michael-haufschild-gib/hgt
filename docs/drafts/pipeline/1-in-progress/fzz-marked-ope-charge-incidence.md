# FZZ marked-OPE charge-incidence classification

- **ID:** fzz-marked-ope-charge-incidence
- **Stage:** 2-fully-proven (awaiting move)
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` (read-only) · FZZ-P mixed replica-charge/support open edge
- **Statement:** For physical `k > 2`, one marked Halder--Jafferis replica insertion has zero first-order OPE exponent against the same winding sign and a nonzero exponent against the opposite sign; after neutral-screening symmetry normalization the latter is `a(k)=2k/(k-2)`. Hence every same-winding marked prime-form/OPE response is support-blind and cannot select the Abel--Jacobi radial wall.

## Goal
Kill the chain `same-winding marked OPE response → source torus replica-area Ward law → FZZLinearReplicaAreaDivisorPassive → FZZ Mellin completeness → RH`. Positive survivor: only opposite-winding branch cuts, support motion, or higher replica order can remain.

## Gates
- [x] 0 → 1 in-progress: source-pure formula and exact RH chain identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone theorem, proof, certificate, novelty audit

## Approach
Use corpus weights `w(δ)=1-δ`, `r(δ)=1-δ/(1-2/k)` from `FZZCigarReplicaBackreaction`. Free-boson Wick contraction gives the exponent inside `|z|^{2E}`
`E_{στ}(δ)=-(k-2)r(δ)/2 + kστ w(δ)/2`.
Prove `E_{σσ}(δ)=1` and `E_{σ,-σ}(δ)=1-k+kδ`. Differentiating one representative and restoring `2s'=2/(k-2)` marked-insertion symmetry gives the published surviving factor `2k/(k-2)` and resolves the literal `(…)` omitted in Halder--Jafferis (3.30) as zero. Then prove arbitrary same-sign prime-form kernels have zero tangent and admit no value predicate selecting `Im λ=0`.

## Paper proof
`[PROVED HERE]` Put `r(δ)=1-kδ/(k-2)` and `w(δ)=1-δ`. With the free-boson normalization fixed by the undeformed exponents `E_same(0)=1` and `E_opp(0)=1-k`, contraction of one marked field with one undeformed field gives
`E_same(δ)=-(k-2)r(δ)/2+kw(δ)/2=1` and
`E_opp(δ)=-(k-2)r(δ)/2-kw(δ)/2=1-k+kδ`.
Thus the same-sign difference from `δ=0` is exactly zero, not merely zero to first order. The opposite-sign difference is `kδ`. The neutral sphere residue has `s'=1/(k-2)` insertions of each sign after analytic continuation; differentiating one representative and restoring the `2s'` marked-insertion symmetry multiplies the differences by `2/(k-2)`. Hence the effective exponents are `0` and `(2k/(k-2))δ`, exactly Halder--Jafferis' `a(k)δ`. For any support kernel `K`, the symmetry-normalized logarithmic response therefore reduces to `(2k/(k-2))δ K_opposite`; the same-sign support term vanishes identically. In particular its value is identical at Abel twists `0` and `i`, while only the first lies on `Im λ=0`; no value predicate can select that wall. No analytic, divisor, or RH premise is used.

## Hostile attacks
- Opposite sign: expected to survive; theorem must not overclaim.
- Area sum `Wδ⁺+Wδ⁻`: kills only diagonal charge blocks, not cross blocks.
- External BRST vertices and branch cuts: outside killed branch.
- Support motion and second replica order: outside killed branch.
- Convention audit: base exponents must recover `1` and `1-k`; symmetry-normalized cross coefficient must recover `a(k)`.

## Novelty
Corpus search found replica weights, neutrality, and final area selector, but no marked OPE charge-block calculation. Literature audit through 2026-08 found Halder--Jafferis (3.30) leaves the same-sign coefficient literally as `(…)`; no later source resolves it or proves the associated Abel-wall no-go. Status: preliminary until proof and formal audit finish.

## Log
- 2026-09-01 — conjecture frozen after corpus and primary-source reconstruction; preliminary hostile audit passed.
