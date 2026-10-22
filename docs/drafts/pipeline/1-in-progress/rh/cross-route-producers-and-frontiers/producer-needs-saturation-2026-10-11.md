# Producer Needs: saturation map (2026-10-11)

- **ID:** producer-needs-saturation-2026-10-11
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (survey card; no theorem)
- **Source:** Opus loop rows 2002–2032 (`rh-goal-loop-opus-2026-09-29.md`); frontier map at commit `ed2e397c0`
- **Statement:** Every producer Need on the frontier map has one of three statuses: RH-strength (a named wall), at its method's cap, or closable only with certified numerics.

## Goal
Stop re-surveying. Before proposing a producer, look up its Need here and name the input that passes the listed obstruction.

## Gates
- [x] 0 → 1  in-progress: compiled from corpus STATUS, the frontier map and loop rows
- [ ] 1 → 2  not applicable (survey)

## Map

| Need (route) | Status | Obstruction / cap | Unlock |
|---|---|---|---|
| WL `√X` one-sided source bound | RH-strength | wall 1; sieve parity loses factor 2 (rows 2002–2003) | none known |
| FU / MC fourth-power, signed bilinear | RH-strength | principal major arc (row 2004) | none known |
| RW all-aperture lower bound | RH-strength | `μ_a ≤ exp(−e^{2a})`, no slack (row 2005) | none known |
| HF PBAP (existence) | RH-strength under U; sectors near-RH (L398) | window and nonnegative cone = Connes–Consani `log 2` (rows 2009, STATUS) | certified numerics (window, C351) |
| HF U / twins (C329) | open, U-side | exactly critical interpolation (row 2021); crystalline with log density (row 2032) | quasicrystal uniqueness at log density |
| TH all-degree heat PSD | RH-strength | moment problem for `Σe^{−τγ²}δ_{γ²}` | none known |
| TH C5 current | not RH-strength, but **insignificant** | the gate card's 2026-09-05 verdict (`theta-c5-completed-compensation-direct-gate.md`): closing direct-J in every regime adds only the equispaced four-node packet stratum `{0,t,2t,3t}` of the RH-equivalent universal Bezoutian positivity (`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`). The seam is non-perturbative: the second atom's third jet `≍ (6A)³e^{−3A}` (row 2035) | none needed: not a producer step (row 2038) |
| LA all-height sign / near-double | RH-strength | CANNOT-471 (50 input classes) | sign test at critical points, exact at `½ + O(1/log T)` |
| WD full horizontal Lamzouri | density-capped | `0.655`; MUST-469 + tail law gives `0.656` (row 2023) | deep-pair density `o(N)` at fixed critical depth |
| TG Gaussian central gap `< ¼` | quasi-RH | zero-free strip | none known |
| TG fixed-scale `o(1)` bad discs | 100%-type | mollifier `θ → ∞` | none known |
| Near-line density (feeds LA/WD/TG) | at cap | `μ = 0.067`; taper `u^{99}` gives `0.063`; cap `0.0597` (row 2031) | Kloosterman-type mollifiers (`θ = 4/7`) |
| Zero proportion (feeds HD) | at cap | `0.6725`; bandwidth-one ceiling `0.68185`; mollifier inertia gives only `2κ − 1` (row 2029) | pair correlation past `α = 1` |
| Weil positivity of `Λ` at aperture `a` | numerics | certificate at `½(log 2 + 1/50)`; `μ_a ≤ exp(−e^{2a})` | certified trace certificates |
| de Bruijn–Newman upper bound | numerics | needs low real zeros up to effective KKL height (row 2020) | verified heights in Lean |
| LI, CCM multi-top, HCF | owned by the concurrent session (MUST-912–920) | — | — |

## Common pattern
- Every RH-strength core reduces to one of: √X precision at the principal frequency (wall 1), invisibility of off-line pairs at depth `≲ 1/log γ` (near-double), or the bandwidth-one/Nyquist wall.
- These are one resolution limit. Prime sums below `e^{1/δ}` cannot tell a pair at depth `δ` from a double critical zero. Bandwidth-one certificates are tight exactly at near-double configurations (row 2016). Inertia certificates bound PSD contributors only from below (row 2030).

## Log
- 2026-10-11 — created from rows 2002–2032.
- 2026-10-11 — row 2038: TH C5 reclassified. **No producer Need on the map is both non-RH-strength and significant.**
- 2026-10-11 — rows 2037–2046.
  - MUST-925 [L]: near-line moment `66/1000` via the Montgomery–Taylor proportion; insignificant, as expected.
  - Five probes (rows 2039–2043) repeated earlier rows of the loop card.
  - The twin door (C329/WP07) is the only RH-free open problem next to the producers. Its live core is C13, where the obstruction is deficits at shared zeros (row 2046).
  - A producer Need exists only as an RH-strength or capped statement.
- 2026-10-11 — rows 2047–2054, twin door (HF producer door) in Lean.
  - MUST-930 and addenda 1–3: every ζᵏ datum (k ≥ 3) that contains k−2 copies of ζ's divisor is ζᵏ. With k−3 copies it is either ζᵏ or deficient infinitely often. For k = 3 the finite-deficit no-go now needs no hypotheses (both signs).
  - Rigidity comes only from `V₂ = ℂζ²`.
  - Open: infinite deficits. The telescoping rigidity works for absolutely summable boundary packets but is exactly borderline at critical density.
- 2026-10-11 — HCF row (from `hcf-exact-layer-loop-2026-10-09.md` rows 189–255). **HCF producer Need R2 = all-rank heat Hankel positivity at one heat time. RH-strength.**
  - It must be rank-uniform: bounded rank is blind above H(N) (CANNOT-503 [L]) and detects at large time exactly the zeros with fewer than N − 2 frequencies below them (MUST-939 [L]).
  - Obstruction: the same single resolution limit as this card's common pattern. Deep zeros need wall 1. Near-line pairs sit at the derivative-channel masking threshold, and evaluating the HCF signature, which has Lesson G's shape (row 249), costs primes to `e^{C/δ}` (row 250, CANNOT-471).
  - Positivity duality (row 193): Λ ≥ 0 is never a zero-side input.
  - Unlock: none known.
