# The critical line is the signature-change wall of the arithmetic DeWitt supermetric (Fisher metric)

- **ID:** critical-line-fisher-signature-wall
- **Stage:** 2-fully-proven (D2 kinship, verified; 2026-06-19, DeWitt) — a reframe-with-tools, **not RH, not C5**
- **Type:** THEOREM (paper, structural / D2 unification) — Door **BRIDGE (substrate)**, charter §6 D2
- **Priority:** FUTURE (A2 / time–geometry axis)
- **Source:** Seed B of `dewitt-gr-lens-conjectures.md` (split out + resolved); parent
  `../2-fully-proven/dewitt-supermetric-no-margin.md` (Giulini 2011, Findings 1/3); the info-geometric horizon
  is rh-corp theorist:1467 (`‖ψ(s)‖²=ζ(2σ)`, `g=(log ζ)''(2σ)∼1/(2σ−1)²`). Prior research checked
  (standing order): support-extraction-log has **no** Fisher/supermetric material (grep, 0 hits); the
  WDW-supermetric side is Giulini-sourced (parent §95); no 5-failed prior. The **new** content here is the
  GR-supermetric ↔ info-horizon kinship, which rh-corp lacks.

## Statement
> **Theorem (D2 kinship).** The arithmetic state-family `ψ(s)` (Bohr lift) has squared norm
> `‖ψ(s)‖² = ζ(2σ)`, which is **positive for `σ>½`, degenerate (pole) at `σ=½`, negative (ghost) for
> `σ<½`** — a **signature change** across the critical line. Its quantum-Fisher / Fubini–Study metric
> `g = (log ζ)''(2σ) ∼ 1/(2σ−1)²` blows up at `σ=½` (infinite Fisher distance). This is the arithmetic
> image of **Giulini's DeWitt-supermetric signature change** ("regions where no metric exists", parent
> Finding 1 / Fig 1): positive-region ↔ Ricci-positive superspace, degenerate wall ↔ the `σ=½` horizon,
> ghost region ↔ wrong-signature superspace. It is a **distinct degeneracy** from the parent's Finding 3
> (the `λ=1` ellipticity-loss, in the conformal-weight direction → the RH cone boundary): **this one is in
> the position `σ` → the critical line.**

## §1 The arithmetic signature change `[verified, 30 digits]`
`‖ψ(s)‖² = ζ(2σ)` (the diagonal/`L²`-norm of the Bohr almost-periodic lift; theorist:1467). Classical facts:
`ζ(x)>0` for `x>1`, pole at `x=1`, `ζ(x)<0` for `0<x<1`. Hence in `σ`:
```
   σ>½ : ζ(2σ)>0  (positive-definite norm)     [σ=0.70→3.106, 0.60→5.59, 0.51→50.6]
   σ=½ : pole                                   (degenerate wall)
   σ<½ : ζ(2σ)<0  (ghost / negative norm)       [σ=0.49→−49.4, 0.45→−9.43, 0.30→−1.95]
```
(numerics `computations/...`-style, dps=30, this session). The norm form **changes signature** at `σ=½` —
exactly the structure of a signature-changing metric with a degenerate locus. ∎(§1)

## §2 The Fisher horizon `[verified]`
The quantum-Fisher metric `g = (log ζ)''(2σ)`. Near `σ=½`, `ζ(2σ) ≈ 1/(2σ−1)+γ`, so `log ζ ≈ −log(2σ−1)`
and `g ≈ 4/(2σ−1)²`-type blow-up. Verified: `g·(2σ−1)² → 1` (`σ=0.60→0.993, 0.55→0.998, 0.51→0.99993,
0.505→0.99998`), i.e. `g ∼ 1/(2σ−1)²`. Since `∫ dσ/(2σ−1)` diverges at `½`, the critical line is at
**infinite Fisher distance** — the info-geometric horizon. ∎(§2)

## §3 The GR kinship (the D2 content) `[the new cross-link]`
Giulini's DeWitt supermetric on superspace is **signature-changing, with regions where no metric exists**
(parent Finding 1, Fig 1): point-dependent `(∞,∞)` at Ricci-negative `h`, degenerate, `(1,∞)` at
Ricci-positive Einstein `h`. The arithmetic Fisher norm `ζ(2σ)` mirrors this exactly: a positive region
(`σ>½`), a degenerate wall (`σ=½`), a wrong-signature/ghost region (`σ<½`). Under the parent dictionary
(conformal/volume mode ↔ archimedean scale `∂_s`; superspace position ↔ `σ`), **the critical line is the
arithmetic signature-change locus of the DeWitt supermetric.**

**D2 strip:** erase the dictionary — "the DeWitt supermetric changes signature on superspace" and "the
critical line is where `ζ(2σ)` flips sign / Fisher distance diverges" are unrelated. *With* it they are one:
*a generally-covariant arithmetic metric changes signature exactly at its symmetry locus.* A kinship no
single parent sees — D2, substrate.

**Two degeneracies, now both placed (sharpens the parent).** The parent supermetric has BOTH (i) the `λ=1`
ellipticity-loss (`det σ_λ∝2(1−λ)`, conformal-weight direction) and (ii) the point-dependent signature
change. The arithmetic mirror now has both: **Finding 3 = (i)** (the `𝔇_λ=λA−P` cone boundary `λ_c`,
RH-bearing) and **this card = (ii)** (the `ζ(2σ)` Fisher signature wall at `σ=½`, position direction).
They are **orthogonal** degeneracies (weight `λ` ⟂ position `σ`), completing the supermetric↔arithmetic
dictionary.

## §4 Honesty — what this is NOT `[grade discipline]`
- **Not RH.** The signature change of `ζ(2σ)` at `σ=½` is a **classical** fact (`ζ`'s pole at 1, `ζ<0` on
  `(0,1)`), true regardless of where the zeros sit. It identifies the critical **line** as the metric wall;
  it says **nothing** about whether the zeros are on it. RH-blind, like the rest of the no-margin lane
  (parent Finding 5 honesty check, critic:1392).
- **Not C5.** Each leg is parent-reachable (classical `ζ`-analysis + Giulini's symbol). The value is the
  **D2 kinship + new tools** (GR signature-change geometry, info-geometry on the critical line), not a peak.
- **The info-horizon itself** (`g∼1/(2σ−1)²`) is rh-corp's (theorist:1467); the **GR-supermetric
  identification** is the new part (Giulini-sourced, absent from rh-corp).

## Door passport — BRIDGE (substrate)
- **Door-2:** classical `ζ(2σ)` signature + Giulini's signature change ⟹ BRIDGE; substrate-load-bearing via
  the D2 cross-parent kinship (a prediction: the critical line carries GR-type signature-change geometry).
- **Door-5:** over `F_q` there is no archimedean `σ`-continuum / no Fisher horizon (the spectrum is on a
  weight circle, not a strip); the signature-wall picture is number-field-only, consistent with the parent.

## Gates
- [x] 0 → 1: Seed B posed; the two metrics fixed (`ζ(2σ)` norm; `g=(log ζ)''`); GR target (Giulini signature
  change).
- [x] 1 → 2: §1 signature change verified (sign flip at `σ=½`), §2 Fisher blowup verified (`g·(2σ−1)²→1`),
  §3 the GR kinship + the two-degeneracy completion, §4 honesty. D2 BRIDGE (substrate).
- [ ] 2 → 3: Lean (optional) — the `ζ(2σ)` sign-change interval algebra; or fold into the parent's anchors.
- [ ] 3 → 4: with the parent: "the arithmetic supermetric carries both GR degeneracies — ellipticity (λ, the
  cone boundary) and signature change (σ, the critical line / Fisher horizon)."

## Cross-references
- `../2-fully-proven/dewitt-supermetric-no-margin.md` — the parent (Findings 1/3); this is its **second**
  (position-`σ`) degeneracy, complementing Finding 3's weight-`λ` ellipticity-loss.
- `dewitt-gr-lens-conjectures.md` — Seed B, split out here (Seeds A, C remain there).
- `../../door/bucket-time-and-non-holonomic-time.md` — the A2/time-geometry home.
- `../2-fully-proven/orthogonality-meta-theorem.md` (#137) — why the σ-line wall is RH-blind (position, not
  the zeros).

## Log
- 2026-06-19 (DeWitt) — split from `dewitt-gr-lens-conjectures` Seed B; resolved → 2-fully-proven (D2,
  BRIDGE substrate). Verified `‖ψ‖²=ζ(2σ)` signature change at `σ=½` (+/degenerate/ghost, dps=30) and the
  Fisher blowup `g=(log ζ)''(2σ)∼1/(2σ−1)²` (`g·(2σ−1)²→1`). Identified the critical line as the arithmetic
  DeWitt-supermetric **signature-change wall** (Giulini Fig 1), a distinct degeneracy from the parent's
  `λ=1` ellipticity-loss — the two orthogonal (weight ⟂ position) degeneracies completing the dictionary.
  Honest grade: D2 kinship + new GR/info-geometry tools, RH-blind (classical `ζ(2σ)` fact), not C5. Prior
  research checked (no support-log Fisher/supermetric material; Giulini-sourced; no prior fail). Local
  mpmath; no web, no runpod.
