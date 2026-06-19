# Is the de Bruijn–Newman constant Λ a period? — FALSE LEAD (collapses to RH)

- **ID:** is-lambda-a-period
- **Stage:** 5-failed (the transcendence-probe framing is degenerate; closed 2026-06-19, DeWitt)
- **Type:** CONJECTURE → **FALSE LEAD / DEGENERATE** (reduces to RH; PSLQ structurally inapplicable)
- **Priority:** FUTURE
- **Source:** ../../door/bucket-the-no-margin.md (#85 SEED-W) · 00-status row #95; support-extraction-log
  #87 §12 (Λ = TP-onset time; `Λ≤0 ⟺ Ξ∈Laguerre–Pólya ⟺ RH`; `Λ=0` = the seam/no-margin).
- **Original statement:** Is the de Bruijn–Newman constant `Λ` (RH ⟺ `Λ=0`; Rodgers–Tao `Λ≥0`) itself a
  **period / transcendental**? Attack proposed: a PSLQ probe of `Λ` against the secular-period basis.

## Verdict — the question is RH-degenerate; the proposed attack is structurally impossible
Worked 2026-06-19 (DeWitt). The card's framing does **not** survive scrutiny:

### F1 — `Λ`'s value is RH-equivalent, so "is `Λ` a period" carries no independent content
- Rodgers–Tao (2018, proven import): `Λ ≥ 0`. de Bruijn: `Λ ≤ 1/2` (Polymath15: `Λ ≤ 0.2`). RH ⟺ `Λ ≤ 0`.
  Combined: **RH ⟺ `Λ = 0`.**
- **Under RH:** `Λ = 0 ∈ ℚ` — trivially a period. The answer is "yes, degenerately," and says nothing.
- **Only in the RH-false world** is `Λ > 0` a nontrivial real — but then its value is defined *implicitly*
  as the zero-collision / TP-onset supremum of the heat flow, with **no closed form**.
- So "is `Λ` a period?" is **not independent of RH**: at the only distinguished value it IS RH
  (`Λ=0 ⟺ RH`). It is RH in disguise, not a transcendence question of its own.

### F2 — the PSLQ probe is structurally impossible (not merely hard)
PSLQ requires the target to many proven digits. `Λ` is known only to the **bounds** `0 ≤ Λ ≤ 0.2`; there is
**no algorithm producing its digits**, because pinning `Λ` below any positive `ε` is an RH-strength
statement (it would bound the heat-flow's complex zeros). A PSLQ run would need a number we provably cannot
compute. The proposed attack cannot be executed — no runpod, no precision, will change this. (Contrast: the
Stieltjes `γ_n` ARE computable to arbitrary precision, which is why their PSLQ probes — Professor's
realization, the DSS-cross numerics — are legitimate. `Λ` is not in that class.)

### F3 — salvage: the no-margin is TAME (Λ=0), opposite the seam from the WILD `γ_n`
The one positive structural fact, via the exponential-motivic / `𝓡`-tame vs `K`-wild framework
(`exponential-period-dss-cross`, `regularization-freshness`):
> **Under RH the no-margin is the tame rational point `Λ=0 ∈ ℚ ⊂ 𝓡`** — it is *not* a fresh/wild
> regularization constant. So the no-margin (`Λ`) and the regularization-freshness (`γ_n`) are **different
> kinds of seam object**: `Λ=0` is tame-critical; `γ_n ∉ 𝓡̄` is wild-fresh. The cross-reference in
> `regularization-freshness` ("`Λ` may be another freshness instance") is **withdrawn**: `Λ` is *not* a
> freshness instance — it is `0`. The genuine arithmetic content near the no-margin is the Laguerre–Pólya
> membership `Λ≤0` = RH (the localization axis, G5 / no-margin), **not** a transcendence/period probe (the
> value axis). These are the two axes the charter keeps separate (#137 orthogonality).

## Why 5-failed and not 2-fully-proven
The card's **stated deliverable** — "place `Λ` in the period/non-period dichotomy via PSLQ" — is
unachievable (F1 degeneracy + F2 non-computability). No theorem is banked; what is learned is that the line
is a **false lead** (the question is RH, mislabeled as transcendence). Filed here so the team does not spend
a runpod attempting an impossible PSLQ probe. The salvage (F3) is a one-line structural note, not a card's
worth of content; it is recorded in `regularization-freshness` (withdraw the `Λ` cross-ref) and the seam
bucket.

## Door passport
- **Door-2:** vacuous — there is no native apparatus in play; the question is RH (localization axis) under a
  transcendence-axis label. Mislabeling, not a native probe.

## Cross-references
- `no-margin-uniform-bound.md` — `Λ=0` is the no-margin's dBN coordinate (the real, RH-equivalent content).
- `regularization-freshness.md` — the `Λ`-as-freshness cross-ref is **withdrawn** (F3): `Λ=0` is tame, not
  fresh.
- `exponential-period-dss-cross.md` — the tame(`𝓡`)/wild(`K`) framework F3 uses.
- support-extraction-log #87 §12 — `Λ≤0 ⟺ Ξ∈Laguerre–Pólya ⟺ RH`; `Λ=0` = seam/no-margin (the seed).

## Log
- 2026-06-19 — created in 0-backlog (PSLQ probe + writeup, bite-size).
- 2026-06-19 (DeWitt) — claimed, worked, **closed to 5-failed.** Found the framing degenerate: `Λ=0 ⟺ RH`
  (F1, with Rodgers–Tao `Λ≥0`), so the value question is RH in disguise; PSLQ is structurally inapplicable
  (F2, `Λ` not computable to any proven digit — pinning it is RH-strength). Salvage (F3): under RH the
  no-margin is the **tame** point `Λ=0`, opposite the seam from the **wild** `γ_n`; withdrew the
  `Λ`-as-freshness cross-ref. No runpod (the point is precisely that no computation can help). No web.
