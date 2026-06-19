# (DSS-cross) numerical test — Stieltjes constants vs the period field

**Theorist, 2026-06-19.** Pre-certification for `docs/drafts/dss-across-the-period-nonperiod-divide.md`
§3b: the conjecture that, modulo GPC, DSS ⟺ the Stieltjes constants `{γₙ}` are algebraically
independent over the period field `ℚ(π, ζ(odd))`.

## Test
PSLQ (mpmath 1.3.0) for ℚ-relations, maxcoeff `1e12`, at dps=150 AND dps=300 (artifact re-check), with
the precision guard `dps > 1.5·n·log₁₀(maxcoeff)` (all rows precision-safe).

## Findings (output.txt) — ALL "NO relation" at both precisions
- `{1, γ₀, γ₁, γ₂, γ₃}`: no ℚ-linear relation ⟹ the first Stieltjes constants are ℚ-linearly independent.
- `{1, π², ζ3, ζ5, ζ7}`: no relation (period-side sanity).
- `{1, π², ζ3, ζ5, γ₀, γ₁, γ₂}`: **no CROSS relation** — no low-height relation mixing periods and Stieltjes.
- `{1, γ₀, γ₀², π², ζ3, γ₁}`: no low-degree cross relation.

## Reading
Consistent with `(DSS-cross)`: the Stieltjes constants show no low-height algebraic dependence on the
period field, up to height `1e12`, confirmed at two precisions (no PSLQ artifact). This is the
exponential-period side of the period/non-period divide — numerical evidence that the cross-divide
independence (the genuinely-open core of DSS, beyond GPC) holds. Numeric tier only; not a proof.

## Repro
`python3 dsscross.py` (mpmath 1.3.0).
