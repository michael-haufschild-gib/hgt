# NEGATIVE RESULT: secular-moment Hankel positivity is RH-BLIND (a failed criterion)

**Theorist, 2026-06-19.** A speculation — "RH ⟺ the secular-moment Hankel `[P_{i+j}]` is PSD"
(via the carrier as a Cauchy–Stieltjes transform + the Hamburger moment problem) — TESTED and FALSIFIED.
Documented per "failures first-class" + the don't-fake discipline (tested before asserting).

## Test (numpy + mpmath zetazero, N=20 zeros, Hankel size 7)
- **RH-true** (real Ξ-zeros `±γ_n`): Hankel `[P_{i+j}]` is PSD (`n₋ = 0`). ✓ (necessary direction holds.)
- **Off-line via FE quadruple** `{γ±iδ, −γ±iδ}` (δ=1, moments stay REAL): Hankel **still PSD** (`n₋ = 0`)
  for k=1,2,3 off-line zeros. ✗ The criterion does NOT detect off-line zeros.

## Why it fails (theory)
Hamburger: a real sequence `{P_k}` has PSD Hankel ⟺ *some* positive measure on ℝ realizes it — NOT
that the actual reciprocal-spectrum measure is on ℝ. Off-line zeros give a conjugate-symmetric measure
off ℝ with real moments that remain realizable by a real measure (moment-determinacy blindness; here
also amplified by the Hankel being near-low-rank, dominated by the largest reciprocal `1/γ_1`). So
`RH ⟹ Hankel PSD` (necessary) but **`Hankel PSD ⇏ RH`** (insufficient).

## Reading
The secular-moment Hankel positivity is a genuine **RH-blind / insufficient** criterion — a new instance
of the field's no-margin/blindness theme. The CORRECT positivity criterion for RH is the **Pick/Nevanlinna
kernel on nodes** (`CarrierPickKernel`, `multiPair_carrier_exact_neg_inertia`: `κ₋ = #off-line zeros`,
which DOES detect off-line — validated on real zeros in `../carrier_real_zeros_inertia/`), NOT the Hankel
of moments. Lesson: positivity-on-nodes (Pick) sees the support; positivity-of-moments (Hankel) does not.
Numeric tier; recorded to steer the team away from the Hankel route.

## Repro
`python3 hankel.py`, `python3 hankel2.py` (FE quadruple, real moments).
