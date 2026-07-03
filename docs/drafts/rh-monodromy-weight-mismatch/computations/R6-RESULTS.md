# R6 results (2026-07-03) — boundary-data returns at a D–H defect box — [MEASURED, NEGATIVE]

Engine: `computations/mwm/engine4.py`; raw: `r6.out`. Box B* = [0.53, 1.2] × [166, 168]
(certified w = 1 defect of f_dh); boundary sample 120 points (30/edge); dps 15;
τ ∈ [0, 400], step 0.1. Margin proxy m = min |f| over the sample = 0.02349.
Return distance d(τ) = max over the sample of |f(s + iτ) − f(s)|.

Pre-registered (07-index-formula.md §5.1): sub-margin returns with positive frequency at
gap scale ≈ 18–21 (the measured defect-gap scale); failure = early kill for the M1/(H)
causal shape in the family.

## Measured

- Sub-margin returns for τ > 1: **ZERO**. Sub-2×-margin: zero. Sub-3×-margin: zero.
- Deepest return over the whole range: d(59.7) ≈ 0.556 ≈ **24× the margin**; next
  d(185.8) ≈ 0.69, d(83.6) ≈ 0.71 (≈ 30×). Typical (median) distance d ≈ 2.7.
- Meanwhile the defect population DOES recur in this same τ-range ≈ 19 times
  (R2: off-line zeros every ≈ 21 on average, gaps median 18).

## Verdict

**The pre-registered prediction is REFUTED.** In the one family where defects exist and
recur, the recurrence is NOT produced by sup-norm returns of the boundary data: defect
recurrence ⇏ data recurrence. The Rouché-transfer mechanism (H) is *sufficient* (the C3
theorem stands as mathematics) but is demonstrably **not how the family does it**.

Robustness of the negative: the sampled sup UNDERestimates the true d(τ) and the sampled
min OVERestimates the true margin, so genuine returns are even scarcer than measured; the
τ-grid (0.1) could hide only near-vertical dips of slope ≳ 10 from d ≈ 0.5 — excluded by
the smoothness of the data at this height. Logical caveat: (H) as stated (positive upper
density) is not refutable by ANY finite window — what is refuted is the *causal reading*
("defects recur because data returns") and the empirical support route for (H).

## What the family actually does (the re-cut this opens)

The D–H off-line zeros are a fixed POPULATION of linear density ≈ T/21; defect windows
recur because the population is spread — a structural/density phenomenon (the
Bombieri–Hejhal / Lamzouri–Lee regime for linear combinations), not an almost-periodicity
phenomenon of the analytic data. Mechanism re-cut for M1:

**(P_k) population-forcing [CONJECTURE, new open shape]:** if D_{σ₀,H,k} ≠ ∅ (one
coarse defect exists) then N(σ₀', T) ≫ T for some σ₀' > 1/2 — "one off-line zero seeds a
linear population." (P_k) + (D) ⟹ D = ∅ directly (no recurrence needed), and then
per-zero divisibility as in 06-reduction Step 2. For linear combinations the population
is unconditional (components + near-collisions force it — exact statement pending C4's
Bombieri–Hejhal reading); the ζ-question is whether FE + reality + one seed force
combination-like structure. This is a sharper, colder question than (H) — and it is
exactly where the family evidence now points.

Cross-links: C4 (in flight) supplies the Bombieri–Hejhal hypotheses; 07 §4's companion
cocycle is orthogonal and unaffected; R3c/R5c unaffected.
