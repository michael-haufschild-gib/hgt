# The moment-neutrality law for subconvexity exponents

- **ID:** `moment-neutrality-law-subconvexity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** originated in `../1-in-progress/lindelof-hypothesis-campaign.md`, cycle 2
- **Statement:** Given a perfect `2j`-th moment (`m j = 1`) and an established pointwise exponent
  `θ`, the greatest lower bound of the pointwise exponents deliverable by the whole moment
  hierarchy is exactly `min(1/(2j), θ)`. Hence a perfect `2j`-th moment improves on `θ`
  **iff `j > 1/(2θ)`**.
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [POSITIVE STATEMENT] [NOT AN LH PROOF]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.MomentNeutralityLaw`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` only. No `sorry`/`admit`/project axiom.
  `scripts/formal_tools.py lint` passes.

## Goal

Target selection for the Lindelöf campaign. The moment literature's flagship open problem is the
sixth moment `∫_0^T |ζ(1/2+it)|^6 dt ≪ T^{1+ε}`. This theorem shows that solving it **cannot
improve the subconvexity exponent at all** against the current record `θ = 13/84`, at any moment
index, however the hierarchy is optimised — the optimised bound is `13/84 + 1/(28k)`, which
descends to `13/84` and never crosses it. The first moment whose full strength surpasses the
record is the eighth.

## Statement

For real `j, θ > 0`, let

```text
momentBound j θ k = 1/(2k)                      if k ≤ j
                  = (1 + 2θ(k-j))/(2k)          if k > j
```

be the pointwise exponent available at moment index `k`. Then

```text
IsGLB (momentBound j θ '' Ioi 0) (min (1/(2j)) θ)      -- isGLB_momentBound
min (1/(2j)) θ < θ  ↔  1/(2θ) < j                      -- momentBound_improves_iff
```

The floor `1/(2j)` is attained at `k = j` (`momentBound_self`); the floor `θ` is approached as
`k → ∞` (`momentBound_tendsto`).

Numerical instances for `ζ` with `θ = 13/84`:

```text
bourgain_threshold          : 1/(2θ) = 42/13 = 3.2307...
sixth_moment_neutral        : min (1/6) (13/84) = 13/84       -- j = 3, no gain
eighth_moment_improves      : min (1/8) (13/84) = 1/8  ∧  1/8 < 13/84
sixth_below_eighth_above    : ¬(42/13 < 3) ∧ (42/13 < 4)
```

A convexity bridge `eq_one_of_convexOn_of_one_le` supplies the `k ≤ j` branch from convexity of
the moment exponent together with `m ≥ 1`, `m 0 = 1`, `m j = 1`.

## The three analytic inputs (hypotheses, not content)

The Lean module is source-independent. The inputs it encodes are:

1. `m k = 1` for `0 ≤ k ≤ j` — Hölder between `m 0 = 1` and `m j = 1`, plus `m ≥ 1`.
2. `m k ≤ 1 + 2θ(k−j)` for `k ≥ j` — Hölder of the `2k`-th moment against the pointwise bound.
3. `μ(1/2) ≤ m k /(2k)` — a near-extremal value is sustained on an interval of length `≍ 1/log T`
   (Sobolev–Gallagher applied to `ζ^k`, a Dirichlet polynomial of length `T^{k/2}`), so it
   contributes `≫ V^{2k}/log T` to the `2k`-th moment.

## Gates

- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  complete paper proof, no open dependency
- [x] 2 → 3  Lean theorem `HTGeometry.isGLB_momentBound`, module builds, axioms clean, lint passes
- [ ] 3 → 4  standalone write-up

## Novelty audit

- The implication "`m j = 1` gives `μ(1/2) ≤ 1/(2j)`" is **classical** (Ivić).
- The **neutrality law** — the exact `min(1/(2j), θ)` formula for the infimum over the whole
  hierarchy, and the resulting threshold criterion `j > 1/(2θ)` — is the new statement. It is what
  makes the sixth moment's neutrality against `13/84` visible; without it the natural (and wrong)
  reading is that the sixth moment conjecture would advance subconvexity.
- Searched: the July 2026 moment survey (arXiv:2509.20335, Florea, JLMS 2026), the ANTEDB
  (Tao–Trudgian–Yang), Heath-Brown QJM 29 (1978), Ng–Shen–Wong arXiv:2204.13891. No such statement
  located. Classification: `NEEDS EXTERNAL AUDIT`, provisionally new-in-form.
- Significance is strategic rather than technical: it reallocates the moment programme's target
  from `j = 3` to `j ≥ 4`.

## Log
- 2026-07-25 — originated, proved, formalized, lint green.
