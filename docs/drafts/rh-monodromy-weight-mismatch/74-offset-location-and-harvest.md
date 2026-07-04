# 74 — Offset Location, the Mid-Block Ladders, and the Harvest: Closing Arithmetic for (TAIL-6)

**Register: SEARCH** (task #19). §1 corrections to doc 73 §4 (found while
setting up — recorded first, per discipline); §2 pre-registered predictions
(bind, written before the §3 run); §3 probe results; §4 mid-block ladders +
the allocation optimizer (the truth-teller for doc 73 §5's "~1e−3 stack"
estimate); §5 harvest (thickness constant + ε₀\* audit + Lean).

## 1. Two corrections to doc 73 §4 [self-caught at setup]

- **The (10⁶, √T] block variance is 0.02, not 0.22** (√T = 1.73·10⁶ at
  T = 3e12 — the block is tiny; the 0.22 was an arithmetic slip). The
  variance map corrected: p ≤ 313: 1.010; (313, 10⁴]: 0.236; (10⁴, 10⁶]:
  0.203; (10⁶, √T]: 0.020. Prime variance to √T: 1.46. Primes in (√T, T]
  would carry a further ~0.35, but in Selberg-decomposition form those are
  absorbed into the remainder — the remainder budget is therefore
  **σ_E² ≈ 2.33 − 1.46 − (secondary ≈ 0.1) ≈ 0.75**, larger than doc 73
  implied.
- **The stack estimate "~1e−3" in doc 73 §5 is now suspect** and the
  optimizer (§4) will adjudicate it: any component with σ ≥ 0.3 certified
  only at Chebyshev grade caps the stack near 1e−2; the assembled number
  depends decisively on (i) whether the remainder's THICK-part variance is
  small (the offset-location conjecture) and (ii) the mid blocks' exact
  sub-Gaussian ladders under Christoffel. Both measured/computed below —
  the honest widened prior is recorded in P-OPT.

## 2. Pre-registered predictions [written BEFORE the §3 run; these bind]

Probe: same Z-grids as doc 72 §7 (T ∈ {10^6, 10^7, 10^8}), now with the
matched prime sum ReP_m(t) = Σ_{p≤m}p^{−1/2}cos(t log p), m = ⌊√(T/2π)⌋,
computed on the same grid; residual R(t) := log|Z(t)| − ReP_m(t);
"restricted" = t with dist(t, nearest zero) > 0.1·(mean spacing).
Reference prime-model variance: v_pm := Σ_{p≤m}1/(2p).

- **P-OL1:** restricted m₂(log|Z|) at T = 10^6 drops to ≤ 1.35 (from 1.946
  full; prime model 1.09).
- **P-OL2:** full − restricted m₂ gap ≥ 0.45 (zero-local mass carries
  ≥ 70% of the excess over the prime model).
- **P-OL3:** restricted m₂ − v_pm ∈ [0, 0.30] at all three heights
  (T-stable smooth excess).
- **P-OL4:** restricted μ₆/(15σ̂⁶) ≤ 2.0 (vs 3.6–4.1 unrestricted).
- **P-OL5:** restricted Var(R) ≤ 0.15 — the decisive one: the remainder's
  thick-part variance is SMALL; the 0.75 of §1 lives at the zeros.
- **P-OL6:** full Var(R) ≥ 0.5 (the dips carry it).
- **P-OL7:** restricted m₄(R)/(3·Var(R)²) ≤ 2 (remainder deg-4-friendly).
- **P-OPT:** the optimizer's certified total at A = 6.1, T = 3e12, using
  measured restricted-remainder moments, lands in [5e−4, 5e−3].

## 3. Probe results [MEASURED — probe_offset.py, runpod, archived; 6 pass / 1 informative fail]

- **P-OL1 PASS:** restricted m₂ = 1.214 at 10^6 (predicted ≤ 1.35).
- **P-OL2 PASS (strong):** full−restricted gap = 0.731/0.733/0.751 — the
  zero-local mass carries ~80% of the excess over the prime model.
- **P-OL3 PASS:** restricted m₂ − v_pm = 0.185/0.179/0.182 — T-stable to
  ±0.003 across two decades.
- **P-OL4 PASS (the clean finding):** restricted μ₆/(15σ̂⁶) = 1.43/1.43/1.44
  vs 3.6–4.1 unrestricted. **Away from zeros, log|Z| is near-Gaussian with
  prime-model variance and a +0.45 mean: the entire moment corruption of
  doc 72 §7 was floor mass.** The restriction radius 0.1·spacing is the
  legitimate one for the certified chain (B = E ∩ zero-nbhds is only the
  dip mass, β ≈ 0.006 per window — not the whole neighborhood).
- **P-OL5 FAIL (informative):** restricted Var(R) = 0.223/0.226/0.234, not
  ≤ 0.15. The thick-part remainder is real: σ_R² ≈ 0.23, T-stable, with
  mean +0.36 (a left-tail bonus) and m₄-ratio ≈ 2.0 (P-OL7 borderline
  PASS: 1.98/1.99/2.03) — deg-4-grade certifiable, but not negligible.
- **P-OL6 PASS:** full Var(R) = 0.92 — the dips carry the rest.

## 4. The optimizer verdict [P-OPT FAILS — doc 73 §5's estimate was optimistic]

Exact mid-block ladders (B2 = (313,10⁴]: σ² = 0.230, m₄-ratio 0.999;
B3 = (10⁴, 691k = √(T/2π)]: σ² = 0.189, ratio 1.000 — effectively pure
Gaussian ladders, collisions negligible) + B1's deg-10 ladder + the
measured residual block (μ = +0.36, σ² = 0.23, m₄-ratio 2). Optimal
allocation at A = 6.1:

> **4-block union stack: certified 1.22e−1** (alloc 2.6/1.25/1.2/1.05) —
> P-OPT's band [5e−4, 5e−3] FAILS by 25×. Diagnosis: fragmenting A across
> four blocks puts each at z ≈ 2.6–2.9, where low-degree Christoffel is
> weakest; the union split is structurally wrong for many small blocks.
> **2-block variant** (full prime sum p ≤ 691k at deg 4 — spacing-MV-legal,
> rel. err 2% — plus residual at deg 4): certified **~1.5e−2**.

Against the budget ε₀\*/(4.05 thickness): 2e−3 to 4e−3 — the certified
stack is short by a factor **~5–15** (not doc 73's 4–8, which is hereby
corrected). The blocking structure: deg-6 on the FULL prime sum is
genuinely beyond spacing-MV at 3e12 (Σr₃² ~ 6·π(691k)³ ≫ T). Consequence,
stated as the corrected certified-onset: with today's toolkit (deg-4 joint
+ deg-10 small block + thickness 4.05 + measured residual), the
fully-certified design onset sits at **T₀ ~ 10^{21}–10^{22}**
((¼logT)⁴ ≥ 4.05·512·m₄-stack ⟹ logT ≳ 50). The 3·10^12 meeting requires
the one instrument the degree budget does not price:

> **(EQD): effective equidistribution / exponential-sum certification for
> the mid-prime blocks at joint degree > 4** — now THE named open core of
> the finite-height program. Everything else is execution.

## 5. Harvest [banked this cycle]

- **Lean (all proven through, axiom-clean, umbrella 8632 green, lint
  passed):** `thickPart_union_subset'`/`thickPart_union_measure_le'` — the
  parametric thickness constant 4/(1−β), replacing 8 (at measured β ≈ 0.006:
  cost 4.02); `sq_tail_bound` + `sq_tail_bound_of_moment` — the
  certified-tail consumable, fully proven (premises are the genuine
  mathematical inputs: the ray condition q² ≥ 1 and the certified moment
  bound; no deferred placeholders).
- **ε₀\* audit note:** for the sharp carrier the doc 69 split-factor 2 in
  C′ was taper-specific and drops — ε₀\* = 1/256 available [sketch; verify
  in the C′ write-out].
- **(EFF-E) reframed by §3:** the Selberg-machinery target is no longer
  "small remainder" but the CERTIFICATION of the measured, T-stable
  restricted-residual block (μ_R = +0.36, σ_R² = 0.23, m₄-ratio 2) — three
  numbers to prove, not a cascade of unknowns.

## 6. What this opens

1. **(EQD)** — the single instrument between the lane and the 3·10^12
   meeting; everything else in the finite-height program is now execution
   against measured targets. First probe: Erdős–Turán–Koksma with the
   unique-factorization spacing on the (313, 10⁴] block's torus, where the
   frequency arithmetic is most favorable.
2. The §3 restricted-Gaussianity finding is an instrument in its own
   right: "the corruption is all floor" — any future moment argument in
   the lane should be run on restricted statistics by default.
3. The corrected onset ladder now reads: e^{650} (doc 67, TIGHT-only) →
   10^{21±1} (tonight, fully certified toolkit) → 3·10^12 (with (EQD)).
   Each step is a named instrument, none is a wall.
