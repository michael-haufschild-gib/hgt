# nad card `hausdorff-positive-higher-spin-cdd-cone` — algebraic core of the converse is proved

Card gate: the Hausdorff converse (completely monotone ⇒ representing measure on `[0,1]`), absent
from mathlib.  `HausdorffCDDMeasureSource.lean` already had necessity
(`hausdorffMoment_isCompletelyMonotone`) and uniqueness (`hausdorffSource_eq_of_moments_eq`).

## Landed 2026-08-12 — `HTGeometry/HausdorffQuadratureWeights.lean` (axiom-clean, wired)

```text
hausdorffCoeff  b N k = (-1)^(N-k) * (fwdDiff 1)^[N-k] b k          -- "T(N,k)"
hausdorffWeight b N k = (N.choose k) * hausdorffCoeff b N k
```

- `hausdorffCoeff_nonneg`, `hausdorffWeight_nonneg` from `HausdorffCompletelyMonotone`.
- **`hausdorffCoeff_refine`** — `T(N,k) = T(N+1,k) + T(N+1,k+1)` for `k ≤ N`.  This is the whole
  trick: the forward-difference recursion with the sign folded in.  It turns the total-mass identity
  into a one-line induction, so **no double sum and no triangle reindexing is needed** (mathlib has
  no lemma for `∑_{k≤N} ∑_{i≤N-k} = ∑_{n≤N} ∑_{k≤n}`; `exact?` finds nothing).
- `sum_hausdorffWeight_succ` (Pascal + `Finset.sum_range_succ'` + `Nat.choose_succ_self`),
  **`sum_hausdorffWeight : ∑_{k ∈ range (N+1)} hausdorffWeight b N k = b 0`**.
- `hausdorffCoeff_shift` — `hausdorffCoeff b N (m+l) = hausdorffCoeff (fun n => b (n+m)) (N-m) l`,
  via `fwdDiff_iter_comp_add`.
- `choose_mul_descFactorial_shift` — `C(N,m+l)·(m+l)ₘ = Nₘ·C(N−m,l)`, via `Nat.choose_mul` and
  `Nat.descFactorial_eq_factorial_mul_choose`.
- **`sum_hausdorffWeight_descFactorial`** — for `m ≤ N`,
  `∑_{k ∈ range (N+1)} hausdorffWeight b N k · (k.descFactorial m) = (N.descFactorial m) · b m`.
  The two lemmas above reduce it to the mass identity for the shifted sequence, so it needs no
  separate induction either.

## What is left of the converse (analytic only)

1. the atomic measures `∑ₖ ENNReal.ofReal (hausdorffWeight b N k) • dirac (k/N)` on `[0,1]`;
2. `|(k/N)^m − (k.descFactorial m)/(N.descFactorial m)| ≤ C(m)/N` uniformly in `k ≤ N`.  Proof
   sketch: `(k)ₘ/(N)ₘ = ∏_{i<m}(k−i)/(N−i) ≤ (k/N)^m` for `k ≤ N`, and
   `k/N − (k−i)/(N−i) = i(N−k)/(N(N−i)) ≤ (m−1)/(N−m+1)`, so `a^m − b^m ≤ m(a−b)` finishes;
3. one weak-compactness extraction in `ProbabilityMeasure ↥(Icc 0 1)` (compact metrizable), after
   normalising by `b 0` and treating `b 0 = 0` separately (complete monotonicity then forces
   `b = 0`).

No entire-function theory and no missing mathlib area is involved — unlike the Nevanlinna
bottleneck, this card's gate is finishable.
