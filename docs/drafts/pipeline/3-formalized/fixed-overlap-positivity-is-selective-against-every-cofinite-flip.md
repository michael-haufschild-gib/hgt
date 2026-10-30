# Fixed-overlap positivity is selective against every cofinite flip

- **ID:** fixed-overlap-positivity-is-selective-against-every-cofinite-flip
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route-obstacles (review-2910) table: SMAP/ACP missing "a selector beyond finite flips";
  walls-ledger 1.18 (gauge selection); TM `LiouvilleTwinSelectivity`; ACP
  `CofinitePrimeFlipsHaveZeroGap` (`cofiniteFlip_harmonicSum_abs_le`); C7.
- **Statement:** Let `ε` be a completely multiplicative sign (`±1`) with bounded harmonic sums
  `|Σ_{n≤M} ε(n)/n| ≤ B`. For every `C²` profile on `[0,1]` with Robin–Euler threshold `< 1` and
  every fixed overlap `c` above it, the complete form of `εΛ` is eventually negative on an atomic
  family of width `c/N`. Every cofinite flip `λ·ω_F` (`F` a finite set of primes) is such a gauge.
  For the Liouville selector, at every `c ≥ 1`: `ζ`'s complete Weil matrix is eventually positive
  definite and every cofinite flip's form is eventually negative on the same atomic families.

## Proof

The Liouville proof uses `λ` only through: complete multiplicativity and `λ² = 1` (gauge
congruence below the spacing, `twistedPrimeSum_atomicTest`, `twistedAtomicWeilForm_eq`), and the
harmonic bound `|S| ≤ 2`. With `|S| ≤ B`: the witness `x = (ε − s)b`, `s = S/H`, lies on the pole
hyperplane, has `n x_n² ≤ 4`, `Σx² ≥ log M − 2` once `H ≥ B + B²`, and
`P_M(εx) = P_M(b) + s²P_M(εb) − 2sΣR_n ε(n)/n ≥ (L − γ − ε/2)H − K` with
`K = B²(1 + C₀) + 2B²(1 + γ) + 2B·B_m` (fixed-point bottom law, Mertens rows). The sub-horizon
Markov bound and the Robin–Euler limit are unchanged. Cofinite flips: `cofiniteFlip_isSignGauge`,
`|Σ λω_F(n)/n| ≤ 2/c_F` (ACP). ζ side: C7 (`liouvilleSelector_selective`).

## Log
- 2026-10-30 — paper proof and Lean: `TM/EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio.lean`
  (`eventually_signTwin_weilQuadTw_neg_of_gt_robinEuler`, `eventually_cofiniteFlip_weilQuadTw_neg_of_gt_robinEuler`),
  `CACT/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean`
  (`liouvilleSelector_selective_of_signGauge`, `liouvilleSelector_selective_of_cofiniteFlip`); axioms standard.
