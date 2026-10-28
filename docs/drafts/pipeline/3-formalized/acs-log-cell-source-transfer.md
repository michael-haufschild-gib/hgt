# Complete signed prime-source transfer through logarithmic cells

- **ID:** acs-log-cell-source-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route ACS; `BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean` and `RHTower/ThetaEulerLogCellResidueChannels.lean`.
- **Statement:** Every real compact C² source has its original Weil prime term recovered by actual quadratic logarithmic-cell energies, with error `O(1/N)`; arithmetic divisibility forms have the same limit. The transfer also holds for arbitrary signed mixed source pairs.

## Goal

Discharge prime-source identification and signed successor-remainder payment for complete
integer logarithmic cells. The theorem includes the full prime series, actual L² vectors,
and the original `RHTower.primeSum`. Full-source ACS effectivity and the joint
Gamma/pole-compatible index bound remain open.

## Gates

- [x] Source-pure statement; no positivity, spectral, index-budget, or zero-exclusion assumption.
- [x] Mixed high-cell remainder estimate formalized.
- [x] Actual L² translation and full prime-series identity formalized.
- [x] Smooth bounds derived from compact C² regularity; full Bochner source identified.
- [x] Quantitative rate and convergence to the original Weil prime term formalized.
- [x] Four exact-file Lean checks; transitive axiom audits; umbrella imports.
- [x] Moved directly from stage 1 to stage 3; no stage-2 proof left pending.

## Exact results

All declarations below are in
`GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`.

- `HighCellRemainder.lean`: `mixedCellRemainder_sq_le`, `abs_primeCellRemainder_le`.
- `LogarithmicCellSourceTransfer.lean`: `inner_shift_cellSection_eq`,
  `abs_primeSectionPair_sub_spine_le`, `fullPrimeSectionPair_eq`.
- `SmoothLogarithmicCellRefinement.lean`: `exists_compact_logSamples_rate`,
  `abs_logQuadrature_sub_integral_le`.
- `CompletePrimeSourceTransfer.lean`: `exists_complete_primeSource_rate`,
  `exists_complete_primeSum_rate`, `exists_tendsto_divisibility_primeSum`,
  `exists_tendsto_complete_primeSum`.

For a compact C² real test `f`, the final quantitative theorem derives `R>0`, an integer
`B≥1`, and `D≥0` such that, for every integer `N≥1`,

`|cellPrimeEnergy (logSamples f R N) N (N*B) - RHTower.primeSum f| ≤ D/N`.

Here `logSamples f R N a = f(log(max(a,N)) - log N - R)`, and `cellPrimeEnergy`
is the full von Mangoldt-weighted series of actual translated L² inner products of
one cell-section vector with itself. No prime tail is dropped.

## Formal proof structure

1. Put `w_a = log(a+1)-log a`. Exact translation of the actual cell vectors gives
   the complete mixed correlation as its divisibility spine plus
   `R_m = Σ_{A≤a≤X} c_a Σ_{r<m} w_(am+r) (d_(am+r)-d_(am))`.
2. Retain both small factors in weighted Cauchy–Schwarz: `w_a/a ≤ A⁻²`.
   Disjoint quotient-remainder blocks charge each derivative edge at most once, giving
   `R_m² ≤ A⁻² (Σ w_a c_a²) (Σ k(d_(k+1)-d_k)²)`.
   Support truncates the derivative sum uniformly in the multiplier.
3. Compactness derives a common source window and fixed multiplicative horizon `B`.
   Global Lipschitz bounds follow from C² regularity. Clipped logarithmic samples have
   adjacent differences at most `K/N`, square mass at most `B*C²`, and derivative energy
   at most `B²*K²`. The entire signed prime successor contribution is therefore `O(1/N)`.
4. For each surviving multiplier, the compact C² correlation
   `H_m(u)=f(u)g(u+log m)` is globally Lipschitz. Telescoping complete logarithmic cells
   identifies the full Bochner integral; rectangle errors sum to at most
   `B*Lip(H_m)/N`. Support proves that every multiplier beyond `B` contributes zero.
5. Combine the signed remainder and source quadrature bounds. On the diagonal,
   clipping contributes zero below `N`, so both inner-product slots contain the same
   actual cell vector. Translation invariance identifies the two autocorrelation
   directions, yielding exactly the existing `RHTower.primeSum`. The rates imply
   convergence of both actual cell energies and arithmetic divisibility forms.

## Validation

Each file passed `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/<Module>.lean`
from `formal/`, without warnings. All printed transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Required dependency oleans were built
individually; the umbrella was wired but not compiled. No added axioms, placeholders,
trusted-computation shortcuts, or raised proof limits.
