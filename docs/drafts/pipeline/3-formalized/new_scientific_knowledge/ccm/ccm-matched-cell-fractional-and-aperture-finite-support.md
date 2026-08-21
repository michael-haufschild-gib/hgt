# CCM matched-cell fractional control and aperture finite support

## Status

Formalized in Lean 4. Results close all-prime convergence for mass-matched prime--polar cells in
two distinct regimes. They do not prove positivity or RH. Frontier map remains read-only.

## Conjecturing loop

Corpus search began from exact matched-cell cosine normal form. Existing asymmetric Suzuki current
already had a summable quadratic-aperture bound, while even residual had no global summability
theorem.

1. Conjecture: cosine Lipschitz control lowers required regularity from full derivative to one
   Fourier first moment. Proved.
2. Conjecture: literal smooth CCM core supplies this first moment because Fourier transform is
   Schwartz. Proved.
3. Conjecture: finite Gamma--Slepian heads inherit same first moment. Not supported by current
   corpus; form norm controls logarithmic, not polynomial, Fourier weight. Pivoted.
4. Reinterpretation: actual canonical heads are aperture-supported. Since translation defect is
   exactly constant beyond aperture diameter, mass matching may make remote cells zero rather than
   merely small. Proved, including separate vanishing of both signed streams.

## Ambient fractional matched-cell theorem

Writing `w_n` for critical Mellin atom weight, `rho_n` for exact matched radius, and `P_n(xi)` for
even cosine phase profile, Lean proves

```text
rho_n <= w_n / (2 exp(log(n)/2))
P_n(xi) <= pi * w_n^2 / exp(log(n)/2) * |xi|.
```

Coefficient `w_n^2 / exp(log(n)/2)` is summable. Therefore any ambient `SoninL2` head satisfying

```text
Integrable (fun xi => |xi| * ‖fourierUnitary f xi‖^2)
```

has absolutely summable even residual and intact prime-minus-matched-polar family. This is strictly
below failed full-derivative requirement. Every literal compact-smooth CCM form vector satisfies
first-moment condition because its Fourier transform is Schwartz.

## Stronger aperture theorem

For every positive aperture `a` and every literal aperture head `f`, corpus gives

```text
2a < h -> translationDefect(h,f) = 2 * ‖f‖^2.
```

Lean now proves uniform radius bound `rho_n <= 1` for `n >= 1`. Hence

```text
2a + 1 < log n
```

forces whole symmetric cell `[log n - rho_n, log n + rho_n]` beyond aperture diameter. Exact mass
matching then yields three separate equalities:

```text
primeAnchor_n(f) - matchedPolarCell_n(f) = 0
matchedSuzukiCurrent_n(f) = 0
matchedSymmetricResidual_n(f) = 0.
```

All three families are eventually zero, hence summable, on every aperture head. No smoothness or
Fourier moment is needed. Infinite all-prime convergence has become exact finite support: Lean
produces a cutoff `N` for which each infinite `tsum` is exactly its `Finset.range N` block. The
infinite intact-cell identity also remains exact:

```text
tsum intactPrimePolarCell = tsum symmetricResidual - tsum matchedSuzukiCurrent.
```

Thus later sign work may operate on a finite producer without silently rearranging conditionally
convergent streams.

## Higher principle exposed

Apparent high-frequency regularity wall was caused by estimating spectral cosine profile before
using physical support. Correct order is:

```text
mass-match prime and polar cell
-> quotient constant exterior translation defect
-> only then estimate remaining finite interior block.
```

For ambient heads without finite support, fractional first-moment theorem remains genuine. For CCM
aperture heads, physical exterior rigidity dominates spectral regularity and eliminates tail
entirely. This is amplitude/source geometry before absolute-value estimation, same ordering
principle independently exposed by reporter-secant transition-core escape.

## Lean certificates

- `formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedSymmetricFirstMomentControl.lean`
- `formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedSmoothCoreConvergence.lean`
- `formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedApertureFiniteSupport.lean`

Key declarations:

```text
ccmActualHeadMatchedCosinePhaseProfile_le_firstMomentKernel
summable_ccmActualHeadMatchedPrimePolarCellDifference_of_firstMoment
integrable_ccmComplexSmoothFormVector_fourierFirstMoment
summable_ccmComplexSmoothFormVector_matchedPrimePolarCellDifference
ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_log_gt
ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_log_gt
ccmActualHeadMatchedSymmetricCellResidual_eq_zero_of_log_gt
eventually_ccmActualHeadMatchedPrimePolarCellDifference_eq_zero
summable_ccmActualHeadMatchedPrimePolarCellDifference_of_aperture
exists_tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_finiteBlock
exists_tsum_ccmActualHeadMatchedSymmetricCellResidual_eq_finiteBlock
exists_tsum_ccmActualHeadMatchedSuzukiCurrent_eq_finiteBlock
tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_symmetric_sub_suzuki
```

## Hostile audit

- First-moment result is not claimed for arbitrary CCM form-domain vectors.
- Aperture result uses literal `suzukiApertureHilbert`; it is not an ambient `SoninL2` statement.
- Eventual zero is proved separately for intact cell, asymmetric current, and even residual; no
  cancellation of two divergent series is hidden.
- Convergence alone gives no sign. Remaining RH-strength problem is sign of exact finite interior
  producer and its cofinal aperture behavior.
- Exact target modules build; audited declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`. No `sorry`, added axiom, computation, or umbrella build was used.

## Next hard conjecture

Use finite-support boundary to identify matched finite interior producer exactly with existing
Gamma-wall source quadratic, then search for source-native finite Gram completion. Required result
must prove sign of complete finite prime--polar--higher-Gamma block; bounding prime, polar, or Gamma
pieces separately is already known to lose RH-strength cancellation.

## Log

- 2026-08-21 — Proved fractional cosine profile bound and first-moment summability.
- 2026-08-21 — Proved literal smooth CCM core supplies Fourier first moment.
- 2026-08-21 — Rejected unsupported canonical-head first-moment extension.
- 2026-08-21 — Proved exact remote-cell cancellation and separate finite support of both signed
  streams on every aperture head.
- 2026-08-21 — Reduced all three infinite sums to exact finite blocks and preserved the
  symmetric-minus-Suzuki split at `tsum` level.
