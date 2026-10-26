# Critical Nyquist finite part and signed broad-source classification

- **ID:** nyquist-critical-finite-part-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Independent BiScaleUncertainty; infinite-grid tail rigidity beyond Trap 5.
- **Parent:** `../../1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`
- **Predecessor:** `../nyquist-weight-order-threshold-2026-10-17.md`
- **Count:** Complete existing paper result formalized; no new contribution count. All 96 public declarations pass transitive axiom audit.
- **Field guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`.
- **Paper:** `docs/reports/BiScaleUncertainty/NyquistCriticalFinitePart.md`
- **Current source audit:** Eight leaves now cover the complete recovered report, including exact continuous primitive and broad-test constants, actual-source classification, quantitative energy, local uniform convergence, and both smooth witnesses. All 96 public declarations have clean transitive axiom lists. All eight final direct source checks passed without diagnostics; complete card promoted to stage 3.

## Proven paper statement

For the actual degree-m Nyquist Taylor residual at critical weight beta=m+1,
subtract its continuous mean density c=(m+1)^(m+1)/(2(m+2)!). The cell discrepancies
are absolutely summable with an explicit inverse-square bound, defining a finite
part B. For every fixed signed compact Lipschitz test H, the broad-test residual
has expansion c L integral_0^infinity H + B H(0) + O_H(1/L). For normalized
autocorrelations of actual fixed smooth compact sources, the leading coefficient
is c (integral f)^2/(2 integral f^2). Thus ordinary zero mean cancels critical
escape; nonzero mean gives linear escape despite vanishing rescaled source energy.

## Goal and novelty boundary

Package 15 gives logarithmic prefix growth and one nonnegative broad-source
divergence witness. It does not identify the finite part or classify signed-source
cancellation. The paper proves both from the actual cell producer.
The counterterm is continuous density c, integrated as c times cell width; it is
never a discrete counterterm inserted before floor summation. No Chebyshev or
positivity receiver premise occurs. No global uniform convergence or grid blindness
is asserted for the broad-source family. Source-dependent regularity constants
must be derived from the fixed smooth source, not inferred from energy alone.

## Plan and gates

1. Finish corpus applicability audit, including additive autocorrelation mass.
2. Prove explicit cell discrepancy, convergent primitive finite part, quantitative
   signed broad-test expansion, source classification and actual zero-mean witness.
3. Audit the dependency-closed paper proof and novelty boundary before new Lean.
4. Formalize the exact connected result with one foreground Lean process at a time.
5. Check every public declaration's axioms, direct leaves, imports, API index,
   formal lint and source hashes; promote and count only after the complete audit.

- [x] Well-posed source-pure candidate and attack mechanism.
- [x] Complete paper proof and internal novelty audit; no global priority claim.
- [x] Exact Lean statements checked and axiom-audited.
- [x] Complete source, dependency, index and import certificate recorded; no contribution-count change.

## Corpus evidence

Two completed deep searches: `/tmp/nyquist-critical-finite-part-deep.json` and
`/tmp/nyquist-critical-cell-discrepancy-deep.json`. Both returned partial=false,
no unfinished stages/errors, 20 candidates and 20 source arguments; all candidate
statements and source arguments inspected. First search mostly retrieved unrelated
multiplicative autocorrelation. Second supplied existing Taylor remainder bounds;
other candidates concern collars, arithmetic quadrature or unrelated kernels.
Prose/passages were screened for relevance; no exhaustive reading claim is made.
Inventory coverage was complete (73844/73848 files, zero pending); semantic coverage
was unmeasured and refresh deferred to the background indexer. Retrieved compiler
metadata was source-only. Package 15 ingredients have their separate Lean certificate.
Focused exhaustive text search found no critical Nyquist finite-part theorem.
This is an internal corpus boundary, not a global novelty claim.

Third search `/tmp/nyquist-critical-source-mean-deep.json` completed with partial=false,
no errors or unfinished stages; all 20 candidates and 20 source arguments inspected.
Inventory coverage: 73855/73855, zero pending. Semantic coverage unmeasured, refresh
deferred, source-only compiler metadata. The ordinary convolution mass identity is
a parent theorem; multiplicative autocorrelation hits do not apply. Direct inspection
of `SignedDyadicCollarPartition.lean` supplied the correct reflected convolution.

## Paper audit

The report proves |alpha_n-c delta_n|<=D delta_n/n<=D/n^2 with D=c 2^(m+1),
absolute convergence of B, the primitive bound 2(3D+2c)exp(-T), and signed
broad-test error (8D+4c)Lip(H)/L. It derives source regularity, signed Fubini,
normalized scaling and vanishing energy from actual compact C^2 sources. A fixed
bump and its difference with a disjoint translate realize both mean alternatives;
the latter has normalized correlation -1/2 at the separating lag. The cases n=1,
m=0, all L>0 and zero test H were checked. No absolute integrability of e-c is
claimed, and no conditional infinite integral is hidden in B's definition.

The exact formalization is complete in eight leaves. Final direct source checks
and the complete dependency certificate passed. No contribution count or global
novelty claim is changed by this formalization.

## Completion proof for the missing analytic statements

Write `t_k=log(k+1)`, `δ_k=t_(k+1)-t_k`, `e=e_m`,
`α_k=∫_(t_k,t_(k+1)] e`, `d_k=α_k-cδ_k`, and `B=Σ d_k`.
The existing kernel is nonnegative, locally integrable, zero on `(-∞,0]`,
and has precisely these cell integrals. Existing estimates give
`|d_k|≤Dδ_k/(k+1)≤D/(k+1)²`, `δ_k≤1/(k+1)`, and
`|Σ_(k≥N)d_k|≤2D/(N+1)`.

Define the actual continuous primitive
`P(T)=∫_0^T e(x)dx-cT`, for `T≥0`. At nodes it equals `Σ_(k<N)d_k`.
For `T∈(t_k,t_(k+1)]`, positivity gives

`|P(T)-P(t_k)|≤α_k+cδ_k≤(D+2c)/(k+1)`.

Adding the nodal tail bound gives `|P(T)-B|≤(3D+2c)/(k+1)`.
Since `exp(T)≤k+2≤2(k+1)`, this is at most
`2(3D+2c)exp(-T)`. At `T=0`, use `|B|≤2D` directly.
Local integrability makes `P` continuous, and the bound proves `P(T)→B`.

For a compact Lipschitz test `H` with Lipschitz constant `A` and any `L>0`,
put `G(x)=H(x/L)`. On each cell, subtract its continuous counterterm and
freeze `G` at the left endpoint:

`∫cell (e-c)G = d_k G(t_k) + E_k`,

where
`|E_k|≤(A/L)δ_k(α_k+cδ_k)≤(A/L)(D+2c)/(k+1)²`.
All integrals with `G` are integrable by compact support and local integrability;
the displayed bounds justify every series rearrangement. The power-tail estimate
`Σ_(n≥1)n^-p≤1+1/(p-1)` for `p>1` yields
`Σ|E_k|≤(A/L)(2D+4c)`.

Moreover `|G(t_k)-H(0)|≤(A/L)t_k`. For `n≥1`,
`log n≤2 sqrt(n)` follows from `log(sqrt(n))≤sqrt(n)-1`.
Hence

`Σ|d_k|t_k≤D Σ_(n≥1)(log n)/n²≤2D Σ_(n≥1)n^(-3/2)≤6D`.

Summing the cell identity and using `Σd_k=B` therefore proves, for signed `H`,

`|∫_0^∞ e(x)H(x/L)dx - cL∫_0^∞ H(x)dx - BH(0)|`
`≤(8D+4c)A/L`.

This argument requires no derivative of `H`, no sign condition on `H`, and no
absolute integrability claim for `e-c`. Zero tests and every positive scale are
included. The continuous counterterm is integrated after the exact cell producer.

For a nonzero compact C² source `f`, let `Q=∫f²>0` and
`H(x)=autocorr(f,x)/Q`. Compactness of `f` and its derivative gives an actual
finite global Lipschitz constant for `H`: bound its increments by
`‖f'‖∞ (∫|f|)|x-y|/Q`. The correlation is even, compactly supported, and
`H(0)=1`. Fubini gives `∫_ℝ H=(∫f)²/Q`, so the half-line integral is
`(∫f)²/(2Q)`. Apply the signed expansion to obtain

`residual_L = c(∫f)² L/(2Q) + B + O(1/L)`.

Thus zero mean gives convergence to `B`; nonzero mean gives positive linear
escape with exactly the stated slope. For the actual rescaled source `f(x/L)`,
the existing source-rescaling identity yields normalized correlation `H(x/L)`;
the C² compact-source increment estimate bounds its normalized archimedean
energy by a constant times `1/L`. The normalization uses its actual squared
source norm `LQ`. Normalized energy therefore tends to zero. These constants
are derived from `f` itself.

Finally the existing bump `p` has support in `[-1,1]` and positive squared norm.
For `g=p-p(·-4)`, disjoint support gives `∫g=0`, `∫g²=2∫p²`,
`autocorr(g,4)=-∫p²`, hence normalized correlation exactly `-1/2` at lag 4.
Both `p` and `g` remain compact and smooth, realizing the two alternatives.
These statements now have exact Lean declarations and clean transitive axiom audits;
the final source-check status is recorded below.

## Log

- 2026-10-18 — Created before the hard proof. Additive source-mean corpus search
  completed; no new Lean written and no result counted.
- 2026-10-18 — Completed and audited paper proof; moved to fully proven paper stage
  during user-requested closeout after the goal was cleared.

## Exact formalization and verification certificate

The complete original report was recovered at commit `727dc15d1`, path
`docs/reports/BiScaleUncertainty/NyquistCriticalFinitePart.md`; it was deleted
from the current tree in `80971df8c`. The scope includes every displayed
claim in that report, including the absolute primitive tail, exact source
Lipschitz and energy constants, local uniform convergence, and the negative
normalized lag of the actual stretched cancellation witness.

All paths below lie in `formal/GaloisForLFunctions/BiScaleUncertainty/`.
All listed declarations use namespace `GaloisForLFunctions.BiScaleUncertainty`.

| Claim | Exact Lean declarations |
|---|---|
| Critical cell discrepancy and absolutely convergent finite part, including every tail | `nyquistCriticalCellDiscrepancy_bounds`, `abs_nyquistCriticalCellDiscrepancy_le_inv_sq`, `summable_abs_nyquistCriticalCellDiscrepancy`, `abs_nyquistCriticalFinitePartTail_le`, `abs_nyquistCriticalFinitePart_le` |
| Continuous primitive, nodal identity, exact exponential error, unique limit and integrable absolute tail | `nyquistCriticalPrimitive_node`, `abs_nyquistCriticalPrimitive_sub_finitePart_le`, `tendsto_nyquistCriticalPrimitive_iff`, `integrableOn_nyquistCriticalPrimitive_sub_finitePart`, `integral_abs_nyquistCriticalPrimitive_tail_le` |
| Exact centered-cell width bound and summable signed test errors | `integral_abs_nyquistCriticalCell_centered_le`, `abs_nyquistCriticalCellTestError_le`, `tsum_nyquistCriticalTestCellMajorant_le` |
| Signed compact Lipschitz expansion, coefficient `8D+4c`, all positive scales | `abs_nyquistCriticalBroadTest_error_le`, `abs_nyquistCriticalBroadTest_full_error_le` |
| Actual source correlation, positivity, signed Fubini mass, derived Lipschitz constants and normalized scaling | `nyquistSourceMass_pos`, `integral_autocorr_eq_sq_integral`, `integral_Ioi_nyquistNormalizedCorrelation`, `lipschitzWith_nyquistNormalizedCorrelation_of_source`, `normalized_sourceRescale_eq_nyquistNormalizedCorrelation` |
| Exact source slope and error, both mean alternatives and the if-and-only-if classification | `abs_nyquistCriticalSource_error_le_of_source_lipschitz`, `tendsto_nyquistCriticalSourceResidual_div_scale`, `tendsto_nyquistCriticalSourceResidual_atTop_of_mean_ne_zero`, `tendsto_nyquistCriticalSourceResidual_iff_mean_zero` |
| Exact normalized energy integral and first-moment bound, vanishing energy, locally uniform actual correlations | `normalizedArchEnergy_broadSource_eq`, `normalizedArchEnergy_broadSource_bounds`, `normalizedArchEnergy_broadSource_le_of_source_lipschitz`, `tendsto_normalizedArchEnergy_broadSource`, `tendstoUniformlyOn_normalized_broadSource` |
| Actual smooth positive-mean and zero-mean sources, disjoint-support identities and lag `4L` | `contDiff_nyquistPositiveMeanWitness`, `contDiff_nyquistZeroMeanWitness`, `nyquistPositiveMeanWitness_integral_pos`, `nyquistZeroMeanWitness_mass_and_lag`, `nyquistZeroMeanWitness_broad_normalized_at_four_mul`, `nyquistCritical_fixedSource_mean_dichotomy` |

Axiom audit `7737` exited 0 without diagnostics. All 96 exact declaration
names were checked; every dependency list is contained in
`{propext, Classical.choice, Quot.sound}`. Source scan found no forbidden
proof token or raised proof limit in these eight leaves. No mathematical
assumption was added to any report statement. The domains of compact
Lipschitz tests and nonzero compact C² sources are retained exactly.

All eight leaves passed final direct source checks, each using
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/<leaf>.lean`
from `formal/`, with exit 0 and no diagnostics. These checks write no olean.
The last check, SourceQuantitative (`54703`), also passed. Source hashes
still match the exact 96-declaration audit.
All eight imports occur once in the owning umbrella; no umbrella was compiled.
A completed corpus query returns the signed witness, primitive-tail and
quantitative energy declarations. Scoped whitespace checks passed.
Global lint currently reports 21 unrelated errors and 416 size warnings,
with no Nyquist diagnostic. No repository-wide green result is claimed.

Evidence: `/tmp/leftovers-nyquist-complete-public-names.json`,
`/tmp/leftovers_nyquist_witnesses_audit.lean`,
`/tmp/leftovers-nyquist-witnesses-audit.log`, and the individual
`/tmp/leftovers-nyquist-*-final.log` files, plus
`/tmp/leftovers-nyquist-final-index.json` and `/tmp/leftovers-nyquist-lint.log`.

| Leaf | Public declarations | Source SHA256 |
|---|---:|---|
| `NyquistCriticalFinitePartAndBroadClassification.lean` | 33 | `3a2c670c2a498fcd6b0d2997922bac4d9cdf2da587d619afd924849ae6110ed7` |
| `NyquistCriticalPrimitive.lean` | 7 | `a61e3fd530ad270f16b110d3444268e490212d9fa77295a3c3976ca8b52273f0` |
| `NyquistCriticalTestCellBounds.lean` | 6 | `89e65fda98b2c060f4d48f40d5e0d919e01f29f4e41fc91223e6d83f03a76cdb` |
| `NyquistCriticalBroadTests.lean` | 4 | `e566034bb5c38472077f815d427d81e607455601cef9240e32c4628ef523f0ca` |
| `NyquistCriticalSourceClassification.lean` | 20 | `01b41de56acffe2680cf870fa022ddbfd3dd95e01e46d7d0ba6773a06cf4572a` |
| `NyquistCriticalSourceQuantitative.lean` | 9 | `17347a8c27936b6fdf7238dfa8819aeff5d807bbad91685b850828dd1b2003a3` |
| `NyquistCriticalSignedWitnesses.lean` | 12 | `deba589422deb8e01a227c153ee32fb76d0a1270be994bac7c78de7bb4bd4158` |
| `NyquistCriticalPrimitiveTail.lean` | 5 | `8686208c7a0af286da6614e2c92160754be35e3d6c5e87d0306f48fb21b67d87` |
