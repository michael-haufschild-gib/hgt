# The zero width is the ground-energy fall rate when the off-line zeros do not cluster

- **ID:** `width-to-ground-energy-floor-when-off-line-zeros-do-not-cluster-2026-10-21`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2110/route-unification-ledger.md`, "Open arrows of the
  dictionaries": the width-to-floor arrow `zetaZeroWidth ≤ σ ⟹ μ(A) ≥ −Ce^{2σA}` (also walls
  ledger, Wall 1, "The open arrow")
- **Statement:** if at most `M` off-line zeros of `ξ` (divisor copies, with multiplicity) have
  height within `1` of any `T`, then the restricted Weil ground energy satisfies
  `μ(A) ≥ −M (2A + 2π) e^{2π} e^{2·zetaZeroWidth·A}` at every aperture `A`, hence
  `polarGroundEnergyRate = zetaZeroWidth`; finitely many off-line zeros give the two-sided law
  `c e^{2σA} ≤ −μ(A) ≤ C e^{2σA}` for all large `A`, `σ = zetaZeroWidth`; unconditionally the
  exponent equals the width or the off-line zeros cluster without bound on unit windows.

## Goal
Close the one arrow of the width dictionary that was missing (width ⟹ ground-energy floor at
rate twice the width), or identify its exact residual. Result: the arrow closes under a uniform
unit-window bound on the off-line zeros, is two-sided when they are finitely many, and the residual
from the width alone is exactly that bound. No hypothesis beyond the stated one; no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`; no computation.

## Gates
- [x] 0 → 1  in-progress: corpus survey with the search tool: `R:CCMParityTopLayerGroundEnergyLaw`
  (two-sided law under a finite top layer), `R:CCMParityQuartetZeroSum` (source quadratic as a
  zero sum), `R:WindowTransformSamplingParseval` (grid Parseval), `R:CCMParityQuartetEvenFloor` and
  `R:CCMParityTopLayerOddFloor` (density extension), `R:CCMRestrictedWeilGroundParity`
  (pure-parity ground state), `Q:TheSideIsTheDepthAndTheWidthIsItsSupremum` (depth = width
  dictionary), `Q:TheZeroWidthIsALandauExponent` (polar exponent).
- [x] 1 → 2  fully-proven: zero-side floor plus the sampling inequality (power series of the
  transform in the moment transforms, weighted Cauchy–Schwarz, cell count, grid Parseval).
- [x] 2 → 3  formalized: `Q:IntervalSourceTransformsSampledOnLocallyBoundedPoints` and
  `Q:TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster` compiled with `lake env lean`,
  axioms standard (`#print axioms` scratch), oleans built single-threaded with
  `lake --old env lean -j 1 -o`, wired into the `SquareRootThreshold` umbrella import block,
  `scripts/formal_tools.py lint` reachable, no `sorry`.
- [ ] 3 → 4  not applicable (no stage 4 for non-RH items).

## Approach
The ground energy is `L²`-normalized while the off-line zero sum of a test is a sum of `|Φ|²` over
points at complex height; the obstruction recorded on the walls ledger was that such sums are
controlled by `e^{2σA}` times a derivative norm. The sampling inequality removes the derivative:
for a source vanishing off `[−A, A]` and points `x_q + iy_q` with `|y_q| ≤ σ` and at most `M`
heights per unit window,
`Σ_q |Φ(x_q + iy_q)|² ≤ M (2A + 2π) e^{2π} e^{2σA} ∫|u|²`.
Proof: `h = 2π/(2A + 2π)`, every point is a grid point `g ∈ hℤ` plus `w` with `|w| ≤ h + σ`;
`Φ(g + w) = Σ_j (iw)^j/j! Φ_j(g)` with `Φ_j` the transform of `x^j u(x)`
(`testTransform_add_eq_tsum_momentSource`); weighted Cauchy–Schwarz with weights `((h+σ)A)^j/j!`
(`sq_tsum_le_tsum_mul_tsum_div`); at most `M` points per cell (`card_filter_gridIndex_le`); grid
Parseval `Σ_k |Φ_j(kh)|² = (2A + 2π)∫|x^j u|² ≤ (2A + 2π)A^{2j}∫|u|²`
(`hasSum_norm_sq_testTransform_grid`, from `R:WindowTransformSamplingParseval`); the factorial
series sums twice to `e^{2(h+σ)A}` and `hA ≤ π`.

Zero side: `Q(u) = Σ_q Re Φ(−z_q) conj Φ(−z̄_q)`, on-line terms `≥ 0`, off-line terms
`≥ −(|Φ(−z_q)|² + |Φ(−z̄_q)|²)/2`, depths `|Im z_q| = |Re ρ − ½| ≤ zetaZeroWidth`; density to the
even and odd form vectors; pure-parity ground state.

Finite case: the maximal depth of a finite off-line set is the width (every copy has depth at most
the width; the width is at most the maximal depth by `zetaZeroWidth_le_iff_xiZeroHalfPlaneBound`
with the copy of each zero), the distinct heights at the top depth give `t : Fin m → ℝ`, the
quartet symmetries (`xiZeroCopyLineConjEquiv`, `xiZeroCopyReflectEquiv`) give the copy at
`|Re z| + i|Im z|`, so `FiniteTopLayer zetaZeroWidth t` and the existing two-sided law apply.

## Theorems (all closed, standard axioms)
- `Q:IntervalSourceTransformsSampledOnLocallyBoundedPoints`: `momentSource`,
  `testTransform_add_eq_tsum_momentSource`, `norm_testTransform_le_tsum_momentSource`,
  `windowLength`, `gridStep`, `hasSum_norm_sq_testTransform_grid`,
  `intervalIntegral_norm_sq_momentSource_le`, `sum_norm_sq_testTransform_grid_le`, `gridIndex`,
  `abs_sub_gridPoint_le`, `card_filter_gridIndex_le`, `sq_tsum_le_tsum_mul_tsum_div`,
  `momentWeight_mul_sq`, `sq_div_momentWeight`, `sum_norm_sq_testTransform_le_of_locallyBounded`,
  `sum_norm_sq_testTransform_le_of_locallyBounded'`,
  `summable_tsum_norm_sq_testTransform_le_of_locallyBounded`.
- `Q:TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster`: `OffLineCopiesLocallyBounded`,
  `clusterFloorConst`, `xiZeroCopy_mem_zetaZeroConfig_carrier`,
  `abs_im_xiSpectralPoint_le_zetaZeroWidth`, `sourceQuadratic_ge_of_offLineCopiesLocallyBounded`,
  `sourceQuadratic_ge_of_offLineCopiesLocallyBounded_of_parity`,
  `neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy`,
  `exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineCopiesLocallyBounded`,
  `polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded`, `inQuartet_of_abs_eq`,
  `exists_xiZeroCopy_spectralPoint_eq_abs`, `xiSpectralPoint_re_ne_zero`,
  `exists_finiteTopLayer_of_finite_offLine`, `exists_groundEnergy_exponential_bounds_of_finite_offLine`,
  `offLineCopiesLocallyBounded_of_finite`, `polarGroundEnergyRate_eq_zetaZeroWidth_of_finite_offLine`,
  `polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`,
  `infinite_offLine_of_zetaZeroWidth_lt_polarGroundEnergyRate`,
  `theWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster`.

## What remains open (the exact residual)
The arrow from the width alone, without the unit-window bound on the off-line zeros. The
`L²`-normalized sum of `|Φ|²` over the off-line copies cannot be bounded by `e^{2σA}∫|u|²` when
the copies cluster without bound: a modulated bump `e^{iγ_k x}φ(x)` against `m_k` off-line copies
of depth `σ` near height `γ_k` with aligned phases `2γ_j A` contributes about `−m_k c_φ e^{2σA}`
against an `L²` norm `∫φ²`, so a floor at rate `2σ` with constant `C` forces the aligned cluster
sizes below `C/c_φ` (paper reasoning, not in Lean). The unconditional local count `≪ log T`
(`Zeta23.RvM.zetaZeroConfig_local_count`) gives only a floor in the archimedean (log-Sobolev)
norm, which the ground energy does not control. The residual is therefore one statement about
`ζ`: a uniform bound on the number of off-line zeros in unit height windows. Nothing in the corpus
or the literature known to the author gives it beyond the trivial `≪ log T`.

## Corpus repair made on the way
`RHTower.integrable_mul_cexp` was declared both in `R:IsolatedDeepZeroHodgeIndex` (continuous with
compact support) and in `R:WindowTransformSamplingParseval` (continuous, vanishing off
`[−L/2, L/2]`), both wired into the `RHTower` umbrella since 2026-09-27, so no module can import
both cones. The second copy, used only inside its own module, is renamed
`integrable_mul_cexp_of_vanish`; its olean was rebuilt single-threaded. No consumer outside the
module used the name.

## The depth-weighted form (2026-10-22)
The count hypothesis is replaced by the squared depths: `OffLineDepthLocallyBounded W` asks
`Σ_{|Re z_q − T| ≤ 1} (Im z_q)² ≤ W` for every `T` (on-line copies cost nothing; the count
hypothesis implies it with `W = M·zetaZeroWidth²`). Mechanism: the conjugate difference
`Φ(c + w) − Φ(c + w̄)` is the odd part of the power series and is at most
`2|Im w| Σ_m r^m/m! |Φ_{m+1}(c)|` (`norm_testTransform_sub_conj_le_tsum_momentSource`, through
`‖w^n − w̄^n‖ ≤ n r^{n−1}‖w − w̄‖`); the weighted cell count
(`sum_weight_mul_grid_le_of_depthWeighted`) and the same grid Parseval give
`Σ_q |Φ(x_q + iy_q) − Φ(x_q − iy_q)|² ≤ 4a²(2a + 2π)e^{2π}e^{2σa} W ∫|f|²`
(`sum_norm_sq_testTransform_sub_conj_le_of_depthWeighted'`). With `Re(p conj q) ≥ −|p − q|²/4`
(`re_mul_conj_ge`) the zero-side floor needs no on-line/off-line split:
`μ(A) ≥ −A²(2A + 2π)e^{2π}e^{2·zetaZeroWidth·A} W` (`neg_depthFloorConst_le_ccmRestrictedWeilGroundEnergy`),
`polarGroundEnergyRate = zetaZeroWidth` (`polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded`),
dichotomy (`polarGroundEnergyRate_eq_zetaZeroWidth_or_depthMass_clusters`,
`exists_window_depthMass_gt_of_zetaZeroWidth_lt_polarGroundEnergyRate`), and the unconditional
comparison `Σ_{window at T ≥ 4} (Im z_q)² ≤ 40·zetaZeroWidth²·log(180T)`
(`sum_sq_im_xiSpectralPoint_window_le`, from `R:ZetaLocalZeroCount`). Collected statement
`theWidthIsTheGroundEnergyRateWhenTheDepthMassDoesNotCluster`. The residual of the width
dictionary is now exactly one logarithm: a `T`-independent bound on the window depth mass in
place of `log T`.

## Prior corpus work found after the build
`R:OffLineDensityWeilLowerBound` (`re_W_ge_of_depth_offLineDensity`, hypothesis
`OffLineDensityBound`) already proves the configuration-space form of the floor,
`Re W(f, f) ≥ −3500(2a + 3) D e^{2η(a+2)} ∫|f|²` for a configuration of width `η` with off-line
multiplicity at most `D` per unit window, by a weighted Bessel inequality (Schur test). The
sampling inequality of `Q:IntervalSourceTransformsSampledOnLocallyBoundedPoints` is an
independent proof of the same kind of bound (grid Parseval, better constant, moment transforms);
the new content of this card is the transfer to the CCM ground energy `μ(A)` of `ζ`, the exponent
identity, the finite-case two-sided law and the dichotomy. `R:ErrorExponentAbscissaExcessLaw`
(`abs_re_sub_half_le_iff_eventually_relaxed`) already proves the configuration-space two-way law
(depth `≤ η` ⟺ relaxed Hodge index at every exponent `θ > 2η` eventually, under the local count
`≪ log t`, no zeros below ordinate `2`, off-line multiplicity `≤ D` per unit window), so the
exponent identity of this card is its transfer to `ζ`'s CCM ground energy.
`R:OffLineClusterWeilUnbounded` is the model on the other side: pairs `¼, ¾ + ie^{k+1}` of
multiplicity `⌊log γ⌋`, within the `log t` local count, with the Weil form unbounded below at every
large level.

## Log
- 2026-10-21 — created directly in 3-formalized: both modules compiled, audited (standard
  axioms), oleans built, wired into the `SquareRootThreshold` umbrella; lint reachable. Ledger
  sections updated (`route-unification-ledger.md`: arrows, open arrows, new section "The
  width-to-floor arrow"; `walls-ledger.md`: Wall 1 open-arrow paragraph and rule).

- 2026-10-22 — depth-weighted form added to both modules (section 7 of the sampling module,
  section 6 of the width-rate module), compiled, audited, oleans rebuilt; ledgers updated.
