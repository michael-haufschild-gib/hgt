# Original-source period resistance: exact regulator-removal classification

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Exact source statement

Let F be the complete finite congruence Maass source, D=||F||², and y>0.
For each positive regulator e define the literal period resistance

    R_e(y) = ∫₀¹ 1/√(D(x+iy)+e²) dx.

The following three conditions are equivalent:

1. D(x+iy)>0 for every x in [0,1].
2. The family R_e(y), over all e>0, is bounded above.
3. R_e(y) has a finite real limit as e→0 through positive regulators.

In this case compactness constructs a source-specific d>0 with √D≥d on
that period. The literal unregularized reciprocal integral R₀(y) is finite,
and for every e>0,

    0 ≤ R₀(y)−R_e(y) ≤ e/d²,
    R_e(y) ≤ R₀(y) ≤ 1/d.

The complementary classification is exact:

    R_e(y) → +∞  ⇔  ∃ x∈[0,1], D(x+iy)=0.

More quantitatively, every actual common zero z=a+iy supplies L≥1 such that

    R_e(y) ≥ [log(L+e)−log(e)]/L.

No actual nodal point is asserted to exist. These statements apply to the
original finite-family source, retaining every component. They assume no
separate amplitude floor, derivative bound or resistance bound: the source
regularity and the chosen branch of the classification supply them.

## Dependency-closed proof

At a common zero z, every source component F_q vanishes. Original C²
regularity makes all horizontal first derivatives continuous. Compactness
of [a,a+1] bounds the sum of their norms by a finite number; enlarging it
provides a positive common derivative bound C. The one-dimensional mean
value estimate, applied to each complex component, gives

    |F_q(x+iy)| ≤ C(x−a),  a≤x≤a+1.

Summing the squares and taking square roots gives

    √D(x+iy) ≤ √(|Deck N| C²)(x−a) ≤ L(x−a)

with L=1+√(|Deck N| C²)≥1. Consequently
√(D+e²)≤L(x−a)+e. Both regulated reciprocal functions are continuous and
integrable on the full interval. Their pointwise comparison and the
fundamental theorem of calculus applied to log(L(x−a)+e)/L yield

    ∫ₐᵃ⁺¹ 1/√(D+e²) dx
      ≥ ∫ₐᵃ⁺¹ 1/(L(x−a)+e) dx
      = [log(L+e)−log(e)]/L.

The original source's proven T-periodicity identifies the left side with
R_e(y), regardless of a. Since L≥1, log(L+e)≥0. The lower bound −log(e)/L
tends to +∞ in the actual positive-regulator filter, proving divergence.

If the original period is zero-free, continuity and compactness attain the
strictly positive minimum d of A(x)=√D(x+iy). Put r=√(D+e²). Then
A≤r≤A+e, and at every point in the period,

    0 ≤ 1/A−1/r = (r−A)/(Ar) ≤ e/d².

All terms are interval-integrable because A≥d>0 and r>0. Integration over
the unit interval gives the asserted quantitative error; comparison with
1/d bounds R₀. Squeezing the error by e/d² proves R_e→R₀.

If zero-freeness fails, nonnegativity of D supplies a common zero.
The divergence theorem contradicts either boundedness or a finite limit.
Conversely, zero-freeness supplies both. Divergence and finite convergence
are incompatible in the proved nontrivial positive-regulator filter.
This proves all three equivalences without selecting either nodal branch.

## Consequence for the active proof chain

The preceding block-path result reduces the original comparison to
resistance/current products at two original heights, with exact coefficient
N(2N+1)/12. This classification resolves the resistance factor's regulator
behavior at every fixed source and height. Source smoothness alone cannot
remove that factor; a zero-free period gives a finite source-specific limit.

The full product can behave differently from resistance alone because its
current-energy factor can vary with e. No divergence, finite limit or
uniform estimate for that product is inferred here. Nodal curvature remains
part of the original measure budget. Joint product control and the passage
from line estimates to a quotient-area lower bound remain open, as do the
quarter inequality and independent full-Xi spectral occurrence. No complete
route is retired and no unconditional RH result is claimed.

## Broad corpus discovery

All searches used the repository research tool with OR matching, no
per-module cap and full declaration-result retrieval:

- Harmonic mean, reciprocal amplitude, inverse moment, weighted Poincare,
  Muckenhoupt, Harnack: 62 rows in 26 modules.
- Nodal, zero mean, real scalar, inverse amplitude, reciprocal norm:
  775 rows in 226 modules.
- Weighted mass, Cauchy defect, harmonic arithmetic, reciprocal weight,
  coarea, congestion: 737 rows in 178 modules.
- Locally Lipschitz, Lipschitz bound, vanishes at, reciprocal integral,
  logarithmic divergence: 734 rows in 613 modules.

Counts describe discovery metadata, not proof inspections. Source inspection
covered actual current-period identities, regulator/full mass, residual
support, curvature atomlessness, Fourier slice calculus, and the existing
toy nodal resistance. The toy proof did not establish the actual-source
classification. Mathlib mean-value, compactness, interval-integral and
filter-limit APIs were checked in the current toolchain. No numerical
experiment or external computation supplied a proof result.

Search outputs: `/tmp/sqb17_weights_broad.json`,
`/tmp/sqb17_nodal_broad.json`, `/tmp/sqb17_mass_broad.json`,
`/tmp/sqb17_lipschitz_broad.json`.

## Lean and audit

Module `GaloisForLFunctions.RHTower.SelbergMaassPeriodResistance` has 17
public definitions/theorems. Main results:

- `exists_linear_amplitude_bound_at_node`
- `exists_periodResistance_log_lower`
- `periodResistance_tendsto_atTop_of_node`
- `periodResistance_error_bounds`
- `periodResistance_tendsto_of_zero_free`
- `periodResistance_bddAbove_iff_zero_free`
- `periodResistance_tendsto_atTop_iff_node`
- `periodResistance_finite_limit_iff_zero_free`

Scratch and final source checks passed without warnings. The sole-target
final build passed; preflight and final build logs identify only the new leaf
as requiring compilation. No full or umbrella build ran. Existing cached
EvenL2LogUnitary informational output was replayed.

All 17 declarations have checked axiom inventories containing only
`propext`, `Classical.choice`, and `Quot.sound`. All 17 are indexed exactly
once, and the module is imported once in the RHTower umbrella. Repository
formal lint passed with existing large-file warnings. No owned Lean/Lake
process remains. No frontier-map edits were made; peer work was preserved.

Logs: `/tmp/sqb17_resistance_scratch.log`,
`/tmp/sqb17_resistance_source.log`, `/tmp/sqb17_resistance_preflight.log`,
`/tmp/sqb17_resistance_build.log`, `/tmp/sqb17_axioms.lean`,
`/tmp/sqb17_axioms.log`, `/tmp/sqb17_audit_names.txt`,
`/tmp/sqb17_index.log`, `/tmp/sqb17_lint.log`.
