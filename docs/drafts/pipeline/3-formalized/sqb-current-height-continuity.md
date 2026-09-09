# Complete original current: height continuity and rectangle mass

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Exact statements

For the full original finite Maass vector source F, put D=Σ|F_q|²,
Aₓ=Re Σ F_q,xx conj(F_q), and Bₓ=Σ|F_q,xx|. Previous formal work proves

    E_e(y) = −∫₀¹ Aₓ(x+iy)/√(D(x+iy)+e²) dx → E₀(y) ≥ 0,
    E₀(y) = −∫₀¹ Aₓ(x+iy)/√D(x+iy) dx.

These are complete period-current integrals, including any integrated
nodal concentration. The quotient at a common zero is zero.

The new module proves:

1. E₀ is continuous at every y>0, including heights with common source zeros.
2. On every compact band 0<a≤b, the actual iterated horizontal-current
   integral converges:

       ∫ₐᵇ∫₀¹ H_e(x+iy) dx dy → ∫ₐᵇ E₀(y) dy,

   where H_e retains all pair, phase and regulator-gradient terms.
3. If E₀(y₀)>0, there exist 0<a<y₀<b and c>0 such that E₀(y)≥E₀(y₀)/2
   throughout [a,b], and the actual rectangle current is at least c for
   every sufficiently small regulator.
4. For 0<a<b, ∫ₐᵇE₀=0 if and only if E₀ vanishes at every height in [a,b].
5. An original common zero with nonzero horizontal first-derivative energy
   supplies the positivity premise in statement 3, by the prior nodal
   current theorem.

All bands and constants depend on the actual source and chosen height.
No positive current height or nonflat node is assumed to exist globally.

## Dependency-closed proof

First prove a general real-parameter calculus lemma for normed vector
targets. At a zero with nonzero derivative, the derivative's punctured
neighborhood property makes that zero isolated within the zero set.
Second countability makes the exceptional set countable. Apply the result
to F_q and then its first derivative: outside the union of two countable
sets, F_q=0 implies F_q,x=F_q,xx=0. The finite coordinate intersection gives
Bₓ=0 at almost every common zero on any fixed horizontal line.

Original C² regularity makes Aₓ and Bₓ jointly continuous in the open upper
half-plane. At nonzero D, the signed quotient Aₓ/√D is continuous by the
quotient rule for continuity. At a common zero with Bₓ=0, the exact source
bound |Aₓ/√D|≤Bₓ squeezes the quotient to zero in every direction. Thus for
each fixed height, the quotient is continuous in height for almost every
horizontal coordinate. A compact rectangle has a finite upper bound for
Bₓ, derived from that same source. Dominated convergence now proves
continuity of E₀ at every positive height. This argument does not require
the common zero set to have measure zero.

For positive regulator e, the regulated signed quotient is jointly
continuous. The same compact bound proves E_e is continuous in height.
Moreover 0≤E_e(y)≤∫₀¹Bₓ(x+iy)dx≤C on the entire compact band, independently
of e. The already proved pointwise period limit E_e(y)→E₀(y) and dominated
convergence in height give statement 2. The exact original horizontal
current/path-energy identity identifies its left side with the literal
iterated current integral.

Continuity of E₀ and E₀(y₀)>0 give a closed band containing y₀ in its
interior with E₀≥E₀(y₀)/2. Its limiting mass is positive. Rectangle-current
convergence therefore gives a fixed positive bound at every sufficiently
small regulator. Nonnegative continuous E₀ also shows that zero band mass
forces zero at every point, including both endpoints. Finally, substitute
the previous source-derived strict positivity at a nonflat common node.

## Scope of the progress

This closes a passage from positive complete line current to positive
two-dimensional rectangle current, including common-zero heights. It is
not a uniform comparison with amplitude mass. The quotient-area quarter
inequality and independent full-Xi spectral occurrence remain open. No
Fubini identification with a quotient measure, explicit nodal measure,
pointwise current-limit interchange, or exclusion of flat nodes is claimed.

## Broad corpus discovery

Both searches used `scripts/formal_tools.py research` with OR matching,
no per-module cap, and complete declaration-result retrieval:

- Level set, Stampacchia, derivative zero, zero set, nodal, Sobolev chain:
  1,160 results in 460 modules.
- Continuity of integral, parameter integral, lower semicontinuity, energy
  continuity, dominated convergence, positive band: 137 results in 82 modules.

Counts describe metadata discovery, not inspection of every proof. Actual
source inspection covered original acceleration/current formulas, original
source C² regularity and nodal rigidity, compact parameter bounds in the
Fourier modules, and Mathlib derivative isolation, countable one-sided
isolated sets, dominated convergence and interval positivity. Analytic
zero-set hits were not used to assume analyticity of the Maass source.
Search outputs: `/tmp/sqb20_zero_set_broad.json` and
`/tmp/sqb20_continuity_broad.json`. No numerical experiment supplied a result.

## Lean audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity`.
It contains 24 public theorems. Main results:

- `ae_flat_second_zeros`
- `periodCurrentLimit_continuousAt`
- `horizontalCurrent_rectangle_tendsto`
- `exists_eventually_positive_horizontal_rectangle`
- `current_band_mass_eq_zero_iff`
- `nonflat_node_positive_horizontal_rectangle`

Scratch: `/tmp/sqb20_height.lean`; log: `/tmp/sqb20_height.log`.
Source check: `lake env lean GaloisForLFunctions/RHTower/SelbergMaassCurrentHeightContinuity.lean`
passed without warnings (`/tmp/sqb20_height_source.log`). Preflight found
only the intended leaf stale. Final audit
`lake build GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity`
passed and compiled only that module in 4.7 seconds; the other jobs in the
8,820-job dependency graph were cached. No umbrella or full build ran.
Logs: `/tmp/sqb20_height_preflight.log`, `/tmp/sqb20_height_build.log`.

All 24 declarations were checked individually in `/tmp/sqb20_axioms.lean`;
their axiom inventories contain only `propext`, `Classical.choice`, and
`Quot.sound` (`/tmp/sqb20_axioms.log`). No proof hole, added axiom, unsafe
declaration or external computation was introduced. The module is wired
once into `RHTower.lean`. All 24 declarations are indexed exactly once in
`/tmp/sqb20_indexed_declarations.json`. Repository index and formal lint
passed (`/tmp/sqb20_index.log`, `/tmp/sqb20_lint.log`); existing unrelated
large-file lint warnings remain. Whitespace and owned-process checks
passed. This work made no edits to the read-only frontier map.
