# SQB full-source cusp norm

Status: 10 public declarations formalized and individually audited. RH remains
unproved. All public axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.
The frontier map is read-only.

## Exact target

For an actual Xi copy with zero rho, write beta=Re rho and u=(rho−1)/2.
Let E be the original complete scalar Eisenstein field, including every Fourier
mode. For every real a, its cusp norm with multiplier y^a is finite precisely when

`integral_{y>2} integral_{−1/2<x≤1/2} y^(2a) |E_u(x,y)|² dx dy/y² < infinity`

`iff 2a+1 < beta`.

Thus the literal quarter multiplier has finite cusp norm iff beta>1/2. Its
unique inversion-invariant compensating density from the previous source audit
restores the original divergent cusp norm at every actual Xi copy. This is a
source-specific domain classification, not an occurrence theorem for the entire
operator or an exclusion of other source maps.

## Dependency-closed paper argument

The existing physical calibration gives
`E_u=Lambda(rho−1)y^(1−rho/2)+T_u`, with Lambda(rho−1) nonzero.
The actual complete Fourier tail obeys a uniform bound on `|y^w T_u(x,y)|`
for every complex w and all x, y≥2. Hence `y^(a−1)T_u` lies in L² of the
product of the unit horizontal interval and the height ray: its square is
bounded by a constant times y^(−2), using w=a.

Subtracting this admitted tail shows that `y^(a−1)E_u` is in L² exactly when
its nonzero constant term is. That term has squared norm
`|Lambda(rho−1)|² y^(2a−beta)`. Product integration over the unit horizontal
interval reduces to the exact power integral on y>2, which is finite iff
2a−beta<−1. This retains the full source and treats the equality case as divergent.

## Corpus search and work plan

Broad OR searches, without per-module caps, covered 658 declarations in 121
modules for integral/order transformations; 1,858 in 413 modules for monodromy,
waves, functional calculus and Poisson transforms; 473 in 117 modules for
automorphic multipliers, Eisenstein powers, truncation and periodization; and
416 in 252 modules for cusp norms, power densities and square integrability.
These counts describe index coverage, not a claim to have read every proof.
Inspected height-power periodization returns the original completed Eisenstein
field. Inspected Bessel-order isomonodromy concerns the order recurrence and does
not provide the required spatial source transformation. The norm proof uses
the actual uniform tail bounds and physical constant-term calibration.

- [x] Identify original source, exact measure and sharp target.
- [x] Complete paper argument with retained Fourier tail.
- [x] Verify APIs and proof in scratch with one foreground Lean process.
- [x] Add audited source module and wire its umbrella import once.
- [x] Run isolated module build, axiom audit and formal lint; global lint result below.
- [x] Update the existing symmetry-and-norm entry in the universal ledger.


## Lean certificate and exact scope

`GaloisForLFunctions.RHTower.SelbergScatteringCuspNorm` exports ten declarations
in `RHTower.SelbergScatteringHeightConjugation`:

- `cuspMeasure` is the product of Lebesgue measure restricted to
  `(−1/2,1/2]` and `(2,infinity)`.
- `cuspLift a f(x,y)=y^(a−1)f(x,y)` includes the square root of the native
  hyperbolic density. `cuspLift_norm_sq` identifies its squared norm exactly.
- `cuspLift_tail_memLp` admits the complete signed Fourier tail for every complex
  source parameter and every real a, uniformly over the whole cusp rectangle.
- `cuspLift_xi_memLp_iff` and `scalarSource_cusp_norm_iff` prove the sharp
  full-source criterion, first as L² membership and then in the explicit density.
- `scalarSource_native_cusp_not_integrable` proves divergence for every actual
  Xi copy using only its already proved open-unit-strip location.
- `quarterShiftSource_weighted_cusp_norm_iff` proves that the density
  `y^b |v|²/y²` is integrable exactly when `b+1/2<Re rho`.
- `quarterShiftSource_cusp_norm_iff` gives the unweighted threshold `Re rho>1/2`.
- `quarterShiftSource_compensated_cusp_not_integrable` proves divergence at
  the unique inversion-invariant weight b=1/2.

The Fourier-tail argument is global over the unit-width cusp rectangle. It does
not discard the tail, replace the field by its constant term, assume nonzero
source data, or insert any zero-location hypothesis. Integrable tail subtraction
is an equivalence, so the strict endpoint is included in the divergent side.
This is a cusp norm result. Scalar modular descent of the quarter multiplier
already fails, and no domain or occurrence assertion for the entire operator
follows from the norm criterion alone.

Validation: scratch checked with `lake env lean /tmp/sqb7_norm.lean`; final
`lake build GaloisForLFunctions.RHTower.SelbergScatteringCuspNorm` passed (7.6s).
The preflight named only this stale module; the final log records only this
module as built. Its umbrella import occurs once. All ten exports were checked
by `#print axioms` in a separate scratch file and found in the refreshed corpus
index. No numerical experiment or computed datum enters a proof.

Repository-wide `scripts/formal_tools.py lint` passes in `/tmp/sqb8_lint.log`,
with existing file-size warnings. Isolated norm-module audit logs:
`/tmp/sqb7_build.log`, `/tmp/sqb7_axioms.log`, `/tmp/sqb7_index_audit.json`.
