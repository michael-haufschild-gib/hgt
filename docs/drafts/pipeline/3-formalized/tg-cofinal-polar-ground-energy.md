# TG: cofinal admission of the actual prime–polar ground source

- **ID:** tg-cofinal-polar-ground-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, principal prime–polar operator cancellation, C9.11z
- **Statement:** A cofinal strong limit of the literal prime atoms minus all original polar cells exists exactly when their positive cumulative critical energy is finite.

## Exact source and statement

Fix a>0. Retain the original normalized ground entry
`B_n = soninGroundEntry a (log(n+2))` and the original polar cell mass

`alpha_n = integral_[log(n+2),log(n+3)] (exp u+1)/u du`.

Put `c_n=1_Prime(n+2)-alpha_n`, `A_n=sum_(j<=n)c_j`,
`G_N=sum_(n<=N)c_n B_n`, and

`E_n=A_n²/((n+2)(n+3))`.

Then the following are equivalent:

1. `sum_n E_n` is finite.
2. There is a cofinal sequence phi and a physical L2 vector g with `G_(phi(k)) -> g` strongly.
3. There is C such that every M admits N>=M with `||G_N||²<=C`.

The same strong-admission equivalence holds after replacing G_N by the finite assembly
of each literal prime atom minus its full original strong polar integral. The correction
is exactly the previously admitted within-cell polar series.

No assertion here proves condition 1 for the actual arithmetic coefficients. No zero-free
hypothesis, RH premise, new axiom, changed prime coefficient or changed polar density
enters the equivalence. Structural hypothesis a>0 selects a nonzero physical aperture.

## Dependency-closed paper proof [PROVED HERE]

The audited native covariance is
`<B_i,B_j>=2a/(j+2)` for i<=j. Set `D_n=B_n-B_(n+1)`.
Subtracting the four literal covariances proves pairwise orthogonality of D_n;
subtracting the diagonal and adjacent terms gives

`||D_n||²=2a/((n+2)(n+3))`.

Also D_i is orthogonal to B_(N+1) whenever i<=N. Finite summation by parts gives

`G_N=sum_(n<=N) A_n D_n + A_N B_(N+1)`.

This retains the complete arithmetic source. Orthogonality gives the exact identity

`||G_N||² = 2a [sum_(n<=N) E_n + A_N²/(N+3)]`.

For 1 -> 2, the family `A_n D_n` has summable squared norms and is therefore
unconditionally summable in the physical Hilbert space. For every epsilon>0 and M,
some N>=M has `A_N²/(N+3)<epsilon`: otherwise, for every N>=M,

`E_N >= epsilon/(N+2)`,

contradicting divergence of the harmonic tail. Choose phi(k)>=k with terminal square
less than `1/(k+1)`. Its terminal vector has squared norm at most `2a/(k+1)` and tends
to zero; the orthogonal series tends to its sum. Their exact finite reconstruction
therefore supplies the required strong limit.

For 2 -> 3, norms of a convergent sequence are bounded and its indices are cofinal.
For 3 -> 1, given any finite energy prefix, choose a later bounded source return.
The exact energy identity, including its nonnegative terminal square, bounds the
prefix by C/(2a). Every nonnegative energy prefix is bounded, so the series is finite.

Finally the original polar cell equals `alpha_n B_n+R_n`, with the literal R_n
unconditionally summable by `SoninPolarGroundDiscretization`. Summing the identity
shows that the native cell assembly is `G_N-sum_(n<=N)R_n`. The latter correction
converges on every cofinal schedule, proving the final equivalence in both directions.

## Frontier change and limits

The C9.11x proposal asked for Cauchy control uniformly over every sufficiently late
sharp cutoff. This theorem identifies what a cofinal construction needs: finite actual
cumulative energy already supplies a schedule on which the endpoint is paid. No
separate uniform terminal estimate is required for that existence statement.

This is not a claim that the actual prime source fails uniform sharp convergence, nor
that a finite energy estimate has been produced. It does not discard the endpoint,
replace signed coefficients by absolute values, replace the physical maximum kernel
by a residue-period kernel, or add a cancellation premise. The hard arithmetic target
is now the single displayed positive series. Gamma completion, Hardy compatibility,
strict sub-unit control and RH remain open.

## Lean and audit

Production: `formal/GaloisForLFunctions/RHTower/SoninPrimePolarCofinalGroundEnergy.lean`.
Final foreground leaf audit exits 0 with empty diagnostics:

`lake --old env lean GaloisForLFunctions/RHTower/SoninPrimePolarCofinalGroundEnergy.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPrimePolarCofinalGroundEnergy.olean`

All eleven public foundation queries use only `propext`, `Classical.choice`,
`Quot.sound`. Logs: `/tmp/tg-c911z-final.log`, `/tmp/tg-c911z-axioms.log`.
The leaf is wired into `RHTower.lean`; no umbrella build was run.

Main public theorems:

- `soninPrimePolarGridSource_norm_sq`
- `soninPrimePolarGrid_bounded_returns_iff_energy`
- `soninPrimePolarGrid_cofinal_limit_iff_energy`
- `soninPrimePolarGrid_energy_terminal_selection`
- `soninPrimePolarCellSource_eq_grid_sub_error`
- `soninPrimePolarCellSource_cofinal_limit_iff_energy`
Search evidence: `/tmp/tg-c911x-cofinal-energy-search.json` (partial snapshot;
background refresh incomplete). Returned candidates, source arguments and proposed
ingredient sets were inspected. Existing positive-prefix and cofinal-selection
results do not identify this literal native source or pay its terminal vector.

## Log

- 2026-10-02 — Exact orthogonal decomposition and cofinal terminal selection proved on paper; foreground Lean audit in progress. No numerical experiment or heartbeat increase.

- 2026-10-02 — Final production leaf and all eleven foundation audits pass; stage 3. Index exits 0; all eleven public API entries verified. Global lint exits 1 on twelve unrelated unwired leaves, with no finding in the new leaf.

Audit logs also include `/tmp/tg-c911z-index.log` and `/tmp/tg-c911z-lint.log`.
