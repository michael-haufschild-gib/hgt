# Positive-ray joint Bohr cofinal current

- **ID:** T2-JOINT-B2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · route T2
- **Statement:** At positive Borel height `y = 1/10`, the terminal-plus-edge finite Route-T2 currents are Cauchy in Bohr mean square. Equivalently, their exact Abel increments have square-summable source coefficients.

## RH proof chain under attack

`finite terminal + edge current`
`=> cancellation-preserving positive-ray cofinal current`
`=> coefficient-faithful scalar/analytic landing`
`=> strict subhalf terminal-width zero`
`=> RH`.

This card targets the second arrow without assuming separate terminal disappearance, raw absolute
convergence, or finite-current landing. If proved, T2's cofinal-control burden is discharged in the
canonical Hilbert/Bohr topology; only point-evaluation/analytic landing remains. If point evaluation
is unbounded on this completion, the same theorem kills the Hilbert realization while preserving
the exact positive source current as the mandatory survivor.

## Internal frontier

- `[CORPUS]` `xiHeatCassiniWoldResidualBorelFiniteAbel` and
  `xiHeatCassiniWoldResidualBorelFiniteRenormalization` give exact finite terminal-plus-edge Abel
  transport.
- `[CORPUS]` `xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub` identifies each Abel
  coefficient with one Wold atom minus one prime-log cell.
- `[CORPUS]` `eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase` gives every late
  prime gap exponent `71/100`.
- `[CORPUS]` `summable_primeLogGap_mul_exp_neg_height` supplies the exact logarithmic-cell
  telescope at every positive decay exponent.
- `[CORPUS]` `tendsto_cesaro_normSq_expSum` gives finite Bohr Parseval for distinct frequencies.
- `[LOCAL-RESEARCH]` Existing T2 modules prove negative-ray continuation, finite positive-ray Abel
  landing, and exact terminal-width classification, but no positive-height joint Bohr completion.

## External frontier and hostile audit

- `[LITERATURE]` Guth--Maynard, *Annals of Mathematics* 203 (2026), prove short-interval primes at
  exponent `17/30 + o(1)`, stronger than the corpus exponent but not formalized in this project.
- `[LITERATURE]` Besicovitch--Bohr theory identifies square-summable distinct-frequency
  coefficients with a `B²` almost-periodic completion and Parseval energy.
- No checked source through August 2026 states the exact Wold-residual terminal-plus-edge theorem or
  its Route-T2 positive Borel current.

Hostile verdict: `SURVIVES PRELIMINARY ATTACK`. Abstract Hoheisel-to-`ell²` conversion is classical,
but the exact cancellation-preserving T2 current and its positive-height source coefficient law are
not present in the corpus or located literature. The claim does not imply scalar landing: point
evaluation is not continuous on generic `B²`. That is the next wall, not a hidden premise here.

## Conjecture/fail/pivot loop

- `[T2-ABS-POS]` raw positive-ray absolute convergence: `[FALSIFIED]` by the corpus upper-ray
  Tonelli no-go.
- `[T2-TERMINAL-SEPARATE]` first prove terminal disappearance: rejected as circular; the corpus
  terminal classification makes the strict-subhalf version RH-equivalent.
- `[T2-JOINT-B2]` keep terminal and edges coupled, then complete in Bohr mean square: `[PAPER-PROVED]`.
  The previous failures do not apply because neither atomwise absolute values nor the terminal
  channel are separated before the finite Abel identity.

## Paper proof [PROVED HERE]

Write `p_n` for the ordered primes, `h_n = log p_n`, `g_n = p_(n+1)-p_n`,
`delta_n = h_(n+1)-h_n`, and `R_n` for the centered Wold residual. Put

`b_n = (R_(n+1)-R_n) exp(h_(n+1)/10)`.

The residual recurrence gives `R_(n+1)-R_n = w_n-delta_n`, where `w_n` is the positive depth-one
Wold coefficient at `p_(n+1)`. Hence

`|b_n|² <= 2 (w_n² + delta_n²) exp(h_(n+1)/5)`.

For all late `n`, Hoheisel gives `g_n <= p_n^(71/100)`. Bertrand gives
`p_(n+1) <= 2p_n`, while

`delta_n <= g_n/p_n <= 2 delta_n`.

Using one copy of the gap bound and one copy of the logarithmic-cell comparison,

`delta_n² p_(n+1)^(1/5)
 <= 2^(6/5) delta_n p_n^(-9/100)`.

The right side is summable by the corpus exponential-potential telescope. The finite prefix is
harmless.

Also `w_n <= log(p_(n+1))/p_(n+1)`. Therefore

`w_n² p_(n+1)^(1/5) <= log(p_(n+1))² / p_(n+1)^(9/5)`,

whose prime sum converges by the corpus prime-log-power Dirichlet theorem. Thus
`sum |b_n|² < infinity`.

Finite Abel transport rewrites the full terminal-plus-edge cutoff as one fixed initial atom plus

`sum_(n<N) b_n exp(-i h_(n+1) x)`.

The frequencies `h_(n+1)` are strictly increasing. Finite Bohr Parseval therefore says that the
mean-square energy of every tail `[L,M)` is exactly `sum_(L<=n<M) |b_n|²`. Summability makes these
tail energies uniformly tend to zero. Hence the coupled finite currents are Cauchy in Bohr mean
square at the strictly positive height `1/10`.

No terminal limit, raw positive-ray Tonelli interchange, or scalar point evaluation is used.

## Open core after this theorem

`[OPEN CORE]` Determine whether the source-selected Bohr completion admits a coefficient-faithful
analytic evaluation/Hardy landing. Generic `B²` point evaluation is discontinuous, so any survivor
must use extra arithmetic structure rather than Hilbert completion alone.

## Gates

- [x] 0 → 1: exact claim, corpus/literature audit, hostile verdict, RH chain
- [x] paper proof dependency-closed after final corpus/literature hostile recheck
- [x] 1 → 2: exact theorem statement and proof audit complete
- [ ] 2 → 3: Lean module, targeted build, axiom audit, umbrella wiring

## Log

- 2026-08-29 — conjectured from T2 finite Abel transport plus formal Hoheisel exponent; raw absolute and separately terminal routes rejected before proof work.
