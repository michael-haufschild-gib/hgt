# Physical energy completion of arbitrary divisor traces

- **ID:** divisor-trace-energy-completion
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Contribution:** 15/100, counted once.
- **Statement:** The physical closure of arbitrary divisor-family integer-hat
  extensions is exactly unit-cell synthesis of square-summable currents with
  zero sum on every finite active-edge component. Cumulative traces recover
  old ℓ² data exactly when square-summable. Explicit full-family ramps converge
  to a completed state outside the old range with squared error1/(n+1).

## Exact result

For A(k) iff some e∈insert d D has e+2 dividing k+1, define p_n(w)=Σ_(j<n)w_j
and C_A={w∈ℓ²:p_(k+1)(w)=0 whenever ¬A(k)}. This closed Hilbert domain has an
isometric physical extension S, exact integer/logarithmic cumulative traces,
and energy Σw_k². Proved closure(range E_A)=S(C_A) in full physical L².
Cellular membership is explicit. Finite-component conservation is equivalent
to the defining prefix constraints. The orthogonal complement in cell data
consists exactly of currents constant along active edges, with zero constants
on infinite tails.

Old-data recovery holds iff the cumulative trace is ℓ². Every completed datum
is recoverable iff active runs are uniformly bounded. Unbounded runs give an
actual completed datum outside the old range; no quantitative general-family
coordinate formula is claimed for that existence result.

For D=ℕ, C_A={w:w_0=0}. The actual state S(δ_1)=unitCell1 has energy1 and a
nonzero constant trace tail, hence no old ℓ² preimage. For N=n+1, actual finite
old data v_N(1+j)=1−j/N,0≤j<N, satisfy

    G(v_N)=δ_1−(1/N)Σ_(j<N)δ_(j+2),
    ‖E(v_N)−unitCell1‖²=1/N →0.

The returning unit current spreads over N cells at energy cost1/N. Finite-
component conservation persists in completion; infinite-component total-current
conservation can disappear. Projection onto C_A also constructs admitted data
from arbitrary ambient ℓ² currents with exact Pythagorean error and contraction.
These are actual producers with unconditional bounds, satisfying Trap10 within
the continuum coprime-shear topic. No RH or unweighted logarithmic H1/full
SourceGraph/affine-unitary identification is claimed.

## Proof and verification

Dependency-closed paper proof preceded Lean:
`docs/reports/BiScaleUncertainty/DivisorTraceEnergyCompletion.md`.
The proof uses bounded prefix functionals, finite-component conservation,
constant-tail ℓ² decay, Hilbert orthogonal decomposition, and closed isometric
synthesis. Classical parent tools are not claimed externally novel.

Five leaves,699 lines,73 public declarations: CellPrefixHilbert107/17,
DivisorCellConstraints195/16, DivisorGradientClosure110/8,
DivisorEnergyCompletion152/19, FullDivisorEnergyEscape135/13.
Totals:59 theorems,12 definitions, one abbreviation and one instance.

- [x] All five serial direct `lake --old env lean -o <normal-output> <leaf>`
  checks exit0 with empty logs and current outputs.
- [x] Exact all73-declaration axiom audit: only propext,Classical.choice,Quot.sound.
- [x] Thirteen principal signatures inspected;52 mathlib API probes checked.
- [x] Five unique umbrella imports and72 exact catalog entries; instance audited separately.
- [x] Scoped whitespace and read-only README boundary verified.
- [x] Facts ledger, overarching card and memory updated; next candidate retained.
- [ ] Global lint: exits1 solely for six unrelated unreachable modules listed below.

Unrelated lint modules: AntitoneDyadicStencil, BandLimitedLaplaceEnergy,
ClampedExponentialRamp, FiniteFilterSchurResidual, NyquistResidualMass,
SignedPrimePolarContinuousFactorialLift. No own, proof-debt or generated-index
error. Existing large-file warnings remain. No full/umbrella build, numerical
experiment, heartbeat increase or added axiom.

Evidence: /tmp/trace_completion_axioms.lean, /tmp/trace-completion-axioms.log,
/tmp/trace-completion-audit-names.json, /tmp/trace-completion-api-entries.txt,
/tmp/trace-completion-index-final.log, /tmp/trace-completion-lint-final.log.
All owned jobs terminal at certification. Overall100-contribution goal active.

## Corpus coverage and next question

All20 candidate statements and20 source-argument statements inspected for the
completion query. partial=true; text/source retrieval interrupted; generation
1446063 pending; refresh incomplete/background_indexer_running; compiler
metadata source-only. Existing interpolation and closed-range results supply
building blocks; no matching completion classifier returned. This is not an
absence or external novelty proof. MIT18.102 and mathlib projection sources
were checked; paper gives links.

Next unproved/uncounted candidate:
`../0-backlog/divisor-component-averaging-projection.md`. Construct explicit
cell averaging followed by finite-component mean subtraction for arbitrary
physical L² input, with exact noncellular/component-mean error decomposition.
