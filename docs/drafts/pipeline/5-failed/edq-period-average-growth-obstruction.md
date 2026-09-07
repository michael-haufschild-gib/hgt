# EDQ uniform period averaging: growth obstruction and positive projection

Stage: 5-failed shortcut; dependency-closed paper proof and exact positive survivor formalized in Lean.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Retired claim

The complete uniform period variance or uncentered mean energy has cofinal
polynomial-log upper returns capable of supplying the EDQ source ceiling.
Lean disproves both statements: the uniform period variance itself grows faster
than every fixed logarithmic power. Only this ceiling/comparability shortcut is
retired; the weighted EDQ architecture remains live.

## Positive survivor and paper proof

Let V_N be the exact centered period covariance from
EulerDeletionMobiusPeriodCovariance, and U_N the primes p with N/2<p<=N.
Such a prime is coprime to every other positive modulus m<=N: a distinct positive
multiple of p would exceed N. The complete covariance formula therefore makes
each of these channels orthogonal to every other channel. Removing them leaves
the covariance of the remaining actual coefficient vector, which is nonnegative.
The exact decomposition is

    V_N = sum_(p in U_N) (1-1/p^2)/12 + covariance(remaining coefficients).

Since p>=2, each retained diagonal is at least 1/16. Thus V_N>=card(U_N)/16,
at every cutoff, without an asymptotic or zero hypothesis.

The corpus's every-window theta lower bound at exponent 3/4, applied to
y=N/2 and L=N/2, gives theta(N)-theta(N/2)>=N/32768 eventually.
Its prime-shell counting comparison then gives card(U_N)>=N/(32768*log N).
Consequently V_N>=N/(524288*log N) eventually. This exceeds every fixed
logarithmic power and forbids even cofinal polynomial-log upper returns.

The already proved actual weighted carrier energy is o(N/(log N)^q) for every
fixed q. Combining q=1 with this variance lower bound gives

    norm(rawVec_N)^2 / V_N -> 0.

This is a quantitative failure of uniform period averaging as an asymptotically
comparable replacement for the actual carrier energy. The exact signed prime
projection and its nonnegative remainder survive; all progression weights in
the actual carrier remain necessary.

## Scientific-method and closure audit

This statement is a [BRIDGE] forced by a visible source calculation, not a new
primary conjecture. No numerical experiment is warranted: the paper proof
predicts the outcome. The exact projection, growth obstruction, and both ratios have
been formalized and audited before retiring the shortcut. No RH proof, off-line zero, or weighted energy ceiling is
claimed. The original RH objective and its remaining weighted comparison are
unchanged.

## Exact new insight and survivor status

Uniform cycle completion preserves an orthogonal reservoir of isolated prime
variance that the actual chronology-weighted energy suppresses asymptotically.
The common coefficients do not make these two energies comparable. The positive
survivor is the exact signed projection with its nonnegative remaining covariance,
the explicit prime-count lower bound, and the vanishing weighted/unweighted ratios.
Paper proof: complete. Lean proof: complete. Neither the proof nor the obstruction
assumes an off-line zero or claims an RH conclusion.

`EulerDeletionPeriodAveragingObstruction.lean`, namespace
`RHTower.DeletionPeriodGrowth`, contains four definitions and eleven public
proofs. `variance_eq_upperPrime_diagonal_add_remaining` is the exact projection;
`upperPrime_card_le_variance` gives the all-cutoff budget;
`variance_eventually_lower` gives N/(524288*log N);
`variance_div_log_pow_tendsto` and both `not_cofinally_log_bounded_*` theorems
close the obstruction. `periodAverage_eq` identifies the literal factorial-period
average. Both `modular_norm_sq_div_*_tendsto_zero` theorems close the quantitative
positive comparison, using the full actual carrier norm.

Validation: complete scratch check with no diagnostics; final targeted leaf build
compiled only this new module. All fifteen new public declarations were audited
once and use only `propext`, `Classical.choice`, and `Quot.sound`. The covariance
foundation's nineteen declarations were separately audited once. Both modules
are wired into `RHTower.lean`; no umbrella build or numerical experiment was run.
The search index was refreshed. Scoped source, umbrella, documentation-link,
whitespace, and new-declaration audit-coverage checks passed. Repository lint found
only the unrelated concurrent unwired module `FiniteDirichletCriticalNonannihilation`;
the global gate is not claimed to pass. All owned Lean processes exited, and the
temporary proof/API/audit source files were removed. No numerical experiment was run.
