# Operational observer-recurrence transfer

- **ID:** `operational-observer-recurrence-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM CANDIDATE / EXPECTATION-VALUE RECURRENCE / NOISE ROBUSTNESS
- **Source:** hostile attack on Hilbert--Schmidt observer metric
- **Statement:** Joint Hilbert--Schmidt recurrence of an observable family uniformly controls
  every state expectation, with an additive calibration-noise law.

## Frontier

- `[CORPUS]` `finiteQuantumObserverDistanceSq_eq_phaseEnergy` gives exact weighted
  Hilbert--Schmidt displacement.
- `[CORPUS]` `exists_finiteQuantumObserver_graphRank_distance_recurrence` gives a graph-rank
  deadline for that displacement.
- `[LITERATURE]` Hilbert--Schmidt Cauchy--Schwarz and
  `||sigma||_HS<=1` for density operators are standard. They are not novelty objects.
- `[LITERATURE]` expectation-value recurrence is an open direction identified in the closest
  2026 pure-state recurrence work, but generic observable almost-periodicity is classical.

## Exact theorem

Let `B_a(t)` be a finite family of complex `d x d` observables and let `lambda_a>0`. Put

```text
D(t)^2=sum_a lambda_a ||B_a(t)-B_a(0)||_HS^2.
```

### Theorem `[FORMALIZED] [REDISCOVERED]`

For every density matrix `sigma` and every observer `a`,

```text
|Tr(sigma(B_a(t)-B_a(0)))|
 <=D(t)/sqrt(lambda_a).                                   (1)
```

More generally, `(1)` holds for every matrix `sigma` with `||sigma||_HS<=1`.

Suppose calibrated matrices `Btilde_a(t)` satisfy

```text
||Btilde_a(t)-B_a(t)||_HS<=nu_a(t),
||Btilde_a(0)-B_a(0)||_HS<=nu_a(0).
```

Then

```text
|Tr(sigma(Btilde_a(t)-Btilde_a(0)))|
 <=D(t)/sqrt(lambda_a)+nu_a(t)+nu_a(0).                   (2)
```

Combining `(1)` with the corpus graph deadline yields a finite clock at which every input state
and every selected observable expectation returns within the displayed error. The prediction is
uniform over states and degrades additively under calibrated Hilbert--Schmidt error.

## Paper proof

Hilbert--Schmidt Cauchy--Schwarz gives

```text
|Tr(sigma Delta B_a)|<=||sigma||_HS ||Delta B_a||_HS.
```

For a density matrix with eigenvalues `p_i>=0` and `sum p_i=1`,

```text
||sigma||_HS^2=sum_i p_i^2<=sum_i p_i=1.
```

The nonnegative `a`-summand in `D(t)^2` gives

```text
lambda_a||Delta B_a||_HS^2<=D(t)^2.
```

Taking square roots proves `(1)`. Apply the triangle inequality to

```text
Btilde_a(t)-Btilde_a(0)
=(B_a(t)-B_a(0))
 +(Btilde_a(t)-B_a(t))
 -(Btilde_a(0)-B_a(0))
```

and repeat Cauchy--Schwarz to obtain `(2)`.

## Hostile attack

1. **“Hilbert--Schmidt distance is contractive.”** False and not claimed.
2. **“This controls trace distance of states without dimension loss.”** False. The theorem is a
   uniform operational statement for observable expectations. State distinguishability requires
   the usual finite-dimensional Schatten conversion.
3. **“The noise model is a complete open-system theorem.”** False. Equation `(2)` is a
   calibration-stability law, not a dynamical decoherence model.
4. **“Expectation Cauchy--Schwarz is itself novel.”** `REDISCOVERED`. Candidate significance
   comes only from composing it with the exact observer-union graph recurrence law.

Verdict: transfer mechanism `REDISCOVERED`; joined graph-observer result
`SURVIVES PRELIMINARY ATTACK`. Exact theorem is formalized in
`FiniteQuantumObserverOperationalRecurrence.lean`, with load-bearing declarations
`finiteQuantumObserver_operational_sq_le`,
`finiteQuantumObserver_operational_norm_le`, and
`finiteQuantumObserver_operational_noise_le`.

## Gates

- [x] 0 → 1: exact statement and complete paper proof
- [x] 1 → 2: normalized matrix pairing; complete dependency-closed proof
- [x] 2 → 3: unconditional Lean theorem and targeted foreground check
- [x] 3 → 4: replaced aspirational protocol by explicit expectation/noise prediction
- [ ] Final: axiom audit and capstone module build
