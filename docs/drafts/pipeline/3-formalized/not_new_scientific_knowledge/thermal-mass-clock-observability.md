# Thermal mass-clock observability and the finite-action HT boundary

- **ID:** `thermal-mass-clock-observability`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`, black-hole/cosmological mass-probe value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ThermalMassClockObservability`
- **Statement:** Positive large-mass observables recover the infimal Euclidean proper-action label
  from normalized logarithmic values, complex single-action signals recover the exponentiated
  action from successive mass ratios, and no hypertranscendental mass response can be an exact
  finite sum of such actions.

## Positive mass-clock readout

Let `P` label geometric saddles or detector channels.  For positive summable weights `b_p` and real
proper-action labels `tau_p`, define the exterior mass-probe observable

```text
Z_m = sum_p b_p exp(-m tau_p).                              (1)
```

Assume `tau` is the infimum visible to the positive weights:

```text
tau <= tau_p for every p,
for every b > tau there is p with tau_p < b.                (2)
```

Lean proves the value relation

```text
-log Z_m / m -> tau.                                       (3)
```

It also proves that `(3)` is unchanged after multiplying `Z_m` by any positive prefactor `q_m`
whose logarithmic rate vanishes:

```text
log q_m / m -> 0.                                          (4)
```

Thus polynomial and other subexponential WKB/detector factors do not alter the geometric clock
value.  The proof reuses the existing source-marked Gibbs support-radius theorem; it does not
duplicate the asymptotic argument.

## Complex phase-clock readout

For one complex action `A` and a nonzero slowly varying prefactor, define

```text
C_m = q_m exp(-m A).                                       (5)
```

Lean proves the exact ratio law

```text
C_(m+1)/C_m = (q_(m+1)/q_m) exp(-A),                       (6)
```

and hence

```text
q_(m+1)/q_m -> 1  implies  C_(m+1)/C_m -> exp(-A).         (7)
```

The real part of `A` is the exponential damping/length label.  Its imaginary part is the
oscillatory clock value, observable modulo the period of the complex exponential.  The observation
coordinate in `(3)` and `(7)` is probe mass, not physical time evolution.

## Hypertranscendental boundary

For finitely many exact actions `A_i`, the complex-mass response

```text
F(z) = sum_(i in S) c_i exp(-A_i z)                         (8)
```

is differentially algebraic.  Lean applies the existing finite exponential-spectrum theorem and
deduces

```text
Hypertranscendental f  implies  f != F                      (9)
```

for every finite action palette `(8)`.  This is the no-go.  The significant positive alternative
is explicit: an HT mass response must contain an infinite action spectrum or an HT/non-DA
prefactor, while its leading action may still be observable through `(7)`.

## Physics provenance and limits

- M. Grinberg and J. Maldacena, *Proper time to the black hole singularity from thermal one-point
  functions*, arXiv:2011.01004.  Their large-mass form is schematically a power of the mass times
  `exp(-m l_hor - i m tau_s)`, so the exterior one-point function reports a horizon length and an
  interior proper-time phase.
- X. Chen, M. H. Namjoo, and Y. Wang, *Quantum Primordial Standard Clocks*, arXiv:1509.03930.  Massive
  fields encode the primordial scale factor through oscillatory non-Gaussianity shapes.

Equations `(3)--(7)` formalize the abstract value-extraction mechanism.  They do not derive a black
hole one-point function, a cosmological correlator, or the WKB saddle expansion from a field theory.
For a nonlinear cosmological clock phase, `(7)` applies only after the relevant asymptotic local
action or ratio has been established.

## Lean surface

- `thermalMassClockValue`
- `thermalMassClockValue_eq_sourceMarkedGibbsPartition`
- `tendsto_thermalMassClockValue_neg_log_div_mass`
- `tendsto_thermalMassClockValue_subexponential_prefactor`
- `complexMassClockSignal`
- `complexMassClockSignal_succ_div`
- `tendsto_complexMassClockSignal_succ_div`
- `finiteMassClockSignal`
- `differentiallyAlgebraic_finiteMassClockSignal`
- `hypertranscendental_ne_finiteMassClockSignal`
- `RHTower.xi_ne_finiteMassClockSignal`

The RHTower specialization uses unconditional completed-Xi hypertranscendence to rule out every
exact finite complex action palette for `xi` itself.  It contains no RH premise and does not claim
that Xi is physically a mass-probe observable; it records the exact consequence should such a
finite-action representation be proposed.

## RH impact

The theorem rules out an exact finite geodesic/saddle palette for any hypertranscendental
prime--Gamma mass-parameter realization.  It also provides a robust source reporter: if a positive
prime--archimedean representation can be parameterized by a mass/cold variable, its extremal action
is recoverable without knowing the detector weights or subexponential prefactor.

It does not produce the missing positive prime residual or prove a moment representation for
`normalizedPrimeArchMoment`.  A limiting action or phase is one scalar asymptotic value; RH needs the
all-order positive moment cone.  The result is therefore a valid model boundary and observability
tool, not a replacement for the source-positivity gate.

## Anti-theatre verdict

Laplace-principle/free-energy asymptotics, exponential ratio extraction, and differential
algebraicity of finite exponential sums are known mathematics.  The corpus gain is the exact,
reusable Lean interface joining black-hole/cosmological mass clocks to general HTGeometry.  No
scientific novelty is claimed.

## Verification

- [x] exact module target built and cached in one foreground process
- [x] direct touched-file Lean check passed
- [x] no numerical computation used
- [x] selected capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`
- [x] module imported by the HTGeometry umbrella
- [x] no full or self-concurrent Lean build used
