# The actual Möbius long-modulus remainder is a quadrature error

- **ID:** pm-long-modulus-quadrature
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Source:** `../../1-in-progress/pm-signed-damping-covariance.md`
- **Statement:** The long-modulus sawtooth and full harmonic tail equal one integrable quadrature error; the complementary square-root head has bounded pronic energy.

## Scope

Formalize the completed paper proofs requested by the user. These results
retain the cancellation needed by PM but do not bound the complete remainder
and do not prove RH. No additional admission premise is introduced.

## Paper proof

Fix ε>0. Put b(d)=μ(d)d^(-ε),
B_D(x)=sum_(D<d<=floor(x)) b(d), and
F_(n,D)(u)=B_D(n/u) for u>0, zero otherwise.

For every d>D, d>=1, its contribution to F is b(d) times the indicator of
(0,n/d]. The sum of the integrals of absolute values is
n sum_(d>D) |b(d)|/d <= n sum_(d>=1) d^(-1-ε), which is finite.
Termwise integration therefore proves that F is integrable and

    integral F = n sum_(d>D) b(d)/d.

For positive integers j, the condition d<=floor(n/j) is equivalent to dj<=n.
Interchanging the finite sums gives

    sum_(j>=1) F(j) = sum_(D<d<=n) b(d) floor(n/d).

Subtracting proves the quadrature identity for the joint long and tail
remainder. Splitting the exact centered divisor prefix at D retains the
short sawtooth and this remainder, with the entire mean tail included.

For 0<ε<1 and D=floor(sqrt n), the short sawtooth is bounded in absolute
value by sum_(d<=D) d^(-ε), hence by
(1+1/(1-ε)) n^((1-ε)/2). Squaring and dividing by n(n+1), the sum through any
horizon is at most (1+1/(1-ε))²(1+1/ε), using the existing power-sum bound.
All domain assumptions concern only positive damping and natural cutoffs.

## Gates

- [x] Dependency-closed paper proofs.
- [x] Exact identities and short-modulus bound formalized.
- [x] Foreground leaf audit with `lake --old env lean`.
- [x] Transitive axiom audit.
- [x] Umbrella import added without compiling the umbrella.

No external novelty claim or check. The short-modulus estimate uses the
existing corpus mechanism; the quadrature identity is not counted as a
solution of the outstanding signed covariance inequality.

## Historical significance gate

The subsequent user instruction requires a theorem or discharged premise
that significantly advances a hard PM obstacle. This exact rewrite alone
does not meet that gate. Its paper proof is retained, but its standalone
formalization is deferred; no admission theorem or new cancellation estimate
is claimed. The preliminary Lean API probe was terminated before producing
diagnostics, and no Lean module or umbrella import was added.

## Current formalization

The current request supersedes that deferral. All 20 public declarations passed
the combined source and transitive axiom audit, with only `propext`,
`Classical.choice` and `Quot.sound`, and no diagnostics. Four canonical leaves
now reside in `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/`.
All four final direct source checks and the three required dependency-olean
builds passed with no diagnostics. Existing oleans were not rebuilt. Unique
umbrella imports and indexed names are verified; global lint has no diagnostic
for these leaves (20 unrelated structural errors and 417 size warnings).

| Exact claim | Leaf and public declaration |
|---|---|
| Actual Möbius floor-cutoff function, pointwise indicator series, integrability and full signed harmonic-tail integral | `LongModulusIntegrableProducer.lean`: `pmLongModulusFunction_eq_tsum`, `integrable_pmLongModulusFunction`, `integral_pmLongModulusFunction` |
| Exact integer sampling and literal sum-minus-integral quadrature | `LongModulusQuadratureSampling.lean`: `pmLongModulusFunction_natCast`, `tsum_pmLongModulusFunction_natCast_succ`, `pmLongModulusQuadrature_eq` |
| Every-cutoff centered-prefix decomposition and retained signed tail | `LongModulusExactDecomposition.lean`: `pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature`, `pmLongModulusQuadrature_eq_longSawtooth_sub_full_tail`, `pmLongModulusQuadrature_eq_longSawtooth_sub_tail_max` |
| Exact square-root head bound, including `n=0`, and the stated pronic-energy constant | `LongModulusShortEnergy.lean`: `abs_pmShortModulusSawtooth_sqrt_le`, `sum_pmShortModulusSawtooth_sqrt_pronic_le` |

All names use namespace `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`.
For `D≤n`, quadrature is the long sawtooth minus the full tail past `n`.
For arbitrary cutoffs it retains the tail past `max n D`; no endpoint is omitted.
The weights are the actual `μ(d)d^(-ε)`. Existing hyperbola interchange,
countable-series integrability and pronic comparison supply the reused mechanisms.
No bound on the full remainder or new cancellation theorem is claimed.

Evidence: `/tmp/leftovers_pm_complete_audit.lean`,
`/tmp/leftovers-pm-public-names.json`, `/tmp/leftovers-pm-complete-audit-r2.log`.
The first failed audit is not a certificate. Progress is recorded in
[the formalization tracker](../../1-in-progress/leftovers-unconditional-formalization.md).

## Final source certificate

Every leaf was checked directly from `formal/` using `lake --old env lean -j 1`
without writing an olean. Only the first three leaves needed new oleans for
downstream imports. No umbrella was compiled. The 20-declaration axiom audit
contains only standard Lean axioms; no premise replaces a missing analytic input.

| Leaf | SHA-256 | Final direct-check log |
|---|---|---|
| `LongModulusIntegrableProducer` | `362193d428b878cc4c5ae1ab1d04a1e122461d9762a16b483c73f08748b1f1f8` | `/tmp/leftovers-pm-integrable-final.log` |
| `LongModulusQuadratureSampling` | `dd2f9abe6a6b07615bcd653b73d4f6999ff30e09d3f70eff26a182363520640d` | `/tmp/leftovers-pm-sampling-final.log` |
| `LongModulusExactDecomposition` | `ddfa3dd0aa31cf7ac53cfcfa901d3f7f5ef918bf861bc56fd4afe5814ed34b8d` | `/tmp/leftovers-pm-decomposition-final.log` |
| `LongModulusShortEnergy` | `90c3ceeb202d6834f4b4fdc097d5355044ad87745939ec84050d92e716802e84` | `/tmp/leftovers-pm-short-energy-final.log` |

This completes the stated quadrature and short-head card. The signed long-remainder
estimate remains outside its conclusion. The larger programme is paused after
completion of the already-started Lean modules.
