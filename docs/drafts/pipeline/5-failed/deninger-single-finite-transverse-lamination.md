# Single finite-transverse lamination

- **ID:** `deninger-single-finite-transverse-lamination`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Statement:** no single compact Leichtnam lamination with finite
  transverse harmonic sector can realize completed zeta.

## Literature boundary

Leichtnam constructs compact laminated suspensions with two-real-dimensional
leaves and \(p\)-adic transversal.  Under his assumptions, including
transverse local constancy of leafwise harmonic forms, Theorem 3 makes the
real harmonic one-form space finite-dimensional.  Theorem 2 then proves:

- test-function-smoothed flow operators are trace class;
- the degree-one generator has finitely many spectral values, all of real
  part \(1/2\);
- the alternating trace is a closed-orbit Lefschetz distribution.

Primary source:
[Leichtnam, *Scaling group flow and Lefschetz trace formula for laminated
spaces with \(p\)-adic transversal*](https://arxiv.org/abs/math/0603576),
Theorems 2 and 3.

## No-go

`[PROVED] [DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO]`

Completed Riemann zeta has infinitely many distinct nontrivial zeros.
A finite-dimensional endomorphism has only finitely many eigenvalues.
Therefore no single model satisfying Leichtnam's finite-harmonic
hypotheses can have middle spectrum equal to the nontrivial zeta divisor.

The stronger resolvent form is already formalized unconditionally in
`RHTower/FiniteSpectralTraceNoGo.lean`: no finite atomic spectral trace,
with arbitrary complex weights, equals \(\xi'/\xi\).

## Positive survivor

`[SURVIVOR] [DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER]`

The arithmetic object must be an infinite pro/nuclear
Kähler--Riemann tower.  Finite stages may satisfy Leichtnam's theorem,
but their harmonic dimensions and spectral supports must be unbounded.
At the limit:

1. reduced \(H^1\) is infinite-dimensional;
2. \(e^{-t/2}\phi^{t*}\) remains unitary by
   `DAC_KAHLER_RIEMANN_FLOW_PURITY`;
3. \(\int\varphi(t)\phi^{t*}\,dt\) is trace class for test functions even
   though individual flow operators need not be;
4. finite-stage orbit traces converge in the distribution topology;
5. no topology, completion, or stage selection uses Xi zeros.

This survivor is the analytic form required by
`DAC_ARITHMETIC_LEFSCHETZ_TRACE_COMPARISON`.

**Verdict:** `SINGLE FINITE-HARMONIC MODEL RETIRED; PRO-NUCLEAR TRACE
TOWER SURVIVES`.

## Log

- 2026-07-26 — Extracted after checking the exact finiteness hypothesis
  and conclusions of Leichtnam Theorems 2 and 3.
