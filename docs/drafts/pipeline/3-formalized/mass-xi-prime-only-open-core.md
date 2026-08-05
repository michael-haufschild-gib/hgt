# Mass--Xi prime-only open core

- **ID:** `mass-xi-prime-only-open-core`
- **Stage:** 3-formalized
- **Type:** EXACT REDUCTION / RH EQUIVALENCE
- **Date:** 2026-08-04
- **Parent:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`

## Exact statement

Fix `a>1/2` and `1/2<c<a`.  Let

```text
P_(a,c)(tau) = integral_R xiMassBottomPrimeIntegrand(a,c,tau,x) dx.
```

Then, for every `sigma>0`, boundedness of `P_(a,c)(sigma+i u)` for all real `u` is equivalent to
boundedness of the mass-shifted Xi trace on that line.  Consequently

```text
RiemannHypothesis
  <-> P_(a,c)(sigma+i u) is uniformly bounded in u
```

for **every fixed** `sigma>0`.  Moreover `P_(a,c)(tau)` is independent of legal depth `c`, and all
legal triples `(a,c,sigma)` define equivalent boundedness propositions.

More generally, for every `lambda>=0`, fixed-line prime growth

```text
|P_(a,c)(sigma+i u)| <= C exp(lambda |u|)
```

is equivalent to the pointwise bound

```text
|Im ((xiMassFamily a).pt q)| <= lambda
```

for every Xi divisor point `q`.  A displacement above `lambda` therefore defeats every proposed
source envelope of that exponent.  The zero-exponent contrapositive is an exact cofinal alternative:
failure of RH is equivalent to the prime integral being unbounded above on every legal fixed line.

## Proof

The exact source split is

```text
integral source = -i P_(a,c) + i A_(a,c),
```

while the contour identity gives

```text
integral source = pi i * xiMassTraceC.
```

`XiMassArchimedeanUniformBound.lean` supplies a constant `B_(a,sigma)` bounding `A_(a,c)` for every
`u`.  Triangle inequalities therefore transfer any line bound from `P_(a,c)` to the trace and back,
with explicit constants.  The existing faithful mass-trace criterion then identifies existence of
one such line bound with RH.

## Scientific content

This removes every auxiliary analytic ambiguity from §9.3.  Uniform Gamma control is not another
RH-strength conjecture, and source-to-trace continuation is not missing.  Remaining theorem is
exactly cofinal von-Mangoldt cancellation.  Any proposed proof that does not act on this prime
integral must first provide a theorem transferring its invariant to this one.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/XiMassPrimeOpenCore.lean`.

Graded module:
`formal/GaloisForLFunctions/RHTower/XiMassPrimeGradedOpenCore.lean`.

Key declarations:

- `integral_xiMassBottomSourceIntegrand_eq_prime_add_arch`;
- `integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace`;
- `xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound`;
- `xiMassBottomPrimeIntegral_depth_independent`;
- `riemannHypothesis_iff_xiMassBottomPrimeLineBound`;
- `xiMassBottomPrimeLineBound_universal`;
- `xiMassBottomPrimeLineGrowth_iff_xiMassTraceFixedLineGrowth`;
- `xiMassBottomPrimeLineGrowth_iff_mass_displacement_le`;
- `exists_xiMassBottomPrimeIntegral_norm_gt_exp_of_mass_displacement`;
- `not_riemannHypothesis_iff_xiMassBottomPrimeIntegral_norm_unbounded`.

All proofs are unconditional.  No `sorry`, `admit`, new axiom, opaque declaration, unsafe code, or
computation is used.

Final verification:

- all route modules pass direct `lake env lean <file>` checks without warnings;
- `lake build GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore` succeeds;
- `#print axioms` on source identity, archimedean shift/bound, fixed-line equivalence, universality,
  graded type, quantitative lower obstruction, and cofinal-unboundedness capstones reports only
  `propext`, `Classical.choice`, and `Quot.sound`;
- repository-wide `scripts/formal_tools.py lint` reaches no proof-debt error but remains red on the
  pre-existing unrelated umbrella issue
  `GaloisForLFunctions.RHTower.MobiusMertensFiniteSectionEnergy` being unreachable from
  `GaloisForLFunctions.RHTower`.

## Open core

Prove `XiMassBottomPrimeLineBound a c sigma` for any one legal triple without assuming any equivalent
spectral bound.  Depth changes, mass changes, and moving to another positive line cannot weaken the
problem: Lean proves all resulting propositions equivalent.  This is RH-equivalent and remains open.

`PNTPlus.MediumPNT` supplies only an error envelope of size
`x exp(-c (log x)^(1/10))`.  Under critical square-root weighting and fixed-mass light-cone decay,
its absolute envelope remains `exp(u/2-c u^(1/10)-O(sqrt u))`; it cannot prove the required bound
without additional signed/oscillatory arithmetic information.
