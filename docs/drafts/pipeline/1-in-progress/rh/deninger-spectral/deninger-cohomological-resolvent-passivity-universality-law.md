# Deninger cohomological resolvent passivity universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `deningerResolventLefschetzTrace`, identifying the multiplicity-exact Deninger divisor
  resolvent trace with the continued prime–archimedean source trace at every admissible point;
- `continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis`, identifying passivity of that
  arithmetic source on the centered upper half-strip with RH;
- `deningerDivisorRelativeResolventTrace_eq_logDeriv`, identifying the same cohomological trace
  with the logarithmic derivative of the centered characteristic determinant off its divisor.

The corpus proves these statements separately but contains no theorem transferring the exact RH
passivity criterion to the Deninger cohomological resolvent.

## Universal law

Let

`L_D(z) = Tr((Theta-1/2)^(-1) - (Theta-1/2-z)^(-1))`

be the multiplicity-exact centered Deninger divisor resolvent trace. Define Deninger upper
passivity by

`Im L_D(z) <= 0`

for every `z` with `0 < Im z < 1/2` and
`zeta(1/2 + i z) != 0`. Then

`Deninger upper passivity`

is equivalent to

`continued prime–Gamma upper passivity`

and both are equivalent to RH.

Thus the arithmetic anti-Herglotz gate is not merely analogous to cohomological resolvent
positivity: on its full regular domain it is exactly the same law.

## Dependency-closed paper proof

1. For `0 < Im z < 1/2`, the Xi coordinate `s = 1/2 + i z` has `0 < Re s < 1/2`; hence
   `s != 1`.
2. Together with the assumed `zeta(s) != 0`, this makes `z` `XiExplicitAdmissible`.
3. `deningerResolventLefschetzTrace` gives pointwise equality of Deninger and continued
   prime–archimedean traces throughout this domain, so their imaginary-part sign conditions are
   equivalent.
4. `continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` converts either sign condition
   into RH.
5. Away from the centered divisor,
   `deningerDivisorRelativeResolventTrace_eq_logDeriv` shows this is also the passivity law of the
   centered characteristic determinant's logarithmic derivative.

No unconstructed Hilbert space, trace-class completion, numerical check, or infinite
sum/interchange is added.

## Formal targets

- `DeningerDivisorUpperAntiHerglotz`;
- `deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz`;
- `deningerDivisorUpperAntiHerglotz_iff_riemannHypothesis`;
- `deninger_cohomologicalResolventPassivityUniversality`.

## Novelty audit

Primary-source search after the dependency-closed Lean proof found:

- Deninger's arithmetic/dynamical cohomology and regularized-determinant program
  ([arXiv:math/0605724](https://arxiv.org/abs/math/0605724));
- a proved dynamical Lefschetz trace and regularized-determinant formula in the foliated setting
  ([arXiv:2410.20758](https://arxiv.org/abs/2410.20758));
- Connes's scaling-Hamiltonian analysis, including a distinct logarithmic-derivative sign
  obstruction ([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)).

None states the exact equivalence formalized here between RH and anti-Herglotz passivity of the
multiplicity-exact centered Deninger divisor relative resolvent on its full arithmetic regular
domain. Exact literature novelty remains **[NOVELTY UNVERIFIED]**.

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerCohomologicalResolventPassivityUniversalityLaw.lean`

and imported by:

`formal/GaloisForLFunctions/RHTower.lean`.

`lake env lean /private/tmp/law472_scratch.lean` passed after expanding the unavailable cached
`DeningerLefschetzTrace` import into its already verified source declarations. Direct module
verification currently stops before elaboration because `DeningerLefschetzTrace.olean` is absent.
Per project discipline, that dependency will be compiled only by the final targeted
`lake build GaloisForLFunctions.RHTower` audit.
