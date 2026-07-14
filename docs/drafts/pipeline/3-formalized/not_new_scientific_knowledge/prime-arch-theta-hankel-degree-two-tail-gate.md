# Prime--archimedean irreducible Eisenstein sparse-degree Hankel law

- **ID:** `prime-arch-theta-hankel-degree-two-tail-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** not new scientific knowledge
- **Lean file:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaHankelDegreeTail.lean`
- **Statement:** For every infinite set `D` of polynomial degrees, nonnegativity of the prime--Gamma trace--Hankel tests only on monic integer polynomials Eisenstein at `2` whose exact degrees belong to `D` is equivalent to RH.

## Main law

Define
```text
PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K :=
  forall p : Polynomial Z,
    K <= p.natDegree ->
      0 <= re (primeArchSourceTraceHankel (p mapped to R)).
```
Lean proves, for every `K`,
```text
PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K iff RH.
```
In particular, the previously isolated degree-two tail is itself exactly RH:
```text
PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative iff RH.
```
No theta-ratio inequality and no separate constant or linear test is required.

## Sparse-degree strengthening

For a set `D` of natural numbers, define
```text
PrimeArchSourceTraceHankelIntDegreeSetNonnegative D :=
  forall p : Polynomial Z,
    p.natDegree in D ->
      0 <= re (primeArchSourceTraceHankel (p mapped to R)).
```
Lean proves
```text
D.Infinite ->
  (PrimeArchSourceTraceHankelIntDegreeSetNonnegative D iff RH).
```
Every infinite subset of the natural numbers is unbounded. For an omitted test `p`, choose one
`d in D` above `natDegree p`; the same perturbations `N p +/- X^d` recover `Q(p) >= 0`. Thus the
criterion may use an arbitrarily sparse cofinal degree schedule, such as powers of two, rather
than every degree above a cutoff.

## Monic strengthening

Define
```text
PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D :=
  forall p : Polynomial Z,
    p.Monic ->
    p.natDegree in D ->
      0 <= re (primeArchSourceTraceHankel (p mapped to R)).
```
Lean proves
```text
D.Infinite ->
  (PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D iff RH).
```
For an arbitrary omitted `p`, choose `d in D` above its degree. Both
`X^d + N p` and `X^d - N p` are monic of exact degree `d`. Their two trace--Hankel values add to
`2 Q(X^d) + 2 N^2 Q(p)`, so nonnegativity for all such monic probes forces `Q(p) >= 0`.

## Irreducible Eisenstein strengthening

Let `I_2` be the ideal of even integers and define
```text
PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D :=
  forall p : Polynomial Z,
    p.Monic ->
    p.IsEisensteinAt I_2 ->
    p.natDegree in D ->
      0 <= re (primeArchSourceTraceHankel (p mapped to R)).
```
Lean proves
```text
D.Infinite ->
  (PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D iff RH).
```
For an omitted `p`, choose `d in D` above its degree and use
```text
X^d + 2 + 4 N p,
X^d + 2 - 4 N p.
```
Both probes are monic of degree `d`, all nonleading coefficients are even, and each constant
coefficient is `2 mod 4`. They are therefore Eisenstein at `2`, hence irreducible over `Z`, while
their quadratic values add to
```text
2 Q(X^d + 2) + 2 (4 N)^2 Q(p).
```
Thus one fixed irreducible coefficient-congruence chamber on any infinite degree schedule is
already positivity-complete.

## Degree-raising proof

Let `Q(p)` denote the real prime--Gamma trace--Hankel quadratic value.  Lean first proves the
polarized dilation identity
```text
Q(c p + q) + Q(c p - q) = 2 c^2 Q(p) + 2 Q(q).
```
For an arbitrary omitted integer polynomial `p`, choose
```text
d = max K (natDegree p + 1),
q = X^d.
```
For every positive integer `N`, both `N p + X^d` and `N p - X^d` have degree exactly `d`, so the
degree-tail hypothesis makes both quadratic values nonnegative. If `Q(p) < 0`, choose `N` so
large that
```text
N^2 * (-Q(p)) > |Q(X^d)|.
```
The polarized identity then makes their nonnegative sum strictly negative, a contradiction.
Therefore `Q(p) >= 0` for every integer polynomial, and the existing countable source criterion
gives RH.

## RH proof impact

Every finite collection of polynomial degrees is logically redundant, almost all remaining
degrees may be discarded, and all tests outside one monic irreducible Eisenstein chamber may be
discarded as well. The remaining proof may choose any convenient infinite degree set and work
only with polynomials whose lower coefficients are even and whose constant coefficient is
`2 mod 4`. This removes the two low-degree theta-cusp ratio hypotheses from the degree-two
capstone and closes the gap between that fixed sparse Eisenstein family and the complete
integer-polynomial source cone.

This does not prove the degree tail itself. It proves that no separate low-degree discharge is
part of the RH obligation.

## Quantitative low-block refinement

The theta-cusp ratio identities still give independent quantitative information. If both ratio
inequalities hold and at least one has strict margin, the `2 x 2` prime--Gamma moment determinant
is strictly positive. Together with a strict leading-determinant tail from size three, this gives
the scalar determinant criterion for RH. This refinement is not needed for the arbitrary
polynomial-degree tail law.

## Principal declarations

- `PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative`
- `primeArchSourceTraceHankel_smul_add_sub_re`
- `PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom`
- `primeArchSourceTraceHankelIntNonnegative_of_degreeTail`
- `primeArchSourceTraceHankelIntDegreeTailNonnegativeFrom_iff_riemannHypothesis`
- `riemannHypothesis_of_primeArchSourceTraceHankelIntDegreeTwoTailNonnegative`
- `primeArchSourceTraceHankelIntDegreeTwoTailNonnegative_iff_riemannHypothesis`
- `PrimeArchSourceTraceHankelIntDegreeSetNonnegative`
- `primeArchSourceTraceHankelIntNonnegative_of_infiniteDegreeSet`
- `primeArchSourceTraceHankelIntDegreeSetNonnegative_iff_riemannHypothesis`
- `primeArchSourceTraceHankel_add_sub_smul_re`
- `PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative`
- `primeArchSourceTraceHankelIntNonnegative_of_monicInfiniteDegreeSet`
- `primeArchSourceTraceHankelIntMonicDegreeSetNonnegative_iff_riemannHypothesis`
- `primeArchTwoEisensteinIdeal`
- `primeArch_twoEisenstein_plus`
- `primeArch_twoEisenstein_minus`
- `irreducible_of_monic_primeArchTwoEisenstein`
- `PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative`
- `primeArchSourceTraceHankelIntNonnegative_of_twoEisensteinInfiniteDegreeSet`
- `primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis`
- `det_primeArchSourceMomentHankelMatrix_two_pos_of_ratioSplit_of_one_strict`
- `PrimeArchSourceMomentHankelDeterminantTailFromThreePositive`
- `riemannHypothesis_of_strictThetaCuspRatioSplit_of_primeArchDeterminantTailFromThree`

The named module builds successfully. `#print axioms` for the polarization identity, arbitrary
degree-tail completion, sparse-degree completion, monic sparse-degree completion, irreducible
Eisenstein completion, their RH equivalences, and the degree-two capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1 source-pure irreducible Eisenstein sparse-degree tail and cancellation identified
- [x] 1 -> 2 complete paper proof
- [x] 2 -> 3 formalized in Lean with no new axioms
- [ ] 3 -> 4 publication-ready treatment not required for the active RH proof
- [ ] RH: prove source trace--Hankel positivity in the fixed `2`-Eisenstein chamber on one infinite degree set
