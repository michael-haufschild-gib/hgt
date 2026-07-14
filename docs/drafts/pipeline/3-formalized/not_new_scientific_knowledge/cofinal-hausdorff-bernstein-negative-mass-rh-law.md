# Cofinal Hausdorff--Bernstein negative-mass RH law

- **ID:** `cofinal-hausdorff-bernstein-negative-mass-rh-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** not asserted as new scientific knowledge; retained for direct RH proof leverage
- **Lean files:** `formal/GaloisForLFunctions/RHTower/PrimeArchCofinalHausdorffDiagonalRH.lean`, `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinExponentialPhase.lean`, and `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinNegativeMassAbscissa.lean`
- **Statement:** At the endpoint-calibrated prime--Gamma source, RH and the prime--polar absolute-abscissa target are each equivalent to the canonical Hausdorff--Bernstein negative mass having any finite ceiling, even only along one cofinal sequence of degrees. Under false RH the monotone defect diverges to positive infinity.

## Main law

Let
```text
s(n) = normalizedPrimeArchMoment(n) / R^n
```
at the endpoint Hausdorff radius `R`. For degree `N + 1`, let
```text
a(N,i) = momentFunctional s (bernsteinPolynomial R (N + 1) i)
E(N)   = sum_i negativePart(a(N,i)).
```
Lean proves
```text
RH iff exists d : Nat -> Nat,
  Tendsto d atTop atTop and Tendsto (fun j => E(d j)) atTop (nhds 0).
```
For the rectangular prime--polar source coefficient, Lean also proves
```text
sigma_abs <= 1 iff exists cofinal d, E(d j) -> 0.
```
Lean additionally proves that `E(N)` is nondecreasing under Bernstein degree elevation.
Consequently, cofinal convergence `E(d(j)) -> 0` forces `E(N) = 0` at every degree. The scalar
criterion is therefore an exact order-unit restatement of complete Bernstein positivity, not a
strict weakening of it.  It also proves the complementary phase law:
```text
not RH iff exists N, 0 < E(N) and forall M >= N, E(N) <= E(M).
```

The cancellation-resistant Xi Bernstein-pencil theorem strengthens this to the finite-ceiling
dichotomy
```text
RH iff exists C, forall N, E(N) <= C
   iff exists cofinal d and C, forall j, E(d(j)) <= C,

not RH -> Tendsto E atTop atTop.
```
For every admissible rectangular prime--polar source, either finite-ceiling condition is also
equivalent to `sigma_abs <= 1`.

## Proof

Replace every signed Bernstein mass `a(N,i)` by its positive part. The resulting sequence is a
finite positive atomic moment sequence. Its `n`th coordinate exceeds the signed Bernstein
approximation by exactly
```text
sum_i negativePart(a(N,i)) * (i / (N + 1))^n.
```
Every node lies in `[0,1]`, so for every fixed `n` this error lies between `0` and `E(N)`.
Canonical signed Bernstein approximants converge coordinatewise to `s` without a positivity
assumption. Consequently, along any cofinal degree sequence on which `E(N)` tends to zero, the
positive-part approximants also converge coordinatewise to `s`. Rescaling by `R^n` places the
prime--Gamma moment sequence in the finite positive-atomic local moment closure, whose existing
source theorem implies RH.

Conversely, RH gives complete calibrated Hausdorff positivity. Every Bernstein mass is then
nonnegative, so `E(N) = 0` at every degree. This proves the equivalence.

Degree elevation has the barycentric identity
```text
B(N,i) = ((N+1-i)/(N+1)) B(N+1,i)
       + ((i+1)/(N+1)) B(N+1,i+1).
```
The negative part is subadditive and commutes with multiplication by nonnegative scalars. After
summing, the two adjacent barycentric columns each combine to total weight one. Hence
```text
E(N) <= E(N+1).
```
If `d(j)` is cofinal and `E(d(j)) -> 0`, monotonicity and `E(N) >= 0` give
`0 <= E(N) <= E(d(j)) -> 0`, so `E(N)=0` for every `N`.

For the genuinely weaker finite-ceiling direction, a nonreal reciprocal-square Xi coordinate
selects a unit-circle phase at which its affine Bernstein base has modulus greater than one. A
finite dominant-mode packet and a summable-tail mean-square argument prevent multiplicities or
the infinite divisor tail from cancelling this mode. Hence false RH forces exponential growth of
one value of the complete Bernstein pencil. Total variation dominates that value, so bounded
negative mass is impossible. Monotonicity then upgrades unboundedness to `E(N) -> +infinity`.

## RH proof impact

The old exact source obligation can be written as
```text
exists cofinal d, E(d j) -> 0.
```
The exponential-phase theorem now supplies the genuinely weaker replacement:
```text
exists cofinal d and fixed C, forall j, E(d j) <= C.
```
No coefficient sign, decay, exact moment realization, or control between checkpoints is needed.

There is also a direct finite-system consumer. Let `a_j` be any positive Hausdorff moment system
and let `b_N(source)` and `b_N(a_j)` be the degree-`N+1` Bernstein packets. RH follows if, on one
cofinal schedule `d`, either
```text
sum_i |b_(d j,i)(source) - b_(d j,i)(a_j)| <= C
```
or the quadratic operator-state budget
```text
(d j + 2) * sum_i |b_(d j,i)(source) - b_(d j,i)(a_j)|^2 <= C^2
```
holds uniformly. The latter is an inverse-dimension squared-norm obligation. Lean specializes it
to the explicit finite Xi thermal truncations, which are already positive endpoint Hausdorff
comparators. Thus thermodynamic physics no longer has to realize all source moments exactly; it
only has to prove this cofinal bounded aggregate discrepancy. That quantitative estimate remains
open and is the precise current source-side proof boundary.

## Principal declarations

- `hausdorffBernsteinNegativeMass`
- `hausdorffBernsteinPositiveAtomicMoment`
- `finitePositiveAtomicMomentSequence_hausdorffBernsteinPositiveAtomicMoment`
- `hausdorffBernsteinPositiveAtomicMoment_sub_signed_eq`
- `hausdorffBernsteinPositiveAtomicMoment_sub_signed_nonneg`
- `hausdorffBernsteinPositiveAtomicMoment_sub_signed_le_negativeMass`
- `bernsteinPolynomial_degree_elevation`
- `hausdorffBernsteinNegativeMass_monotone`
- `hausdorffBernsteinNegativeMass_eq_zero_of_cofinalVanishing`
- `cofinalHausdorffBernsteinNegativeMassVanishing_iff_forall_eq_zero`
- `exists_persistent_hausdorffBernsteinNegativeMass_of_not_cofinal`
- `not_riemannHypothesis_iff_exists_persistent_primeArchBernsteinNegativeMass`
- `PrimeArchBernsteinNegativeMassBounded`
- `riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded`
- `PrimeArchBernsteinNegativeMassCofinallyBounded`
- `riemannHypothesis_iff_primeArchBernsteinNegativeMassCofinallyBounded`
- `tendsto_primeArchBernsteinNegativeMass_atTop_of_not_riemannHypothesis`
- `primeArchBernsteinNegativeMassCofinallyBounded_iff_rectangularPrimePolarSource_negativeAbscissa_le_one`
- `bernsteinCoefficientL1DiscrepancyAtDefectDegree`
- `hausdorffBernsteinNegativeMass_le_l1Discrepancy`
- `riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_l1Discrepancy_bounded`
- `bernsteinCoefficientSquareDiscrepancyAtDefectDegree`
- `riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy`
- `riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy`
- `CofinalHausdorffBernsteinNegativeMassVanishing`
- `finitePositiveAtomicLocalMomentClosure_of_cofinalHausdorffBernsteinNegativeMassVanishing`
- `riemannHypothesis_of_cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing`
- `cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalBernsteinNegativeMassVanishing`

## Verification

The module compiles with the repository Lean toolchain. `#print axioms` for the local-closure
theorem, the RH equivalence, and the prime--polar absolute-abscissa equivalence reports only
`propext`, `Classical.choice`, and `Quot.sound`. The formal lint gate passes with no active
`sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 -> 1: scalar source defect and positive-part approximation are well posed
- [x] 1 -> 2: coordinatewise error bound and closure proof are complete
- [x] 2 -> 3: Lean compilation, axiom audit, and formal lint pass
- [x] 3 -> 4: integrated as the monotone scalar phase law in the source--temperature master paper
- [x] RH reduction: replace exact/cofinal vanishing by any fixed finite ceiling along a cofinal schedule
- [x] Physics consumer: reduce finite thermal realization to a cofinal `O(1/N)` squared Bernstein-packet discrepancy
- [ ] RH: prove that quantitative discrepancy bound unconditionally for the prime--Gamma source
