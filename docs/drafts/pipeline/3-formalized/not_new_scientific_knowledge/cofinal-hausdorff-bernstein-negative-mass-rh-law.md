# Cofinal Hausdorff--Bernstein negative-mass RH law

- **ID:** `cofinal-hausdorff-bernstein-negative-mass-rh-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** not asserted as new scientific knowledge; retained for direct RH proof leverage
- **Lean file:** `formal/GaloisForLFunctions/RHTower/PrimeArchCofinalHausdorffDiagonalRH.lean`
- **Statement:** At the endpoint-calibrated prime--Gamma source, RH and the prime--polar absolute-abscissa target are each equivalent to the total negative mass of the canonical Hausdorff--Bernstein system tending to zero along one cofinal sequence of degrees.

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

## RH proof impact

The remaining source obligation can be written as one scalar asymptotic defect:
```text
exists cofinal d, E(d j) -> 0.
```
However, the monotone defect law shows that this does not reduce the RH proof burden: its cofinal
vanishing is equivalent to exact nonnegativity of every Bernstein mass at every degree. Its value
is diagnostic and organizational: it identifies complete Hausdorff positivity as the vanishing of
a canonical monotone order-unit defect. A genuinely weaker source target must instead control a
larger class such as bounded or subexponential growth of `E(N)` and separately prove that such
control excludes off-critical Xi values.

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
- [ ] RH: find a genuinely weaker unconditional source bound; cofinal vanishing is exact positivity
