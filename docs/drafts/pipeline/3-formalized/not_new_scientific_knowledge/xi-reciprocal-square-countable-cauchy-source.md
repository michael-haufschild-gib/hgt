# Xi reciprocal-square countable Cauchy source criterion

- **ID:** `xi-reciprocal-square-countable-cauchy-source`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / COUNTABLE VALUE-RELATION CRITERION
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiReciprocalSquareCountableCauchySource.lean`
- **Statement:** RH is equivalent to vanishing of one real reciprocal-square orientation defect
  at every regular Gaussian-rational pole in the centered strip.

## Goal

Continue the top-down interface reduction

```text
all finite continued-Cauchy packets
  -> individual continued-Cauchy vectors
  -> countably many Gaussian-rational Cauchy vectors
  -> RH.
```

For a regular Gaussian-rational pole `q`, define the scalar defect

\[
\delta_\Xi(q)
=
\operatorname{Im}
\left\langle
R_\Xi^2 k_q,k_q
\right\rangle.
\]

Lean proves

\[
\mathrm{RH}
\iff
\delta_\Xi(q)=0
\quad\text{for every regular }
q\in\mathbb Q+i\mathbb Q,quad |\operatorname{Im}q|<\frac12.
\]

## Exact chain

The Gaussian-rational Cauchy family is norm-dense in the full continued-Cauchy source family.
The zero locus of

\[
v\longmapsto
\langle R_\Xi^2v,v\rangle-
\langle v,R_\Xi^2v\rangle
\]

is norm-closed.  Hence vanishing of every rational scalar defect gives quadratic reality on every
individual continued-Cauchy vector.  Horizontal pole exhaustion then transfers reality to every
exact Xi multiplicity fibre.  The fibre eigenvalue is the centered reciprocal square; its reality
forces the corresponding zero onto the critical line.

```text
delta_Xi(q) = 0 for every regular Gaussian rational q
  -> rank-one reality on the full continued source domain
  -> reciprocal-square reality on every Xi multiplicity fibre
  -> every Xi zero has real part 1/2
  -> RH.
```

The reverse implication follows from self-adjointness of `R_Xi^2` under RH.

## Remaining open source problem

The theorem removes uncountable quantification, finite coefficient families, and all mixed Cauchy
relations.  The unresolved producer is now the countable scalar identity

\[
\delta_\Xi(q)=0
\]

derived from the explicit continued prime--Gamma source at each regular Gaussian-rational pole,
without using Xi divisor orientation, Weil positivity, real-rootedness, or an RH-equivalent
positive measure.

This is still an RH-strength terminal relation because `R_Xi` is indexed by the actual divisor.
The contribution is the strict reduction of the source theorem that would close it.

## Lean certificate

The public declarations are:

```text
XiReciprocalSquareGaussianRatCauchyQuadraticReal
xiReciprocalSquareGaussianRatOrientationDefect
xiReciprocalSquareGaussianRatOrientationDefect_eq_zero_iff
XiReciprocalSquareGaussianRatOrientationDefectsVanish
xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_quadraticReal
xiReciprocalSquareOneCauchyQuadraticReal_of_gaussianRat
riemannHypothesis_of_xiReciprocalSquareGaussianRatCauchyQuadraticReal
xiReciprocalSquareGaussianRatCauchyQuadraticReal_iff_riemannHypothesis
xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_riemannHypothesis
xiReciprocalSquareContinuedCauchyQuadraticReal_of_gaussianRat
```

The module is imported by `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: countable scalar defect family isolated
- [x] 1 → 2 fully-proven: density, closedness, fibre transfer, and RH implication complete
- [x] 2 → 3 formalized: Lean module is placeholder-free and umbrella-wired
- [ ] 3 → 4 publication-ready: only after the scalar defect receives a source-side formula
