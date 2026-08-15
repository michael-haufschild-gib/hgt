# Route P primitive base Cauchy capacity reduction

- **ID:** `route-p-primitive-base-cauchy-capacity-reduction`
- **Label:** P-G181
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT CONJUGATED CAPACITY REDUCTION
- **RH used:** no
- **Computation used:** no
- **Parents:** P-G173, P-G175, P-G176, P-G180

## Conjecture loop

P-G180 proved that the collision column is the reconstructive dyadic defect `(I-V)psi` of the
base Laplace column `psi`.  The next conjecture was that conjugating out this defect might destroy
the strict source-versus-zero capacity gap.  It does not.

Define the base Cauchy cube

```text
B_R(a,b,kappa)=2R^3/[R(a+b)+i kappa]^3.
```

Lean proves every finite `B_R` packet is a principal compression of P-G173's doubled Schur cube,
hence positive semidefinite, and

```text
B_R(a,a,0)=1/(4a^3).                                  (P-G181.1)
```

On primitive Euler cell `(p,e)`, resolved von Mangoldt congruence gives exact base weight

```text
w_base(p,e)=(216/115) w_collision(p,e).                (P-G181.2)
```

Therefore the complete base budget satisfies

```text
B_base=(216/115) B_collision < 2.                      (P-G181.3)
```

Every strict-right Xi zero has `0<a<=1/2`, so its exact base charge obeys

```text
1/(4a^3) >= 2.                                         (P-G181.4)
```

Consequently the law placing all strict-right-zero base traces below `B_base` is equivalent to RH.

## Proof

P-G173 realizes its doubled cubic Gram as the third Schur power of a Hardy Cauchy Gram.  Restricting
both doubled indices to `Sum.inl` gives `B_R`; positivity follows from positivity of principal
submatrices. Direct diagonal evaluation proves (P-G181.1). Primitive diagonal congruence and the
ratio `(1/4)/(115/864)=216/115` prove (P-G181.2). P-G175's strict bound
`B_collision<115/108` gives (P-G181.3). Cubing `a<=1/2` gives (P-G181.4). A singleton strict-right
zero then contradicts capacity, while RH makes every target packet empty. `QED`

## New knowledge and no-go closure

- **Positive survivor:** dyadic Calderón conjugation preserves the full strict one-zero capacity
  gap on a simpler one-scale positive Cauchy cube.
- **Exact simplification:** the remaining source-to-divisor producer need not transport P-G173's
  four-term collision difference. It may land the base covariance first; P-G180 reconstructs the
  collision carrier afterward.
- **No-go closure:** repeated dyadic defects cannot improve the threshold. Base and defect capacity
  laws are both terminal RH receivers.
- **New open core:** construct coefficient-faithful Gamma--Euler continuation of the base covariance
  `r s (-zeta'/zeta)(1+r+s)` to the Xi divisor before divisor specialization.

This is not RH. It removes dyadic differencing from the only exterior producer still needed.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePPrimitiveBaseCauchyCapacityReduction.lean
```

Capstones:

- `routePBaseCauchyCubicKernelMatrix_posSemidef`;
- `routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal`;
- `routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum`;
- `routePStrictRightZeroBaseCauchyCubicCharge_ge_two`;
- `routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis`.

Scratch `lake env lean /tmp/pg181.lean` passed. Exact leaf module build passed. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired without building
umbrella.

## Next gate

Identify and continue the base covariance itself, retaining literal primitive coefficients and
Gamma real structure. Test whether a source-defined two-variable completed logarithmic derivative
has a positive polar residue equal to the base Xi charge; if not, extract the precise signed
archimedean obstruction and pivot before introducing another receiver-side capacity statement.
