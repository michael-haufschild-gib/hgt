# Route P completed Xi conormal multiplicity split

- **ID:** `route-p-completed-xi-conormal-multiplicity-split`
- **Label:** P-G183
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CANONICAL MINIMUM-ENERGY DIVISOR LIFT
- **RH used:** no
- **Computation used:** no
- **Parents:** P-G178, P-G182; Xi multiplicity-copy fibre

## Conjecture loop

P-G182 left an apparent multiplicity obstruction: a raw order-`m` logarithmic residue has amplitude
`m psi` and energy `m^2 ||psi||^2`, whereas the divisor Hilbert metric contains `m` copies and must
charge only `m ||psi||^2`. The first conjecture was that a new zero-dependent square-root
normalization had to be inserted into the analytic continuation. Corpus audit changed the
interpretation: Xi's divisor already carries a canonical `m`-element copy fibre. The correct map is
the minimum-energy right inverse of its codiagonal.

For total residue `v`, define

```text
Split_m(v)_j = v/m,       j in Fin(m).                 (P-G183.1)
```

Lean proves, for every Xi divisor support point and without a simplicity assumption,

```text
sum_j Split_m(v)_j = v,
sum_j |Split_m(v)_j|^2 = |v|^2/m.                     (P-G183.2)
```

Thus the operator norm is exactly `1/sqrt(m)`: P-G182's forced half-density is not an ad hoc
coefficient but the Hilbert norm of canonical residue copy-resolution.

## Exact minimum-energy theorem

Applying `(P-G183.1)` to the raw residue `m psi` places exactly `psi` on every divisor copy and
gives the desired linear energy `m |psi|^2`. More strongly, if any copy vector `u` conserves that
same raw residue,

```text
sum_j u_j = m psi,
```

Lean proves the Pythagorean identity

```text
sum_j |u_j|^2
  = m |psi|^2 + sum_j |u_j-psi|^2.                    (P-G183.3)
```

Consequently equal splitting is the unique minimum-energy copy resolution. This closes both
existence and canonicity of multiplicity normalization.

## Completed-Xi application

For every Xi divisor support point `rho`, every analytic-multiplicity copy `j`, and every radial
coordinate `r`, Lean applies the split directly to P-G182's raw completed-Xi conormal column and
proves

```text
Split_m((z-rho) C(z,r))_j  -->
  r exp(-(rho-1/2)r)          as z --> rho punctured. (P-G183.4)
```

Hence actual completed-Xi residue formation followed by canonical copy resolution lands exactly
one base Cauchy feature on every divisor copy, including multiple zeros.

## New knowledge and higher principle

- **Multiplicity obstruction closed:** no simple-zero premise and no externally chosen
  `1/sqrt(m)` coefficient remain.
- **Universal principle:** for a finite-to-one counting map, half-density normalization is the
  norm of the normalized adjoint of aggregation. The amplitude formula is division by fibre size;
  its Hilbert norm is inverse square-root fibre size.
- **Relation to P-G178:** arithmetic depth pullback and divisor copy resolution are opposite faces
  of the same change-of-counting-measure law. Depth replication needs square-root gain to preserve
  amplitude; codiagonal residue resolution gains inverse square-root norm automatically.
- **No theatre check:** P-G183 removes a genuine P-G182 obstruction. It does not introduce a new
  terminal capacity statement or define a map from an assumed zero bound.

This is not RH. The remaining theorem is now independent of analytic multiplicity: construct the
coefficient-faithful support-level Gamma--Euler continuation from P-G181's primitive base synthesis
to P-G182's raw completed-Xi conormal current and prove its pre-divisor norm bound. Canonical split
then supplies the multiplicity-exact divisor landing contractively.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePCompletedXiConormalMultiplicitySplit.lean
```

Capstones:

- `routePXiConormalMultiplicitySplit_sum`;
- `routePXiConormalMultiplicitySplit_energy`;
- `routePXiConormalMultiplicitySplit_pythagorean`;
- `routePXiConormalMultiplicitySplit_minimal_energy`;
- `routePXiConormalMultiplicitySplit_unique_minimizer`;
- `routePCompletedXiConormalColumn_fiber_residue`.

Scratch `lake env lean /tmp/pg183.lean` passed. Exact leaf module build passed. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired without building
umbrella.

## Next gate

Construct and bound the support-level continuation before residue specialization. Required input
is literal primitive base coefficients, not an interpolant chosen from the target zeros. Required
output is the raw completed-Xi conormal current; P-G183 then performs the only permissible
multiplicity resolution and cannot increase energy.
