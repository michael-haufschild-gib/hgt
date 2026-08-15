# Route P completed Xi conormal base residue

- **ID:** `route-p-completed-xi-conormal-base-residue`
- **Label:** P-G182
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT COMPLETED-DIVISOR LANDING IDENTIFICATION
- **RH used:** no
- **Computation used:** no
- **Parents:** P-G176, P-G181

## Conjecture loop

P-G181 leaves one positive base Cauchy cube as Route P's entire receiver. The conjecture was that
this matrix is not an abstract zero-side kernel but the residue Gram of a source-defined completed
meromorphic family. Define

```text
C(z,r)=logDeriv(xi)(z) r exp(-(z-1/2)r).
```

If `rho` is a Xi zero of analytic multiplicity `m`, Lean proves

```text
Res_(z=rho) C(z,r)=m r exp(-(rho-1/2)r).               (P-G182.1)
```

After division by `m`, its radial residue feature is

```text
psi_rho(r)=r exp(-(rho-1/2)r).
```

For strict-right zeros `rho,tau`, the Barnes--Mellin Gamma integral gives

```text
integral_(0,infinity) conj(psi_rho(r)) psi_tau(r) dr
  =2/[conj(rho-1/2)+(tau-1/2)]^3.                     (P-G182.2)
```

This is exactly P-G181's base Cauchy cube, entry by entry, on every finite zero packet.

## Proof

The completed Xi normalized-logarithmic-derivative residue theorem supplies (P-G182.1). Continuity
of the exponential column transports that residue into the radial family. The complex Gamma
integral at exponent three evaluates the Gram integral; elementary real/imaginary-part algebra
identifies its denominator with the base collision frequency. Extensionality then identifies the
entire finite matrix. `QED`

## Multiplicity obstruction and positive survivor

Raw logarithmic residues do not yet give the divisor Hilbert metric. A multiplicity-`m` residue has
base charge

```text
E_raw=m^2/(4a^3),        E_divisor=m/(4a^3).           (P-G182.3)
```

Lean proves `E_raw=E_divisor` for positive `m,a` iff `m=1`. It also proves that the unique positive
scalar `c` satisfying `(cm)^2=m` is

```text
c=1/sqrt(m).                                             (P-G182.4)
```

Thus the missing producer is not an unnormalized logarithmic-residue map. It must carry the
canonical divisor half-density: one square root of analytic multiplicity, equivalently a
copy-resolved conormal landing whose squared norm counts multiplicity linearly.

This is new obstruction-reducing knowledge, not RH. It closes identification of P-G181's entire
target matrix with an actual completed-Xi residue Gram and isolates the precise normalization that
any source-to-divisor contraction must implement. It does not assume simplicity of zeros or a
target capacity law.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePCompletedXiConormalBaseResidue.lean
```

Capstones:

- `routePCompletedXiConormalColumn_normalized_residue`;
- `integral_star_routePXiBaseConormalResidueFeature_mul`;
- `routePStrictRightZeroConormalResidueGramMatrix_eq`;
- `routePRawXiConormalResidueCharge_eq_divisor_iff`;
- `routePXiConormalMultiplicityHalfDensity_unique`.

Scratch `lake env lean /tmp/pg182.lean` passed. Exact leaf module build passed. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired without building
umbrella.

## Next gate

Construct the source-defined coefficient-faithful conormal operator before zero specialization.
Its divisor landing must resolve analytic order into the canonical copy fiber (or equivalently
apply the forced inverse-square-root half-density), and its trace norm must be bounded by P-G181's
primitive base budget. The operator and its norm may not be defined from the desired zero capacity.
