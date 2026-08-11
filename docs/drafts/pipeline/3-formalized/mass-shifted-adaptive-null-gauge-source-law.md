# Mass-shifted adaptive null-gauge source law

- **ID:** `mass-shifted-adaptive-null-gauge-source-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-U SOURCE PRODUCER
- **Scientific status:** `[LEAN-PROVED] [NEW SCIENTIFIC KNOWLEDGE CANDIDATE]`
  `[INTERNAL NOVELTY NONCOLLISION] [NOT RH]`
- **Parent:** `mass-shifted-adaptive-shear-adjacent-defect-law.md`,
  `mass-shifted-adaptive-shear-outgoing-ray-integral.md`

## Target

Let `P` be the monic null polynomial selected by a singular shifted-Hankel face, let
`A = P X^m`, `N = deg A`, and `K = 2N+1`.  Let `delta` be the actual Xi/flat-quadrature defect
sequence.  Define the null-root gauge

```text
kappa_A(u) = sum_(j=0)^N A_j (-u)^(N-j)
```

and the admission-sensitive source germ

```text
G_A(u) = kappa_A(u)^(-1)
  * sum_(r>=0) (-1)^r choose(2N+r,r) delta(A^2 X^r) u^r.
```

Prove that, when `delta_k=0` below `K`,

```text
[u^2] G_A
  = K * (K * A.nextCoeff * delta_K + (N+1) * delta_(K+1))
  = K/2 * CompletedAdaptivePsharp_A(y).
```

This is source-first: `delta`, null amplitude, barycenter, and factorial successor packet remain
coupled before reflection aggregation.  It is not a fixed reporter or post-hoc orientation map.

## Conjecture loop

1. **Pointwise Gamma--Green curvature lands on adaptive packet — FAIL.** Existing mate curvature
   is positive on divisor fibres, but its oriented Hodge factor is not the conjugate adaptive
   polynomial mate. Scalar landing would assume the missing sign.
2. **Ordinary moving-null energy curvature equals adaptive packet — FAIL.** Its second coefficient
   is `K*((N+1)delta_(K+1)-2 b delta_K)`, with wrong barycenter coefficient.
3. **Positive power of root gauge — FAIL.** Raw order two already sees the subleading coefficient
   `2*A.nextCoeff` of `A²`; `kappa_A^K` therefore overcounts barycenter.
4. **One inverse root gauge — SURVIVES.** Since `kappa_A(0)=1` and
   `[u]kappa_A^(-1)=A.nextCoeff`, Cauchy multiplication corrects the raw second coefficient to
   exactly `K*(K*A.nextCoeff*delta_K+(N+1)*delta_(K+1))`. One inverse is forced by mixed
   bilinearity: normalize one amplitude, not both factors of a quadratic energy.
5. **Right-cone local minimality signs second coefficient — FAIL.** Genuine crossing has nonzero
   positive first moving-energy derivative, so local nonnegativity does not force second
   coefficient nonnegative. Positive survivor is exact producer identity; remaining arithmetic
   theorem is positivity of this admitted covariant coefficient on outgoing source rays.
6. **Reuse the contact coefficient unchanged downstream — FAIL.** The amplitude admitted at the
   original face need not remain flat. The exact survivor is the degree-`<K` residual law: raw
   coefficient equals `K * adaptiveShear + lowerFlagMemory`. Subtracting that memory gives the
   completed arithmetic packet at every outgoing mass, and every genuine crossing forces this
   corrected value to become negative.

## Gates

- [x] exact paper algebra
- [x] Lean definition of full null-root gauge and gauged contact series
- [x] prove gauge is literal leading coefficient of Möbius-transported amplitude
- [x] Lean coefficient identity with actual shifted-Xi defects
- [x] identify completed mixed-amplitude/source aggregate
- [x] literal Archimedean plus Chebyshev-discrepancy specialization before reflection aggregation
- [x] full moving-flag decomposition and strict lower-contact residual degree
- [x] umbrella wiring
- [x] re-run lint, axiom audit, targeted build after moving-flag strengthening

## Lean realization

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveNullGaugeSourceLaw
```

Main declarations:

```text
coeff_mobiusTransportedNullPolynomial_eq_eval_adaptiveNullRootGauge
degree_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_lt_contact
coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_shear_add_lowerResidual
momentFunctional_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_eq_zero_of_flat
coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_adaptiveShear_of_flat
two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_completedPacket
two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_arch_add_discrepancy
exists_xiShiftedAdaptiveNullGaugeCorrectedSource_neg_on_outgoingRay_of_genuine_crossing
coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_adaptiveShear
coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_nullAmplitude_eq_shear
two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_completedPacket
two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_arch_add_discrepancy
```

The first theorem closes producer provenance: the gauge is not chosen from the desired answer but
is exactly the transported null amplitude's leading coefficient.  The final theorem lands in the
literal pre-reflection `Arch + Discrepancy` source packet.

The moving-flag theorem prevents an invalid downstream reuse.  Away from flat contact, the raw
second coefficient equals `K * adaptiveShear` plus an explicit polynomial residual.  That residual
has degree `< K`, so admission annihilates it exactly at contact; later it is the surviving lower
flag memory.  The crossing corollary proves unconditionally that every genuine crossing forces a
later negative value of the corrected coefficient, making its outgoing nonnegativity the exact
remaining arithmetic source law.

## Hostile audit

- No positivity is inferred from a second derivative with nonzero first derivative.
- No divisor-fibre Gamma--Green square is scalar-identified with adaptive shear.
- No fixed finite observer, orientation Boolean, or post-reflection reporter appears.
- `kappa^K` was rejected because it overcounts the subleading coefficient already present in
  `A^2`; `kappa^(-2)` belongs to a two-factor normalized quadratic energy, not the required mixed
  amplitude.
- Internal corpus search found no existing null-root inverse-gauge contact coefficient law.  This
  is an internal noncollision result, not a literature priority claim.
- A later negative shear does **not** imply a later negative raw null-gauge coefficient: the
  original amplitude need not remain flat.  The exact downstream object is raw coefficient minus
  lower-contact residual.

## Remaining exact obstruction

At contact, prove arithmetic nonnegativity of

```text
[u^2] (kappa_A^(-1) * C_A)
```

for amplitudes admitted by actual shifted-Hankel null flags.  On the outgoing ray, prove
nonnegativity of the corrected covariant

```text
[u^2] (kappa_A^(-1) * C_A) - L_v(R_(A,N)) = K * S_A(v).
```

Conjecture 52 says every genuine crossing forces a later negative value of this corrected object,
not necessarily of the raw coefficient.  The present theorem identifies producer and exact flag
memory; it does not yet exclude that value or prove RH.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryAdaptiveNullGaugeSourceLaw.lean
scripts/formal_tools.py lint
lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveNullGaugeSourceLaw
```

All passed after the moving-flag strengthening.  `#print axioms` for all ten audited producer,
residual, specialization, and crossing theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.
