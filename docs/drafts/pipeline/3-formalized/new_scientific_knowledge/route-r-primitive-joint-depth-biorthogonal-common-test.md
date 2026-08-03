# Route R primitive joint-depth biorthogonal common-test landing

- **ID:** `route-r-primitive-joint-depth-biorthogonal-common-test`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **RH used:** no
- **Xi zero used:** no
- **Computation used:** no
- **Parent:** `singular-infinite-source-pointed-common-test-factorization.md`

## Frontier statement

Route R requires primitive promotion to occur before any divisor or
prime-power scalarization. The earlier positive common-test source used the
single symmetric amplitude

```text
sqrt(Lambda(n)/n).
```

That realizes the correct scalar kernel, but it takes the geometric mean
before pairing and therefore does not exhibit the promoted source and the
reciprocal-promotion descent leg separately.

For `pe=(p,e)`, put `n=p^(e+1)`. For complex right-half-plane parameters
`w,v`, define the two retained-label coefficients

```text
L_w(pe) = [log(p)/sqrt(n)] n^(-w),
R_v(pe) = [1/sqrt(n)]       n^(-v).
```

The first coefficient is the literal primitive-promoted Gamma boundary
amplitude. The second is the reciprocal-promotion co-source. Prime and
valuation-depth labels remain present on both legs until their Hilbert
pairing.

## Theorem

If `Re(w)>0` and `Re(v)>0`, then `L_w` and `R_v` belong to
`ell^2(Primes x Nat)`, and

```text
<R_v,L_w>
  = sum_(p prime) sum_(e>=0)
      log(p) p^(-(e+1)(1+w+conj(v)))
  = LSeries Lambda (1+w+conj(v)).
```

Consequently

```text
<R_v,L_w> / (w+conj(v))
  = eulerPrimitiveCommonTestKernel(w,v).
```

This is unconditional and two-variable. It constructs the exact
source-to-common-test landing on the joint prime/depth carrier rather than
recovering only a scalar real-displacement trace.

## Maximal regular codiagonal and singular reflection wall

The Hilbert-vector hypothesis on both legs is stronger than required for
the coordinate product. The direct biorthogonal codiagonal is absolutely
summable on the larger chamber

```text
Re(w)+Re(v)>0,
```

and throughout that chamber still equals

```text
LSeries Lambda (1+w+conj(v)).
```

Thus one leg may already have crossed its individual Hilbert wall while the
paired source remains regular. This identifies the maximal regular direction
needed before a rigged/singular completion is introduced.

At exact reflected balance, take real `a` and `(w,v)=(a,-a)`. Every
prime-depth coordinate then satisfies the displacement-independent identity

```text
L_a(p,e) conjugate(R_(-a)(p,e))
  = Lambda(p^(e+1))/p^(e+1).
```

The depth-zero prime face contains `log(p)/p`, whose series diverges.
Therefore the full balanced codiagonal is not summable for any `a`. Ordinary
absolute pairing cannot cross the reflection-balanced face; Route R's
remaining continuation must be singular before the codiagonal is formed.

## Proof

For every prime-depth coordinate, the squared norms are

```text
|L_w(pe)|^2
  = [log(p)^2/n] exp(-2 Re(w) log(n)),

|R_v(pe)|^2
  = [1/n] exp(-2 Re(v) log(n)).
```

These are exactly the previously proved promoted-boundary and
reciprocal-promotion square families at displacements `2 Re(w)` and
`2 Re(v)`. Their positive-displacement summability gives the two Hilbert
vectors.

At zero displacement, primitive promotion cancels only across the two legs:

```text
[log(p)/sqrt(n)] [1/sqrt(n)] = log(p)/n = Lambda(n)/n.
```

For prime powers this is the square of the resolved von Mangoldt depth-one
amplitude. Complex conjugation on the right leg changes `n^(-v)` to
`n^(-conj(v))`; therefore each coordinate product equals the Dirichlet term

```text
LSeries.term Lambda (1+w+conj(v)) n.
```

Since `Re(1+w+conj(v))>1`, the von Mangoldt L-series is absolutely summable.
Unique factorization makes `(p,e) |-> p^(e+1)` injective. The von Mangoldt
support is contained in prime powers, so the prime-power reindexing theorem
identifies the joint-depth sum with the full L-series. Multiplication by the
common Hardy Cauchy factor `1/(w+conj(v))` yields the stated common-test
kernel.

## Anti-theatre audit

This is not RH, a zero detector, or a renamed scalar Euler identity. New
frontier content is the simultaneous construction of both nonidentical
Hilbert legs on the complete prime/depth carrier and proof that their
two-variable pairing is the pre-existing Route-R common-test kernel.
Primitive promotion is visible and remains attached to source incidence
until the final pairing.

The theorem removes one precise ambiguity from Route R: common-test landing
does not require taking the geometric mean before source pairing. It does not
supply the unresolved source-derived Ward sign. Remaining producer must add
the Gamma/Green reflection differential and prove that its arithmetic
boundary contribution annihilates the nonright divisor complement before
the four-unit Ward consumer.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthBiorthogonalCommonTest.lean
```

Capstones:

- `xiGammaEulerPrimitiveCommonTestSourceLp`;
- `xiGammaEulerPrimitiveCommonTestCoSourceLp`;
- `xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term`;
- `inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq`;
- `xiGammaEulerPrimitiveJointDepthCommonTestPairing_eq`;
- `summable_xiGammaEulerPrimitiveJointDepthPairedCodiagonal_of_re_add_pos`;
- `xiGammaEulerPrimitiveJointDepthPairedCodiagonal_eq`;
- `not_summable_xiGammaEulerPrimitiveBalancedReflectionCoeff`.

## Exact surviving frontier

Construct the Gamma/Green-reflected differential on this biorthogonal
joint-depth common-test source and prove its boundary form equals the
four-unit Ward form with source-derived positive orientation. Existing
positive-cone, finite signed-orbit, and absolutely summable signed-orbit
rigidity theorems force that differential to be divisor-coupled before
frequency separation or singular beyond absolute orbit summability.

## Pole-filled source-to-Xi landing

Literal paired source now lands through singular wall, not only in common-test L-series. On
regular chamber, set `u=w+conj(v)` and subtract pairing from two forced polar Cauchy channels:

```text
1/u + 1/(u+1) - <R_v,L_w>.
```

This is proved equal to pole-filled `regularizedCriticalMellinDefect(u)`. Under exact centered
coordinate `z=-i(u+1/2)`, Gamma completion

```text
i (regularizedCriticalMellinDefect(u) + gammaRealLogConnection(u+1))
```

equals `xiRelativeResolventTrace(z)` on regular resolvent locus `Re u>-1`, `u!=0`,
`zeta(u+1)!=0`. The theorem is unconditional; nonvanishing is domain condition for meromorphic
value equality, not zero-location hypothesis.

Additional Lean module:

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthSingularXiLanding.lean
```

Capstones:

- `xiGammaEulerPrimitiveJointDepthLaplaceDefect_eq_regularized`;
- `criticalMellinToCenteredXi`;
- `xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_xiRelativeResolventTrace`.

Source construction, polar renormalization, singular continuation coordinate, Gamma completion,
and Xi landing are therefore closed. Remaining Route-R theorem is not another continuation: it
is signed/off-diagonal arithmetic annihilation on divisor boundary.

## Genuine signed carrier

The two nonidentical source legs now live in one actual Hilbert direct sum
`ell2(Fin 2 x (Primes x Nat))`.  Slot exchange is proved unitary,
self-adjoint, and involutive.  Its Krein form has strict positive diagonal
and strict negative anti-diagonal sectors, and the source/co-source cross
coefficient is exactly the full von Mangoldt channel.  Polar and Gamma
completion of its canonical complex split lands in the Xi relative
resolvent.  This supplies the negative/off-diagonal producer forced by the
depth-one positive-completion obstruction.

Additional Lean module and research card:

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthKreinXiLanding.lean

docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-r-joint-depth-krein-xi-landing.md
```

This still does not annihilate actual Green provenance.  Rank-one reflected
prime/depth incidence is a flat coboundary, so surviving source differential
must be nonseparable across Euler--Gamma/divisor provenance before
codiagonalization.
