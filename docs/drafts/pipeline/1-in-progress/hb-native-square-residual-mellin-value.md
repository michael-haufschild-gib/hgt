# HB: original physical source and outgoing response

Chain: literal theta cusp → Xi occurrence → complete native source projection
→ original causal response and physical adjoint pairing → independent
Hawking-clock extinction → RH. Goal remains open; frontier map read-only.

## Closed original-period continuation

The [complete native period continuation](../3-formalized/hb-native-period-continuation.md)
is formalized in eight audited leaves with 33 new public theorems. It
assembles the [original Fourier diagonal](../3-formalized/hb-native-fourier-mellin-value.md)
and [full reflected cutoff moment](../3-formalized/hb-native-cutoff-orbit-mellin.md),
retaining the complementary principal term as a single admitted integral.

For the original cutoff `eta(y)=smoothTransition(y-2)`, define

```text
W(w) = 3^w/w - integral_(2,3] eta(y) y^(w-1) dy,
M_q(t) = sum_(j:Fin 3) c_j W(t+p_j),
(p_0,p_1,p_2) = (2-2q,1,2q),
(c_0,c_1,c_2) = (Lambda(2q-1)^2/2,
                 Lambda(2q-1) Lambda(2q), Lambda(2q)^2/2).
```

Both original cutoff power integrals are evaluated with their absolute
admission proved: the complementary lower moment is `W(w)` for `Re w>0`,
and the upper cutoff moment is `-W(w)` for `Re w<0`. The finite transition
is entire. The full meromorphic expression is

```text
Jc_q(s) = Lambda(s+2q-1) Lambda(s)^2 Lambda(s-2q+1)/2
          + Lambda(2s) M_q(s-1) + Lambda(2s-1) M_q(-s).
```

Lean proves `Jc_q(s)=scalarResidualPeriod q (s-1/2)` for right-half Xi
sources `Re q>1/2` and `Re s>2`. No source-admission, interchange,
arithmetic-identification, or RH premise is supplied. The displayed
parameter restrictions remain explicit.

## Closed physical value of the continuation

The constructed continuation is analytic at `s=q/2`, and Lean proves

```text
Jc_q(q/2) = Lambda(5q/2-1) Lambda(q/2)^2 Lambda(1-3q/2)/2
            + Lambda(q-1) M_q(-q/2).
```

`Lambda(q)=0` eliminates the forward principal correction, whereas
`Lambda(q-1)` is proved nonzero. Thus equality with the diagonal alone
is exactly the condition `M_q(-q/2)=0`. That condition has not been
proved. The complete source cannot be replaced by the diagonal alone.

## Closed actual physical quotient pairing

[Original physical quotient pairing](../3-formalized/hb-native-physical-quotient-pairing.md)
is formalized in six audited leaves and 15 public theorems. Uniform
spectral-and-height control of the complete Fourier tail, two endpoint
height weights and compact bounds on the Xi coefficients give a common
integrable majorant on the full original quotient domain. Consequently
`clearedResidualPeriod q` is entire for every Xi source.

The meromorphic identity principle extends the proved chamber equality
as a germ to every parameter. At the physical parameter, continuity and
the proved nonzero clearing factor identify actual values. Thus, for
`Re q>1/2`, `scalarResidualPeriod q ((q-1)/2)=Jc_q(q/2)` with the full
reflected correction retained. The source restriction is explicit.
`continuedAngularSourceProjection_physical_value` substitutes this
actual native period into the complete original source, retaining all
three evaluated differential cutoff channels.

## Closed bounded physical source testing

The existing `SelbergScatteringCuspNorm` classification proves that the
physical angular field has divergent native cusp squared norm. It cannot
be inserted directly as an angular Hilbert-space test. Its inverse-height
multiple is square-integrable: the physical principal power becomes
`Lambda(q-1) y^(-q/2)`, and the complete Fourier tail has the required
weighted bound. The original residual and all three differential cutoffs
remain square-integrable after multiplication by height.

[Bounded physical source testing](../3-formalized/hb-physical-weighted-source-testing.md)
is formalized in four audited leaves and 15 new public theorems. The
conjugate inverse-height field represents the bounded original bilinear
functional. Its radial extension, the adjoint of tensor insertion, maps
the actual height-weighted complete source to the original physical
source projection for every Xi source and target. All four original
channels remain, and their joint class is meromorphic in the stronger
height-weighted norm throughout the nonreal band `|Re w|<2`. The two
height factors cancel inside the original integral. This source testing
map does not yet identify the adjoint of the original outgoing inverse
or its residue, nor prove weighted admission of that response.

## Next hard obligation: original outgoing response and left residue

Construct the outgoing continuation of the original causal joint
response in its physical domain, retaining the original radial endpoint
condition and full modular angular operator. Prove agreement with
`jointWaveResponse` on the original overlap, then identify and evaluate
the physical advanced/adjoint left-source projection of the complete
angular expression. The source value alone does not prove pole survival
or complete source nonvanishing. Independent Hawking-clock extinction
and RH remain open. No numerical experiment is indicated.
