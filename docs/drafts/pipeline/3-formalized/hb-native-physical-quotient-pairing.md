# HB: original physical quotient pairing and full angular source

Status: formalized in six audited leaves, 15 new public theorems. The
original quotient integral is entire after polynomial clearing. For
right-half Xi sources, its actual physical value equals the previously
constructed complete meromorphic continuation. All three differential
cutoff channels remain in the full angular projection. RH remains open.

## Original integral and common majorant

Keep the original residual `S_q`, fundamental-domain measure `mu`, and
complete scalar field `E_u`. Write

```text
P(u) = u(2u-1)(2u+1),
Eclear_u(z) = (2u+1) Xi(2u) y^(1/2-u)
             + (2u-1) Xi(1+2u) y^(1/2+u) + P(u) tail_u(z),
K_q(u) = integral Eclear_u(z) S_q(z) dmu(z).
```

For nonreal `u`, the existing pointwise identity gives
`Eclear_u=P(u) E_u`. The new argument proves regularity of the actual
integral, rather than defining its values by continuation.

For `|u|<=R`, the original arithmetic coefficient has bound
`(N+1)^(3R+1)`. The Bessel height-decay bound splits into a fixed
summable exponential in `N` and `exp(-y/2)`. Bounding its order-dependent
constant on the spectral ball gives one bound on the complete signed
tail for every horizontal coordinate and every `y>=l>0`.

Every fixed complex height power times `S_q` is bounded on the entire
fundamental domain: compactness controls its truncated part; rapid
weighted decay of the original square remainder controls the cusp.
For `a<=Re w<=b` and `y>0`,

```text
y^(Re w) <= y^a + y^b.
```

Consequently two endpoint weights dominate all principal powers on a
spectral ball. Compact bounds on the entire Xi coefficients and clearing
polynomial, together with the uniform tail bound, give a single constant
majorant for `Eclear_u S_q` on the fundamental domain. Its measure is
finite. The Cauchy dominated-integral theorem now proves `K_q` entire.
An indicator extends the integrand by zero off the domain without
changing its original quotient integral.

## Physical identification

Let `Jc_q(s)` denote the complete continuation in
[the original period formula](hb-native-period-continuation.md). For
`Re q>1/2`, the proved chamber identity and nonreal clearing identity give

```text
K_q(u) = P(u) Jc_q(u+1/2)
```

on an open neighborhood of `3+i`. The difference is meromorphic on the
connected complex plane. Its locally zero germ has infinite order;
propagation of meromorphic order forces the difference germ to vanish
at every parameter.

At `u=(q-1)/2`, `K_q` and `P(u) Jc_q(u+1/2)` are continuous. Equality of
their punctured germs therefore gives equality of their actual values.
Xi support proves this parameter nonreal and `P(u)!=0`, permitting
cancellation. Thus the absolutely convergent original period satisfies

```text
J(q,(q-1)/2) = Lambda(5q/2-1) Lambda(q/2)^2 Lambda(1-3q/2)/2
               + Lambda(q-1) M_q(-q/2).
```

The restriction `Re q>1/2` is explicit and retained. Entirety of `K_q`
itself holds for every Xi source. Equality of the actual physical period
with its diagonal alone is equivalent to `M_q(-q/2)=0`; no such vanishing
is assumed or proved.

Substitution in the original angular integral yields the complete source
projection: its native radial coefficient multiplies this full value,
and the sum of the three original cutoff radial coefficients times
`scalarCutoffBoundaryValue((q-1)/2,principalExponent(q,i))` remains.

## Lean and verification

All leaves use prefix `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawking`:

| Suffix | Content |
| --- | --- |
| `BMNativeScalarUniformCusp` | Uniform full Fourier-tail bounds |
| `BMNativeResidualUniformWeights` | Original residual and endpoint weight bounds |
| `BMNativeClearedDomination` | Common majorant on spectral balls and the full domain |
| `BMNativePeriodRegularity` | Original integral admission and entirety after clearing |
| `BMNativePhysicalPairing` | Global germ equality and actual physical value |
| `BMNativePhysicalSourceValue` | Complete original physical angular projection |

The six leaves contain 443 lines and 15 public theorems. All six scratch
`lake env lean` checks and six individual canonical `lake build <module>`
audits passed without warnings. The canonical audits used existing
dependency artifacts in a private cache workspace. Exactly the 15 new
public theorem axiom checks returned only `propext`, `Classical.choice`
and `Quot.sound`. Six sources and twelve olean/ilean artifacts were
installed with byte verification; all six leaves were wired into the
umbrella. No numerical experiment, full build or umbrella build was run.

All 18 installed source/artifact hashes and six unique imports were
verified. Scoped whitespace and documentation links passed. One index
refresh completed. The repository-wide static `lint --check-generated`
run returned exit 1 because the separately added
`GaloisForLFunctions.HTGeometry.FokasLenellsContourFundamental` was
unreachable from its theorem-area umbrella. No new HB leaf was reported
unreachable or had proof debt. The global static gate therefore did not
pass; the six individual Lean audits above did pass.

## Remaining physical obligation

The full angular source value is now identified. It does not construct
the outgoing joint response inverse or identify the physical
advanced/adjoint left resonance. The next required result must connect
the original causal response to its outgoing continuation, retaining the
actual radial endpoint condition and full modular angular operator,
then evaluate the left-source projection and prove pole survival.
Independent Hawking-clock extinction remains unproved.
