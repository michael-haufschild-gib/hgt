# HB: complete native period continuation and physical cutoff correction

Status: formalized. Eight leaves construct a meromorphic continuation
agreeing with the original native quotient integral for right-half Xi
sources in the proved unfolding chamber. The continuation is analytic at
the physical testing parameter and has an exact reflected cutoff
correction. The [original quotient regularity and physical identification](hb-native-physical-quotient-pairing.md)
now identify that value with the actual physical integral for right-half
Xi sources. RH remains open.

## Complete original-period formula

Write `q : XiZeroCopy`, `u=q-1/2`, `eta(y)=smoothTransition(y-2)`, and

```text
A_q(y) = Lambda(2q-1) y^(1-q) + Lambda(2q) y^q,
A_q(y)^2/2 = sum_(j:Fin 3) c_j y^(p_j),
(p_0,p_1,p_2) = (2-2q,1,2q),
(c_0,c_1,c_2) = (Lambda(2q-1)^2/2,
                 Lambda(2q-1) Lambda(2q), Lambda(2q)^2/2).
```

All coefficients and powers are derived from the literal principal
half-square. Xi support gives `0<Re p_j<2`. Define

```text
T(w) = integral_(2,3] eta(y) y^(w-1) dy,
W(w) = 3^w/w - T(w),
M_q(t) = sum_(j:Fin 3) c_j W(t+p_j).
```

The original finite transition `T` is entire. `W` is meromorphic
everywhere and analytic away from zero. Both original cutoff power
integrals are absolutely admitted in their respective chambers, with

```text
integral_0^infinity (1-eta(y)) y^(w-1) dy = W(w),  Re w>0,
integral_(2,infinity) eta(y) y^(w-1) dy = -W(w),   Re w<0.
```

Consequently, the complete continued native period is

```text
Jc_q(s) = Lambda(s+2q-1) Lambda(s)^2 Lambda(s-2q+1)/2
          + Lambda(2s) M_q(s-1) + Lambda(2s-1) M_q(-s).
```

Lean proves `Jc_q(s)=scalarResidualPeriod q (s-1/2)` for
`Re q>1/2` and `Re s>2`. It also proves `Jc_q` meromorphic on the whole
complex plane. The right-half source restriction belongs to agreement
with the original quotient integral, inherited from the proved original
divisor-product evaluation. Meromorphy of the displayed expression does
not remove that restriction.

## Admission and original-source identification

The original residual strip admission transfers by absolute Fubini to
its weighted horizontal mean. The full cutoff orbit equals its original
height profile above height `1/2`; below that height the height profile
itself is zero. Thus the original principal remainder
`(1-eta) A_q^2/2` is the complete residual mean minus the admitted Fourier
diagonal plus the lower cutoff correction extended by zero. This proves
its own absolute admission without splitting divergent principal and
parabolic terms at infinity.

The resulting exact three-moment identity is

```text
J(q,s-1/2) = 4 Lambda(2s) I(q,s)
  + Lambda(2s) integral_0^infinity y^(s-2) (1-eta(y)) A_q(y)^2/2 dy
  - Lambda(2s-1) integral_(2,infinity) y^(-s-1) eta(y) A_q(y)^2/2 dy.
```

Here `I` is the [original Fourier diagonal](hb-native-fourier-mellin-value.md).
The last term uses the [complete reflected orbit identity](hb-native-cutoff-orbit-mellin.md).
Finite power expansion and the two admitted cutoff identities give
`M_q(s-1)` and `-M_q(-s)` for the remaining integrals. Their signs and the
half-square normalization give the displayed `Jc_q` formula.

## Physical value and exact remaining correction

At `s=q/2`, every displayed completion argument is nonreal. The three
arguments of each principal moment are also nonzero. Lean proves that
the complete continuation is analytic there, and

```text
Jc_q(q/2) = Lambda(5q/2-1) Lambda(q/2)^2 Lambda(1-3q/2)/2
            + Lambda(q-1) M_q(-q/2).
```

The actual Xi zero gives `Lambda(q)=0`, eliminating the forward
principal correction. Lean separately proves `Lambda(q-1) != 0`.
It follows that equality with the diagonal alone is equivalent to
`M_q(-q/2)=0`. This is an exact cancellation criterion, not a proof
that the remaining moment vanishes or that the complete source is nonzero.

## Lean leaves and verification

All leaves are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawking` and namespace `RHTower.D4BMJointSource`:

| Leaf suffix | Closed content |
| --- | --- |
| `BMNativePeriodAssembly` | Admission and exact original three-moment assembly |
| `BMNativeCutoffPowerMoments` | Both original cutoff power integrals and finite transition |
| `BMNativeCutoffMellinMeromorphy` | Entire transition and meromorphic cutoff moment |
| `BMNativePrincipalPowerExpansion` | Literal three coefficients, powers, and integrands |
| `BMNativePrincipalMellinValue` | Both original principal moment values |
| `BMNativeLambdaMeromorphy` | Completion meromorphy, physical analyticity and Xi factors |
| `BMNativePeriodContinuation` | Actual convergence-chamber agreement and meromorphy |
| `BMNativePeriodPhysicalValue` | Analytic physical value and exact cancellation criterion |

The eight leaves contain 654 source lines and 33 new public theorems.
All scratch `lake env lean` checks and all eight individual canonical
`lake build <module>` audits passed without warnings. The final audits
used an isolated workspace with existing dependency artifacts. Exactly
33 new public theorem axiom checks returned only `propext`,
`Classical.choice`, and `Quot.sound`. Eight sources and sixteen
olean/ilean artifacts were installed with byte verification and wired
into the umbrella. No full or umbrella build or numerical experiment
was run.

One index refresh and one repository-wide static `lint --check-generated`
run completed; the static gate passed with exit zero and no errors.
The gate emitted existing large-file size notices. All 24 installed file
hashes match the audited sources and artifacts. Scoped whitespace and
documentation-link checks passed.

## Original physical identification and remaining response obligation

The [original physical quotient pairing](hb-native-physical-quotient-pairing.md)
now has a common integrable majorant over parameter neighborhoods and
the full quotient domain. Its polynomial-cleared integral is entire.
The identity principle and nonzero physical clearing factor prove
`scalarResidualPeriod q ((q-1)/2)=Jc_q(q/2)` for `Re q>1/2`.
The actual full angular source formula retains this reflected correction
and all three differential cutoff terms. The outgoing joint inverse,
physical advanced/adjoint pairing, complete source nonvanishing, and
independent Hawking-clock extinction remain open.
