# HB: original Fourier–Mellin interchange and diagonal value

Status: formalized. The original complex diagonal Fourier integral is
absolutely admitted and evaluated for every Xi source when `Re s>2`.
For right-half Xi sources, its completed value is one half of the
four-Lambda product. This is the diagonal contribution, not the whole
native period or its physical continuation. RH remains open.

## Exact statements

Let `q : XiZeroCopy`, `u=q-1/2`, and retain the original coefficients
and Bessel amplitudes:

```text
c_N(u) = (N+1)^u sum_(d | N+1) d^(-2u),
a_N(u,y) = c_N(u) sqrt(y) K_u(2 pi (N+1)y),
M(u,y) = sum_N norm(a_N(u,y))^2.
```

For every Xi source and `Re s>2`, Lean proves

```text
sum_N integral_0^infinity norm(y^(s-2) a_N(u,y)^2) dy < infinity,
I(q,s) := integral_0^infinity y^(s-2) sum_N a_N(u,y)^2 dy
        = sum_N integral_0^infinity y^(s-2) a_N(u,y)^2 dy.
```

The first display denotes the proved summability of the real integrals
of norms. Every individual mode and the complete complex sum are
integrable. The exact value is

```text
B(s,u) = 2^(s-3) Gamma(s/2+u) Gamma(s/2)^2 Gamma(s/2-u) / Gamma(s),
I(q,s) = (2 pi)^(-s) B(s,u) L(sigma_(-2u)^2, s-2u).
```

For `Re q>1/2` and `Re s>2`, the original divisor series is summable and

```text
L(sigma_(-2u)^2, s-2u) = zeta(s-2u) zeta(s)^2 zeta(s+2u) / zeta(2s),
4 Lambda(2s) I(q,s) = Lambda(s+2u) Lambda(s)^2 Lambda(s-2u) / 2.
```

The factor `1/2` follows from the original half-square source. The
four-Lambda theorem retains the explicit right-half restriction on `q`;
the integral admission and Gamma–L-series identity do not require it.
These are closed theorems about the stated parameter domains, without
an RH premise or assumed source bound, integral interchange, or arithmetic
identification.

## Proof from the original source

The paired Fourier waves are real. Conjugating the coefficient sequence
and applying their exact orthogonality gives the Hermitian mean identity.
For the actual scalar and its original principal part `A_u`, this yields

```text
integral_0^1 norm(scalar_u(x,y))^2 dx = norm(A_u(y))^2 + 8 M(u,y).
```

The original identity `scalar_q^2/2 = globalSquareResidual_q + P_h_q`,
the global residual bound, and the complete cutoff-orbit norm bound
give `norm(scalar_q)^2 <= A+B S_2`. The actual horizontal mean of the
positive height-power sum then bounds

```text
M(u,y) <= A+B (y^2+D_2 y^(-1)),  y>0,
```

with nonnegative constants depending on the original Xi source. At the
lower height end, multiplying by `y^(r-2)` gives powers `r-2`, `r`, and
`r-3`, all integrable when `r>2`. At the upper end, the original Bessel
tail estimates bound `y^r M(u,y)` for every real `r`, yielding an integrable
`y^(-2)` majorant for the weighted mass.

Dominated convergence applied to the sums of mode norms proves
summability of their integrals. The complex sum/integral interchange
then follows with the original coefficient squares unchanged. The
Hermitian norm estimate supplies admission; it does not replace the
complex quadratic source by an energy.

The actual two-Bessel Mellin theorem applies because Xi support gives
`abs(Re u)<1/2`. A proved change of variable supplies the factor
`(2 pi (N+1))^(-s)`. The literal divisor coefficient identity identifies
the resulting series with its original L-series. For right-half Xi
sources, the shifts `-2u` have negative real part and `Re(s-2u)>1`,
so the corpus Ramanujan product theorem applies in its proved chamber.
The Gamma and pi factors are normalized explicitly, and `zeta(2s)`
is cancelled using its proved nonvanishing there.

## Lean leaves and verification

All leaves are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawking`:

| Leaf suffix | Closed content |
| --- | --- |
| `BMCuspHermitianMean` | Original paired-wave conjugation and Hermitian mean |
| `BMCuspScalarEnergy` | Exact scalar and tail coefficient-norm identities |
| `BMNativeFourierEnergyBounds` | Actual global source and weighted mass bounds |
| `BMNativeFourierMassAdmission` | Absolute weighted mass admission at both ends |
| `BMNativeFourierMellinInterchange` | Integral-norm summability and complex interchange |
| `BMNativeFourierBesselValue` | Original scaled Bessel integral and Gamma factor |
| `BMNativeFourierDirichletValue` | Literal coefficient L-series and Ramanujan value |
| `BMNativeFourierCompletedValue` | Original half-square diagonal four-Lambda value |

The eight leaves contain 734 source lines and 37 new public theorems.
Each passed scratch `lake env lean` and an individual final canonical
`lake build <module>` in an isolated workspace using existing dependency
artifacts. All builds exited zero without warnings; the final leaf
emitted an informational tactic suggestion. A scratch-only axiom audit
of exactly these 37 theorems returned only `propext`, `Classical.choice`,
and `Quot.sound`. Eight sources and sixteen olean/ilean artifacts were
installed with byte verification. All eight imports are wired into the
umbrella. No full or umbrella build or numerical experiment was run.

After one index refresh, the repository-wide static `lint --check-generated`
gate returned exit 1 with four unrelated `HTGeometry` modules unreachable
from their umbrella: `FokasLenellsContourFifth`, `FokasLenellsContourMoment`,
`FokasLenellsOriginIntegrability`, and `FokasLenellsOriginWeightedProfile`.
It reported no error in these eight HB leaves, no proof-debt error, and
no generated-index error. That static audit failed; the individual
module and new-theorem audits above did pass. Scoped whitespace and
documentation-link checks passed, and all 24 installed file hashes match
the audited artifacts.

## Remaining original-source obligation

The [complete native period continuation](hb-native-period-continuation.md)
assembles the actual constant and cutoff contributions, proves agreement
with the original quotient integral in the right-half Xi convergence
chamber, and evaluates its analytic continuation at `s=q/2`. The reflected
cutoff correction survives unless its displayed moment vanishes.

The [next original-pairing obligation](../1-in-progress/hb-native-square-residual-mellin-value.md)
is parameter regularity of the actual quotient integral, to identify its
physical value with the constructed continuation. The complete differential
cutoff channels, original outgoing response, physical advanced/adjoint
pairing, source nonvanishing, and independent extinction remain required.
