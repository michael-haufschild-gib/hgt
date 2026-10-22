# HB: source-derived rapid decay of the complete nonconstant native cusp mass

- **ID:** HB-QNCD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [native cusp-mode coercivity](hb-native-cusp-mode-coercivity.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticNativeCuspComparison.lean`

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.
This theorem removes an assumed upper-cusp value from the comparison for the
constructed native angular responses. Derivative products, the complete
physical boundary current and extinction remain open.

## Exact source-derived bound

For either original response branch b and original Xi occurrence q, let c_n
be the literal period-one response coefficient, f_n its full forcing
coefficient, u_n=|c_n|^2, and L_n=(2*pi*n)^2. For every N in Nat, the source
produces Y>=4 and C_N>=0 such that, for every nonzero integer n and y>=Y,

```
u_n(y) <= u_n(Y)*exp(Y-y) + (C_N/L_n)*y^(-(2*N+4)).
```

No modal boundary condition is supplied. All derivative, forcing and native
admission inputs are discharged by HB-QNCM. The cusp height can depend on
q, b and N; the original spectral parameter and common physical clock do not
change.

## Proof without an upper boundary premise

Put p=2N+4. The literal source gives |f_n|^2/y^4<=C*y^-p uniformly in n.
Choose Y=max(4,coercivityHeight(q,b),p+1). For n!=0, L_n>=2. The barrier

```
b_n(y)=u_n(Y)*exp(Y-y)+(2*C/L_n)*y^-p
```

satisfies b_n''<=L_n*b_n-C*y^-p. Indeed its exponential term has second
derivative equal to itself, while
p*(p+1)/y^2<=1 and 2/L_n<=1 control the power term. The original source
inequality u_n''>=2|c_n'|^2+L_n*u_n-|f_n|^2/y^4 gives
(u_n-b_n)''>=L_n*(u_n-b_n).

Native admission proves integral_Y^infinity u_n/y^2 finite. For every
positive epsilon and every T there must therefore be a B>=max(Y,T) with
u_n(B)<=epsilon*B. If not, epsilon/y would be dominated by the integrable
u_n/y^2 throughout a tail, contradicting divergence of the inverse function.

On [Y,B], v=u_n-b_n-epsilon*y has nonpositive endpoints and v''>=L_n*v.
A positive interior maximum would have v''<=0, contradicting L_n>0.
If u_n(y)>b_n(y), take epsilon=(u_n(y)-b_n(y))/(2*y) and B>=y; the finite
comparison then contradicts that same positive gap. Thus u_n<=b_n.
This replaces the upper-boundary assumption by the original native norm.

## Complete summation and retained mean

Define U_b(y)=sum_(n!=0)u_n(y). Parseval supplies summability of all initial
masses. The integer inverse-square series admits the complete forcing bound,
without evaluating the series numerically or truncating its modes. Hence

```
U_b(y) <= U_b(Y)*exp(Y-y)+C_N*y^(-(2*N+4)),
y^r*U_b(y) -> 0                      for every real r.
```

The exact decomposition is

```
responseMeanSquare(q,b,y) = u_0(y)+U_b(y).
```

Consequently the difference between the original native slice mass and its
retained zero-mode mass decays with every real polynomial weight. The native
homogeneous mean coefficients have not been set to zero.

## Public Lean interface

- `nativeMode_cusp_bound`: source-derived comparison for every nonzero mode.
- `nonconstantMass`: sum of all nonzero original modal masses.
- `nativeMass_decomposition`: full slice mass equals zero mode plus that sum.
- `nonconstantMass_cusp_bound`: complete summed comparison.
- `nonconstantMass_weighted_tendsto_zero`: every real polynomial weight.
- `nativeMass_remainder_weighted_tendsto_zero`: the same limit for the full
  native slice minus its original zero-mode mass.

## Remaining physical interface

For the actual tested vertical current, weighted response/derivative products
and the full cusp boundary finite part remain. A direct next proof tests the
classical PDE for R_perp=R-mean(R), with forcing F_perp=F-mean(F), by a squared
real compact height multiplier m. Finite periodic integration by parts gives

```
integral |grad(m*R_perp)|^2 + Re(alpha)*integral m^2*|R_perp|^2/y^2
= integral (m')^2*|R_perp|^2
  - Re integral m^2*F_perp*conjugate(R_perp)/y^2.
```

The paper identity retains the weight-gradient error and signed source work.
Taking m=y^r with lower and receding upper cutoffs should use this leaf's mass
decay and the literal forcing bound to produce weighted gradient admission.
That cutoff limit has not been formalised here. It may avoid transferring
completed gradient representatives before obtaining the estimate. Weighted
integrability alone is not pointwise decay; the endpoint-limit argument must
also control the actual current derivative or a trace.

The zero-mode products, differentiated test, source-work periods, changing
metric weights, independent channels and remaining physical faces remain in
the complete action. This leaf proves no finite-clock invariance and no
left-QNM extinction.

## Verification

All six public declarations passed together in scratch Lean at default limits.
The exact isolated leaf audit passed in 43 seconds using cached dependencies.
Source SHA256: `3a1955a582f89e686f5a79c3ed04e78640c97d664baa93b50890b348fe5f334a`. Matching artifacts were published to the
local cache; no dependency or umbrella build was run. No heartbeat, depth or transparency
settings are raised; no computations or additional axioms are introduced.


Final verification: all six public API rows, the single umbrella import,
unchanged audited source hash and audit-directory cleanup were verified.
All owned Lean and search processes completed. Index refresh covered three
changed files; lint first reported stale API/OVERVIEW generation. A second
refresh covered one new change. Final `lint --check-generated` failed solely
on the then-unreachable
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarJetQuadraticEinstein`.
No global lint success is claimed and no unrelated unfinished source was
changed. The exact new leaf audit passed. Log:
`formal/.lake/hb-extinction-scratch/native-cusp-comparison-final-lint.log`.

## Successor

[HB-QNCE](hb-native-weighted-cusp-energy.md) now derives polynomially weighted
integrability of the complete native nonconstant derivative energy from this
mass decay and the original forced equation. Its independent gradient Parseval
restores the native zero-mode derivative. Exact leaf audited at default limits.
The next unresolved source step is upper-current trace control with every
signed test/source contribution retained.
