# HB independent-frequency endpoint radial inverse

- **Stage:** 3-formalized
- **Goal:** unconditional closed Lean proof/falsification of RH through HB; not achieved.
- **Scope:** actual retained-source radial response, with independent transform frequency and genuine horizon/AdS endpoints.

## Proof chain and result

Literal theta cusp → Xi occurrence → retained spin-two source → original causal
response and left-QNM pairing → independent Hawking-clock extinction → RH.

The independent-frequency radial construction is closed: actual homogeneous
solutions and their derivatives, nonzero physical Wronskian, exact original
source profile, absolute convergence of both endpoint integrals, the forced
physical equation, finite ingoing amplitude, zero AdS value, and vanishing
endpoint Wronskian phases. The original-radius equation uses actual derivatives
of this response and the original smooth-onset current's time integral.

The result holds in `Re(w) > abs(Im chi)`. The source's Xi occurrence, physical
rate, both angular fields, and smooth onset remain fixed as w varies. This is
a radial inverse at a supplied angular parameter. It does not identify the
full angular differential operator with that parameter or construct the full
time-retarded Einstein response.

## Exact operator and basis

Write `f=r²-1` and `z=1-r^(-2)`. The coordinate derivatives are `2/r³` and
`-6/r⁴`. At angular value `lambda=1/4+chi²`, the original wave expression is

`w²*u-f²*u_rr-2*r*f*u_r+(f/r²)*lambda*u = -4*z*L_w,chi(u)`,

where

`L_w,chi(u) = z*(1-z)*u_zz+(1-3*z/2)*u_z-w²*u/(4*z)-(1/4+chi²)*u/4`.

This is exactly the corpus's `D4BMPhysicalMaster.radialJet (I*w) chi`.
The original current multiplier `-2*f/r³` becomes `C_hat/(2*r)` on its
right-hand side. The coordinate and source multipliers are proved together.

Set

- `a=1/4+w/2+I*chi/2`, `b=1/4+w/2-I*chi/2`, `c=1+w`;
- `H=z^(w/2)*2F1(a,b;c;z)`;
- `V=z^(w/2)*(1-z)^(1/2)*2F1(c-a,c-b;3/2;1-z)`;
- `p=z*sqrt(1-z)`;
- `C=Gamma(c)*Gamma(1/2)/(Gamma(c-a)*Gamma(c-b))`.

Every relevant Gamma argument has positive real part in the chamber, and
`c-a-b=1/2`. The analytic series, power, and coordinate derivatives are
actual derivatives. Their complete dressed jets satisfy the original L.

Gauss summation gives `H→C` at AdS. The differentiated square-root Abel limit
gives a finite limit for `sqrt(1-z)*H'`. The independently constructed V has
`V/sqrt(1-z)→1` and `sqrt(1-z)*V'→-1/2`. Abel's identity and these actual limits
therefore give

`p*(H*V'-H'*V) = -C/2 ≠ 0`

throughout the physical interior. The Wronskian is attached to the constructed
solutions, rather than asserted from a denominator definition.

## Exact source and full-endpoint convergence

For fixed physical rate s, amplitude a0, original covectors J and K, and fixed
smooth-onset frequency factor

`T=1/(w-2*s)+onsetCorrection (2*s) w`,

the original current's actual time transform is

`C_hat(z)=z^(w/2)*(1+sqrt(1-z))^(2*s-w)*a0²*(A0*J+(1-z)*B0)*T`,

where `A0=(5*s²+15*s+4)/4` and
`B0=s*(s-1)*((s+2)²*J-K)/4`.

This identity is proved from the literal quadratic current, compact envelope,
and tortoise coordinate. Both covectors and the onset correction are retained.
The factor after `z^(w/2)` is continuous and bounded on the complete `[0,1]`.

The horizon Gauss coefficients are absolutely summable since their gap is
1/2. Hence `|H*C_hat| ≤ C1*z^Re(w)` on `(0,1)`.

For the outer series, the proved coefficient asymptotic has gap `-w` and
implies `|c_n| ≤ C2*n^(Re(w)-1)` for positive n. Choose
`N=ceil(Re(w))`, so `Re(w) ≤ N < Re(w)+1`. Comparison with
`binomial(n+N-1,N-1)` and its exact geometric sum gives

`|2F1(c-a,c-b;3/2;1-z)| ≤ C3/z^N`.

Consequently `|V*C_hat| ≤ C4*z^(Re(w)-N)`. Both bounds are integrable across
the full interval. This argument retains resonant frequencies: neither a
nonresonance premise nor an Euler connection formula is needed.

## Constructed response and endpoint conditions

Define the genuine endpoint moments

`A(z)=integral_0^z H(t)*C_hat(t)/(-C) dt`,
`B(z)=integral_z^1 V(t)*C_hat(t)/(-C) dt`,

and `u=V*A+H*B`. Absolute convergence is proved before applying FTC. The first
moving-endpoint terms cancel; the second derivative retains the Wronskian
source term. Thus

`L_w,chi(u)=sqrt(1-z)*C_hat(z)/2`.

Composition with `z(r)` proves both actual radius derivatives and the original
forced radial wave equation with its `-2*f/r³` current multiplier. Specializing
s,J,K,T to the fixed Xi source identifies its right-hand side with the
already constructed half-line smooth-onset Laplace integral.

Both moments extend continuously to `[0,1]`. At AdS, `V→0` and `B→0`, so
`u→0`. At the horizon, the stronger estimate `A=O(z^(Re(w)+1))` combines with
the outer factor bound to show

`u/z^(w/2) → B(0)` and `u→0`.

The positive exponent is `Re(w)+1-N>0`; the integer ceiling loses no admitted
frequency. The actual Wronskian phases equal `(-C/2)*A` and `(-C/2)*B`, so the
ingoing phase vanishes at the horizon and the outer phase vanishes at AdS.

## Lean surface and audit

All modules use prefix `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplace`
and namespace `RHTower.D4BMLaplaceRadial`.

| Module suffix | New public theorems |
|---|---:|
| Parameters | 8 |
| Coordinate | 4 |
| GaussFactors | 5 |
| PowerJets | 3 |
| Dressing | 2 |
| OuterFactor | 2 |
| HorizonEndpoint | 2 |
| PowerLimits | 4 |
| Solutions | 4 |
| BoundaryValues | 6 |
| BoundaryDerivatives | 2 |
| Wronskian | 3 |
| CoefficientGrowth | 1 |
| SumBounds | 2 |
| SourceProfile | 3 |
| RetainedSource | 1 |
| KernelBounds | 2 |
| SourceAdmission | 3 |
| EndpointGreen | 4 |
| GreenBoundary | 4 |
| OriginalRadialInverse | 3 |
| GreenPhases | 2 |

All 22 development leaves passed `lake env lean` in scratch. All 22 exact
canonical `lake build <module>` audits passed in an isolated cache-only package;
each compiled exactly its requested new leaf. No dependency, full, or umbrella
build ran. Source bytes match the audit copies; all 44 installed olean/ilean
artifacts match the audited output. All 22 modules are wired once into RHTower.

One scratch `lake env lean` audit checked exactly the 70 new public theorem
axiom sets. Each uses only `propext`, `Classical.choice`, and `Quot.sound`;
earlier theorem batches were not re-audited. No added axiom, proof gap,
numerical certificate, or computation was used. Scoped whitespace and source
checks passed. The declaration/search indexes were refreshed; repository-wide
`lint --check-generated` passed with existing large-file warnings. All owned
Lean/Lake jobs exited; the owned scratch and cache-only audit package were
removed.

## Remaining original causal problem

Assemble the radial inverse through the actual global angular operator and
admit the source's principal cusp powers together with its native remainder.
The corpus already identifies the retained gradient term through
`D_ang J = 2*(s+1)*(s+2)*J+2*K`. This relation must enter the original angular
operator calculus; evaluating J,K at a point does not implement that calculus.
Uniform frequency control, time-causal inversion, constrained Einstein
reconstruction, other sectors, and the original left-QNM action pairing
remain required. Radial Wronskian phases are not that full physical pairing.
Independent Hawking-clock extinction and RH remain unproved.

No numerical experiment was used. The frontier map is read-only and was not
edited by this work. No new route-independent restriction was established
that requires an additional STATUS ledger entry.
