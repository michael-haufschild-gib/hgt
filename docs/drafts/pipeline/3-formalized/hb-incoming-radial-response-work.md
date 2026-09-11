# HB: actual incoming radial response work

- **ID:** HB-RRW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [active source-contact attack](../1-in-progress/hb-source-contact-spin-two-balance.md)
- **Statement:** The original incoming SV-SV radial clock-mass coefficient is two actual angular divergences minus explicit full-response work, whose local Q² multiplier is nowhere zero on the Xi divisor.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Source equations and exact identity

For an actual Xi copy q, put rho=q.1, s=rho-2, t=-rho-1, p=st,
lambda=rho(rho-1)=2-p, alpha=(2s+1)(2s+2), beta=(2t+1)(2t+2).
Let Q be the complete half-square of the literal scalar, E its complex-bilinear
gradient energy, and A,B the constructed full angular responses on the two
physical branches. The source supplies

```
Delta A = alpha(A+Q),       Delta B = beta(B+Q),
Delta Q = 2lambda Q+E,      |grad Q|_bilinear² = 2QE.
```

The original incoming current supplies these fixed coefficients:

```
ds=s(s-1)/4,  dt=t(t-1)/4,
rs=-2s dt[(t+1)²-st]+(st/3)beta,
rt= 2t ds[(s+1)²-st]-(st/3)alpha,
rQ=2ds dt(s-t)(1-st).
```

Define

```
G = beta grad A (B+Q)-alpha grad B (A+Q),
J = Q[rs grad A+rt grad B+(2rQ/3)grad Q],
CQQ = rs alpha+rt beta+(4lambda/3)rQ,
W = rs alpha Q A+rt beta Q B+CQQ Q²,
F = -(p/3)y² div G+y² div J-W.
```

Then the exact original radial clock-mass coefficient satisfies

```
y² clockCoefficients(q,a,b,w,1,0) = (a²b²/16) F(w).
```

Both full responses and both angular currents remain. No cusp power substitutes
for a response, no boundary current is discarded, and no positive norm replaces
the complex-bilinear gradient.

## Dependency-closed proof

Differentiate J by the actual Fréchet product rule. Its divergence is

```
y² div J = y²[rs grad A.grad Q+rt grad B.grad Q
                  +(2rQ/3)grad Q.grad Q] + W+(2rQ/3)QE.
```

Using the scalar square identity combines the last term with the gradient-square
term into rQ times the complete gradient square. Substitution in the previously
proved original radial angular-exchange identity gives F. Smoothness and all
three forced equations follow from the constructed literal fields; no equation
or regularity premise is supplied by the caller.

Exact polynomial factorization gives

```
CQQ = p(s-t)(p³+25p²-28p+20)/6.
```

The Xi strip gives Re(p)=2+Re(rho)(1-Re(rho))+Im(rho)²>2.
Also s-t=2rho-1 is nonzero because every Xi occurrence has nonzero imaginary
part. Write z=p-2=x+iy. Its cubic is z³+31z²+84z+72. If it vanished, its
imaginary part would give y(3x²+62x+84-y²)=0. For y=0 the real part is strictly
positive. Otherwise eliminate y² from the real part to obtain
`-8x³-248x²-2090x-2532=0`, impossible for x>=0. Thus CQQ is nowhere zero.
This does not prove W or the integrated current nonzero: the response and face
terms can compensate it.

## Original-clock horizon contributions

For every nonnegative physical translation h, the already defined exponential
translation moment, at the unchanged common rate -6, now satisfies

```
y² clockMoment(-6,h,incomingCurrent(q,a,b,r=1,.,w,radial))
  = h exp(-6h) (a²b²/16) F(w).
```

The moment uses the original `clockDifference`; it is not claimed to be the
complete nonlinear action or its ordinary translation difference.

For every original terminal time V, the unshifted horizon integral is

```
y² integral_0^V incomingCurrent(q,a,b,1,v,w,radial) dv
  = clockMass(V) (a²b²/16) F(w)
    + y²[Cmixed (3 clockMass(V)+onsetSquare(V)/2)
          + Cenergy clockEnergy(V)].
```

Here Cmixed and Cenergy are the original row-one mixed and derivative-energy
clock coefficients. The onset endpoint and derivative energy are retained
exactly. Angular divergences remain unevaluated; this is time integration at a
fixed angular point, not the complete physical boundary passage.

## Remaining extinction interface

The complete reduced causal cokernel obeys C=-Sigma Eclock, with Sigma>0 and
Eclock>=0. A source-derived identity Re(Cphys)>=0 after actual physical-action
identification would therefore force Eclock=0. Another sufficient target is an
exact complete-action decomposition Cphys=L(Z)+R with a proved source identity
Z=0 and a source-derived estimate `abs(Re R)<=kappa Sigma Eclock`, for one fixed
`0<=kappa<1`. Substitution gives Sigma Eclock<=kappa Sigma Eclock and hence
extinction. These are requirements on the missing interface, not new assumptions
or proved estimates.

This leaf supplies the exact radial response work that such a comparison must
include. It does not establish its integrated angular boundary cancellation,
control the complete independent SS/SV/VV channels, eliminate changing-weight or
mixed-correction boundary terms, or identify the final left-QNM projection with
a vanishing source current. The earlier retained spin-two/native-contact law and
this radial response-work law must both survive that comparison.

## Search-guided attacks

Corpus hybrid and deep/method searches returned the actual forced equations,
original incoming angular exchange, and native Green candidates. Generated
ingredient sets did not certify applicability. The 300-second follow-up reported
partial text/source retrieval, a semantic deadline, and pending compiler metadata.

A broad newest-first dilation search found
[Deng–Yang, Dilation-Covariant Hankel Pencils](https://arxiv.org/html/2609.06661v1)
(September 2026). Its finite recurrence method presupposes covariance and a
sparse Mellin spectrum. It cannot supply the missing covariance of the complete
theta-driven nonlinear response from the finite principal powers.

Broad virial, boundary, dissipation and reciprocity searches also found
[Chung–Sudhir–Wang, Perturbative Dissipation in Minimal Warm Inflation](https://arxiv.org/html/2608.08345v1)
(August 2026). Section 2.2 reduces a leading derivative-coupling friction coefficient
to endpoint current correlations, then requires the relevant boundary terms and
long-time correlation to vanish. For HB the surviving test is a full source-current
identity with evaluated endpoints; finite-clock onset and cusp contacts cannot
be removed by that argument. No statement from either paper is imported into Lean.

## Lean certificate

Module: [ThetaCuspHawkingBMQuarticResponseWork.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResponseWork.lean).
Namespace: `RHTower.D4BMQuarticResponseWork`.

Public theorems:

- `incoming_radial_mass_reduced_source_work`
- `incoming_radial_horizon_clockMoment_source_work`
- `incoming_radial_horizon_finite_source_work`
- `squareWorkCoefficient_factor`
- `physical_rate_product_re`
- `squareWorkCoefficient_ne_zero`

The four accompanying definitions name the original coefficients, transferred
current, remaining local coefficient, and full-response work. Scratch
`lake env lean /tmp/hb-quartic-response-work.lean` passed without diagnostics.
Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseWork`
passed without warnings in 100 seconds against cached imports; no dependency or
umbrella build ran. No heartbeat, recursion-depth, or transparency override was
added. The umbrella imports the leaf once.

Audited source SHA-256:
`fff02f940650480f3348d087656b672f274bb63b4b45b696fd0fa502564f1385`.
Source and cached artifacts were verified before the isolated audit directory
was removed. Complete extinction and RH remain open.

All ten public declarations appear once in the regenerated API; the umbrella
import, eleven local links across the two task cards, and source SHA were checked.
Whole-tree `scripts/formal_tools.py lint --check-generated` remains non-green:
eight other worktree modules are unreachable, and generated gaps/overview files
became stale during concurrent work after regeneration. No lint error names this
leaf. All owned Lean/Lake/search processes completed.
