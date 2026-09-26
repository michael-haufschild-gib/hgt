# Signed cold-aperture / degree profile of the literal theta source

- **Owner:** root; independent of other agents' aperture logs.
- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean), [BRIDGE]; no global novelty claim.
- **Mission:** unconditional proof or falsification of RH remains open.
- **Result:** exact incoming profile and a literal-theta obstruction to global all-degree aperture convexity.

## Exact statements

Let `Phi=thetaCuspFullSource`, `A_j=j+1/2`, and

`M_j(lambda)=integral_(0,infinity) x^(2j) exp(lambda*x^2) Phi(x) dx`,
`q_j(lambda)=(M_(j+1)(lambda)/M_j(lambda))/A_j`,
`S_j(lambda)=q_j(lambda)-2*q_(j+1)(lambda)+q_(j+2)(lambda)`.

For every `u>0`, set `L_n=(n+1/2)/u`. Then

`L_n^4*S_n(-L_n) -> (d^3/dy^3) log(Phi(sqrt(y)))|_(y=u)`.

This is `ThetaColdCorner.tendsto_scaled_theta_curvature`. All literal source inputs are proved.
At `u=9`, the limit is strictly negative. Therefore

`eventually n, S_n(-(n+1/2)/9)<0`.

`eventually_negative_theta_diagonal` has no input hypotheses. The closed theorem
`not_all_degree_aperture_curvature_nonnegative` excludes `forall lambda<=0, forall j, S_j(lambda)>=0`.

**Scope:** global all-degree aperture convexity is false for actual theta. Degree-zero GABTC and RH
remain unresolved. This is neither an off-line Xi zero nor an RH falsification.

## Why the previous endpoint argument fails

Fixed-degree cold positivity and large-degree positivity on each compact aperture interval do not
control the corner where degree and cold aperture grow together. A finite section's cold starting
point depends on its terminal degree; there is no common compact interval containing all starts.
The literal theta source now exhibits the missing negative incoming profile.

The original inference is isolated in the root failed-route card:
`../5-failed/rh-global-all-degree-aperture-convexity-root-2026-09-26.md`.
Other agents' parent cards and logs were not edited.

## Dependency-closed paper proof

### 1. Exact Gaussian averages and joint concentration

Let `G_(L,j)=Gamma(A_j)/(2*L^A_j)` and
`B_j(H)=integral_(0,infinity) x^(2j) exp(-L*x^2) H(x) dx / G_(L,j)`.
The existing exact Gamma integral gives mass one and `G_(L,j+1)=(A_j/L)*G_(L,j)`.
For the squared coordinate `Y=x^2`, the exact centered second moment is

`E[(Y-u)^2]=(A_j/L-u)^2+A_j/L^2`.

For bounded continuous `f` on `[0,infinity)`, continuity and a global bound give, for every
`epsilon>0`, a constant `C>=0` with

`|f(y)-f(u)| <= epsilon+C*(y-u)^2`.

Integrating this inequality proves concentration whenever `1/L ->0` and `A_j/L ->u`.
In particular, `B_j(H) -> H(sqrt(u))` for every bounded continuous `H`.
No differentiated saddle asymptotic is used.

### 2. Exact falling Euler identities

Write `E=(x/2)d/dx`. Differentiating `x^(2j+1) exp(-L*x^2) H(x)` and integrating gives

`A_j*(B_(j+1)(H)-B_j(H))=B_j(EH)`.

The boundary primitive vanishes at zero and infinity. Bounded `H` and `EH` give integrability.
Define

`H0=Phi`,
`H1=x*Phi'/2`,
`H2=(x^2*Phi''-x*Phi')/4`,
`H3=(x^3*Phi'''-3*x^2*Phi''+3*x*Phi')/8`.

These satisfy `H_(k+1)=(E-k)H_k`. Exact algebra then gives

`(A_j)_k * Delta^k B_j(Phi)=B_j(H_k)`, `k=1,2,3`,

where `(A)_k=A*(A+1)*...*(A+k-1)`. Every `H_k` is continuous and bounded by the literal
source's global Schwartz derivative bounds. Apparent square-root derivative singularities at zero
have cancelled against the shifted moment weights; no analytic extension at zero is needed.

### 3. Exact curvature quotient and its limit

Set `F_r=B_(j+r)(Phi)`, and

`J0=F0`, `J1=L*(F1-F0)`, `J2=L^2*(F2-2*F1+F0)`,
`J3=L^3*(F3-3*F2+3*F1-F0)`.

The moment/Gamma dictionary gives `q_(j+r)(-L)=F_(r+1)/(L*F_r)`. Common-denominator algebra gives

`L^4*S_j(-L) = [J0^2*J3-3*J0*J1*J2+2*J1^3
                 +L^-1*(J0*J1*J3+J1^2*J2-2*J0*J2^2)]/(F0*F1*F2)`.

Along `L_n=A_n/u`, concentration and the falling Euler identities give

`J0 -> Phi(sqrt(u))`, `Jk -> H_k(sqrt(u))/u^k`, `k=1,2,3`.

Each `F_r` tends to the same strictly positive source value. The denominator stays nonzero, and
the explicit `L^-1` remainder vanishes. The limit is

`[Phi^2*H3-3*Phi*H1*H2+2*H1^3]/[u^3*Phi^3]`, evaluated at `x=sqrt(u)`.

Exact source logarithmic derivative identities identify this with `(log(Phi(sqrt(u))))'''`.

### 4. Explicit negative region for the literal profile

Let `ell=log Phi`, `s=pi*(exp x)^2`. Existing complete higher-tail bounds and exact first-atom
formulas yield, for `x>0`,

`ell' <= -2*s+33/5`,
`ell'' >= -4*s-801/100`,
`ell''' <= -8*s+78`.

For `x>=3`, `exp x>=1+x>=4` and `pi>3` give `s>48`. Also
`4*x^2-6*x+3>=2*x^2`. Hence

`x^2*ell'''-3*x*ell''+3*ell' < -114*x^2+28*x+20 < 0`.

The exact coordinate identity is

`8*x^5*(log(Phi(sqrt(y))))'''|_(y=x^2)=x^2*ell'''-3*x*ell''+3*ell'`.

Thus the literal profile is negative for every `y>=9`. Choosing `u=9` in the exact limit proves
the eventual actual-theta negative diagonal, and therefore the closed global-convexity no-go.

## Independent positive-source falsifier and sharp survivor

`GaussianMomentColdDegreeCorner` already gives the positive even density
`exp(-x^2)*(1+(64/105)*x^6)`. Its normalized moment ratios obey the same cooperative curvature
flow, have both separate positive endpoint regimes, but have curvature exactly `-7/40` at
`lambda=-1`, degree zero, and a negative natural cold/degree diagonal.

For the full family `exp(-x^2)*(1+a*x^6)`, with `a,c,A>0`, exact sign classification is

`S>=0 iff (2*c^3/(a*(A+2)*(A+3))-(7*A+13))^2 >= 9*(5*A^2+18*A+17)`.

The joint profile `A=c*u` is

`c^4*S -> 6*a*(1-7*a*u^3+a^2*u^6)/(1+a*u^3)^3`.

This surrogate falsifies the endpoint inference independently; it is not used as a theta premise.
Its 23 public theorem audits and named build pass.

## Lean certificates

All modules are under `formal/GaloisForLFunctions/RHTower/` and wired into `RHTower.lean`.

| Module | Exact content | Public theorem audits |
|---|---|---:|
| `GaussianMomentColdDegreeCorner` | Positive-source counterexample, sharp sign classification | 23 |
| `ThetaColdDegreeCornerLogJet` | Literal profile sign and coordinate derivative identity | 4 |
| `ColdGammaShapeConcentration` | Exact moments, joint concentration, bounded-jet shape shift | 17 |
| `SourceFallingEulerMomentShift` | Original-source Euler integration and finite differences | 8 |
| `ThetaColdDegreeEulerJets` | Literal bounded jets, exact three differences, log dictionary | 12 |
| `ThetaColdDegreeCornerLimit` | Full signed limit and unconditional actual-theta no-go | 19 |

Every named build passes. All public theorem axiom reports contain only `propext`,
`Classical.choice`, `Quot.sound`. Current-turn 39-theorem audit:
`/tmp/rh-theta-cold-diagonal-axioms.log`; final leaf build:
`/tmp/rh-theta-cold-diagonal-build.log`. Global lint status is recorded in the root fact log.
No numerical experiments or git commands. Publication novelty has not been claimed or certified.

## Whole-route decision

Retire global all-degree nonnegative curvature as an input to the cooperative maximum-principle
producer. The strongest positive survivor is the exact signed incoming profile, now Lean-closed.
Any replacement producer must account for its signed influence on low degree. Before spending more
work on degree-zero GABTC, audit whether it closes the actual RH route's missing global sign or only
an auxiliary inequality. RH remains the unachieved objective.
