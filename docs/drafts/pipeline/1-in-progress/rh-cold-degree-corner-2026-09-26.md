# Cold aperture / degree corner — root research

- **Owner:** root; separate from other agents' aperture logs.
- **Stage:** 1-in-progress.
- **Type:** [BRIDGE], hostile test of an existing producer mechanism.
- **Parent target:** unconditional all-degree theta moment sign; RH remains the goal.

## Frozen claim under attack

The composite-balance card proposes that fixed-degree cold positivity, eventual large-degree
positivity uniformly on every compact aperture interval, and the cooperative affine-Gamma
curvature flow exclude entrance from degree infinity. Test this implication in actual positive
Gaussian-polynomial moment sources before relying on it for theta.

**Scientist's question:** are the two endpoint limits controlling the same boundary? They do not
cover the corner where the degree and the cold aperture grow together. A finite section's cold
starting point depends on its terminal degree, so it is not contained in one fixed compact
aperture interval.

## Exact falsifier candidate

Use the positive even source

`f(x)=exp(-x^2)*(1+a*x^6)`, `a>0`.

Its half-line Gaussian-aperture moments at `lambda=-L` are

`M_j(-L)=Gamma(A)/(2*c^A)*(1+a*A*(A+1)*(A+2)/c^3)`,

where `A=j+1/2`, `c=L+1`. Consequently the Gamma-normalized ratio is exactly

`q_j(-L)=(c^3+a*(A+1)*(A+2)*(A+3))/(c*(c^3+a*A*(A+1)*(A+2)))`.

For fixed `j`, `c^4*(q_j-2*q_(j+1)+q_(j+2)) -> 6*a>0`.
For fixed compact positive `c` intervals the curvature is positive at sufficiently large degree.
Yet at `a=8/105`, `c=1`, the first three ratios are exactly
`7/4, 2, 19/10`, so their second difference is `-7/20`.
These are symbolic identities to verify, not numerical experiments.

The proposed positive survivor is the exact joint corner law. If `A/c -> u>0`, then

`c^4*S_j(-L) -> 6*a*(1-7*a*u^3+a^2*u^6)/(1+a*u^3)^3`.

It is the third derivative of `log(1+a*u^3)`, with a genuine negative interval between
`a*u^3=(7-3*sqrt(5))/2` and `(7+3*sqrt(5))/2`. This locates the missing incoming boundary rather
than declaring that no maximum principle exists. Paper algebra and Lean verification pending.

## Theta-specific continuation of the test

For a smooth positive source `Phi`, Gamma concentration suggests the general corner identity
`L^4*S_j(-L) -> (d^3/dy^3) log(Phi(sqrt(y)))|_(y=u)` when `(j+1/2)/L -> u`.
The literal theta tail has leading log profile `9*sqrt(y)/2-pi*exp(2*sqrt(y))`, whose third
derivative is negative at large `y`. This is a candidate falsification of global all-degree
aperture convexity, not yet a proof. It does not falsify the degree-zero GABTC conjecture.

## Plan and route gate

1. Verify exact positive-source moments, curvature numerator and corner sign classification.
2. Separate fixed-degree, compact-aperture and joint-limit quantifiers explicitly.
3. Attack the actual theta corner via source derivative bounds and Gamma concentration.
4. Audit the strongest survivor; formalize exact closed results without adding premises.

Do not infer a theta counterexample from the Gaussian-polynomial source. Do not infer RH or its
failure from any source-curvature result. The real next producer would need signed control of the
incoming corner or another arithmetic comparison, not the already proved finite-section law.
