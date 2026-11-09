# Positive theta sources with finite endpoint-jet surgery

- **ID:** positive-theta-finite-jet-surgery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; finite-divisor detection beyond finite endpoint data.
- **Statement:** For every finite endpoint jet order, positive strip width, and positive relative tolerance, a strictly positive even smooth theta source within that tolerance of the actual source has transform equal to an entire finite rational modification of actual `xi`, preserving those endpoint jets and introducing off-line zeros within that width. Every finite literal prime deletion remains positive on the positive half-line.
- **Contribution count:** One (#15), including the uniform division estimate, finite-source construction, and prime-deletion neighborhood.
- **Novelty boundary:** Arbitrary endpoint jets under finite rational surgery are proved. Positive compact theta-source surgery, including positivity after all finite prime deletions, is also known, but changes the divisor beyond a finite rational modification. Positivity under one real zero division is known.

## Proof

Use `n=2K+2` actual donor pairs with ordinates in `[L,L+ell]`. The existing perturbation is `epsilon q^(n-1)/product(q+a_j)`, where `q=s(s-1)`, `a_j=gamma_j^2+1/4`, and `epsilon=O(ell^n L^(2-n))`.

Let `k` be the positive even theta source. There is a universal `B>=1` such that every real zero-division operator `T_gamma f(x)=gamma integral_0^infinity sin(gamma t) f(|x|+t) dt` satisfies `|T_gamma f(x)|<=B |gamma| C k(x)` whenever `|f|<=Ck`. On `|x|>=1`, the corpus's relative tail estimate gives this with constant `2 thetaEnvelopeUpper/(pi thetaEnvelopeLower)`. On `|x|<=1`, bound the sine by one, the tail integral by `integral k`, and `1/k` by its compact maximum. These constants are independent of `gamma` and donor separation.

Put `S_gamma=T_gamma/gamma^2`. At a transform zero, its transform is division by `gamma^2-z^2=q+a_gamma`, with `q=-z^2-1/4`. Its relative operator norm is at most `B/L` for `gamma>=L`. Since `gamma<=L+ell<=2L` and `L>=16`, `a_gamma<=5L^2`. Hence `I-a_gamma S_gamma` has relative norm at most `(1+5B)L`.

Start with `S_gamma k` for the last donor and apply `I-a_j S_gamma_j` for the other `n-1` donors. The resulting real even smooth source `u` has every exponential moment and satisfies
`uhat(z) product(gamma_j^2-z^2)=XiC(z) q^(n-1)`.
At each step, the next distinct positive donor remains a transform zero: evaluate the preceding identity there; all prior denominator factors are nonzero. Thus every division is legitimate and smooth. With `R=1+5B`, its relative bound is
`|u|<=B R^(n-1) L^(n-2) k`.

For the centered donor parameters in the finite-surgery construction, `A-w=L^2+1/4` and `w<=3L ell/2`. Consequently
`epsilon<=2*3^n ell^n/L^(n-2)`.
Choose
`0<ell<=min(delta/8,1/8,tau/(2*3^n B R^(n-1)))`, where `0<tau<=min(eta,1/2)` and `eta>0` is arbitrary.
Since `ell<=1` and `n>=2`, the product of `epsilon` and the relative bound for `u` is at most `tau`. Therefore `f=k-epsilon u>=k/2>0` and `|f-k|<=eta k` everywhere. It is even and smooth and has every exponential moment. Thus the finite-divisor deformations occur arbitrarily close to the actual theta source in the relative uniform norm.

The transform of `f` is the entire rational surgery with numerator `D(q)-epsilon q^(n-1)`. The previous root-confinement theorem places all replacement roots off the line within depth `delta`; the monomial difference retains endpoint derivatives through order `n-2`. Reflection, reality, and vertical normalization follow from the same exact multiplier. This closes every analytic input on paper.

The existing `ThetaEndpointPositiveDeformation` treats sources keeping an assumed off-line divisor. It does not supply these unconditional critical donors or the height-uniform positivity threshold needed to plant new off-line zeros.

Every finite literal prime deletion can remain positive simultaneously. Put `G=1+thetaCuspHigherAtomDominationWeight`; first-atom domination gives `k<=G a_1`. The exact shift identity gives `d^(-1/2) k(x+log d)<=G a_d(x)` on `x>=0`. Distinct prime subsets have distinct products, so summing these bounds yields `|D_S g(x)|<=C G k(x)` whenever `|g|<=Ck`, uniformly over finite prime sets `S`. Since `D_S k>=a_1` and `k<=G a_1`, the relative ball `|f-k|<=k/(2G^2)` satisfies `D_S f>=a_1/2>0`. Reduce the surgery tolerance to this radius. This strengthening belongs to the same contribution.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`.

| Module | Certificate |
|---|---|
| `UniformRealZeroDivisionBounds.lean` | `exists_uniform_real_zeroDivision_bound`, `realZeroResolvent_bound` |
| `FiniteDonorThetaSources.lean` | `finiteDonorThetaSource_transform`, `finiteDonorThetaSource_uniform_bound` |
| `UniformThetaPrimeDeletionBounds.lean` | `thetaPrimeDeletion_lower_of_relative_ball` |
| `PositiveThetaFiniteEndpointSurgery.lean` | `positive_theta_sources_preserve_finite_endpoint_jets` |

The capstone has only the arbitrary natural jet parameter and positive width/tolerance parameters. It supplies actual distinct critical donor zeros, a real even smooth source with every exponential moment, strict positivity and relative closeness, simultaneous positivity after every finite prime deletion on `x>=0`, the exact entire transformed function, both symmetries, endpoint derivatives through order `2K`, vertical multiplier normalization, and off-line replacement zeros with the stated confinement.

All four modules and the strengthened `ArbitraryEndpointJetsSurviveFiniteSurgery.lean` pass direct `lake --old env lean` audits without warnings. The capstones use only `propext`, `Classical.choice`, and `Quot.sound` transitively. All four new modules are umbrella-wired.

The positive survivor is a uniform relative neighborhood preserving every finite prime deletion, together with explicit finite-divisor surgery inside that neighborhood. These source-positivity and finite-jet constraints do not detect finite exceptional divisors. No Dirichlet-series representation of the modified function is asserted. RH and the original obstacles remain open.
