# Theta Xi as a reflected Lévy dispersion and a three-dimensional spherical transform

- **Stage:** 3-formalized (paper identities formalized unconditionally in Lean; see `theta-levy-spherical-dispersion-duality-formalized.md`).
- **Status:** [PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]
- **Routes:** SQB and WS2.
- **Dependency:** The literal even completed-theta source `k`, its strict decrease on the positive ray, and the one-port renewal formula in [theta-renewal-phase-cosh-factorization.md](../../3-formalized/theta/theta-renewal-phase-cosh-factorization.md).
- **Scope:** An unconditional change of mathematical object. It does not locate complex Xi zeros.

## The two reflected jump exponents

Use the normalization of the [one-port spectral bridge](../../3-formalized/theta/theta-half-port-stieltjes-spectral-bridge.md):
\[
h(z)=\int_0^\infty k(x)e^{izx}\,dx,\qquad
\Xi(z)=h(z)+h(-z),\qquad
\omega(x)=-k'(x)>0\quad(x>0).
\]
Here `k` is even, positive, smooth, and super-exponentially decreasing on the positive ray. Set
\[
K(z)=\int_0^\infty\omega(x)(1-e^{izx})\,dx.                 \tag{1}
\]
The measure `ω(x) dx` is a finite positive jump measure of total mass `k(0)`. Integration by parts gives the **entire identities**
\[
\boxed{K(z)=-iz h(z),\qquad K(z)-K(-z)=-iz\Xi(z).}             \tag{2}
\]
Thus every nonzero Xi zero is exactly a complex equality of the two *reflected exponents* `K(z)=K(-z)`. On the real axis write
\[
B(u)=\int_0^\infty\omega(x)(1-\cos ux)\,dx>0\quad(u\ne0).
\]
The one-port phase-space point satisfies
\[
K(u)=B(u)-i\,\frac{u\Xi(u)}2,\qquad
u h(u)=\frac{u\Xi(u)}2+iB(u),\qquad
B(u)=\pi u\sigma(u^2)\quad(u>0).                              \tag{3}
\]
At a positive real Xi zero the point `K(u)` lies on the strictly positive real axis. Off-axis confinement is the distinct problem of excluding reflected exponent equality at nonreal `z`; positivity of `B` alone does not do it.

## One primitive is an infinitely divisible dispersion law

Evenness and smoothness give `k'(0)=0`, so `ω(x)/x` is bounded at zero and integrable at infinity. Define the finite positive measure and its entire even exponent
\[
d\nu(x)=\frac{\omega(x)}x\,dx,\qquad
G(z)=\int_0^\infty(1-\cos zx)\,d\nu(x).                       \tag{4}
\]
Differentiating under the integral and integrating by parts once more yields
\[
\boxed{G'(z)=\int_0^\infty\omega(x)\sin(zx)\,dx
             =\frac{z\Xi(z)}2,\qquad
        K(z)-K(-z)=-2iG'(z).}                                  \tag{5}
\]
For real `u ≠ 0`, `G(u)>0`. For every time `t>0`, `exp(-tG(u))` is the characteristic function of a symmetric compound-Poisson law: its rate is `t ν((0,∞))` and a jump has sign `±` with equal probability and positive magnitude distributed proportionally to `ν`. The characteristic function extends to an entire nowhere-zero function, and
\[
\frac{d}{dz}e^{-tG(z)}=-\frac{tz\Xi(z)}2e^{-tG(z)}.           \tag{6}
\]
Consequently the nonzero Xi divisor is precisely the common complex critical-point set of this entire characteristic-function semigroup. RH becomes a critical-point confinement claim for the **literal theta jump law**, rather than a claim that Xi itself is a positive spectral density. This distinction matters: a zero-free characteristic function can have nonreal critical points.

Equation (5) also gives a real-frequency weighted-area law, despite the sign changes of Xi:
\[
\boxed{\int_0^u v\Xi(v)\,dv=2G(u)>0\quad(u>0).}               \tag{7}
\]

## Spherical lift and quadratic size bias

Put `M=Xi(0)=2∫₀^∞k(x)dx=2∫₀^∞xω(x)dx`. On `ℝ³` define the radial probability density
\[
f_3(y)=\frac{\omega(|y|)}{2\pi M|y|},
\]
with the continuous value `-k''(0)/(2πM)` at the origin. Spherical integration proves
\[
\boxed{\int_{\mathbb R^3}e^{i\langle\xi,y\rangle}f_3(y)\,dy
 =\frac{\Xi(|\xi|)}M\quad(\xi\in\mathbb R^3).}               \tag{8}
\]
Equivalently, let the radius have probability law
\[
dP_R(x)=\frac{2x\omega(x)}M\,dx
       =\frac{2x^2}M\,d\nu(x).
\]
Then `Xi(z)/M = E[sin(zR)/(zR)]`, with the value at zero defined by continuity. Thus the same `ν` generates a one-dimensional symmetric compound-Poisson exponent and, after **quadratic size bias**, the three-dimensional isotropic characteristic function `Xi/M`. In particular `ξ↦Xi(|ξ|)/M` is positive definite on `ℝ³`. Neither positive definiteness nor infinite divisibility of the related semigroup is a zero-location theorem.

## Exact meeting with theta renewal phase

Let `a=1/4`, `c=Θ(1)`, and use the actual renewal transforms
`C(r)=∫₀^∞Q(x)cos(rx)dx`, `S(r)=∫₀^∞Q(x)sin(rx)dx` from the renewal card. Its source identity gives, for `r>0`,
\[
\boxed{G'(2r)=2cr e^{-C(r)}[a\cos S(r)-r\sin S(r)],}         \tag{9}
\]
\[
\boxed{B(2r)=2cr\{r-e^{-C(r)}[r\cos S(r)+a\sin S(r)]\}>0.}  \tag{10}
\]
The cumulative companion of (9) is a **source-specific nonlinear renewal inequality**:
\[
\boxed{\int_0^r s e^{-C(s)}[a\cos S(s)-s\sin S(s)]\,ds>0
       \quad(r>0),}                                             \tag{11}
\]
because its left side equals `G(2r)/(4c)`. Local signs of the integrand may alternate; its complete initial integral stays positive. Equations (9)--(11) connect the positive renewal law and the positive jump law without replacing their signed Xi quadrature by a positive quantity.

There is also a **complex half-plane** consequence of the two positive descriptions. Put
`N(λ)=∫₀^∞e^{-λt}ν_renewal(t)dt` as in the renewal card, so `D(λ)=c-N(λ)`. The one-port formula, analytically continued from the positive Laplace ray, simplifies to
\[
h(2i\lambda)=ac-(a+\lambda)N(\lambda).
\]
Consequently
\[
\boxed{H(\lambda):=\lambda[ac-(a+\lambda)N(\lambda)]
  =\frac12\int_0^\infty\omega(x)(1-e^{-2\lambda x})\,dx,\qquad
  \operatorname{Re}H(\lambda)>0\quad(\operatorname{Re}\lambda>0).} \tag{12}
\]
The last inequality follows termwise from
`Re(1-e^{-2λx}) ≥ 1-e^{-2(Re λ)x} > 0`. Thus an affine transform of the **actual theta renewal Laplace function** is positive-real on the whole right half-plane. Its standard positive-real Pick kernel is positive semidefinite there. The nonzero zero equation becomes `H(λ)=H(-λ)`, with the right-hand value strictly in that half-plane when `Re λ>0`. This is a concrete two-sheet interpolation target: the missing arithmetic law must control the *reflected continuation* at equality, beyond the positive-real sheet in (12).

## Paper proof and producer test

The source's decay justifies integration by parts in (2), (5), and the exponential-moment differentiation in (4)--(6). The boundary terms vanish at infinity; `sin(0)=0` handles the origin in (5). Strict positivity of `G(u)` and `B(u)` follows because `ω` is positive on an interval and `1-cos(ux)` vanishes only on a discrete set when `u≠0`. The compound-Poisson assertion follows by expanding `exp[t∫(cos(ux)-1)dν]` as the Poisson probability series. For (8), spherical coordinates give `4π∫r²f_3(r) sinc(|ξ|r)dr=(2/M)∫rω(r)sinc(|ξ|r)dr=Xi(|ξ|)/M`; the same integration by parts gives the mass normalization. Finally (9)--(11) substitute the exact renewal formula for `h(2r)` into (3) and (5).

The proposed **mathematical jump** is to attack the reflected-exponent equality in (2) using the *joint* arithmetic constraints on the two theta jump descriptions, rather than ask one positive measure to orient Xi by itself. A viable producer must use the square-lattice/modular identity in the actual `ω` or `Q`; the generic positivity arguments proving (1)--(8) apply to other decreasing even sources with off-real Fourier zeros. The next test is a source-specific inequality or topological degree for the **pair** `(K(z),K(-z))` on the critical strip that is strong enough to exclude equality away from the symmetry axis, yet survives the high-frequency cancellation recorded in the renewal-resonance card. No such inequality or degree has been established here. Priority of the spherical and Lévy representations in the literature has not been audited; no claim of external novelty is made.

## Log

- 2026-09-28: every identity and inequality (1)–(12), the compound Poisson law, the spherical lift (8), positive definiteness and the Pick kernel formalized unconditionally in Lean (modules `ThetaReflectedJumpExponents`, `ThetaJumpRenewalMeeting`, `ThetaJumpCompoundPoisson`, `ThetaSphericalRadialLift`); moved to stage 3.
