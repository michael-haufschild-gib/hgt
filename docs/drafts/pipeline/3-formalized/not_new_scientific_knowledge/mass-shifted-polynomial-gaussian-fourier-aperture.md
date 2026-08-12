# Mass-shifted polynomial--Gaussian Fourier aperture

- **ID:** `mass-shifted-polynomial-gaussian-fourier-aperture`
- **Stage:** 3-formalized
- **Route:** U, C43-Y / PDH.9
- **Scientific status:** `[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
- **Depends on:** `mass-shifted-complex-gaussian-translation`; `StripHorizontalShift`

## Exact frozen claim FGA.1

For every `P in R[X]` and `eta in R`, put

\[
 f_P(x)=P(x)^2e^{-2\pi x^2},\qquad d=\operatorname{natDegree}P,
\]

and use the Fourier convention

\[
 \widehat f_P(\eta)=\int_{\mathbb R}f_P(x)e^{-2\pi i\eta x}\,dx.
\]

Then, including `P=0` and constant polynomials,

\[
 \boxed{
 |\widehat f_P(\eta)|
 \le
 \exp\!\left(-\frac{\pi\eta^2}{2}
       +|\eta|\sqrt{4\pi d}\right)
 \left\|P(x)e^{-\pi x^2}\right\|_2^2.}
 \tag{FGA.1}
\]

No parity, nonvanishing, coefficient bound, RH premise, or analytic hypothesis occurs.

## Exact Route-U shadow

Let `q(x)=Q(x^2)`, where `deg Q<=d`, and

\[
 F_{Q,t}(x)=q(x)^2e^{-tx^2},\qquad
 M_Q(t)=\int_{\mathbb R}F_{Q,t}(x)\,dx,
 \quad t>0.
\]

After `y=sqrt(t/(2pi)) x`, set

\[
 R(y)=q\!\left(\sqrt{2\pi/t}\,y\right),\qquad
 \eta=\frac{\xi}{\sqrt{2\pi t}}.
\]

Then `deg R<=2d`, the Jacobian cancels between Fourier integral and mass, and FGA.1 gives

\[
 \boxed{
 \frac{|\widehat F_{Q,t}(\xi)|}{M_Q(t)}
 \le \exp\!\left(-\frac{\xi^2}{4t}
          +2\sqrt d\frac{|\xi|}{\sqrt t}\right).}
 \tag{FGA.2}
\]

Here `widehat F` uses `exp(-i xi x)`; because `F` is even and real this equals its cosine
transform. This is exactly C43-Y (24.137) and PDH.9.

## Conjecture and hostile verdict

The initial claim was restricted to even polynomials and nonnegative frequency. That restriction
was an artifact of the Route-U consumer. The stronger FGA.1 holds for every real polynomial and
signed frequency: negative frequency is conjugate to positive frequency for a real density.

Hostile checks:

- `P=0`: both sides vanish, despite `natDegree 0=0`.
- `d=0`: translation costs one; completing the square gives the exact Gaussian decay.
- Odd/mixed `P`: no evenness is used for positive frequency; real-valuedness alone handles the
  other sign.
- Contour orientation: with the negative Fourier character and `eta>=0`, the correct line is
  `z=x-i eta/2`. The upper line produces the wrong growing factor.
- The unnormalized C43 frequency is not mathlib's Fourier frequency. The factor
  `eta=xi/sqrt(2pi t)` is essential and gives exactly `-xi^2/(4t)`.

Verdict: `[BRIDGE]`, not standalone new scientific knowledge. Exact weighted derivative bounds,
Hermite/Fock translations, and polynomial--Gaussian Fourier structure are classical. Li--Geng--
Ling--Wang, arXiv:2411.16359, give exact weighted `L2` Bernstein--Markov factors; Bonami--Demange--
Jaming, arXiv:math/0102111, characterize polynomial Gaussians through Fourier uncertainty; complex
Hermite/Fourier--Wigner and Fock/Gabor literature supplies adjacent transform structure. No source
found states the completed-Xi C43-Y/PDH composition. Priority is not claimed for FGA.1.

## Dependency-closed paper proof

It suffices first to assume `eta>=0`. Map `P` coefficientwise to `P_C in C[X]` and define the
entire function

\[
 G_\eta(z)=P_C(z)^2\exp(-2\pi z^2-2\pi i\eta z).
\]

On every closed horizontal strip, polynomial growth is absorbed by Gaussian real-direction decay:
for fixed strip width `c`, coefficient norm `S`, and degree `d`,

\[
 |P_C(z)|^2\le S^2(1+|z|)^{2d}
 \le S^2(|\Re z|+c+1)^{2d},
\]

while

\[
 \Re(-2\pi z^2-2\pi i\eta z)
 =-2\pi(\Re z)^2+2\pi(\Im z)^2+2\pi\eta\Im z.
\]

The last two terms are bounded on the strip, and
`-2pi x^2<=-2|x|+1/2`. Hence a constant `C` exists with

\[
 |G_\eta(z)|\le Ce^{-|\Re z|/2}.
\]

The horizontal contour theorem therefore applies at `c=eta/2` and yields

\[
 \int_{\mathbb R}G_\eta(x)\,dx
 =\int_{\mathbb R}G_\eta(x-i\eta/2)\,dx.
 \tag{FGA.3}
\]

Direct expansion gives

\[
 -2\pi(x-i\eta/2)^2-2\pi i\eta(x-i\eta/2)
 =-2\pi x^2-\pi\eta^2/2.
\]

Consequently

\[
 \begin{aligned}
 |\widehat f_P(\eta)|
 &\le e^{-\pi\eta^2/2}
   \int_{\mathbb R}|P_C(x-i\eta/2)|^2e^{-2\pi x^2}\,dx\\
 &=e^{-\pi\eta^2/2}
   \|P_C(\mathord\cdot-i\eta/2)e^{-\pi x^2}\|_2^2.
 \end{aligned}
 \tag{FGA.4}
\]

The Lean-closed complex Gaussian translation theorem gives

\[
 \|P_C(\mathord\cdot-i\eta/2)e^{-\pi x^2}\|_2
 \le e^{(\eta/2)\sqrt{4\pi d}}
       \|P e^{-\pi x^2}\|_2.
\]

Squaring and combining exponents proves FGA.1 for `eta>=0`. For `eta<0`, the density `f_P` is
real-valued, so pointwise conjugation of the Fourier kernel and commutation of conjugation with the
Bochner integral give

\[
 \widehat f_P(\eta)=\overline{\widehat f_P(-\eta)}.
\]

Norm invariance, `|-eta|=|eta|`, and `eta^2=(-eta)^2` reduce to the nonnegative case. This proves
FGA.1 for all signed frequencies.

For FGA.2, the displayed positive linear change of variables is legitimate because polynomial
Gaussians are integrable. Both numerator and denominator acquire the same factor
`sqrt(2pi/t)`. Since `natDegree R<=2d`, monotonicity of the square root lets FGA.1 use `2d` in place
of the actual degree. Substitution gives

\[
 -\frac\pi2\frac{\xi^2}{2\pi t}=-\frac{\xi^2}{4t},\qquad
 \frac{|\xi|}{\sqrt{2\pi t}}\sqrt{4\pi(2d)}
 =2\sqrt d\frac{|\xi|}{\sqrt t}.
\]

Thus FGA.2 follows exactly.

## Lean closure and completed normalization audit

Active-toolchain inspection confirms that `Real.fourier_real_eq_integral_exp_smul` uses the
`exp(-2 * pi * I * eta * x)` convention frozen in FGA.1, while
`MeasureTheory.Measure.integral_comp_mul_left` supplies the positive real dilation needed for
FGA.2. Stage 2 is therefore dependency-closed without changing any constant or quantifier.

The exact target is now closed in
`formal/GaloisForLFunctions/RHTower/PolynomialGaussianFourierAperture.lean`:

- `norm_fourier_polynomialGaussianEnergy_le` proves FGA.1 for every real polynomial and every
  signed frequency.
- `norm_routeUPolynomialGaussianFourier_le` proves the native unnormalized Route-U estimate before
  division.
- `routeUPolynomialGaussianFourier_div_mass_le` proves FGA.2 with positivity of `t` encoded in its
  subtype and with no nonzero-polynomial or positive-mass premise. The zero-mass case is closed.

The module is imported by `GaloisForLFunctions.RHTower`. `lake env lean` passed, and the final audit
`lake build GaloisForLFunctions.RHTower.PolynomialGaussianFourierAperture` built `8825/8825` jobs.
`#print axioms` for all three capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration occurs in the module.

Corpus-wide lint still reports unrelated pre-existing modules unreachable from theorem-area
umbrellas. It does not report a banned declaration or reachability failure for this module.
