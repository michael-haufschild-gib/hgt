# Mass-shifted hard-edge hyperbolic Weil boundary

- **ID:** `mass-shifted-hard-edge-hyperbolic-weil-boundary`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, canonical cofinal first-contact limit
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-hard-edge-paley-wiener-compactification`,
  `mass-shifted-completed-source-hard-edge-compactness`, and the Lean-proved finite-face
  real-rootedness/null-row theorems

## Result

Let `a_j -> infinity` and let `p_j` be canonical nonzero null polynomials at shifted-Xi first
contacts: the block of size `d_j+1` at shift `a_j^2` is positive semidefinite and singular, while
its preceding leading block is positive definite.  Suppose, after a subsequence,

\[
 {d_j\over a_j}\longrightarrow\tau>0.                         \tag{HHWB.1}
\]

Normalize the literal hard-edge tests

\[
 g_j(z)={a_j\over\sqrt{a_j^2+z^2}}
 p_j\!\left((a_j^2+z^2)^{-1}\right)                           \tag{HHWB.2}
\]

to have real `L^2` norm one.  Then a subsequence converges strongly in `L^2(R)` and locally
uniformly on `C` to a nonzero real even Paley--Wiener function `f` of type at most `2tau`.
Moreover there is a real entire function `F` such that

\[
 \boxed{\qquad f(z)=F(z^2),\qquad F\in\mathcal{LP},qquad
             \operatorname{ord}F\le {1\over2}.\qquad}          \tag{HHWB.3}
\]

Here `LP` is the Laguerre--Polya class.  In particular,

\[
 F(u)=c u^m\prod_k\left(1-{u\over r_k}\right),
 \qquad c\in\mathbb R\setminus\{0\},\quad r_k\in\mathbb R\setminus\{0\},
 \quad \sum_k|r_k|^{-1}<\infty.                               \tag{HHWB.4}
\]

The same limit is completed-Weil null and retains the complete canonical boundary incidence.  Put
`sigma=2tau` and

\[
 V_\sigma(x)=\vartheta_\infty(x)-
 \sum_{\substack{n\ge2\\ \log n\le2\sigma}}
 {\Lambda(n)\over\sqrt n}\cos(x\log n).                      \tag{HHWB.5}
\]

For every real even strip-Schwartz Paley--Wiener test `h` of type strictly below `sigma`,

\[
 \boxed{\qquad
 \int_{\mathbb R}V_\sigma(x)f(x)h(x)\,dx
 +2\pi f(i/2)h(i/2)=0.
 \qquad}                                                      \tag{HHWB.6}
\]

Every strictly smaller Paley--Wiener aperture has nonnegative completed Weil form.  Thus a
hypothetical Route U escape is not an arbitrary Weil witness: it is a hyperbolic
squared-variable boundary state for one finite-prime, Gamma-confining restricted-Weil equation.

For every real zero `r` of `F` with $r\ne-1/4$, division by that zero is an admissible same-type
variation and gives

\[
 \boxed{\quad
 \int_0^\infty {V_\sigma(\sqrt u)F(u)^2\over(u-r)\sqrt u}\,du
 +{2\pi F(-1/4)^2\over-1/4-r}=0.
 \quad}                                                       \tag{HHWB.16}
\]

The apparent real-axis singularity is removable because `F(r)=0`.  If `r=-1/4`, the correct polar
term is $2\pi F(-1/4)(F/(u-r))(-1/4)=0$, not the undefined scalar quotient `0/0`; in that case
(HHWB.16) means the same integral identity with zero polar term.  The signed measure below has
compactly supported negative part and a positive Gamma tail.

## 1. Exact Möbius numerator

Set

\[
 P_j(\zeta)=p_j\!\left({1+\zeta\over2a_j^2}\right),\qquad
 z_{a_j}(z)={a_j^2-z^2\over a_j^2+z^2}.                       \tag{HHWB.7}
\]

Then, with each quotient interpreted after continuous cancellation at a zero of `F`,

\[
 p_j((a_j^2+z^2)^{-1})=P_j(z_{a_j}(z)).                       \tag{HHWB.8}
\]

The finite-face theorem
`xiShiftedHankelNullPolynomial_root_im_eq_zero` says that every zero of `p_j`, hence of `P_j`, is
real.  Terminal rigidity gives `deg P_j=d_j`; no root is lost before the hard-edge transform.

Clear the exact Cayley denominator in the squared variable:

\[
 S_j(u)=\left(1+{u\over a_j^2}\right)^{d_j}
 P_j\!\left({1-u/a_j^2\over1+u/a_j^2}\right).                \tag{HHWB.9}
\]

This is a real polynomial.  If `rho` is a root of `P_j`, its corresponding finite root is

\[
 u=a_j^2{1-\rho\over1+\rho}\in\mathbb R.                     \tag{HHWB.10}
\]

When `rho=-1`, the associated linear numerator is constant and the degree drops; it creates no
nonreal root.  Therefore every `S_j` is real-rooted.

## 2. Locally uniform nonzero limit

Completed-source compactness gives strong `L^2` convergence of a subsequence.  Its proof also gives
locally uniform complex convergence: in Cayley angle `theta=2 arctan(z/a_j)`, normalized packets
have trigonometric degree at most `d_j`, circle norm squared `2/a_j`, and the reproducing-kernel
bound is uniform on compact complex `z` because `d_j/a_j` is bounded.  Hence Montel compactness
produces an entire limit, and strong real `L^2` convergence identifies it with `f`.  Norm one makes
`f` nonzero.

Since the half-density in (HHWB.2) tends locally uniformly to one,

\[
 P_j(z_{a_j}(z))\longrightarrow f(z)                           \tag{HHWB.11}
\]

locally uniformly.  Every term is even, so `f(z)=F(z^2)` for a unique entire `F`.

For `u` in a fixed compact set, choose any square root `z`; (HHWB.11) is uniform on the containing
`z`-compact.  Also, by (HHWB.1),

\[
 \left(1+{u\over a_j^2}\right)^{d_j}\longrightarrow1         \tag{HHWB.12}
\]

locally uniformly.  Equations (HHWB.9)--(HHWB.12) give

\[
 S_j(u)\longrightarrow F(u)                                   \tag{HHWB.13}
\]

locally uniformly on `C`.  By the defining closure theorem for the Laguerre--Polya class, the
nonzero limit `F` belongs to `LP`.

The Cayley angular-momentum argument in the compactness theorem gives
`supp widehat f subset [-2tau,2tau]`.  Paley--Wiener growth then gives
`|F(u)|=|f(sqrt u)|<=C_epsilon exp((2tau+epsilon)|u|^(1/2))` up to a polynomial factor.
Thus `ord F<=1/2`.  The general Laguerre--Polya canonical product consequently loses its quadratic
and linear exponential factors and has genus zero, which is exactly (HHWB.4).

## 3. Passing the canonical null row

For every fixed `sigma'<sigma`, lift a real even strip-Schwartz test `h` of type `sigma'` by the
hard-edge Poisson-summed Chebyshev construction at the same `a_j`.  Its degree is at most
`sigma'a_j/2+O(1)<d_j` eventually.  The complete finite Hankel null row therefore gives

\[
 \mathcal W(g_j,h_j)=0.                                      \tag{HHWB.14}
\]

The passage to the limit uses all three completed-source faces:

1. local uniform convergence passes the polar evaluation at `i/2`;
2. strong `L^2` convergence passes the Gamma integral because `h_j` converges in every
   strip-Schwartz seminorm and `vartheta_infinity(x)=O(log(2+|x|))`;
3. the polarized exterior-circle estimate for the Cayley degrees `d_j+deg h_j` makes the complete
   prime tail uniformly summable, while each finite prefix is an ordinary `L^2` pairing.

Hence `mathcal W(f,h)=0`.

Because `f` and `h` have Fourier supports in `[-sigma,sigma]` and
`[-sigma',sigma']`, respectively,

\[
 \widehat{fh}(L)=0\qquad(|L|>\sigma+\sigma').                 \tag{HHWB.15}
\]

The completed prime sum is therefore exactly finite.  Adding the individually zero terms with
`sigma+sigma'<log n<=2sigma` and inserting the explicit formula yields (HHWB.6).  This is a literal
finite-prime Euler equation, not an infinite-prime truncation or approximation.

Finally, any lower-type `h` has hard-edge lifts of degree below the singular block.  Their
finite quadratic values are nonnegative.  The same source passage gives
`mathcal W(h,h)>=0` at every aperture strictly below `sigma`.

It remains to justify `mathcal W(f,f)=0`, because strong `L^2` convergence by itself does not pass
the logarithmic Gamma diagonal.  Completed-source coercivity and lower semicontinuity give
`int log(2+|x|)|f(x)|^2 dx<infinity`.  For `0<r<1`, `f_r(x)=f(rx)` has type below `sigma` and
converges to `f` in the logarithmically weighted `L^2` form norm.  To approximate `f_r`, choose a
smooth Fourier multiplier equal to one on its support and supported strictly inside the type
boundary, apply it after a growing physical cutoff, and use boundedness of its Schwartz convolution
kernel under the moderate logarithmic weight.  This gives smooth interior-frequency convergence
in the form norm and extends the lower-row equation to `f_r`.  Since the restricted prime
sum is finite, Gamma multiplication is form-continuous, and Paley--Wiener evaluation at `i/2` is
bounded, letting `r` increase to one in `mathcal W(f,f_r)=0` proves `mathcal W(f,f)=0`.

## 4. Root-division Cauchy law

The same form-core argument extends (HHWB.6) from lower type to every function in the type-`sigma`
logarithmic form domain.  If `r` is a real zero of `F`, then

\[
 h_r(z)={f(z)\over z^2-r}={F(z^2)\over z^2-r}                  \tag{HHWB.17}
\]

is entire, has type at most `sigma`, and belongs to that form domain; division improves its real
tail by two powers.  Substitution in (HHWB.6), followed by `u=x^2`, proves (HHWB.16).

Equivalently, define

\[
 d\nu_f(u)=\mathbf1_{u>0}{V_\sigma(\sqrt u)F(u)^2\over\sqrt u}\,du
       +2\pi F(-1/4)^2\delta_{-1/4}.                          \tag{HHWB.18}
\]

Then

\[
 \nu_f(\mathbb R)=0,
 \qquad \int_{\mathbb R}{d\nu_f(u)\over u-r}=0
 \quad(F(r)=0).                                               \tag{HHWB.19}
\]

The first equality is completed-Weil nullity.  Since
`vartheta_infinity(x)=(1/2)log(|x|/(2pi))+o(1)` and the prime sum in (HHWB.5) is finite and bounded,
`V_sigma(x)>0` for all sufficiently large `|x|`.  Thus the negative part of `nu_f` is supported in
one compact subset of `[0,infinity)`, while its tail is positive.  If `r` is simple and
`F(u)=(u-r)G_r(u)`, (HHWB.16) is the signed barycenter identity

\[
 \int_{\mathbb R}(u-r)G_r(u)^2
 \left(\mathbf1_{u>0}{V_\sigma(\sqrt u)\over\sqrt u}\,du
       +2\pi\delta_{-1/4}\right)=0.                            \tag{HHWB.20}
\]

This is the exact infinite hard-edge descendant of finite flat quadrature.  The stronger root-jet
consequence is proved separately in `mass-shifted-hard-edge-root-jet-radical-rigidity`: distinct
root divisions are ordinary Lagrange-orthogonal modes, while a root of multiplicity `m` creates
$\lfloor m/2\rfloor$ additional exact radical vectors.

## Conjecture--failure--pivot audit

1. **Real-rooted finite null polynomials lose all information at moving degree.** `[FALSIFIED]`.
   Exact Cayley denominator clearing produces the real-rooted numerator sequence (HHWB.9).
2. **Real-axis convergence is enough for Laguerre--Polya closure.** `[FALSIFIED AS A PROOF]`.
   The closure requires compact convergence on `C`; the normalized Cayley reproducing kernel and
   Montel argument supply it.
3. **The limit is merely a generic finite-type Weil witness.** `[FALSIFIED]`.  It lies in the
   squared-variable `LP` class, retains the entire lower null flag, and solves the finite-prime
   equation (HHWB.6).
4. **`LP` alone closes RH.** `[FALSIFIED AS AN INFERENCE]`.  Functions such as
   `sin(sqrt u)/sqrt u` show that nonzero order-one-half `LP` Paley--Wiener states exist.  Missing
   theorem must use (HHWB.6), not hyperbolicity alone.
5. **The null row supplies no same-type variation.** `[FALSIFIED]`.  Lower-type dilation is a core
   for the logarithmic restricted-Weil form, so every real zero supplies the exact root-division
   equation (HHWB.16).
6. **Positive Gamma tail alone orients a root equation.** `[FALSIFIED AS AN INFERENCE]`.  The
   compact finite-prime well remains signed and can balance that tail.  Surviving object is the
   simultaneous Cauchy system (HHWB.19), not one selected barycenter.
7. **The simultaneous simple-root Cauchy system is overdetermined.** `[FALSIFIED AS A MECHANISM]`.
   Partial fractions identify it with ordinary extremal/Lagrange orthogonality.  Its non-trivial
   survivor is root-jet radical rigidity: coalescing roots force ground-space degeneracy.

## Higher universal principle

Finite Hankel real-rootedness and restricted-Weil ground-edge geometry are two representations of
one boundary object.  The Möbius numerator (HHWB.9) is the exact shadow map:

\[
 \text{finite Jacobi characteristic polynomial}
 \longrightarrow
 \text{squared-variable Laguerre--Polya boundary state}.
\]

Completed prime--Gamma incidence supplies phase-space compactness; finite Hankel positivity
supplies hyperbolicity; the hard-edge limit fuses them into a finite-prime confining Euler
equation.  Earlier root-sign no-gos remain valid: they show that the new invariant is `LP` in
`z^2`, not positivity of its roots.

## Exact remaining open core

`[OPEN CORE]` Exclude a nonzero `f(z)=F(z^2)` satisfying simultaneously:

- `F in LP`, `ord F<=1/2`, and `f in PW_sigma intersect L^2(R)`;
- the finite-prime Gamma equation (HHWB.6);
- nonnegativity of every strictly smaller restricted-Weil aperture.

Generic restricted-Weil positivity is RH.  The simple-root Cauchy equations themselves are generic
extremal orthogonality and no longer qualify as the next target.  The exact remaining discriminator
is the dichotomy proved in `mass-shifted-hard-edge-root-jet-radical-rigidity`: either the critical
ground is simple, where Connes--van Suijlekom already force the zeros of `f` onto the real axis, or
the literal completed-Xi source produces a degenerate first birth.  Progress must prove a new
prime--Gamma sign in the simple branch or a source-derived simplicity/degeneracy contradiction in
the second branch.

## Novelty and collision audit

- `[CORPUS]` `XiShiftedHankelNullPolynomialRoots.lean` proves finite full-degree real-simple roots;
  no corpus theorem passes them through the critical hard-edge limit.
- `[LOCAL-RESEARCH]` earlier Route U root-threshold and positive-carrier no-gos prove that real,
  simple, or even positive finite roots do not orient the crossing.  This theorem does not
  contradict them; it extracts the surviving global hyperbolicity class.
- `[LITERATURE]` Laguerre--Polya closure under compact limits of real-rooted polynomials is
  classical; see Assiotis, [*Random entire functions from random polynomials with real zeros*](https://arxiv.org/abs/2202.03362),
  and Borcea--Branden, [*Polya--Schur master theorems for circular domains and their boundaries*](https://arxiv.org/abs/math/0607416).
- `[LITERATURE]` Connes--van Suijlekom,
  [*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://arxiv.org/abs/2511.23257),
  obtains a different real-zero mechanism from an isolated simple even convolution ground state.
  It does not derive squared-variable `LP` closure from reciprocal-Hankel first contacts or the
  finite-prime equation (HHWB.6).

No matching source-specific theorem was located.  Priority remains unverified pending independent
specialist review.

## Lean status

No Lean declaration is claimed.  Exact formalization requires the already formal finite root
theorem plus the source-specific compactness theorem, complex normal-family passage, Cayley
numerator real-root preservation, Laguerre--Polya closure, Paley--Wiener support, and the literal
finite-prime null-row limit.  An abstract theorem assuming compact convergence or the Euler
equation would not formalize this result.

## Lean status (updated)

The Möbius/Cayley half of the theorem — sections 1 and 2 — is now formal and axiom-clean.

    HTGeometry/HardyCrossParseval.lean                (pre-existing corpus asset)
      circleAverage_poly_mul_conj                     polarized polynomial Parseval on a circle

    HTGeometry/CirclePolynomialSupBound.lean          (axiom-clean, wired, built)
      norm_polySum_le                                 Cauchy-Schwarz sup bound from coefficient
                                                      energy
      sum_normSq_coeff_eq_circleAverage               the coefficient energy is the mean square on
                                                      the unit circle
      zhukovskyLift, eval_zhukovskyLift,
        natDegree_zhukovskyLift_le                    `w^d P((w+w⁻¹)/2)` as a polynomial of degree
                                                      at most `2d`
      cayleyEnergy                                    the mean square of `P` on the Cayley interval
      norm_eval_cayley_le, norm_eval_cayley_le'       **the reproducing-kernel bound**: off the
                                                      interval, `|P|` is at most
                                                      `sqrt(2d+2) sqrt(energy) max(|w|,|w|⁻¹)^(d+2)`

    HTGeometry/LocallyUniformProduct.lean             (axiom-clean, wired, built)
      tendstoUniformlyOn_mul_of_bound,
        tendstoLocallyUniformly_mul                   products of locally uniformly convergent
                                                      complex families with continuous limits

    RHTower/XiShiftedHardEdgeCayleyPacketBound.lean   (axiom-clean, wired, built)
      hardEdgeDiskVariable                            `w = (a + iz)/(a - iz)`
      zhukovsky_hardEdgeDiskVariable                  the hard-edge coordinate `(a²-z²)/(a²+z²)` is
                                                      its Zhukovsky image
      max_norm_hardEdgeDiskVariable_le                on `|z| <= R` the disc variable stays within
                                                      `(a+R)/(a-R)` of the circle
      ratio_pow_le_exp                                `((a+R)/(a-R))^n <= exp(2Rn/(a-R))`
      norm_eval_hardEdgeCoordinate_le                 **the normality bound**: a degree-`d` packet
                                                      is bounded on `|z| <= R` by its circle energy
                                                      times `exp(2R(d+2)/(a-R))`, uniform when the
                                                      degree grows proportionally to the aperture

    RHTower/XiShiftedHardEdgeCayleyNumerator.lean     (axiom-clean, wired, built)
      cayleyNumerator                                 **(HHWB.9)** the degree-`d` numerator of
                                                      `P((a²-u)/(a²+u))`
      eval_cayleyNumerator                            **(HHWB.8)** it is the cleared substitution
      cayleyNumerator_root_im_eq_zero                 **(HHWB.10)** the numerator of a real-rooted
                                                      polynomial is real-rooted: the exceptional
                                                      value `-1` would force `a = 0`
      tendstoLocallyUniformly_of_comp_sq              locally uniform convergence transfers along
                                                      the squaring map `u = z²`
      cayleyNumerator_limit_zero_im_eq_zero,
        scaled_cayleyNumerator_limit_zero_im_eq_zero  Laguerre--Pólya closure: a nonzero entire
                                                      locally uniform limit of the numerators has
                                                      only real zeros

    RHTower/XiShiftedHardEdgeCayleyLimit.lean         (axiom-clean, wired, built)
      norm_one_add_pow_sub_one_le                     `|(1+w)^d - 1| <= d(1+|w|)^d |w|`
      tendstoLocallyUniformly_one_add_div_pow         **(HHWB.12)** `(1 + u/a²)^d -> 1` locally
                                                      uniformly when `d/a² -> 0`
      tendstoLocallyUniformly_scaled_cayleyNumerator  **(HHWB.13)** the normalized numerators have
                                                      the same limit as the packets
      hardEdgeCayleyLimit_zero_im_eq_zero             **(HHWB.3)/(HHWB.4)** the hard-edge limit is
                                                      real-rooted

What the last theorem consumes is exactly the output of the parent compactness card — locally
uniform convergence of the normalized packets — together with `a_j -> infinity` and
`d_j / a_j² -> 0`, both of which follow from `d_j/a_j -> tau`.  The normality bound
`norm_eval_hardEdgeCoordinate_le` is the estimate the parent card's Montel argument needs.

Still to formalize for this card: section 3, the passage of the finite Hankel null row to the
limit (HHWB.6), and section 4, the root-division Cauchy law (HHWB.16).
