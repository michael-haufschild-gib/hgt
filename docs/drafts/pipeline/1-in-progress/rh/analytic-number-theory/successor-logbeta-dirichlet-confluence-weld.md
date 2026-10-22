# Successor/log-Beta Dirichlet confluence weld

- **ID:** `successor-logbeta-dirichlet-confluence-weld`
- **Stage:** 1 — in progress
- **Type:** SOURCE-SPECIFIC CONFLUENCE THEOREM / SYMMETRIC MARKOV
  REALIZATION / THIRD-COMPLETION INPUT
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH]`
  `[CLASSICAL LOG-BETA/LEVY PARENT]`
  `[CORPUS-NEW TOEPLITZ/MARKOV WELD]`
  `[EXTERNAL NOVELTY PROVISIONAL]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  - `suzuki-gamma-beta-markov-stokes-transparency.md`;
  - `successor-toeplitz-q-digamma-confluence-orientation-law.md`;
  - `von-mangoldt-weighted-density-boundary-anomaly.md`;
  - `../../../3-formalized/not_new_scientific_knowledge/reflected-digamma-anomaly-reality-selector.md`.

## Frontier statement

The calibrated Suzuki Gamma Markov factor and the successor Toeplitz
countertrace do not merely both involve Gamma functions.  After the
critical half-weight Esscher shift, the infinitesimal log-Beta Markov
channel has the complete Bernstein exponent

```text
Lambda(r)
 =1/2*(psi((1+r)/2)-psi(1/2))
 =integral_0^infinity
    (1-exp(-r*x))/(2*sinh(x)) dx.                       (1)
```

Its reflected sum

```text
Sigma(r)=Lambda(r)+Lambda(-r)                           (2)
```

is the analytic continuation of a nonnegative symmetric Lévy/Dirichlet
symbol.  Under `r=2*z-1`, the reflected q-digamma countertrace
confluence law is exactly

```text
psi(z)+psi(1-z)
 =2*Sigma(2*z-1)+2*psi(1/2).                           (3)
```

Thus the strict critical-line orientation already proved for the
reflected digamma anomaly is the off-unitary analytic continuation of
one canonical symmetric Markov generator.  The successor singular
countertrace supplies a source route to this generator; the calibrated
Suzuki channel supplies its completely positive environment.

This is an operator-level weld, not a proof of RH.  Ordinary Markov
`L2` still loses Xi conormal fibres.  The remaining problem is to
construct a source-effective singular extension of this Dirichlet form
which retains the Toeplitz boundary current and every co-Poisson/Xi
principal conormal jet.

## 1. Exact log-Beta Lévy exponent

For `0<epsilon<1`, put

```text
a_epsilon=1/4-epsilon/4,
b_epsilon=1/4+epsilon/4,
B_epsilon ~ Beta(a_epsilon,epsilon/2),
Y_epsilon=-(1/2)*log(B_epsilon).                        (4)
```

The Markov factor in the calibrated Suzuki multiplier is

```text
F_epsilon(s)
 =E[exp(-s*Y_epsilon)]
 =Gamma(a_epsilon+s/2)*Gamma(b_epsilon)
   /(Gamma(b_epsilon+s/2)*Gamma(a_epsilon)).            (5)
```

For `Re(s)>-2*a_epsilon`, the digamma integral and integration
from `a_epsilon` to `b_epsilon` give the exact
Lévy--Khintchine formula

```text
-log F_epsilon(s)
 =integral_0^infinity (1-exp(-s*x))*nu_epsilon(x) dx,   (6)

nu_epsilon(x)
 =exp(-(1-epsilon)*x/2)*(1-exp(-epsilon*x))
   /(x*(1-exp(-2*x))).                                  (7)
```

The density in `(7)` is nonnegative.  Expanding the renewal denominator
also gives the exact Gamma-depth decomposition

```text
nu_epsilon(x)
 =sum_(n>=0)
   [exp(-(2*n+(1-epsilon)/2)*x)
    -exp(-(2*n+(1+epsilon)/2)*x)]/x.                   (8)
```

Hence the calibrated archimedean environment has countably infinite
activity across the Gamma pole lattice.  This is not the rational-prime
Wold clock: `(8)` is the archimedean depth direction.  Treating the two
as one scalar renewal would be false.

## 2. Infinitesimal calibrated channel

Define

```text
K_epsilon(s)=-(1/epsilon)*log F_epsilon(s).             (9)
```

On every compact subset of `Re(s)>-1/2`, dominated convergence in
`(6)`--`(7)` proves

```text
K_epsilon(s) -> K(s),                                  (10)

K(s)
 =integral_0^infinity
    (1-exp(-s*x))*exp(-x/2)/(1-exp(-2*x)) dx
 =1/2*(psi(1/4+s/2)-psi(1/4)).                         (11)
```

For the domination, near zero the product of
`1-exp(-s*x)` with `nu_epsilon(x)/epsilon` is bounded.
On a compact set at positive distance from `Re(s)=-1/2`,
the large-`x` part has one uniform exponential majorant.
Equation `(11)` follows from the standard digamma difference integral.

Thus the first calibrated Gamma defect is not merely a scalar
derivative.  It is the Laplace exponent of a source-defined
infinite-activity subordinator.

## 3. Critical half-weight Esscher centering

The Mellin critical half-weight forces the centered exponent

```text
Lambda(r)=K(r+1/2)-K(1/2).                             (12)
```

Substitution in `(11)` gives

```text
Lambda(r)
 =integral_0^infinity
    (1-exp(-r*x))*exp(-x)/(1-exp(-2*x)) dx
 =integral_0^infinity
    (1-exp(-r*x))/(2*sinh(x)) dx
 =1/2*(psi((1+r)/2)-psi(1/2)).                         (13)
```

The half-weight is not a fitted normalization: it is exactly the
Esscher shift which moves the Suzuki quarter-Gamma law to the
critical Mellin center.

For real `tau`, reflection gives

```text
Sigma(i*tau)
 =Lambda(i*tau)+Lambda(-i*tau)
 =2*integral_0^infinity
     (1-cos(tau*x))/(2*sinh(x)) dx
 >=0,                                                   (14)
```

with strict inequality for `tau!=0`.  Equivalently, the symmetric
Lévy measure

```text
dPi(x)=dx/(2*sinh(|x|)),        x!=0,                   (15)
```

has characteristic exponent `Sigma(i*tau)`.  It is a Lévy measure
because its density is `O(1/|x|)` at zero and exponentially decaying
at infinity.  Therefore the Fourier multiplier with symbol
`Sigma(i*tau)` is a nonnegative self-adjoint Dirichlet generator on
`L2(R)`, and its heat operators form a symmetric conservative Markov
semigroup.

This supplies complete positivity and Hausdorff contractivity at the
critical center without choosing a divisor, zero, or target metric.

## 4. Exact successor countertrace identification

For `|Re(r)|<1`, equations `(2)` and `(13)` give

```text
Sigma(r)
 =1/2*
   [psi((1+r)/2)+psi((1-r)/2)-2*psi(1/2)].             (16)
```

Set

```text
z=(1+r)/2,       r=2*z-1.                              (17)
```

Then `(16)` is exactly `(3)`.

Independently, the successor Toeplitz paper proves that an isolated
arithmetic edge has a q-digamma countertrace boundary and that, after
the source-forced logarithmic subtraction and reflection,

```text
countertraceConfluence(z)=psi(z)+psi(1-z).              (18)
```

Combining `(3)` and `(18)` proves:

> **Theorem — successor/log-Beta Dirichlet confluence weld.**
> The reflected cofinal boundary of the source-defined successor
> Toeplitz countertrace is, up to the real constant `2*psi(1/2)`,
> twice the analytic continuation of the symmetric Dirichlet generator
> obtained by critical Esscher centering of the infinitesimal calibrated
> Suzuki log-Beta Markov channel.

The equality is exact.  It does not identify a finite full-source
counterweight with a product of one-edge q-symbols; the full recurrence
is nonlinear in the sum of edge moments.  Only an edge-retaining
source completion may pass from the finite q-laws to `(18)`.

## 5. Orientation and what it would consume

For `z=sigma+i*t`, `0<sigma<1`, `t>0`, the formalized corpus theorem is

```text
Im(psi(z)+psi(1-z)) > 0  iff sigma<1/2,
Im(psi(z)+psi(1-z)) = 0  iff sigma=1/2,
Im(psi(z)+psi(1-z)) < 0  iff sigma>1/2.                 (19)
```

The real constant in `(3)` does not affect `(19)`.  Hence the analytic
continuation of the symmetric Markov symbol has a strict horizontal
orientation away from its unitary spectrum.

If a source-built boundary representation made every nonzero Xi
conormal jet an actual spectral boundary class for this symmetric
Dirichlet generator, its spectral value would be real and `(19)` would
force the corresponding zero onto the critical line.

That conditional sentence is not counted as progress by itself.  In
an arbitrary rigged space a self-adjoint differential operator can
have complex-eigenvalue functionals in the algebraic dual.  The
required theorem must construct the topology and prove spectral
temperedness from Euler--Gamma/co-Poisson source maps; it may not
assume continuity of Xi evaluation or reality of `(18)` at a zero.

## 6. Candidate third completion

The exact weld narrows the third-completion target to a falsifiable
object.

> **[CONJECTURE — SOURCE-EFFECTIVE TOEPLITZ/DIRICHLET BOUNDARY
> COMPLETION.]**  The directed algebra of finite von Mangoldt successor
> sections, with its canonical Toeplitz countertrace and completed
> Euler multiplication, has a Hausdorff edge-retaining boundary
> completion such that:
>
> 1. its regular quotient is the symmetric Markov Dirichlet form
>    `(14)`--`(15)`;
> 2. its singular boundary is the cofinal Toeplitz countertrace rather
>    than a bounded `L2` density;
> 3. a source-derived transverse renormalization maps the coherent odd
>    Gamma--Jacobi residual into the carré-du-champ needed to make the
>    full prime--jet incidence closable;
> 4. prime dilation acts contractively and the completed co-Poisson
>    multiplier acts by a closed source map;
> 5. every uncensored Xi principal conormal jet has a nonzero,
>    spectrally tempered boundary image.

Items 1--2 are now fixed by proved source laws.  Items 3--5 are open.
Deleting the named source construction and asserting item 5 in an
arbitrary quotient is RH-equivalent and rejected.

The first serious theorem is not another positivity wrapper.  It is
an all-edge Mosco/graph convergence theorem from the q-digamma
countertrace forms to `(14)`, with the actual odd Gamma--Jacobi defect
and completed Euler trace present before co-Poisson annihilator
specialization.

## 7. Hostile audit

1. **Classical parent.**  Beta Mellin transforms, infinite divisibility
   of log-Beta laws, Gamma-ratio Lévy formulas, complete Bernstein
   functions, and symmetric Lévy semigroups are parent mathematics.
2. **Not the Thorin/RH measure.**  The positive measure `(15)` is
   archimedean and explicit.  It is not the Xi-zero Thorin measure and
   does not imply the completed seam Stieltjes condition.
3. **No scalar-clock collapse.**  Gamma depth `(8)` and rational-prime
   Wold depth are different directions.  Their eventual interaction
   must be bivariate.
4. **Ambient `L2` is still too small.**  The Markov semigroup in
   Section 3 does not restore point or Xi-conormal fibres.  It supplies
   the regular quotient of a possible third completion, not the
   completion itself.
5. **Finite q stages are not selectors.**  Their counterfeit reality
   resonances remain.  Only the source-controlled q-to-one confluence
   has the strict selector `(19)`.
6. **Generic off-line Euler systems survive the archimedean theorem.**
   They can share `(14)` without carrying the literal von Mangoldt
   successor countertrace, odd Gamma--Jacobi incidence, and completed
   co-Poisson map.  The arithmetic source weld is indispensable.
7. **No generalized eigenvector shortcut.**  Self-adjointness excludes
   complex eigenvalues only for actual spectral classes in the chosen
   topology, not arbitrary analytic functionals.
8. **Raw Gamma--Jacobi scale matching is false, but the source
   second-jet scale repairs its leading order.**  For the arithmetic
   successor edge,

   ```text
   h_n=log(log(n+1)/log(n)) ~ 1/(n*log(n)),
   1-tanh(log(n))=2/(n^2+1).
   ```

   Hence the q-countertrace defect scale `h_n^2` and the odd
   Gamma--Jacobi boundary scale differ by an asymptotic factor
   `2*log(n)^2`.  However the first nonconstant successor jet carries
   the literal degree-two normalization `log(n+1)^2`, and

   ```text
   2*log(n+1)^2*h_n^2/(1-tanh(log(n))) -> 1.
   ```

   Indeed

   ```text
   n*log(n+1)*h_n -> 1,
   1-tanh(log(n))=2/(n^2+1).
   ```

   Thus the source itself repairs the leading energy scale; the
   Gamma-conductor Schur cost is not the repair.  This does not identify
   the two marginals as kernels.  Their depth exponents use different
   conventions (`q^(2*N)` versus odd-Jacobi coefficient or squared-tail
   powers), so the required anisotropic mode reindexing has an unresolved
   factor until a typed cross-kernel is fixed.  Item 3 still requires a
   singular source transgression, but it may no longer be rejected on
   leading-scale grounds.

## 8. Literature boundary

Parent sources located in the first audit:

- D. Ostrovsky, *Theory of Barnes Beta Distributions*,
  `arXiv:1305.4422`, for infinitely divisible logarithms of
  Beta/Barnes-Beta Gamma ratios;
- P. Bosch and T. Simon, *On the infinite divisibility of inverse
  Beta distributions*, `arXiv:1405.4176`;
- C. Berg, S. Koumandos, and H. L. Pedersen, *Nielsen's beta function
  and some infinitely divisible distributions*, `arXiv:1905.04131`,
  especially Gamma-ratio Laplace representations;
- P. Patie and M. Savov, *Bernstein-gamma functions and exponential
  functionals of Lévy processes*, `arXiv:1604.05960`.

These sources make Sections 1--3 parent in isolation.  Searches found
no source coupling the calibrated Suzuki log-Beta infinitesimal,
critical Esscher centering, the von Mangoldt successor Toeplitz
q-digamma confluence, and the reflected RH orientation as in
`(3)`--`(18)`.  This is a provisional noncollision report, not a
priority certificate.

## Gates

- [x] exact log-Beta Lévy density
- [x] Gamma-depth renewal decomposition
- [x] locally uniform infinitesimal-channel limit
- [x] critical Esscher-centered complete Bernstein exponent
- [x] symmetric Lévy/Dirichlet realization
- [x] exact q-digamma countertrace confluence weld
- [x] hostile distinction from Thorin/RH and ambient `L2`
- [x] preliminary primary-source novelty audit
- [ ] independent mathematical and literature audit
- [ ] prove all-edge q-form to Dirichlet-form convergence
- [ ] construct bivariate prime--jet/Gamma--Jacobi incidence
- [ ] prove completed Euler/co-Poisson graph closability
- [ ] prove Xi conormal spectral temperedness
- [ ] formalize only dependency-closed non-RH core
- [ ] RH

## Log

- 2026-07-29 — Derived the exact Lévy density of the calibrated Suzuki
  log-Beta factor, its infinitesimal Gamma-depth exponent, and the
  critical half-weight Esscher transform.  Symmetrization gives the
  Lévy density `1/(2*sinh(|x|))`.
- 2026-07-29 — Identified the reflected successor q-digamma
  countertrace confluence exactly with the analytic continuation of
  this symmetric Dirichlet generator.  Recorded ambient-`L2`,
  generalized-eigenvector, finite-q resonance, and generalized-prime
  falsifiers; no RH or conormal survival claim made.
- 2026-07-29 — Tested the apparent q-countertrace/Gamma--Jacobi scale
  match.  Raw scales differ by a logarithmic-square factor.  A later
  audit found that the literal degree-two successor normalization
  supplies exactly that factor asymptotically; only the typed
  kernel/depth transgression remains open.
