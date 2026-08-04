# Exact gap-scale Euler response of the constrained CCM endpoint layer

- **ID:** `ccm-constrained-endpoint-euler-response-constant`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** Slepian--Pollak finite-Fourier theory, Fuchs fixed-mode concentration
  asymptotics, Slepian's full fixed-mode PSWF expansions, and
  `constrained-prolate-two-mode-ground-state.md`
- **Statement:** For the normalized vanishing-integral `h_0`--`h_4` CCM source, the prime-dilation
  response of its leading lower endpoint tail is
  `(4*pi/33)(-zeta'(2)/zeta(2))d_1+o(d_1)`. With the two signed prime atoms in the Weil kernel, the
  actual prime-form contribution is
  `-(8*pi/33)(-zeta'(2)/zeta(2))d_1+o(d_1)`.

## Setup

For `c>0`, let

```text
(Q_c f)(x)=integral_(-1)^1 sin(c(x-y))/(pi*(x-y)) f(y)dy             (1)
```

on `L2(-1,1)`. Let `psi_(m,c)` be a real normalized eigenfunction with simple eigenvalue
`nu_m(c)`, and choose the fixed-mode branch continuously. In the CCM normalization put

```text
c=2*pi*lambda^2,
e_(m,lambda)(x)=lambda^(-1/2) psi_(m,c)(x/lambda),
d_m(lambda)=1-nu_m(2*pi*lambda^2).                                  (2)
```

Thus `e_(m,lambda)` is normalized on `[-lambda,lambda]`. For the positive compressed-Fourier
sector used by CCM, write

```text
e_0=e_(0,lambda),   e_1=e_(4,lambda),
d_0=1-chi_0^2,      d_1=1-chi_4^2,
ell_j=integral_R e_j,
g_lambda=(ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2).               (3)
```

The source `g_lambda` has unit norm and zero integral.

## Exact endpoint-response identity

`[PROVED HERE]` For every simple prolate branch,

```text
d/dc log(nu_m(c))=2*|psi_(m,c)(1)|^2/c.                             (4)
```

Equivalently, in the scaled CCM variable,

```text
|e_(m,lambda)(lambda)|^2
 =-d_m'(lambda)/(4*(1-d_m(lambda))).                                (5)
```

### Proof

Let

```text
(F_c f)(x)=integral_(-1)^1 exp(i*c*x*y)f(y)dy.
```

Direct calculation gives

```text
Q_c=(c/(2*pi)) F_c^* F_c.                                          (6)
```

Hellmann--Feynman and differentiation of the kernel in `(1)` give

```text
nu_m'(c)
 =1/pi * integral integral
    psi_(m,c)(x)psi_(m,c)(y)cos(c(x-y))dxdy
 =1/pi * |integral psi_(m,c)(x)exp(i*c*x)dx|^2.                     (7)
```

The finite-Fourier eigenrelation says

```text
F_c psi_(m,c)=mu_m(c)psi_(m,c).
```

Evaluation at `x=1` and `(6)` give

```text
|integral psi_(m,c)(x)exp(i*c*x)dx|^2
 =|mu_m(c)|^2 |psi_(m,c)(1)|^2
 =(2*pi/c)nu_m(c)|psi_(m,c)(1)|^2.                                 (8)
```

Equations `(7)`--`(8)` prove `(4)`. Scaling the endpoint by `lambda^(-1/2)` and using
`dc/dlambda=4*pi*lambda` proves `(5)`.

## Fixed-mode endpoint asymptotic

The classical fixed-mode prolate expansion, in its differentiable Poincare form, gives for every
fixed `m`

```text
d_m(lambda)
 =A_m lambda^(2m+1) exp(-4*pi*lambda^2)
    *(1+O(lambda^(-2))),

d_m'(lambda)/d_m(lambda)
 =-8*pi*lambda+(2m+1)/lambda+O(lambda^(-3)),                        (9)
```

with `A_m>0`. The first line is the Fuchs asymptotic already used in the constrained-prolate cards;
the differentiated expansion is supplied by the classical full fixed-mode PSWF expansion, not by
formal differentiation of an isolated `~` statement.

Combining `(5)` and `(9)` proves

```text
|e_(m,lambda)(lambda)|^2/(lambda*d_m(lambda)) -> 2*pi.              (10)
```

## Endpoint constant for the constrained source

For `m=0,4`, `(9)` implies

```text
d_0/d_1=O(lambda^(-8)),
e_0(lambda)/e_1(lambda)=O(lambda^(-4)).                             (11)
```

The exact constrained-prolate theorem gives

```text
ell_0^2/(ell_0^2+ell_1^2)->8/11.                                   (12)
```

Equations `(3)`, `(10)`--`(12)` therefore yield

```text
|g_lambda(lambda)|^2/(lambda*d_1(lambda)) ->16*pi/11.               (13)
```

The leading lower exterior term in the Poisson endpoint expansion is

```text
a_lambda T_(L_lambda)(s),
a_lambda=g_lambda(lambda)/(pi*sqrt(lambda)),
L_lambda=2*pi*lambda^2,
T_L(s)=e^(-s/2)S(L e^s).                                           (14)
```

Hence

```text
|a_lambda|^2/d_1(lambda) ->16/(11*pi).                              (15)
```

## Exact all-prime response constant

Define the complete lower-exterior prime-dilation quadratic response of the leading endpoint layer
by

```text
R_lambda
 =sum_(n>=2) Lambda(n)n^(-1/2)
    integral_0^infinity
      [a_lambda T_(L_lambda)(s)]
      [a_lambda T_(L_lambda)(s+log n)]ds.                           (16)
```

The full exterior sawtooth incidence theorem proves absolute convergence and

```text
sum_(n>=2) Lambda(n)n^(-1/2)
  integral_0^infinity T_(L_lambda)(s)T_(L_lambda)(s+log n)ds
 ->pi^2/12 * (-zeta'(2)/zeta(2)).                                  (17)
```

Multiplying `(15)` and `(17)` gives the claimed exact limit:

```text
R_lambda/d_1(lambda)
 ->(4*pi/33)*(-zeta'(2)/zeta(2)).                                  (18)
```

Every quantity on the right is positive.

## Signed prime contribution to the exterior Weil form

In additive logarithmic coordinates, the prime part of the even screw kernel is

```text
K_prime(t)
 =-sum_(n>=2) Lambda(n)n^(-1/2)
    *(delta_(log n)(t)+delta_(-log n)(t)).                          (19)
```

Let the leading lower tail be supported on `x<=-log(lambda)` and write

```text
b_lambda^0(-log(lambda)-s)=a_lambda T_(L_lambda)(s),  s>=0.
```

The two atoms in `(19)` give equal correlations, so the prime part of the global Weil form is

```text
Q_prime(b_lambda^0,b_lambda^0)=-2 R_lambda.                         (20)
```

Therefore `(18)` yields the signed asymptotic

```text
Q_prime(b_lambda^0,b_lambda^0)/d_1(lambda)
 ->-(8*pi/33)*(-zeta'(2)/zeta(2)).                                 (21)
```

## Positive consequence for the CCM route

The leading exterior prime layer is now calibrated at the same exponential scale as the
constrained positive-sector gap:

```text
leading prime endpoint response = explicit positive constant*d_1+o(d_1),
actual prime Weil contribution  = explicit negative constant*d_1+o(d_1).             (22)
```

Thus the true-Weil comparison must preserve and combine three `d_1`-scale quantities rather than
merely bound an unspecified small tail:

```text
the signed prime contribution in (21)
  + the archimedean endpoint response
  + the subleading/interior prime-incidence response.                                (23)
```

A proof that the sum in `(23)` equals a positive constant times `d_1`, with a remainder
`o(d_1)`, would prove that the CCM seed has cofinally vanishing positive Weil Rayleigh quotient.
Together with a matching true-gap or floor argument, this feeds respectively the determinant or
direct cofinal-Weil branch. Equation `(21)` supplies the first exact signed arithmetic coefficient
in that comparison.

The theorem does **not** identify the full exterior Weil form with `(16)`. Since `g_lambda` is
supported on `[-lambda,lambda]`, its summation vector vanishes identically for `u>lambda`; the
complete exterior representative is the lower tail. The remaining obligations are the
archimedean term, the full lower-tail remainder after subtracting `(14)`, and the passage from the
model seed to the true Weil ground state.

That remainder must be kept intact in the zeta-multiplier graph domain. In particular, the Poisson
central correction by itself is proportional to `e^(-s/2)`. Its isolated prime correlations would
contain `sum Lambda(n)/n`, which diverges. The source is nevertheless in the graph domain because
the central correction cancels with the rest of the exact Fourier tail. Thus pointwise endpoint-jet
sizes do not license a termwise Weil-form expansion; the positive next theorem is a bilinear
estimate for

```text
exact lower tail - a_lambda T_(L_lambda)
```

as one source-defined graph-domain vector.

## Novelty and significance verdict

### Parent overlap

- Slepian--Pollak and Fuchs supply `(4)` in equivalent normalization and the fixed-mode asymptotic
  input `(9)`.
- `constrained-prolate-two-mode-ground-state.md` supplies the `8/11` coefficient.
- `ccm-cofinal-prime-sawtooth-incidence-law.md` supplies absolute summability and the full
  exterior Euler scalar.

The exact constants `16/(11*pi)` and `(18)` were not located verbatim in the checked parent sources.
However, `ccm-prolate-endpoint-jet-resummation-law.md` proves that the fixed endpoint expansion is
not cofinally ordered at frequencies comparable to `lambda`. The vector `b_lambda^0` is therefore
a formal first-component calibration, not a proved leading approximation to the exact CCM tail.

After vocabulary erasure, the result is a direct combination of a classical endpoint response, a
constrained two-mode coefficient, and periodic dilation averaging. Its unproved connection to the
actual radial tail prevents it from clearing the significance gate even if the displayed constant
is novel as a formula. It is classified as a bridge. A significant new result must instead compute
the weighted dilation correlations of the **uniform radial-prolate profile** or prove the
renormalized exact-tail remainder theorem.

## References

- D. Slepian, H. O. Pollak, *Prolate spheroidal wave functions, Fourier analysis and uncertainty I*,
  Bell System Technical Journal 40 (1961), 43--63.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean status

**Partially formalized, 2026-08-04.**  The decision recorded here earlier ("the formal tree has no
sinc-kernel operator, parameter derivative, normalized prolate branch, or Fuchs asymptotic.  No Lean file is
added") is out of date on its first count: the tree owns the sinc kernel and the finite-Fourier layer, in
`formal/GaloisForLFunctions/RHTower/SlepianKernelFourier.lean`,
`SlepianKernelFubini.lean` and `SlepianBandCommutation.lean`:

- `sincSmooth`, `sincSmooth_zero`, **`sincSmooth_eq_integral`**, **`sincKernelSmooth_eq_integral`** — the sinc
  kernel with its removable singularity resolved, *equal* to the character integral.  This is equation `(6)`,
  `Q_c = (c/2 pi) F_c^* F_c`, at the level of kernels.
- **`double_integral_fourierChar_eq_sincKernel`** — the same identity in integrated form, so the band operator
  really is the Gram operator of the finite Fourier transform.
- `differentiable_sincSmooth`, `deriv_sincKernelSmooth_fst`, **`slepian_commutation`** — the kernel's
  smoothness and the commutation with the prolate operator.

Equation `(7)` is now proved as well, in
`formal/GaloisForLFunctions/RHTower/CCMEndpointResponseIdentity.lean`:

- `bandFourier`, `intervalIntegrable_bandFourier_integrand`, **`conj_bandFourier`** — the finite Fourier
  transform of a real function on the band, and the fact that conjugating it flips the frequency.
- **`double_integral_cos_eq_norm_sq`** — the cosine factorisation

  ```text
  int_(-1)^1 int_(-1)^1 psi(x) psi(y) cos(c(x-y)) dx dy = |int_(-1)^1 psi(x) exp(i c x) dx|²,
  ```

  for every real continuous `psi`.  This is exactly the second equality of `(7)`, and it is what converts the
  Hellmann–Feynman derivative of the sinc kernel — whose `c`-derivative is the *smooth* kernel
  `cos(c(x-y))/pi`, with no singularity — into a squared modulus.  No Fubini theorem is used: the product of
  the two single integrals is the double integral because each factor is constant in the other variable, and
  the real part passes through both integrals by the `RCLike` interchange.

The Fuchs asymptotic `(9)` and the constrained-prolate limit `(12)` remain imported.



Equations `(4)` and `(5)` are proved as well, in the same module — given the two branch inputs, they are
arithmetic:

- **`endpointResponse_eq`** — equation `(4)`.  From the Hellmann–Feynman derivative
  `nup = (1/pi) int int psi psi cos(c(x-y))`, the eigenrelation at the band edge
  `bandFourier c psi = mu · psi(1)`, and the operator identity in the form `nu = (c/2 pi)‖mu‖²`, it follows
  that `nup = 2 nu |psi(1)|²/c`.  The cosine factorisation supplies the middle step; nothing else is used.
- **`hasDerivAt_ccmGap`** — the chain rule in the CCM variable: `d(λ) = 1 - nu(2 pi λ²)` has derivative
  `-nup · 4 pi λ`.
- **`endpointResponse_scaled`** — equation `(5)`: with `|e_(m,λ)(λ)|² = |psi(1)|²/λ` and `1 - d = nu`, the
  identity `(4)` is exactly `|e_(m,λ)(λ)|² = -d'(λ)/(4(1 - d(λ)))`.

So the whole of `(4)`–`(5)` is unconditional modulo two named inputs about the branch: the Hellmann–Feynman
derivative of the sinc family, and the finite-Fourier eigenrelation for a normalized eigenfunction.  Both are
statements about a differentiable simple eigenvalue branch, which is the layer of spectral theory this card
imports.


**Hellmann–Feynman itself is now proved**, as general infrastructure in
`formal/GaloisForLFunctions/HTGeometry/HellmannFeynman.lean` — mathlib has no such lemma:

- **`hellmann_feynman`** — for a differentiable curve of normalized vectors with
  `A t (psi t) = nu t • psi t`, if the curve `t ↦ A t (psi t)` has derivative `w + A c (psi' c)` — `w` being
  the family's own motion, i.e. `(dA/dc) psi` — and `A c` is self-adjoint against `psi'(c)`, then
  `nu'(c) = ⟪psi c, w⟫`.  The eigenvector's motion cancels because
  `⟪psi, A psi'⟫ = ⟪A psi, psi'⟫ = nu ⟪psi, psi'⟫`, so nothing about `psi'` is needed beyond its existence;
  self-adjointness is needed only against that one vector, and only the value at `c` is used.

- **`endpointResponse_of_hellmannFeynman`** (in the endpoint module) — the composition.  Given the
  Hellmann–Feynman data, the identification of `⟪psi, w⟫` with the double integral of the cosine kernel (which
  is the `c`-derivative of the sinc kernel), the finite-Fourier eigenrelation at the band edge, and the
  operator identity `(6)`, the conclusion is `(4)`: `nu'(c) = 2 nu(c) |psi(1)|²/c`.

So of the two branch inputs, the *differentiation* half is no longer an import: what remains is the
representation-theoretic half — that the eigenfunction of the band operator satisfies the finite-Fourier
eigenrelation, and that the abstract expectation is the double integral of the kernel — together with the
imported Fuchs expansion `(9)` and constrained limit `(12)`.


Both remaining spectral inputs are now reduced to their true content:

- **`exists_scalar_of_commuting_of_simple`** (in the Hellmann–Feynman module) — if `F` commutes with `Q`, is
  homogeneous, and the `nu`-eigenspace of `Q` is spanned by `psi`, then `F psi = mu • psi` for some scalar.
  So the finite-Fourier eigenrelation is *not* an extra analytic assumption: it is a consequence of the band
  eigenrelation together with the commutation `Q_c = (c/2 pi) F_c^* F_c` and simplicity of the branch — which
  is the hypothesis the card already carries ("every simple prolate branch").
- **`expectation_cosKernel_eq`** — the expectation of the cosine-kernel operator, in the integral realisation
  of the inner product, is exactly the double integral of `(7)`:
  `int psi(x) (int cos(c(x-y))/pi · psi(y) dy) dx = (1/pi) int int psi psi cos(c(x-y))`.  No Fubini theorem is
  needed: the iterated order is kept and only the outer factor is pulled inside.

What the card still imports is therefore only the classical asymptotic input — the differentiated fixed-mode
(Fuchs) expansion `(9)` and the constrained limit `(12)` — plus the existence of a differentiable simple
branch with a normalized eigenfunction, which is the spectral-theory statement the parent sources supply.


The family's own differentiability — the last analytic ingredient of the Hellmann–Feynman step — is proved at
kernel level, uniformly:

- **`abs_sin_add_sub_taylor_le`** — `|sin(a+b) - sin a - b cos a| <= b²`, by the mean value inequality applied
  to `t ↦ sin(a+t) - sin a - t cos a`, whose derivative `cos(a+t) - cos a` is bounded by `|t|`.
- **`abs_sincSmooth_taylor_le`** — for every aperture `c`, increment `h` and kernel variable `u`,

  ```text
  |sincSmooth (c+h) u - sincSmooth c u - h · cos(c u)/pi| <= h² |u| / pi.
  ```

  The bound is uniform in `u`, and at `u = 0` the kernel is *linear* in `c` (`sincSmooth c 0 = c/pi`), so the
  error vanishes identically there — the removable singularity causes no trouble.  Since the band is compact,
  a uniform kernel bound is exactly Hilbert–Schmidt differentiability of the operator family, with derivative
  the cosine-kernel operator whose expectation `(7)` computes.

**The branch itself is now proved too**, in the generality the card needs — Kato-type perturbation theory for a
compact symmetric family, which mathlib does not have.  Three new modules:

- `HTGeometry/SimpleEigenvalueBordered.lean` — the *bordered system* of a simple eigenvalue.  Instead of
  inverting `T = A - nu_0`, which is impossible because `T` kills the eigenvector, one inverts
  `S (phi, t) = (T phi - t · psi_0, ⟪psi_0, phi⟫)` on `E × R`.  From a pseudo-inverse `R` of `T` modulo the
  eigendirection the inverse is written down explicitly, `S^{-1}(y, a) = (R y + a psi_0, -⟪psi_0, y⟫)`, and
  `borderedMap_bijective` proves both composites.  The left inverse is where simplicity enters:
  `T (R (T phi) - phi) = 0` puts the difference in `ker T = span psi_0`, and pairing with `psi_0` pins the
  coefficient.  No compactness, no completeness, no continuity of the inverse.

- `HTGeometry/SimpleEigenvalueBranch.lean` — the implicit function theorem applied to the *eigen-residual*
  `f (c, (phi, nu)) = (A c phi - nu phi, ⟪psi_0, phi⟫ - 1)`, whose zero set is exactly the set of eigenpairs
  normalized against `psi_0`.  `hasStrictFDerivAt_eigenResidual` computes its derivative and
  `eigenResidualDeriv_comp_inr` identifies the partial derivative in `(phi, nu)` with the bordered map, so
  `borderedCLM_isInvertible` is precisely the invertibility hypothesis of mathlib's
  `implicitFunctionOfProdDomain`.  Out come `exists_differentiable_simple_eigen_branch` (a differentiable
  branch with the linear normalization `⟪psi_0, psi c⟫ = 1`),
  `exists_differentiable_normalized_simple_eigen_branch` (rescaled by `‖psi c‖^{-1}`, hence a genuine unit
  eigenvector, differentiable because the norm is `1` at the base point), and
  `exists_normalized_branch_deriv_eq_expectation` — the branch *plus* `nu'(c_0) = ⟪psi_0, w⟫`.  The last step
  needs Hellmann–Feynman with a merely local eigenrelation, so `hellmann_feynman_eventually` was added and the
  global form derived from it.

- `HTGeometry/SimpleEigenvalueCompactBranch.lean` — the pseudo-inverse is *constructed* for a compact
  symmetric operator, so no hypothesis is left.  On `W = {phi | ⟪psi_0, phi⟫ = 0}` — closed, hence complete —
  the operator restricts (symmetry plus the eigenrelation), the restriction is compact
  (`IsCompactOperator.restrict'`), and `nu_0` is *not* an eigenvalue of the restriction: by simplicity an
  eigenvector there would be a multiple of `psi_0`, which lies in `W` only if it is zero.  So the Fredholm
  alternative puts `nu_0` in the resolvent set of the restriction, and the resolvent composed with the
  projection `y ↦ y - ⟪psi_0, y⟫ psi_0` *is* the pseudo-inverse
  (`exists_pseudoInverse_of_isCompactOperator`) — no gap estimate, no open mapping theorem, no contour
  integral.  The capstone `exists_normalized_branch_of_isCompactOperator` therefore reads: a compact symmetric
  operator with a simple nonzero eigenvalue, perturbed differentiably, has a differentiable branch with a
  normalized eigenvector and `nu'(c_0) = ⟪psi_0, w⟫`.

All of it is unconditional and axiom-clean (`propext, Classical.choice, Quot.sound`).  What the card still
imports is therefore only the classical asymptotic input — the differentiated fixed-mode (Fuchs) expansion
`(9)` and the constrained limit `(12)` — together with the Hilbert-space realisation of the concrete band
operator `bandTransform` as a compact symmetric operator on `L²[-1, 1]`, which is what would let the abstract
branch theorem be instantiated on the prolate family rather than merely applied to it.

## Lean gates

- [x] Lean: the sinc kernel equals the finite-Fourier character integral — equation `(6)` (already in the
  tree)
- [x] Lean: the cosine factorisation of equation `(7)`
- [x] Lean: equations `(4)` and `(5)` from the two branch inputs (arithmetic, once the factorisation is in
  hand)
- [x] Lean: **Hellmann–Feynman** for a differentiable normalized branch — new general infrastructure,
  absent from mathlib — and its composition with the factorisation, giving `(4)` from the spectral inputs
- [x] Lean: the finite-Fourier eigenrelation reduced to commutation plus simplicity, and the expectation of
  the kernel derivative identified with the double integral of `(7)`
- [x] Lean: the family's differentiability in the aperture — a uniform second-order kernel bound, hence
  Hilbert–Schmidt differentiability with the cosine kernel as derivative
- [x] Lean: existence of a differentiable simple branch with normalized eigenfunction — Kato-type
  perturbation theory for a compact symmetric family, absent from mathlib: bordered system, implicit function
  theorem for the eigen-residual, and the Fredholm construction of the pseudo-inverse
- [ ] Lean: the concrete band operator `bandTransform` realised as a compact symmetric operator on
  `L²[-1, 1]`, which instantiates the branch theorem on the prolate family
- [ ] Lean: the differentiated fixed-mode (Fuchs) expansion `(9)` — imported classical asymptotics
- [ ] Lean: the constrained limit `(12)` and the response constants `(13)`–`(18)`

## Gates

- [x] exact endpoint-response identity proved
- [x] fixed-mode endpoint scale derived
- [x] constrained endpoint coefficient derived
- [x] growing all-prime response constant derived
- [ ] independent proof of the differentiated fixed-mode normalization
- [ ] exact archimedean endpoint response
- [ ] subleading/interior incidence remainder `o(d_1)`
- [ ] true Weil Rayleigh-excess or cofinal-floor transfer
