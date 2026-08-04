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

All of it is unconditional and axiom-clean (`propext, Classical.choice, Quot.sound`).

**The abstract branch theorem is now instantiated on the actual band operator**, in two further modules:

- `RHTower/ProlateL2Operator.lean` — the band operator as a bounded operator on the *real* Hilbert space
  `L²[-1, 1]`.  `continuousKernelOperator` sends a continuous kernel on the square to an operator, by way of
  the field form of the Hilbert–Schmidt kernel theorem (generalised in `FiniteTimeBandFourierCompact` from `ℂ`
  to any `RCLike` field for this purpose), so `isCompactOperator_continuousKernelOperator` is immediate and
  `continuousKernelOperator_symmetric` is Fubini for a bounded kernel against two `L¹` functions.  Also proved
  here: the values are the inner products against the kernel rows (`continuousKernelOperator_coeFn_inner`),
  whence `norm_le_of_kernel_repr : ‖B‖ ≤ (b-a)‖G‖` for any operator represented by a continuous kernel `G`
  — Cauchy–Schwarz pointwise, then one factor `√(b-a)` for each of the row norm and the output `L²` norm.
  Specialised to the smoothed sinc kernel: `isCompactOperator_bandOperatorL2`, `bandOperatorL2_symmetric`.

- `RHTower/ProlateL2Family.lean` — the aperture dependence.  The uniform second-order kernel bound
  `abs_sincSmooth_taylor_le` transfers to operator norm through `norm_le_of_kernel_repr` (a linear combination
  of kernel operators is the kernel operator of the combination, `coeFn_comb_inner`), giving
  `‖B(c+h) - B(c) - h · Cos_c‖ ≤ 4h²/pi`; hence `hasDerivAt_bandOperatorL2`, and with the Lipschitz bound
  `‖Cos_{c₁} - Cos_{c₂}‖ ≤ (4/pi)|c₁ - c₂|` the family is `C¹`, hence strictly differentiable, hence — via
  `HasStrictFDerivAt.clm_apply` — jointly strictly differentiable in `(c, phi)` in exactly the split form the
  branch theorem consumes.  The capstone `exists_bandOperatorL2_branch` reads: *a simple nonzero eigenvalue of
  the band operator, with normalized eigenfunction, extends to a differentiable branch of normalized
  eigenpairs with* `nu'(c_0) = ⟪psi_0, Cos_{c_0} psi_0⟫`.

- `RHTower/ProlateL2Regularity.lean` — the dictionary to the classical prolate functions.  The band operator
  smooths, so an `L²` eigenvector has a distinguished continuous representative, namely its own band integral
  `Phi(x) = nu⁻¹ ∫ sinc_c(x-y) psi(y) dy`.  `continuous_eigenExtension` proves `Phi` continuous on all of `ℝ`
  by dominated continuity, uniformly in `x` thanks to the global bound `abs_sincSmooth_le : |sinc_c(u)| ≤
  |c|/pi` (from `|sin t| ≤ |t|`); `eigenExtension_ae_eq` identifies it with `psi` almost everywhere; and
  `bandTransform_eigenExtension` gives the *pointwise* eigenrelation of the corpus's function-level transform,
  `bandTransform c Phi x = nu · Phi x` for **every** real `x` — which is the form the Slepian differential
  machinery acts on.  The subtype-to-interval integral conversion is `integral_subtype_unit`.

So the spectral half of `(4)`–`(5)` is now proved for the operator itself, not assumed, and it is stated both
in the Hilbert space and pointwise.  What the card still imports is only the classical asymptotic input: the
differentiated fixed-mode (Fuchs) expansion `(9)` and the constrained limit `(12)`.

**The constant-transport half of `(10)`--`(18)` is proved**, in
`RHTower/CCMEndpointResponseConstants.lean`.  Each equation of the card that is a *limit inference* is now a
theorem whose hypotheses are exactly the named inputs, and nothing else:

- `tendsto_endpointSq_div_leakage` — equation `(10)`: from the endpoint identity `(5)` in the form
  `E = -d'/(4(1-d))` together with `d -> 0` and the logarithmic asymptotic `d'/(lambda d) -> -8 pi`, the
  normalized endpoint square tends to `2 pi`.
- `tendsto_endpointSq_div_reference` — the transport form of `(11)`: a mode whose leakage is negligible
  against the reference leakage has vanishing normalized endpoint square.
- `tendsto_ellSqRatio_of_deltaRatio` — equation `(12)`: the constrained ground-state statement
  `delta/d_1 -> 8/11` and the coefficient statement `ell_0²/(ell_0²+ell_1²) -> 8/11` are the same, given the
  exact orthogonality formula `(3)` for `delta` and negligibility of the ground leakage.
- `tendsto_constrainedEndpointSq` — equation `(13)`: for the two-mode seed
  `g = (ell_1 e_0 - ell_0 e_1)/sqrt(ell_0²+ell_1²)` the normalized endpoint square tends to `16 pi/11`.  The
  ground term and the cross term vanish; the cross term needs the elementary bound
  `|2 ell_0 ell_1/(ell_0²+ell_1²)| <= 1` and the identity `|uv|/w = sqrt(u²/w) sqrt(v²/w)`
  (`tendsto_cross_div_zero`).
- `tendsto_lowerExteriorAmplitudeSq` — equation `(15)`: the endpoint scaling `a = g(lambda)/(pi sqrt lambda)`
  turns `16 pi/11` into `16/(11 pi)`.
- `tendsto_primeResponse_div_leakage` — equation `(18)`: the amplitude constant against the exterior sawtooth
  incidence constant `pi²/12 · z` gives `(4 pi/33) z`.

So the arithmetic of the response constants is machine-checked end to end, and what remains are exactly three
analytic imports: the differentiated fixed-mode asymptotic `(9)`, the constrained ground-state ratio
`delta/d_1 -> 8/11`, and the exterior sawtooth incidence constant `(17)`.

**The exterior sawtooth incidence constant `(17)` is proved**, in
`RHTower/CCMEndpointSawtoothResponse.lean`, by identifying the endpoint layer's own pairing with the
sawtooth incidence layer the tree already owns (`CCMSawtoothDilationIncidence`,
`CCMSawtoothExteriorTail`: the exact period mean `1/(12 n)`, the uniform `O(1/L)` averaging error, the
`O(1/n)` domination and the dominated limit):

- `sawTail L s = e^{-s/2} S(L e^s)`, and `sawTail_mul_shift` computes the pairing with the `log n`
  translate pointwise: the two half-weights combine to `e^{-s} n^{-1/2}`, the dilation
  `L e^{s+log n} = n L e^s` moves inside the second sawtooth, and `S = pi · sawUnit(·/(2 pi))`
  contributes `pi²`.  `integral_sawTail_mul_shift` turns this into the corpus's exterior response
  through the change of variables `x = L e^s`.
- `tendsto_sawTailPrimeResponse` — equation `(17)`: the complete von Mangoldt incidence of the
  endpoint tail converges to `(pi²/12) sum Lambda(n) n^{-2}` as the aperture grows.
- `ofReal_tsum_vonMangoldt_div_sq` identifies that Euler scalar with `-zeta'(2)/zeta(2)` (mathlib's
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` transported across the real-to-complex cast), and
  `tendsto_sawTailPrimeResponse_ofReal` states `(17)` with the zeta constant.
- `tendsto_primeResponse_div_leakage_sawTail` — equation `(18)` with the constant supplied: given the
  amplitude limit `(15)`, the response over the reference leakage tends to
  `(4 pi/33) sum Lambda(n) n^{-2}`.

The whole chain of the card is therefore machine-checked from one place onwards: the only inputs still
imported are the differentiated fixed-mode asymptotic `(9)` and the constrained ground-state ratio
`delta/d_1 -> 8/11`.

**The imported asymptotic `(9)` is now reduced to its envelope form.**  An envelope alone says nothing
about derivatives, but one structural fact repairs that, and the repair is proved in
`HTGeometry/LogDerivativeFromEnvelope.lean`:

- `tendsto_deriv_of_monotoneOn_of_tendsto_div` (and its antitone companion) — if `f x / x -> L` and
  `deriv f` is eventually monotone in either direction, then `deriv f -> L`.  Two applications of the
  mean value theorem: monotonicity puts `deriv f u` on one side of every slope over `[u, c]`, whose
  limit is `L`, which bounds the derivative; the slope over `[c/2, c]` also tends to `L` and is caught
  between the derivative's endpoint values, which squeezes it.
- `tendsto_log_div_of_envelope` — a two-sided envelope `c₁ x^k e^{-b x} <= D x <= c₂ x^k e^{-b x}`
  gives `log (D x)/x -> -b`.
- `tendsto_logDeriv_of_envelope_of_antitoneOn` — the two combined: envelope plus antitone logarithmic
  derivative give `D'/D -> -b`.
- `tendsto_scaled_logDeriv` — under the CCM reparametrisation `c = 2 pi lambda²` this becomes
  `d'(lambda)/(lambda d(lambda)) -> -(2 · 2 pi · b)`, which at `b = 2` is exactly the card's `-8 pi`.
- `tendsto_endpointSq_div_leakage_of_envelope` (in `CCMEndpointResponseConstants`) — the composition:
  from the envelope, the antitone logarithmic derivative and the endpoint identity `(5)`, equation
  `(10)` follows.

So `(9)` is needed only in its *envelope* form — the two-sided fixed-mode Fuchs scale, which is the
form the tree already models in `ConstrainedProlateLeakageStructure.FuchsEnvelope` — together with
antitonicity of the leakage logarithmic derivative.  The sharp constant `A_m` is not used anywhere.

**The `8/11` is now derived, not imported.**  `hermiteWeight j = binom(4j, 2j)/16^j`, with
`hermiteWeight 1 = 3/8`, and `tendsto_ellSqRatio_of_hermiteLimits` shows that the prolate-to-Hermite
coefficient limits `ell_0² -> A`, `ell_1² -> A · 3/8` force

```text
ell_0²/(ell_0²+ell_1²) -> 1/(1 + 3/8) = 8/11,
ell_1²/(ell_0²+ell_1²) -> 3/11,
```

so `tendsto_constrainedEndpointSq_of_hermiteLimits` gives `(13)` directly from those limits — the
constrained-prolate ground-state theorem is not needed as a separate input, only the Hermite limits it
itself rests on.

**Equation `(6)` is now proved at the level of the quadratic form**, in
`RHTower/BandQuadraticFormFourier.lean` — the form in which the variational characterisation of the
band eigenvalues is stated:

- `sincKernelSmooth_eq_cos_integral` — the real cosine form of the kernel,
  `sinc_c(x-y) = (c/(2 pi)) ∫_(-1)^1 cos(c t (x-y)) dt`, proved by evaluating the elementary cosine
  integral and matching the removable singularity at `x = y` and the degenerate aperture `c = 0`.
- `swap_interval_integral` — Fubini on a box for a jointly continuous integrand, in interval-integral
  form (compactness gives integrability, `Measure.prod_restrict` matches the two product measures).
- `double_integral_sincKernel_eq_energy` — the band quadratic form of a continuous test function is a
  Fourier energy:

  ```text
  ∫∫ sinc_c(x-y) psi(x) psi(y) = (c/(2 pi)) ∫_(-1)^1 ‖F_(c t) psi‖² dt,
  ```

  by averaging the cosine factorisation `(7)` over the band; the triple integral is rearranged by two
  applications of the box Fubini, the outer one using continuity of the parametric inner integral.
- `double_integral_sincKernel_nonneg` — hence the band form is positive semidefinite for every
  nonnegative aperture, which is what makes the largest band eigenvalue the maximum of a nonnegative
  Rayleigh quotient and gives the variational route to the leakage envelope.

**The concentration reading of the band form is proved**, in `RHTower/BandFrequencyWindow.lean`:

- `bandFourier_eq_fourier` — the card's finite-Fourier moment is mathlib's Fourier integral of the
  band truncation, at frequency `-a/(2 pi)`: the `2 pi` of mathlib's character is absorbed in the
  frequency, nothing else changes.
- `energy_eq_frequency_window` — the change of variables `xi = -c t/(2 pi)` turns the band average of
  moments into an integral over the frequency window, its Jacobian cancelling the prefactor `c/(2 pi)`
  exactly.
- `double_integral_sincKernel_eq_frequency_energy` — hence

  ```text
  ∫∫ sinc_c(x-y) psi(x) psi(y) dx dy = ∫_(-c/2pi)^(c/2pi) ‖𝓕 psi(xi)‖² d xi
  ```

  for every continuous test function: the band quadratic form *is* the spectral energy inside the
  band.  With Plancherel this exhibits the leakage as the spectral tail outside the band, which is the
  exact quantity any envelope estimate has to bound — and the form in which an explicit trial function
  gives an upper envelope.

**The leakage of a test function is now an exact spectral tail**, in
`RHTower/BandLeakageSpectralTail.lean`:

- `memLp_bandTrunc`, `integrable_bandTrunc` — the band truncation of a continuous function lies in
  every `L^p` of the line (bounded, supported in a finite-measure set).
- `lp_norm_sq_eq_integral` — the squared `L²` norm as an integral of squared norms.
- `coeFn_fourier_bandTruncL2` — mathlib's `L²` Fourier transform of the truncation's class is its
  classical Fourier integral, via the corpus bridge `l2_fourier_coeFn_eq_l1_fourier_of_integrable`.
- `integral_norm_sq_fourier_bandTrunc` — Plancherel: total spectral energy equals `L²` energy.
- `leakage_eq_spectral_tail` — hence, for every continuous test function and every positive aperture,

  ```text
  ∫_(-1)^1 psi² - ∫∫ sinc_c(x-y) psi(x) psi(y) = ∫_(|xi| > c/(2 pi)) ‖𝓕 psi(xi)‖² d xi.
  ```

  The left side is the Rayleigh deficit of the band operator at `psi`, so *any* explicit test function
  now yields an upper bound for the band leakage, and the envelope's exponential rate is exactly the
  decay rate of the best test function's spectral tail.  The naive trials (Gaussian, smooth bumps) give
  rate `e^{-c}`; the classical rate `e^{-2c}` needs a trial whose in-band spectral mass is
  exponentially large, e.g. the Kaiser–Bessel window `I_0(c sqrt(1-x²))` with Fourier pair
  `2 sinh(sqrt(c²-omega²))/sqrt(c²-omega²)` — which is the next construction (`I_0` is absent from
  mathlib).

**The computational core of the Kaiser–Bessel trial is proved**, in `RHTower/BandTrialMoments.lean`:
the even moments of the trial weights `(1-x²)^k`,

```text
M(j, k) = ∫_(-1)^1 x^(2j) (1 - x²)^k dx,      M(j, k) · j! · (2j+2k+2)! = (2j)! · k! · 4^(k+1) · (j+k+1)!,
```

with no Beta or Gamma function anywhere: `(1-x²)^(k+1) = (1-x²)^k - x² (1-x²)^k` gives the recursion
`M(j, k+1) = M(j, k) - M(j+1, k)` (`trialMoment_succ`), the base case is the elementary power integral,
and the induction step is the polynomial identity

```text
(2j+2k+4)(2j+2k+3) - 2(2j+1)(j+k+2) = 4(k+1)(j+k+2),
```

discharged by `linear_combination`.  Stating the closed form multiplicatively keeps every step inside
the factorials.  These moments are exactly the coefficients needed to integrate the Kaiser–Bessel
series `I_0(c sqrt(1-x²)) = sum_k (c²/4)^k (1-x²)^k/(k!)²` against `cos(omega x)` term by term, which is
the route to the trial's Fourier pair and hence to the upper leakage envelope.

The first of those two interchanges is done: `integral_trialWeight_cos` gives, for every weight and
every frequency,

```text
∫_(-1)^1 (1-x²)^k cos(omega x) dx = sum_j (-1)^j omega^(2j) M(j, k)/(2j)!,
```

by term-by-term integration of the cosine series, dominated by the exponential series (the pointwise
bound `‖term‖ <= |omega|^(2j)/(2j)!` on the band, `integral_tsum_of_summable_integral_norm`).  So each
trial weight's finite-Fourier transform is now an explicit power series in the frequency whose
coefficients are the closed-form moments.

The algebra that collapses the resulting double series is proved as well:

- `trialCoeff_eq` — the `(j, k)` term of the Kaiser–Bessel cosine series is exactly a binomial
  coefficient over an odd factorial,

  ```text
  (c²/4)^k/(k!)² · (-1)^j omega^(2j) M(j,k)/(2j)! = 2 binom(j+k, j) (c²)^k (-omega²)^j/(2(j+k)+1)!,
  ```

  after expanding `(j+k+1)! = (j+k+1) binom(j+k,j) j! k!` and `(2j+2k+2)! = 2(j+k+1)(2(j+k)+1)!`.
- `antidiagonal_trialCoeff_sum` — summing that over `j + k = m` is the binomial theorem:

  ```text
  sum_(j+k=m) 2 binom(m,j)(c²)^k(-omega²)^j/(2m+1)! = 2 (c² - omega²)^m/(2m+1)!.
  ```

The regrouping itself is now proved too, in `RHTower/BandTrialSeries.lean`:

- `antidiagonal_binomial_sum` — the collapse for arbitrary `a`, `b`, so the same lemma serves the
  alternating series (`a = -omega²`) and its absolute values (`a = +omega²`).
- `tsum_eq_tsum_sum_antidiagonal` — antidiagonal reindexing of *any* summable family on `ℕ × ℕ`
  (mathlib has this only inside the Cauchy product formula), via
  `sigmaAntidiagonalEquivProd` and `Summable.tsum_sigma'`.
- `summable_trialTerm` — summability of the double family: the absolute values collapse on each
  antidiagonal to `2 (omega² + c²)^m/(2m+1)!`, and `summable_oddFactorial_pow` dominates that by the
  exponential series (`m! <= (2m+1)!`).
- `tsum_trialTerm_eq` — hence

  ```text
  sum_(j,k) 2 binom(j+k,j)(c²)^k(-omega²)^j/(2(j+k)+1)! = sum_m 2 (c² - omega²)^m/(2m+1)!,
  ```

  which is `2 sinh(sqrt(c²-omega²))/sqrt(c²-omega²)` inside the band and
  `2 sin(sqrt(omega²-c²))/sqrt(omega²-c²)` outside it.

**The trial's band transform is now proved**, in `RHTower/BandKaiserTrial.lean`:

```text
K_c(x) = sum_k (c²(1-x²)/4)^k/(k!)²  (= I_0(c sqrt(1-x²))),
∫_(-1)^1 K_c(x) cos(omega x) dx = sum_m 2 (c² - omega²)^m/(2m+1)!,
```

by term-by-term integration in the weight exponent (`summable_kaiserTerm`: squared factorials dominate
factorials, so the interchange is dominated by the exponential series), the moment expansion of each
weight transform, the coefficient identity, and the antidiagonal collapse; the iterated sum is
reindexed through `Equiv.prodComm` and `Summable.tsum_prod'`.

Inside the band every term of the series is positive, so a *single* term bounds the transform below —
that is what makes the trial's in-band spectral mass exponentially large, with no Stirling estimate on
the trial itself.  Outside the band the same series is `2 sin(sqrt(omega²-c²))/sqrt(omega²-c²)`, whose
square has a polynomial tail integral.  Both closed forms and both mass bounds are now proved, in `RHTower/BandKaiserBounds.lean`:

- `tsum_oddFactorial_sinh`, `tsum_oddFactorial_sin` — the odd-factorial series is `2 sinh v/v` for a
  positive argument `v²` and `2 sin u/u` for a negative one `-u²` (mathlib's `Real.sinh_eq_tsum`,
  `Real.sin_eq_tsum` after pulling out `2/v`).
- `integral_kaiserTrial_cos_of_lt`, `integral_kaiserTrial_cos_of_gt` — hence the trial transform is
  `2 sinh(sqrt(c²-omega²))/sqrt(c²-omega²)` inside the band and
  `2 sin(sqrt(omega²-c²))/sqrt(omega²-c²)` outside it.
- `abs_integral_kaiserTrial_cos_le` — **the tail bound**: beyond the band edge the transform is at most
  `min(2, 2/sqrt(omega²-c²))` in absolute value, from `|sin t| <= min(1, |t|)`.
- `tsum_oddFactorial_mono`, `integral_kaiserTrial_cos_ge` — **the inner-band bound**: on `|omega| <= 1`
  the transform is at least `2 sinh(sqrt(c²-1))/sqrt(c²-1)`, because every term of the series is
  positive and monotone in `c² - omega²`; and `sinh_quotient_ge` turns that into `(e^v - 1)/v` with
  `v = sqrt(c²-1)`, i.e. exponential growth in the aperture.

So the trial's in-band spectral mass is at least of order `e^(2c)/c²` and its out-of-band mass is at
most of order `log c`, giving the ratio `O(c² log c) e^(-2c)`.  The tail integral is proved too, in `RHTower/BandKaiserTail.lean`:

- `min_four_le_cauchy` — the elementary envelope `min(4, 4/t²) <= 8/(1+t²)`.
- `sq_integral_kaiserTrial_cos_le` — since `omega² - c² >= (|omega| - c)²`, the square of the trial
  transform beyond the band edge is at most the Cauchy envelope `8/(1 + (|omega| - c)²)`.
- `integral_Ioi_cauchy_envelope` — the tail integral of that envelope is `4 pi`, *independent of the
  aperture* (improper FTC with primitive `8 arctan(omega - c)`).

So the trial's out-of-band spectral mass is bounded by the absolute constant `8 pi` (both sides), while
its in-band mass is at least of order `e^(2c)/c²`.  Both of those steps are now proved, in `RHTower/BandVariational.lean`:

- `one_sub_norm_le_rayleigh_deficit` — **the variational bound**: for any bounded operator on a real
  inner-product space and any nonzero vector, `1 - ‖B‖ <= (‖psi‖² - ⟪B psi, psi⟫)/‖psi‖²`.  It is pure
  Cauchy–Schwarz — the leakage envelope needs no spectral theorem, only that every Rayleigh quotient is
  at most the operator norm.
- `integral_eq_zero_of_odd`, `bandFourier_of_even` — **the even-test bridge**: on an even test function
  the finite-Fourier moment is real and equals the cosine transform, the sine part being an odd
  integral over a symmetric interval; and `kaiserTrial_even` supplies the evenness of the trial.

So every ingredient of the upper leakage envelope is proved: the trial, its transform, the two mass
bounds, the tail integral, the leakage-as-spectral-tail identity, and the variational bound.  That last bridge is now proved as well, in `RHTower/BandFormBridge.lean`:

- `inner_continuousKernelOperator_eq`, `norm_sq_eq_integral` (extracted in `ProlateL2Operator`) — the
  quadratic form and the energy of a kernel operator as subtype double integrals.
- `bandClass`, `coeFn_bandClass` — the `L²` class of a continuous test function on the band.
- `inner_bandOperatorL2_bandClass`, `norm_sq_bandClass` — the dictionary in interval integrals:

  ```text
  ⟪B_c (psi|), (psi|)⟫ = ∫∫ sinc_c(x-y) psi(x) psi(y),      ‖(psi|)‖² = ∫ psi².
  ```

- `one_sub_norm_bandOperatorL2_le` — hence the **function-level variational bound**: every continuous
  test function with nonzero band class bounds the band leakage,

  ```text
  1 - ‖B_c‖ <= [∫ psi² - ∫∫ sinc_c(x-y) psi psi]/∫ psi².
  ```

So the leakage of the true band operator is now bounded by a completely explicit function-level
quantity, and the Kaiser–Bessel trial supplies the numerator and denominator estimates
(`sq_integral_kaiserTrial_cos_le`, `integral_Ioi_cauchy_envelope`, `integral_kaiserTrial_cos_ge`).  `RHTower/BandKaiserContinuity.lean` adds what the assembly needs on the trial side:

- `kaiserSeries`, `continuousOn_kaiserSeries`, `continuous_kaiserSeries`, `continuous_kaiserTrial` —
  the trial is the entire series `sum_k u^k/(k!)²` at `u = c²(1-x²)/4`; on each ball the series is
  uniformly dominated, so the sum is continuous there, hence everywhere, hence so is the trial.  This
  makes the trial a legitimate test function for the variational bound.
- `norm_sq_fourier_bandTrunc_of_even` — for an even test function the spectral density is the square of
  the cosine transform, `‖𝓕 (trunc Phi) xi‖² = (∫ Phi(x) cos(2 pi xi x) dx)²` (the Fourier
  normalisation plus the even-test bridge).
- `norm_sq_fourier_bandTrunc_kaiser_le` — hence the trial's spectral density beyond the band edge obeys
  the Cauchy envelope `8/(1 + (|2 pi xi| - c)²)` in the Fourier variable.

The numerical assembly is now carried out in `RHTower/BandLeakageEnvelope.lean`, and it closes the
upper half of the leakage envelope for the **true** band operator, unconditionally:

- `integrable_cauchyShift`, `integral_cauchyShift` — a shifted and scaled Cauchy kernel is integrable
  on the line with the aperture-free value

  ```text
  ∫ 8/(1 + (a xi - b)²) d xi = 8 pi/a,
  ```

  by translation invariance of the volume and the scaling law of the Haar integral.  The shift is free:
  it is exactly what allows the band edge to be placed anywhere without changing the tail constant.
- `cauchyPair`, `folded_cauchy_le_pair`, `integral_cauchyPair` — the folded envelope
  `8/(1 + (|2 pi xi| - c)²)`, which is what the trial's density obeys, is dominated by the *sum* of the
  two shifted kernels centred at `+c` and `-c`; whichever sign the frequency has, one of the two
  reproduces the folded envelope exactly and the other is nonnegative.  The sum has total mass
  `2 · 8 pi/(2 pi) = 8` on the whole line, so folding costs a factor `2` and nothing else.
- `lt_abs_of_notMem_window`, `integral_tail_kaiser_le` — hence the trial's **entire** out-of-band
  spectral mass is at most `8`, an absolute constant with no dependence on the aperture.  No splitting
  of the tail into two half-lines is needed: the pointwise domination holds on the complement of the
  window and the two-sided envelope is integrable on all of `ℝ`.
- `sq_intervalIntegral_le` — the interval form of Cauchy–Schwarz against the constant function,
  `(∫_a^b f)² <= (b - a) ∫_a^b f²`, proved by expanding the nonnegative integral of `(f - mean)²`.
- `integral_kaiserTrial`, `energy_kaiserTrial_ge`, `energy_kaiserTrial_pos`,
  `bandClass_kaiserTrial_ne_zero` — the mean of the trial over the band is the `omega = 0` value of its
  transform, `2 sinh(c)/c`, so its energy is at least `(2 sinh(c)/c)²/2`; in particular the trial is a
  nonzero band class and admissible in the variational bound.
- **`one_sub_norm_bandOperatorL2_mul_sinh_le`** — the closed-form envelope

  ```text
  (1 - ‖B_c‖)·(2 sinh(c)/c)² <= 16,
  ```

  obtained by feeding the constant tail mass and the exponential energy into the function-level
  variational bound through the spectral-tail identity.
- **`one_sub_norm_bandOperatorL2_le_exp`** — hence, for every aperture `c >= 1`,

  ```text
  1 - ‖B_c‖ <= 64 c² e^(-2c).
  ```

This is the sharp exponential rate `e^(-2c)` of the classical leakage asymptotic, with an explicit
polynomial correction and an explicit absolute constant, proved for the corpus's own band operator
with no imported asymptotic.  Gaussian and polynomial trials cannot reach it — they give `e^(-c)`; the
Kaiser–Bessel window is what makes the in-band mass grow like `e^(2c)/c²` against an aperture-free
tail.

The trivial half of the envelope — `‖B_c‖ <= 1` — is *not* formal (the kernel is not small) but
spectral, and it is now proved in `RHTower/BandOperatorContraction.lean`, which also turns the envelope
into an aperture limit:

- `isFiniteMeasure_intervalVolume`, `compactSpace_interval`, `denseRange_toLp_interval` — the band
  subtype is a compact space carrying a finite measure, so its measure is automatically weakly regular
  and the continuous functions are dense in `L²[-1, 1]`.
- `exists_continuous_bandClass_eq` — every continuous function on the band is the restriction of a
  continuous function on the line (`IccExtend`), so the corpus's band classes exhaust the range of
  `toLp` and the density argument reaches all of the lemmas stated for test functions on the line.
- `forall_of_continuous_of_isClosed` — the transfer principle: a closed property of `L²` classes that
  holds on the continuous ones holds on all of them.
- `inner_bandOperatorL2_nonneg`, `inner_bandOperatorL2_le_norm_sq` — hence the band form of *every*
  `L²` class lies between `0` and its energy.  The upper half is the spectral-tail identity (the
  deficit is an integral of a square); the lower half is the Fourier-energy reading of the form.
- **`norm_bandOperatorL2_le_one`** — for a symmetric operator the norm is the supremum of the absolute
  Rayleigh quotients, so the band operator is a positive contraction: `‖B_c‖ <= 1`.
- **`abs_one_sub_norm_bandOperatorL2_le`** — combining with the envelope, `|1 - ‖B_c‖| <= 64 c² e^(-2c)`
  for `c >= 1`.
- **`tendsto_norm_bandOperatorL2_atTop`** — therefore `‖B_c‖ -> 1` as `c -> infinity`, at the
  exponential rate: at large aperture the band operator is asymptotically the identity on its own
  scale.

The *qualitative* form of the lower envelope — that the leakage is strictly positive — is now proved
as well, and it required building the Paley–Wiener side of the theory, which mathlib does not have.
`HTGeometry/CompactFourierEntire.lean` moves the frequency into the complex plane:

- `compactFourier`, `hasDerivAt_compactFourier`, `differentiable_compactFourier` — for a continuous
  amplitude on a compact interval, `z ↦ ∫_a^b f(x) e^(i z x) dx` is **entire**.  Differentiation under
  the integral is legitimate because on the interval the derivative of the integrand is dominated by
  the constant `sup|f| · max(|a|,|b|) · exp((‖z‖+1) max(|a|,|b|))`.
- **`entire_eq_zero_of_ae_vanishing_on_real_interval`** — an entire function vanishing *almost
  everywhere* on a nondegenerate interval of real frequencies vanishes identically.  A null set cannot
  swallow a punctured interval, so every punctured neighbourhood of the centre still contains a zero
  and the identity theorem applies.  The almost-everywhere form is what a vanishing tail *integral*
  delivers, so no continuity of the transform is needed.

`RHTower/BandUncertainty.lean` applies this to the band:

- `bandFourierEntire`, `bandFourierEntire_ofReal`, `differentiable_bandFourierEntire` — the spectral
  amplitude `xi ↦ 𝓕 (trunc Phi) (xi)` is the restriction to the real axis of an entire function of the
  frequency.
- **`eqOn_zero_of_spectral_tail_eq_zero`** — the qualitative uncertainty principle: a continuous test
  function whose spectral mass outside the window vanishes is zero on the open band.  Tail mass zero
  gives almost-everywhere vanishing beyond the band edge; the identity theorem spreads it to all
  frequencies; Fourier inversion (both the truncation and its transform are integrable, the latter
  because it is zero) returns the truncation at each of its continuity points.

`RHTower/BandStrictGap.lean` closes the gap with the Fredholm alternative:

- **`not_hasEigenvalue_one`** — `1` is not an eigenvalue of `B_c`.  An eigenvector at `1` has a
  continuous representative (the corpus regularity dictionary), its Rayleigh quotient is `1`, so its
  spectral tail vanishes, so by uncertainty it is zero on the open band — and the two endpoints are a
  null set, so its energy is zero, contradicting that an eigenvector is nonzero.
- **`norm_bandOperatorL2_lt_one`**, `one_sub_norm_bandOperatorL2_pos` — hence `‖B_c‖ < 1` for every
  aperture.  The Fredholm alternative leaves only two cases: `1` is an eigenvalue (excluded above) or
  `1` lies in the resolvent set, and then mathlib's Rayleigh theory gives a uniform gap
  `rayleigh <= ‖B_c‖ - eps`, which contradicts the norm being the supremum of the (nonnegative)
  Rayleigh quotients.

So the leakage is now known to satisfy `0 < 1 - ‖B_c‖ <= 64 c² e^(-2c)`, and in particular its
logarithm is defined — which is what any logarithmic-derivative statement about the leakage needs.
What remains is purely quantitative: the *rate* of the lower bound,
`1 - ‖B_c‖ >= c_0 c^(1/2) e^(-2c)`, and the antitonicity of the logarithmic derivative.  By the exact
endpoint ODE `(4)` the missing rate is equivalent to a lower bound on the endpoint value
`|psi_c(1)|²`, which is the differentiated form of the same classical asymptotic.

The structural input any sharp two-sided estimate must use is now formalized, in
`RHTower/BandLimitedExtension.lean`: the eigenfunctions are *band-limited*, in the Paley–Wiener sense.

- `swap_interval_integral_complex` — the complex rectangle Fubini (the corpus had only the real one).
- **`bandTransform_eq_windowIntegral`** — the sinc kernel is the inverse transform of the frequency
  window, so for every continuous test function

  ```text
  (B_c Phi)(x) = (c/2 pi) ∫_(-1)^1 F(-c t) exp (i c x t) dt,     F(omega) = ∫_(-1)^1 Phi(y) e^(i omega y) dy.
  ```

  Inserting the window representation of the kernel and interchanging the two compact integrals leaves
  the whole `x`-dependence in one exponential, whose frequency runs over a compact interval.
- `bandSpectrum`, `continuous_bandSpectrum`, `bandFourier_eq_compactFourier` — the corpus's
  finite-Fourier moment *is* a compact Fourier transform at a real frequency, so its continuity (indeed
  analyticity) in the frequency is free.
- `bandTransformEntire`, `bandTransformEntire_ofReal`, **`differentiable_bandTransformEntire`**,
  `norm_bandTransformEntire_le` — hence the band transform of any continuous test function extends to
  an entire function of exponential type `|c|`, with the explicit Paley–Wiener bound
  `‖F(z)‖ <= C e^(|c| |Im z|)` (the general growth lemma `norm_compactFourier_le` is in
  `CompactFourierEntire.lean`).
- **`exists_entire_extension_eigenExtension`** — an `L²` eigenfunction is `1/nu` times its own band
  transform, so **the prolate eigenfunctions are restrictions of entire functions of exponential type
  `c`**, with an explicit growth constant.

This is the frame in which the missing rate lives: the leakage compares the eigenfunction's mass inside
the band with the mass its entire extension is forced to carry outside, and the exponential type is the
only thing that controls that comparison.

That comparison is now an *identity*.  `RHTower/FourierPlancherelIntegral.lean` supplies the analytic
tool mathlib lacks — Plancherel for the classical Fourier *integral* rather than for `L²` classes:

- `lp_norm_sq_eq_integral`, `coeFn_fourier_toLp`, **`integral_norm_sq_fourier_eq`**,
  `integrable_norm_sq_fourier` — for a function that is both integrable and square integrable,
  `∫ ‖𝓕 f (xi)‖² d xi = ∫ ‖f x‖² dx` and the spectral density is integrable.  The corpus's band-specific
  Plancherel is now a one-line consequence.
- `continuous_fourier_of_integrable` — the Fourier integral of an integrable function is continuous
  (mathlib's `L¹` transform is a bounded continuous function and represents the classical integral).

`RHTower/BandTransformEnergy.lean` then computes the energy:

- `windowSpectrum`, `integrable_windowSpectrum`, `memLp_windowSpectrum` — the spectrum truncated to the
  frequency window is integrable and square integrable.
- **`bandTransform_eq_fourier_windowSpectrum`** — the band transform *is* the Fourier integral of its
  windowed spectrum, `(B_c Phi)(x) = 𝓕 (1_([-k,k]) 𝓕 (trunc Phi)) (-x)`: the Jacobian `2 pi/c` of the
  window change of variables cancels the prefactor of the window representation exactly.
- **`integral_sq_bandTransform_eq_form`** — hence by Plancherel the *total* energy of the band transform
  on the line is the band quadratic form,

  ```text
  ∫_ℝ (B_c Phi)² = ∫∫ sinc_c(x-y) Phi(x) Phi(y),
  ```

  which is the projection identity `‖P f‖² = ⟪P f, f⟫` in explicit form.
- `bandClass_eigenExtension`, **`integral_sq_eigenExtension`**, **`integral_outside_sq_eigenExtension`** —
  for an eigenfunction, `nu² ∫_ℝ psi² = nu ‖psi‖²`, so its band-limited extension carries energy
  `‖psi‖²/nu` on the line and

  ```text
  ∫_(|x| > 1) psi² = ‖psi‖² (1 - nu)/nu
  ```

  outside the band.  **The leakage is exactly the mass the eigenfunction's entire extension is forced to
  spend outside `[-1, 1]`.**

So the missing rate is now a statement with no operator theory left in it: for an entire function of
exponential type `c` with unit mass on `[-1, 1]`, the mass outside `[-1, 1]` is at least
`c_0 c^(1/2) e^(-2c)`.  That is the concentration inequality Fuchs's asymptotic proves, and it is the
only remaining analytic input on this side.

The standard toolbox for that class of functions is now in the tree, in `RHTower/PaleyWienerNorms.lean`
— mathlib has neither inequality:

- `compactFourier_eq_fourier_indicator`, **`integral_norm_sq_compactFourier`** — a function synthesised
  from a compactly supported spectrum, `Psi(x) = ∫_(-k)^k H(v) e^(2 pi i v x) dv`, is the Fourier
  integral of the spectrum extended by zero, so Plancherel computes its energy exactly:
  `∫_ℝ |Psi|² = ∫_(-k)^k |H|²`.
- **`norm_sq_compactFourier_le`** (Nikolskii) — Cauchy–Schwarz on the synthesis integral:
  `|Psi(x)|² <= 2k ∫ |H|² = 2k ∫_ℝ |Psi|²`.
- **`hasDerivAt_compactFourier_real`**, **`integral_norm_sq_deriv_compactFourier_le`** (Bernstein) — the
  derivative of a synthesis is the synthesis of the frequency-multiplied spectrum, and since
  `|2 pi v| <= 2 pi k` on the window its energy is at most `(2 pi k)²` times the original.
- `bandTransform_eq_compactFourier`, `integral_sq_bandTransform_eq_synthesis`,
  **`sq_bandTransform_le`**, **`integral_sq_bandTransform_bernstein`** — instantiated at the band
  window `k = c/(2 pi)`: the band transform obeys `(B_c Phi)(x)² <= (c/pi) ∫_ℝ (B_c Phi)²` and its
  derivative has energy at most `c²` times its own.
- **`sq_eigenExtension_le`** — hence every eigenfunction of the band operator obeys the pointwise bound
  `psi(x)² <= (c/pi) ‖psi‖²/nu` at every real point.

These are the sup-norm and derivative bounds every route to the sharp rate uses.  They do not by
themselves produce it: fed through the exact endpoint ODE `(4)` they give only
`L'(c) >= -(2/pi)`, because the pointwise bound is polynomial while the truth is exponentially small —
the extremal analysis (WKB for the prolate ODE, or the Riemann–Hilbert method) is what supplies the
exponent, and that remains the open input.

The extremal analysis is an *ODE* argument, and the corpus already owns a prolate-ODE layer —
`prolateSLAction`, the conserved Wronskian and its endpoint collapse (`ProlateWronskian`), the
one-turning-point variation mechanism (`ProlateOneTurningVariation`), the band self-adjointness
`prolateSLAction_band_symmetric` (`ProlateBandSymmetric`), the Hermite rescaling identity
(`FuchsProlateScale`) — but that layer was only ever connected to the *integral* operator in the easy
direction (`slepian_commutation_eigen`: an ODE solution is carried to an ODE solution).  The connector
in the spectral direction is now built, in `RHTower/ProlateJointEigen.lean`:

- **`contDiff_bandTransform`** — the band transform of a continuous function is `C^∞`, because it is the
  real part of an entire function of the space variable (the Paley–Wiener representation of the previous
  step).  **`contDiff_eigenExtension`** — hence every eigenfunction of the band operator is `C^∞`, being
  `1/nu` times its own band transform.  This discharges the differentiability hypotheses the commuting
  theorem carries.
- `prolateSLAction_const_mul` — the prolate action is homogeneous on differentiable functions.
- **`bandTransform_prolateSLAction`** — the commuting theorem read in the spectral direction: if
  `T Phi = lambda Phi` pointwise then `T (P_c Phi) = lambda (P_c Phi)`.  **The prolate Sturm–Liouville
  action maps the pointwise `lambda`-eigenspace of the band transform into itself.**
- `inner_bandClass_eq`, `bandOperatorL2_bandClass` — the `L²` dictionary the spectral step consumes: the
  band class of a continuous function transports the inner product to the interval pairing and the band
  operator to the band transform.

The spectral step is now carried out, in `RHTower/ProlateJointEigenExistence.lean`, and it produces the
joint eigenfunction with **no simplicity hypothesis**:

- `finiteDimensional_of_isCompactOperator_smul` — Riesz, in the form the eigenspace needs: if
  multiplication by a nonzero scalar is a compact operator then the space is finite dimensional.
- `bandEigenCLM`, `bandEigenspace`, `mem_bandEigenspace_iff`, `completeSpace_bandEigenspace`,
  **`finiteDimensional_bandEigenspace`** — the `lambda`-eigenspace is a closed (hence complete) subspace
  on which the compact band operator acts as `lambda · id`, so it is finite dimensional.
- `integrable_sincKernel_mul`, `eigenExtension_add`, `eigenExtension_smul`, `contDiff_prolateSLAction`,
  `prolateSLAction_add`, `bandClass_add`, `bandClass_smul`, `bandClass_congr` — the linearity plumbing:
  the smooth representative depends linearly on the eigenvector, the prolate action is linear on smooth
  functions, and the band class is linear on continuous test functions.
- `eqOn_of_bandClass_eq` — two continuous test functions with the same band class agree on `[-1,1]`
  (vanishing band energy, then openness of the nonvanishing set inside the band and continuity).
- **`prolateOnEigenspace`**, **`isSymmetric_prolateOnEigenspace`** — the prolate action *is* a symmetric
  linear operator on the eigenspace; symmetry is `prolateSLAction_band_symmetric`, whose boundary terms
  vanish because `1 - y²` does at the endpoints.
- **`exists_joint_prolate_band_eigen`** — hence for every band eigenvalue `lambda ≠ 0` with a nonzero
  eigenvector there are `Phi ≠ 0` smooth and `chi` with

  ```text
  ∀ x,  (B_c Phi)(x) = lambda Phi(x),        ∀ x ∈ [-1,1],  P_c Phi (x) = chi Phi (x).
  ```

  **The actual concentration operator's eigenfunctions solve the prolate differential equation.**

The corpus's ODE layer therefore now applies to the real object: the conserved Wronskian and its endpoint
collapse, the one-turning-point variation mechanism, and the Hermite rescaling identity all take
`prolateSLAction c Phi = chi Phi` as their hypothesis.  That is the entry point for the extremal analysis
the remaining rate needs, and equally for the Hermite-limit gate.

The first quantitative endpoint estimate along that route is in `RHTower/ProlateEndpointLowerBound.lean`:

- `prolateFlux`, `prolateFlux_one`, `hasDerivAt_prolateFlux`, **`prolateFlux_eq_neg_integral`** — the
  Sturm–Liouville flux `(1-y²) psi'` vanishes at `y = 1` because the weight does, so integrating the
  equation from `y` to the endpoint gives the exact representation

  ```text
  (1-y²) psi'(y) = -∫_y^1 (chi + c² t²) psi(t) dt.
  ```

- **`deriv_nonpos_of_turning`** — beyond the turning point (`chi + c² y² >= 0`) a nonnegative solution has
  nonpositive flux, hence is *decreasing*: the singular endpoint imposes monotonicity with no boundary
  condition.
- **`endpoint_lower_bound`** — bounding the integrand by its value at the left endpoint gives the
  differential inequality `(1+y) psi'(y) >= -(chi + c²) psi(y)`, whose integrating factor is the pure
  power `(1+y)^(chi+c²)`.  Hence

  ```text
  psi(1) >= psi(y_0) · ((1+y_0)/2)^(chi + c²).
  ```

  **A positive prolate solution has an explicit lower bound at its singular endpoint.**

This is the elementary form of the endpoint control the sharp asymptotic refines, and it is the mechanism
a WKB estimate sharpens (same flux representation, same monotonicity, sharper comparison function).  It
does not yet close the rate gate: the exponent `chi + c²` is larger than the true one by a factor of order
`c` — the crude step is bounding `psi(t)` by `psi(y_0)` over the whole remaining interval instead of by its
own exponential decay — so the leakage bound it produces through the exact endpoint ODE is
`e^(-O(c²))` rather than `e^(-2c)`.  Sharpening that one comparison is the remaining analytic content.

The machinery that sharpening runs on is now in place, and it is mathlib-missing on both counts.
`HTGeometry/DifferentialInequalityComparison.lean`:

- **`nonpos_of_hasDerivAt_le_mul`** — comparison for a linear differential inequality with *variable*
  coefficient: `d(a) <= 0` and `d' <= K d` on `(a,b)` with `K` merely continuous on `[a,b]` force `d <= 0`
  there.  The proof is the integrating factor `exp(-∫ K)`; mathlib has only the constant-coefficient
  Grönwall inequality.
- **`riccati_le_of_le_of_supersolution`** — hence the Riccati comparison: a subsolution of
  `u' = u² + b u - q` starting below a supersolution stays below it, the difference satisfying the linear
  inequality with coefficient `u₁ + u₂ + b`.

`RHTower/ProlateRiccati.lean` instantiates this on the prolate equation:

- `prolateLogDeriv`, **`hasDerivAt_prolateLogDeriv`** — the logarithmic derivative `v = -psi'/psi` of a
  nonvanishing solution satisfies exactly

  ```text
  v' = v² + (2y/(1-y²)) v - (chi + c² y²)/(1-y²).
  ```

- **`le_endpoint_of_logDeriv_le`** — any upper bound `v <= V` on the logarithmic derivative converts into
  the endpoint bound `psi(y_1) >= psi(y_0) exp(-∫_(y_0)^(y_1) V)`, by monotonicity of `psi · exp(∫ V)`.

The next step turned out to need the *other* comparison direction, and that direction is sharp with no
error term.  `DifferentialInequalityComparison.lean` gained the backward pair:

- **`nonpos_of_hasDerivAt_ge_mul`** — if `d(b) <= 0` and `d' >= K d` then `d <= 0` on `[a,b]`: the same
  integrating factor, now making `d exp(-∫ K)` increasing, so it is controlled by its *right*-endpoint value.
- **`riccati_le_of_le_of_subsolution`** — hence a Riccati **sub**solution that dominates the solution at the
  right endpoint dominates it on the whole interval, propagating the bound leftwards.

`RHTower/ProlateWKBSubsolution.lean` then supplies the profile:

- `prolateWKB`, `hasDerivAt_prolatePotential`, `hasDerivAt_prolateWKB` — the WKB profile
  `V = sqrt((chi + c² y²)/(1-y²))` and its derivative.
- **`prolateWKB_subsolution`** — since `V² = q` exactly, the Riccati defect of `V` collapses to `V' - b V`,
  and that is nonpositive precisely where

  ```text
  c² (1 - 2y²) <= chi,
  ```

  i.e. on the outer part of the band.  **There the WKB profile is a Riccati subsolution** — the sharp
  direction, with no error term.

That combination is now assembled, in the same module:

- `continuousOn_prolateWKB`, `continuousOn_prolateLogDeriv` — the two continuity inputs of the comparison.
- **`prolateLogDeriv_le_prolateWKB`** — on the outer band the logarithmic derivative of a positive solution
  is bounded by the WKB profile, given only that it is bounded by it at the right endpoint (the backward
  comparison propagates it leftwards).
- **`le_endpoint_prolateWKB`** — hence

  ```text
  Phi(a) · exp (-∫_a^b sqrt((chi + c² y²)/(1 - y²))) <= Phi(b)
  ```

  on the outer band: **the solution decays at most like the exponential of the exact WKB integral, with no
  error term.**

`∫ sqrt((chi + c² y²)/(1-y²))` is the true tunneling exponent, of size `c(1 + o(1))`.

The inner stretch — between the turning point `y_t = sqrt(-chi)/c` and the mid-band point `y ≈ 1/sqrt 2` —
cannot use the same profile: there the WKB function is a *super*solution, and the forward comparison has no
admissible starting value (at the turning point `V` vanishes while `v` does not).  Working the problem out
shows the fix is to keep the *backward* direction throughout and enlarge the profile, and the two enlarged
profiles are now proved to be subsolutions:

- **`const_subsolution`** — a nonnegative constant `W` is a Riccati subsolution wherever `q <= W²`; in the
  allowed region `q < 0`, so *every* nonnegative constant qualifies there.  This covers `[0, y_t + delta]`.
- `hasDerivAt_prolateWKB_smul`, **`prolateWKB_smul_subsolution`** — scaling the WKB profile by `k >= 1`
  produces the slack `((k²-1)/k) (1-y²) V Q`, and the scaled profile is a subsolution exactly where that
  slack covers the defect `y (c²(1-2y²) - chi)`.  This covers `[y_t + delta, y_*]` for suitable `k = 1 + eta`.

Chaining the three backward comparisons — constant on `[0, y_t+delta]`, scaled WKB on `[y_t+delta, y_*]`,
plain WKB on `[y_*, y_1]` — plus the crude flux bound on the last `1 - y_1 ~ c^(-2)` gives
`∫_0^1 v <= (1+eta) ∫ sqrt(Q/p) + O(1)`, i.e. the sharp exponent provided `eta = o(1)` and `delta` are chosen
compatibly (the natural scales are `delta ~ c^(-2/3)`, `eta ~ c^(-1/3)`).

One of the two remaining computations — the size of the WKB exponent — is now done exactly, in
`RHTower/ProlateWKBIntegral.lean`, and it needs no asymptotics at all:

- **`prolateWKB_le_of_nonpos`** — since the eigenvalue parameter is nonpositive, the WKB profile is
  dominated pointwise by its `chi = 0` value `c y / sqrt(1-y²)`.
- `hasDerivAt_negMulSqrt`, **`integral_prolateWKB_le`**, **`integral_prolateWKB_le_aperture`** — that
  dominating profile has the elementary antiderivative `-c sqrt(1-y²)`, so on every subinterval of the right
  half band

  ```text
  ∫_a^b sqrt((chi + c² y²)/(1-y²)) dy <= c (sqrt(1-a²) - sqrt(1-b²)) <= c,
  ```

  an *exact* inequality — sharp, since at `chi = 0, a = 0, b = 1` it is an equality.  No `o(1)` and no
  eigenvalue asymptotic is needed for this direction.
- **`exp_neg_aperture_le_endpoint`** — combining with the outer-band comparison: on the outer band a
  positive solution of the prolate equation loses at most the factor `e^(-c)`,

  ```text
  Phi(a) e^(-c) <= Phi(b).
  ```

  Through the exact endpoint identity `(4)` an `e^(-c)` on the eigenfunction is the `e^(-2c)` of the
  leakage: **the correct exponential rate, with an explicit constant `1` in the exponent.**

What is still needed to convert this into the leakage envelope is the inner-band bookkeeping — verifying the
scaled-subsolution hypothesis at the scales `delta ~ c^(-2/3)`, `eta ~ c^(-1/3)` and chaining the three
comparisons — and the initial condition `v(b) <= V(b)` near the endpoint, which the crude flux bound of the
earlier step supplies for `1 - b ~ c^(-2)`.

## Lean gates

- [x] Lean: the sinc kernel equals the finite-Fourier character integral — equation `(6)` (already in the
  tree), and its quadratic-form reading: the band form is a Fourier energy and is positive
  semidefinite (`BandQuadraticFormFourier`)
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
- [x] Lean: the concrete band operator realised as a compact symmetric operator on real `L²[-1, 1]`,
  differentiable in the aperture, with the branch theorem instantiated on it
  (`exists_bandOperatorL2_branch`)
- [x] Lean: the regularity dictionary — an `L²` eigenfunction of the band operator has a continuous
  representative satisfying the pointwise `bandTransform` eigenrelation at every real point
  (`bandTransform_eigenExtension`)
- [x] Lean: the response-constant transport — `(10)`, `(11)`, `(12)`, `(13)`, `(15)`, `(18)` as limit
  inferences from their named inputs (`CCMEndpointResponseConstants.lean`)
- [x] Lean: the reduction of `(9)` to its envelope form — envelope plus antitone logarithmic
  derivative give the differentiated asymptotic (`LogDerivativeFromEnvelope`,
  `tendsto_endpointSq_div_leakage_of_envelope`)
- [x] Lean: the **upper** leakage envelope for the true operator at the sharp exponential rate —
  `1 - ‖B_c‖ <= 64 c² e^(-2c)` for `c >= 1`, from the Kaiser–Bessel trial: aperture-free out-of-band
  mass (shifted Cauchy kernels, folded and integrated) against exponentially growing in-band energy
  (`BandLeakageEnvelope.lean`, `one_sub_norm_bandOperatorL2_le_exp`)
- [x] Lean: the band operator is a **positive contraction** — the band form of every `L²` class lies
  between `0` and its energy (by density of the continuous test functions), hence `‖B_c‖ <= 1`; with
  the envelope this gives `|1 - ‖B_c‖| <= 64 c² e^(-2c)` and `‖B_c‖ -> 1`
  (`BandOperatorContraction.lean`, `tendsto_norm_bandOperatorL2_atTop`)
- [x] Lean: the **strict** band gap `‖B_c‖ < 1`, hence `0 < 1 - ‖B_c‖` — the qualitative lower
  envelope.  Requires the Paley–Wiener theory mathlib lacks: the compact Fourier transform is entire
  (`CompactFourierEntire.lean`), an entire function vanishing a.e. on a real interval vanishes, the
  band uncertainty principle (`BandUncertainty.lean`), and the Fredholm alternative
  (`BandStrictGap.lean`, `norm_bandOperatorL2_lt_one`)
- [x] Lean: **Paley–Wiener for the band transform** — the sinc kernel is the inverse window transform,
  so the band transform of any continuous test function is a window integral, hence entire of
  exponential type `|c|`; the prolate eigenfunctions are therefore restrictions of entire functions of
  exponential type `c` (`BandLimitedExtension.lean`, `exists_entire_extension_eigenExtension`)
- [x] Lean: **Plancherel for the classical Fourier integral** (absent from mathlib, which has only the
  `L²`-class isometry) and the **leakage as an outside mass**: the band transform is the Fourier integral
  of its windowed spectrum, so its total energy on the line is the band quadratic form, and an
  eigenfunction's entire extension spends exactly `‖psi‖²(1 - nu)/nu` of its energy outside the band
  (`FourierPlancherelIntegral.lean`, `BandTransformEnergy.lean`,
  `integral_outside_sq_eigenExtension`)
- [x] Lean: the **Paley–Wiener toolbox** — Plancherel, Nikolskii and Bernstein for a compactly supported
  spectrum, instantiated on the band: `(B_c Phi)(x)² <= (c/pi) ∫ (B_c Phi)²`, the derivative energy bound
  `<= c²`, and the eigenfunction sup bound `psi(x)² <= (c/pi)‖psi‖²/nu`
  (`PaleyWienerNorms.lean`, `sq_eigenExtension_le`, `integral_sq_bandTransform_bernstein`)
- [x] Lean: the **spectral direction of the commuting theorem** — band eigenfunctions are `C^∞` (from the
  Paley–Wiener representation) and the prolate Sturm–Liouville action maps the pointwise eigenspace of the
  band transform into itself, with the `L²` dictionary for the spectral step
  (`ProlateJointEigen.lean`, `bandTransform_prolateSLAction`, `contDiff_eigenExtension`)
- [x] Lean: the **joint eigenfunction** — the band eigenspace is finite dimensional (Riesz, since the
  compact operator acts on it as `lambda · id`) and the prolate action is a symmetric operator on it, so
  every band eigenvalue carries a smooth nonzero eigenfunction that also satisfies
  `P_c Phi = chi Phi` on `[-1,1]`, with no simplicity hypothesis
  (`ProlateJointEigenExistence.lean`, `exists_joint_prolate_band_eigen`)
- [x] Lean: the **flux representation and the endpoint lower bound for the prolate equation** — the flux
  vanishes at the singular endpoint, a positive solution is decreasing beyond the turning point, and
  `psi(1) >= psi(y_0)((1+y_0)/2)^(chi+c²)` by the pure-power integrating factor
  (`ProlateEndpointLowerBound.lean`, `endpoint_lower_bound`)
- [x] Lean: the **Riccati transfer machinery** — variable-coefficient differential-inequality comparison
  and its Riccati corollary (mathlib has only constant-coefficient Grönwall), the prolate Riccati equation
  for `v = -psi'/psi`, and the conversion of any bound `v <= V` into the endpoint bound
  `psi(y_1) >= psi(y_0) exp(-∫ V)` (`DifferentialInequalityComparison.lean`, `ProlateRiccati.lean`)
- [x] Lean: the **sharp outer-band WKB bound** — backward differential-inequality comparison, its Riccati
  subsolution form, the fact that the WKB profile `sqrt((chi+c²y²)/(1-y²))` is a Riccati subsolution exactly
  where `c²(1-2y²) <= chi`, and the assembled decay bound
  `Phi(a) exp(-∫ sqrt((chi+c²y²)/(1-y²))) <= Phi(b)` with no error term
  (`DifferentialInequalityComparison.lean`, `ProlateWKBSubsolution.lean`, `le_endpoint_prolateWKB`)
- [x] Lean: the **two enlarged subsolutions** covering the inner band — constants (valid throughout the
  allowed region) and scaled WKB profiles `k · sqrt(Q/p)` with the explicit slack criterion
  (`ProlateWKBSubsolution.lean`, `const_subsolution`, `prolateWKB_smul_subsolution`)
- [x] Lean: the **WKB exponent is at most the aperture** — an exact, sharp inequality
  `∫ sqrt((chi+c²y²)/(1-y²)) <= c(sqrt(1-a²) - sqrt(1-b²)) <= c` via the elementary antiderivative, and hence
  the explicit outer-band endpoint bound `Phi(a) e^(-c) <= Phi(b)` — the correct exponential rate with
  constant `1` (`ProlateWKBIntegral.lean`, `exp_neg_aperture_le_endpoint`)
- [ ] Lean: the **rate** of the lower leakage envelope, now equivalent to a pure concentration
  inequality for entire functions of exponential type `c` — unit mass on `[-1, 1]` forces mass at least
  `c_0 c^(1/2) e^(-2c)` outside — and antitonicity of the logarithmic derivative.  The polynomial
  toolbox above is not enough: the exponent needs the extremal (WKB / Riemann–Hilbert) analysis
- [x] Lean: the constrained ground-state ratio `8/11` derived from the prolate-to-Hermite coefficient
  limits, with the Hermite weight arithmetic `q_1 = 3/8` (`tendsto_ellSqRatio_of_hermiteLimits`)
- [ ] Lean: the prolate-to-Hermite coefficient limits `ell_j(lambda) -> h_(4j)(0)` for the true
  operator — the last classical input on the coefficient side
- [x] Lean: the exterior sawtooth incidence constant `(17)` — the endpoint pairing identified with the
  corpus sawtooth incidence layer, with the Euler scalar identified as `-zeta'(2)/zeta(2)`
  (`CCMEndpointSawtoothResponse.lean`)

## Gates

- [x] exact endpoint-response identity proved
- [x] fixed-mode endpoint scale derived
- [x] constrained endpoint coefficient derived
- [x] growing all-prime response constant derived
- [ ] independent proof of the differentiated fixed-mode normalization
- [ ] exact archimedean endpoint response
- [ ] subleading/interior incidence remainder `o(d_1)`
- [ ] true Weil Rayleigh-excess or cofinal-floor transfer
