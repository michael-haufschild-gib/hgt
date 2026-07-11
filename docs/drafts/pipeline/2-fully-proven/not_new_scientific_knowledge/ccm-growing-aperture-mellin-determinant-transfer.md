# CCM growing-aperture Mellin determinant transfer

- **ID:** `ccm-growing-aperture-mellin-determinant-transfer`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent source:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Theorem 5.10 and
  Sections 7--8
- **Statement:** On the growing CCM aperture, the exact norm of Mellin evaluation determines the
  eigenvector convergence rate needed for locally uniform regularized-determinant convergence.
  Ordinary `o(1)` spectral convergence is insufficient.

## Setup

Let

```text
I_lambda=[lambda^(-1),lambda],   lambda>1,
H_lambda=L2(I_lambda,d*u).
```

For `f in H_lambda`, extended by zero outside `I_lambda`, define

```text
M_lambda(f)(z)=integral_(I_lambda) f(u)u^(-iz)d*u.      (1)
```

Write `z=x+iy`. Connes--Consani--Moscovici prove that the regularized determinant of their
self-adjoint rank-one perturbation is, up to a nonvanishing exponential factor,

```text
det_reg(D_lambda-z)=-i lambda^(-iz) M_lambda(xi_lambda)(z),   (2)
```

where `xi_lambda` is the normalized finite-Weil ground vector. They also prove locally uniform
Mellin convergence of the explicit prolate seed `k_lambda` to Riemann's `Xi`. The missing analytic
transfer is therefore from `xi_lambda` to `k_lambda` on a support whose logarithmic length diverges.

## Exact evaluation norm

`[PROVED HERE; BRIDGE]` The operator norm of evaluation at `z=x+iy` is

```text
||M_lambda(·)(z)||_(H_lambda -> C)^2
  = integral_(lambda^(-1))^lambda u^(2y)d*u
  = 2 log(lambda),                                      y=0,
  = sinh(2y log(lambda))/y,                             y!=0.   (3)
```

The quotient in the last line is positive and even in `y`. Consequently, for `a>0`,

```text
sup_(|Im z|<=a) ||M_lambda(·)(z)||
  = sqrt(sinh(2a log(lambda))/a)
  ~ lambda^a/sqrt(2a).                                 (4)
```

For `a=0`, the norm is `sqrt(2 log(lambda))`.

### Proof

The functional in `(1)` is the `H_lambda` inner product with the function `u^(iz)`. Its squared
norm is therefore

```text
integral_(lambda^(-1))^lambda |u^(iz)|^2 d*u
  = integral_(lambda^(-1))^lambda u^(2y)d*u,
```

which evaluates to `(3)`. Equality in Cauchy--Schwarz is attained by a scalar multiple of the
representing function, so this is the exact norm, not only an upper bound. Monotonicity in `|y|`
gives `(4)`.

## Locally uniform transfer theorem

Let `f_lambda,g_lambda in H_lambda`. If, for every `a` with `0<a<1/2`,

```text
lambda^a ||f_lambda-g_lambda||_2 -> 0,                 (5)
```

then

```text
M_lambda(f_lambda)-M_lambda(g_lambda) -> 0             (6)
```

uniformly on every compact subset of the open strip `|Im z|<1/2`.

It is enough, in particular, to have

```text
||f_lambda-g_lambda||_2=O(lambda^(-1/2)).              (7)
```

### Proof

If a compact set `K` lies in `|Im z|<=a<1/2`, equations `(3)`--`(4)` and Cauchy--Schwarz give

```text
sup_(z in K) |M_lambda(f_lambda-g_lambda)(z)|
  <= sqrt(sinh(2a log(lambda))/a) ||f_lambda-g_lambda||_2
  =O(lambda^a ||f_lambda-g_lambda||_2).                (8)
```

Condition `(5)` makes the right side tend to zero. Equation `(7)` implies `(5)` because
`a<1/2`.

The powers in `(5)` are sharp for arbitrary aperture errors: equality cases in `(3)` attain the
evaluation norm at every fixed boundary height `y=a`. Additional parity, smoothness, or source
structure may improve the requirement for the specific CCM vectors, but no smaller universal
`L2` operator norm is available.

Evenness under `u->u^(-1)` does not improve the exponent. In the logarithmic coordinate
`t=log u`, restriction to the even subspace replaces the representing exponential by
`cos(zt)`. Its squared norm on `[-log(lambda),log(lambda)]` is

```text
sinh(2y log(lambda))/(2y)+sin(2x log(lambda))/(2x),     (8a)
```

with the continuous limiting values at `x=0` or `y=0`. The first term still grows as
`lambda^(2|y|)`. Thus the exact CCM parity removes no power from `(5)`.

## Exact strengthening of the spectral residual target

Let `A_lambda` be a self-adjoint finite-Weil operator, let `g_lambda` be a unit prolate seed, put

```text
r_lambda=<A_lambda g_lambda,g_lambda>,
R_lambda=||(A_lambda-r_lambda)g_lambda||,
Gap_lambda=the spectral separation of the target eigenvalue.   (9)
```

A Davis--Kahan residual estimate gives, after choosing phase and provided the target eigenvalue is
isolated,

```text
||xi_lambda-g_lambda||_2=O(R_lambda/Gap_lambda).        (10)
```

Therefore the local target `R_lambda=o(Gap_lambda)` proves only `o(1)` eigenvector convergence and
does not by itself imply determinant convergence on the growing aperture. A direct sufficient
target is

```text
lambda^a R_lambda/Gap_lambda -> 0
for every a<1/2,                                       (11)
```

or the convenient stronger estimate

```text
R_lambda/Gap_lambda=O(lambda^(-1/2)).                  (12)
```

The normalization of the CCM vector is immaterial here: their determinant convergence permits a
nonzero scalar and a factor `exp(alpha_lambda+i beta_lambda z)`. One first selects the scalar and
phase minimizing the `L2` difference, then applies `(5)`.

## Interaction with the logarithmic boundary theorem

For every finite cutoff satisfying the CCM simple-even hypothesis, `(2)` is the determinant of a
self-adjoint operator. Hence all zeros of the normalized approximant are real in the spectral
variable `z`, equivalently on `Re(s)=1/2` in the zeta variable `s=1/2+iz`. Its reflected prime-clock
energy is therefore exactly zero:

```text
E_N(Re(s)-1/2)=E_N(0)=0.                               (13)
```

Thus this architecture automatically satisfies the metric gate in
`finite-prime-logarithmic-boundary-transfer`. Its entire remaining RH burden is the analytic gate:

```text
normalized det_reg(D_lambda-z) -> Xi(z)
locally uniformly and zero-preservingly.               (14)
```

The positive general theorem is that a finite-prime family proves RH when its normalized
approximants carry the `Xi` divisor
locally uniformly and every approximant zero `z` satisfies

```text
E_N(Re(z)-1/2)=o((log N)^2).                           (14a)
```

For the CCM real-zero determinants `(14a)` holds identically with left side zero. Consequently the
general two-gate theorem collapses here to the single divisor-preserving convergence requirement
`(14)`.

The sharper prime-boundary result does not add a second CCM mechanism. For a horizontal defect
`epsilon_N log N -> c`, `prime-clock-critical-window-scaling.md` gives the universal overlap

```text
O(c)=exp(-Phi(c)/2)>0
```

at every finite critical coordinate. The symmetric Dickman specialization in
`prime-boundary-symmetric-dickman-zero-free-law.md` strengthens this to a zero-free finite and
limiting characteristic profile. At a CCM spectral zero one has `c=0`, hence `Phi(0)=0` and
`O(0)=1`. Therefore the entire prime-clock/Dickman boundary channel is maximally nonvanishing on
the finite CCM zero fiber. It can neither manufacture the missing `Xi` divisor nor repair a failure
of `(14)`. Finite determinants having all zeros on the line proves nothing about `Xi` until a
normalization makes those same characteristic functions converge locally uniformly to `Xi` and
thereby carry every `Xi` zero.

The CCM paper already proves `(14)` with the prolate seed `k_lambda` substituted for the true Weil
ground vector. Equations `(5)` and `(11)` give exact sufficient rates for transferring that result
to the true self-adjoint determinants.

This isolates the live proof chain without conflating finite self-adjointness with RH:

```text
simple-even true Weil ground state
  + relative residual estimate (11)
  + proved prolate-seed Mellin convergence
  => locally uniform determinant convergence
  => zero preservation by Rouche/Hurwitz
  + exact zero-fiber energy (13)
  => RH.                                                (15)
```

The unproved content is entirely in the first two lines, especially `(11)`. The last three lines
are rigorous transfer theory.

There is a distinct, strictly shorter payoff if the comparison controls the true lowest Weil
eigenvalue itself. By `ccm-cofinal-weil-spectral-floor-criterion.md`,

```text
epsilon(lambda_j)->0 on one cofinal aperture sequence
  => QW>=0 on every compactly supported Weil test
  => RH.                                                (15d)
```

Hence an eigenvalue asymptotic `epsilon(lambda)=c d_1(lambda)+o(d_1(lambda))` already proves RH and
does not need determinants. The divisor gate `(14)` remains indispensable only for the finite
real-zero **determinant** branch. These are two different cofinal completions: exact Weil positivity
versus locally uniform characteristic-function convergence.

## Position in the repository's Hilbert--Polya pipeline

This theorem is one link in an existing chain, not a new standalone route.

### Inputs already proved in the pipeline

1. `ccm-restricted-summation-aperture-gauge.md` proves that the apparent source point-value defect
   can be removed without changing the restricted summation vector. The genuine transfer object is
   the exterior arithmetic tail.
2. `constrained-prolate-two-mode-ground-state.md` proves that the CCM `h_0`--`h_4` seed is selected
   by the exact vanishing-integral prolate concentration problem and supplies its surrogate gap.
3. `constrained-prolate-fixed-mode-spectral-ladder.md` proves the complete fixed-depth constrained
   ladder, including the `lambda^8` adjacent separation and the exact Hermite/CCM Gram--Schmidt
   limits. These are falsifiable local spectral fingerprints for any true-Weil comparison.
4. `ccm-weil-exterior-tail-quotient-gate.md` identifies the aperture vector with the negative
   exterior tail modulo the global Weil radical. `ccm-poisson-tail-l2-unboundedness.md` then proves
   quantitatively that the successful tail estimate must use the special prolate source in a
   zeta-weighted/oscillatory topology. An abstract scalar concentration bound supplies only its
   starting datum.
   `ccm-bv-muntz-graph-domain-extension.md` closes the qualitative endpoint issue: the actual
   zero-extended prolate contrast belongs to the maximal zeta-multiplier graph domain and its global
   summation vector vanishes at every zeta zero. The missing input is a cofinal rate, not domain
   membership.
   `ccm-endpoint-oscillation-poisson-tail-bound.md` then proves that the special source avoids the
   generic coherent dilation-sum growth: its leading Fourier endpoint tail is a bounded sawtooth
   series, and its central Poisson correction is of deficit order. The residual open datum is a
   closed-Weil estimate for the remaining endpoint jets relative to the constrained gap.
5. `ccm-galerkin-cofinal-diagonal-transfer.md` proves that fixed-aperture form-core convergence and
   a diagonal choice of Galerkin dimensions transfer any continuous determinant limit to finite
   CCM determinants. No estimate uniform in the aperture and Galerkin dimension is needed.
6. `finite-prime-logarithmic-boundary-transfer.md` proves the final cofinal boundary theorem. For
   the CCM family its metric gate is already zero by finite self-adjointness; only the locally
   uniform divisor-carrying analytic gate remains.
7. `prime-clock-critical-window-scaling.md` and
   `prime-boundary-symmetric-dickman-zero-free-law.md` show that the full critical crossover is
   zero-free. In particular, it supplies no hidden divisor mechanism once the finite CCM zeros have
   zero horizontal defect.
8. `ccm-cofinal-weil-spectral-floor-criterion.md` proves that any cofinal `o(1)` theorem for the
   true continuous Weil floor already implies RH. Such an eigenvalue theorem belongs to the exact
   Weil-positivity branch and must not be misreported as merely preliminary to `(14)`.

The resulting exact open target should be stated projectively. After removing the explicit
nonvanishing exponential in `(2)`, put

```text
d_lambda=inf_(c in C^x) ||c xi_lambda-k_lambda||_2.     (15a)
```

A sufficient continuous-aperture theorem is

```text
lambda^a d_lambda -> 0 for every a<1/2,                (15b)
```

together with simplicity and evenness of the continuous lowest Weil eigenvalue on a cofinal
aperture sequence. The Galerkin card then supplies the finite determinant family automatically.

### Positive structural requirements forced by the pipeline

- A remote-divisor-complete Weil family must escape test-space compactness or approach the radical.
  CCM supplies both positive resources: a growing aperture and a prolate vector converging toward
  the radical.
- The unknown critical tail must be accessed by a cofinal test family. Condition `(15b)` is exactly
  such a family; its support and effective resolution grow with `lambda`.
- The full `Xi` divisor must be carried by an infinite cofinal family of characteristic functions.
  CCM supplies finite entire determinants at each stage and asks that their normalized cofinal
  limit be `Xi`.
- Boundary information must grow cofinally rather than remain in finitely many prolate channels.
  The growing Mellin topology in `(15b)` supplies this unbounded family of boundary evaluations.
- Critical-line localization and zero detection must occur in the **same** characteristic
  functions. CCM meets this by proving each normalized determinant real-zero and then requiring
  those very determinants to converge locally uniformly to `Xi`.
- The full complex divisor, rather than only its ordinate measure or HT/source class, must survive
  the limit. Locally uniform convergence in `(14)` supplies exactly this transverse information.
- The infinite prime-log module must be carried by an infinite-dimensional constraint system. The
  limiting CCM Weil operator has that architecture; no finite autonomous flow is used as the source
  generator.

This distinction is load-bearing. The sufficient Hilbert--Polya datum is

```text
real-zero entire determinants F_lambda
  + locally uniform convergence F_lambda -> Xi on a complex strip.   (15c)
```

The second line is transverse-divisor information, not an ordinate statistic.

### Neighboring semilocal Sonin route is distinct

The Route-B Jacobi/prolate program studies a different semilocal operator realization. Its raw
grading defect is triangularly determinant-blind, its natural cyclic and transported cores are
disjoint, and unitary transport is impossible. Those theorems neither prove nor refute `(15b)`:
the CCM infrared determinant is the Mellin transform of the true finite-Weil ground vector, not the
Fredholm determinant of the Route-B raw grading defect. No positivity, domain, or resolvent claim
from Route B is imported into the present chain.

The same separation applies to the `rhtower_status_1107.md` route table. Route A is closed as an
independent trace--Hankel sign producer; Route C is open at a different absolute source estimate;
Route D is a computational consumer whose noncomputational generator is retired. The CCM infrared
determinant branch is not evidence for any of those missing source theorems and should be tracked as
a separate cofinal characteristic-function route.

### June--July 2026 external calibration

Suzuki's screw-function realization proves that the continuous restricted Weil operator is the
Friedrichs extension of an explicit operator, that its lowest eigenvalue varies continuously with
the aperture, and that its ground state is simple-even for sufficiently small aperture. It does not
prove simple-evenness in the large-aperture regime required by `(15b)`. Suzuki also constructs a
different unconditional real-zero characteristic family from self-adjoint extensions of the scaling
derivative. Its proposed large-aperture limit is conjectural and does not establish the CCM
ground-vector comparison. Moreover, `suzuki-screw-characteristic-meromorphic-limit-correction.md`
proves that the stated uniform convergence on every compact subset of `C` is impossible for its
meromorphic target `z^2 xi/xi'`; that comparison lane must be reformulated on pole-free compacta or
in a precise spherical topology.

Groskin's July 2026 finite Guinand--Weil dictionary proves that every finite CCM/CvS Galerkin
quadratic value is exactly the zero-side sum of an explicitly induced band-limited Weil test. Its
archimedean tail theorem gives rigorous finite sign-certification budgets. This upgrades the finite
matrix from a numerical proxy to an exact finite Weil instrument, but it neither proves
large-aperture simple-evenness nor supplies the locally uniform determinant limit `(14)`.

## Positive completion obligations and resolved reductions

- `[REQUIRED GROWING TOPOLOGY]` The projective ground-vector comparison must satisfy `(15b)`, not
  only ordinary `L2` convergence. This is the exact topology in which Mellin evaluation stays
  uniformly controlled on compact substrips.
- `[REQUIRED SIGN-INDEFINITE SIMPLICITY MECHANISM]` Large-aperture simple-evenness must come from
  parity-separated min--max theory, an oscillation/no-crossing theorem, source transversality, or
  projective comparison. The exact screw kernel leaves the Dirichlet/Perron--Frobenius class beyond
  an explicit aperture.
- `[OPEN CORE]` Prove `(11)` using the exterior-tail Weil quotient identity and the constrained
  prolate fixed-mode gap ladder.
- `[AVAILABLE SOURCE DOMAIN]` The genuine zero-extended prolate source lies in the maximal
  zeta-multiplier graph domain, so the proof can work with the actual source rather than a Schwartz
  fiction.
- `[AVAILABLE ARITHMETIC CANCELLATION]` Poisson summation turns the leading Fourier endpoint tail
  into a uniformly bounded sawtooth series and reduces the remaining tail to explicit endpoint
  jets. The zero-integral central correction is already at deficit scale.
- `[OPEN CORE]` Prove the smallest true finite-Weil eigenvalue is simple with even eigenvector for
  every cofinal cutoff used by the determinant family.
- `[CONDITIONAL ROUTE]` If the two open cores hold, the existing CCM determinant identity and their
  prolate Mellin theorem supply the cofinal zero-preserving family required by the logarithmic
  boundary theorem.
- `[PIPELINE-SHARPENED OPEN CORE]` Because the Galerkin diagonal theorem is already proved, the
  source-specific target is exactly the continuous simple-even theorem plus `(15b)`. A joint
  `lambda`--Galerkin estimate, a separate finite-zero energy estimate, and a Route-B determinant
  construction are not dependencies.
- `[ALTERNATIVE RH-SUFFICIENT CORE]` Prove only that the true continuous Weil floor is `o(1)` on a
  cofinal aperture sequence. This bypasses the determinant branch because it is already cofinal
  Weil positivity, not because finite real spectra carry the `Xi` divisor.
- `[REQUIRED DIVISOR SOURCE]` The missing zero set must come from the cofinal characteristic
  determinant itself. The prime-clock/Dickman crossover is strictly nonzero at every finite
  boundary coordinate and equals one on the CCM zero fiber, so it acts as a stable metric channel,
  not as the divisor carrier.

## Novelty and significance verdict

The exact norm `(3)` and transfer estimate `(8)` are elementary Hilbert-space/Mellin analysis. The
combination with the CCM determinant and the minuscule spectral gap gives a useful new route
specification, but the mathematical content fails the novelty gate after the RH vocabulary is
erased. It is classified as a rigorous `[BRIDGE]`, not new scientific knowledge.

The July 2026 source audit checked the current arXiv version of *Zeta Spectral Triples*. It states
the desired compact-substrip convergence and proves it for the explicit prolate seed, but does not
state an `L2` eigenvector rate or the exact growing-aperture evaluation norm `(3)`. This does not
promote the elementary theorem past the parent-theory gate; it only confirms that `(11)` is a new
explicit formulation of the paper's missing approximation requirement.

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- A. Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828.

## Lean decision

The formal tree does contain generic Fredholm-determinant identities, locally uniform canonical
products, compact self-adjoint eigenvector existence, and the finite-prime boundary-transfer
theorems. It does not contain the CCM closed Weil form, the CCM regularized determinant, a
growing-aperture Mellin operator, or the source-specific residual/eigenvector comparison in `(11)`.
Formalizing Cauchy--Schwarz alone would therefore be a wrapper and would not certify the CCM
analytic inputs. No Lean file is added.

## Gates

- [x] exact growing-aperture Mellin evaluation norm proved
- [x] sharp universal compact-substrip transfer rate proved
- [x] Davis--Kahan residual target strengthened quantitatively
- [x] metric gate discharged for the self-adjoint determinant family
- [x] analytic gate identified with the published CCM determinant family
- [ ] simple-even true finite-Weil ground state theorem
- [ ] source-specific residual estimate `(11)`
