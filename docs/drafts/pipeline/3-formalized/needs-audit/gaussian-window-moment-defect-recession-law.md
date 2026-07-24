# Gaussian-window moment-defect recession law

- **ID:** `gaussian-window-moment-defect-recession-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / UNIVERSAL MOMENT-CONE LAW / RH SOURCE APPLICATION
- **Date:** 2026-07-20
- **Scientific status:** `[PROVED HERE] [NO COMPUTATION] [UNCONDITIONAL]
  [CANDIDATE NEW SYNTHESIS] [PARENT COMPONENTS CLASSICAL] [NOVELTY UNVERIFIED]`
- **Statement:** A Gaussian spectral window preserves the complete polynomial-square moment cone
  exactly when the underlying continuous density is nonnegative; if the density is positive at
  the cooling center but negative elsewhere, every fixed moment section eventually becomes
  strictly positive while the least negative section degree diverges to infinity.

## Goal

Turn the Hedenmalm center-mixed Fourier obstruction into an exact positive carrier law.  The law
must explain simultaneously why a complete moment tower detects every negative spectral region
and why finite-degree Gaussian cooling can miss that region.  Applied to the actual theta current,
it should state positively that an RH proof must prevent orientation defect from entering through
degree infinity.

## Gates

- [x] 0 -> 1 in-progress: exact universal statement, source application, and hostile boundary
- [x] 1 -> 2 fully-proven: dependency-closed paper proof with no RH or positivity premise
- [x] 2 -> 3 formalized: weighted polynomial-density infrastructure and exact Lean capstones
- [ ] 3 -> 4 publication-ready: independent priority audit and source-focused manuscript

## Universal theorem

Let `J : R -> R` be continuous and bounded.  For `tau>0`, define

```text
Q_(J,tau)(p)=integral_R p(x)^2 exp(-tau*x^2) J(x) dx
```

for real polynomials `p`, and let

```text
H_(J,tau,d)(i,j)
 =integral_R x^(i+j) exp(-tau*x^2) J(x) dx,
0<=i,j<=d.
```

Then, for every one fixed `tau>0`, the following are equivalent:

```text
J(x)>=0 for every x in R;                                (A)
Q_(J,tau)(p)>=0 for every real polynomial p;             (B)
H_(J,tau,d) is positive semidefinite for every d.         (C)
```

The same equivalence therefore holds with `for some tau>0` or `for every tau>0` in `(B)` and
`(C)`.  Gaussian damping changes neither the complete moment-cone orientation nor its negative
support.

Assume in addition that `J(0)>0`.  For every fixed `d` there is `T_d>0` such that

```text
tau>=T_d  ==>  H_(J,tau,d) is positive definite.         (D)
```

If `J` is negative somewhere, define the least defect degree

```text
delta_J(tau)=min {d : H_(J,tau,d) is not positive semidefinite}.
```

The equivalence makes this a finite natural number at every `tau>0`, while `(D)` gives the exact
recession law

```text
for every d, eventually delta_J(tau)>d as tau->infinity. (E)
```

Thus strong Gaussian cooling makes every prescribed finite section strictly positive but cannot
heal a genuine sign defect: the witness is forced cofinally to higher polynomial degree.

## Proof of the complete-cone equivalence

`(A) -> (B)` is immediate by integration, and `(B) <-> (C)` is the coefficient identity

```text
Q_(J,tau)(sum_(i=0)^d c_i X^i)
 =sum_(i,j=0)^d c_i c_j H_(J,tau,d)(i,j).
```

For the converse, put

```text
dnu_tau(x)=exp(-tau*x^2)|J(x)| dx.
```

Polynomials are dense in `L^2(nu_tau)`.  Here is a self-contained proof.  If `g` is orthogonal
to every polynomial, the finite signed measure `dmu=g dnu_tau` has exponential moments of every
order.  Indeed, boundedness of `J` and the Gaussian factor give

```text
integral exp(2c|x|) dnu_tau(x)<infinity
```

for every `c>0`, and Cauchy--Schwarz gives the corresponding exponential bound for `|mu|`.
Consequently

```text
F(z)=integral exp(zx) dmu(x)
```

is entire.  Every derivative of `F` at zero is a polynomial moment of `mu` and therefore
vanishes.  Hence `F=0`; Fourier uniqueness for finite measures gives `mu=0`, so `g=0` in
`L^2(nu_tau)`.  The orthogonal complement of the polynomials is trivial, proving density.

If `(A)` fails, continuity gives a bounded open interval `U`, a number `eta>0`, and

```text
J(x)<=-eta  on U.
```

Choose a nonzero continuous `phi` compactly supported in `U`.  Polynomial density supplies
`p_n -> phi` in `L^2(nu_tau)`.  Since

```text
|integral (p_n^2-phi^2) exp(-tau*x^2)J(x)dx|
 <=||p_n-phi||_(L2(nu_tau))
   (||p_n||_(L2(nu_tau))+||phi||_(L2(nu_tau))),
```

the quadratic values converge to

```text
integral phi(x)^2 exp(-tau*x^2)J(x)dx<0.
```

For large `n` this contradicts `(B)`.  Therefore `(B) -> (A)`.

The density input is compatible with Labouriau's exponential-moment polynomial-density theorem,
but the argument above is included so the present theorem has no unproved external dependency.

## Proof of finite-section positivity under cooling

Let

```text
G_d(i,j)=integral_R y^(i+j) exp(-y^2)dy.
```

This is the Gram matrix of the monomials `1,y,...,y^d` in Gaussian `L^2`, hence is positive
definite.  After `y=sqrt(tau)x`, put

```text
K_tau(i,j)=integral_R y^(i+j) exp(-y^2)J(y/sqrt(tau))dy,
D_tau=diag(tau^(-i/2)).
```

Then the exact congruence is

```text
H_(J,tau,d)=tau^(-1/2) D_tau K_tau D_tau.                (1)
```

Boundedness of `J` supplies the integrable majorants
`||J||_infinity |y|^(i+j)exp(-y^2)`.  Since `J(y/sqrt(tau))->J(0)`, dominated convergence gives

```text
K_tau -> J(0) G_d                                      (2)
```

entrywise.  The limit is positive definite because `J(0)>0`; the positive-definite cone is open
in the finite matrix space.  Thus `K_tau` is positive definite for all sufficiently large `tau`,
and the invertible positive diagonal congruence `(1)` proves `(D)`.  Combining `(D)` with the
finite defect supplied by failure of `(A)` proves `(E)`.

## Hedenmalm--theta specialization

For `0<a<1/2`, let `M_a` be the actual center-mixed theta density and define its scaled real
Fourier current

```text
J_a(b)=Re Fourier(thetaCuspHorizontalAutocorrelationTangent a)(b/(2*pi)).
```

The existing source identities prove:

1. `J_a` is continuous and rapidly decreasing;
2. `J_a(0)>0`, since it is the zero-frequency integral of the strictly positive density `M_a`;
3. `J_a(b)>=0` for every critical aperture and frequency if and only if RH.

Therefore RH is equivalent to the single-temperature complete moment law

```text
for every 0<a<1/2, every d,
H_(J_a,1,d) is positive semidefinite.                    (3)
```

Because `J_a` is even, the full matrix in `(3)` splits, after a parity permutation, into the two
Hankel towers

```text
[integral b^(2i+2j) exp(-b^2)J_a(b)db]_(i,j),
[integral b^(2i+2j+2) exp(-b^2)J_a(b)db]_(i,j).          (4)
```

Equivalently, `(4)` is the pair of alternating even-derivative Hankel towers at zero of the
Gaussian-smoothed center-mixed density.  Hence `(3)` uses one spatial point, one fixed spectral
temperature, and no arbitrary frequency or node packet.

If RH is false, there is a critical aperture `a` for which `J_a` is negative somewhere.  At that
same aperture, every Gaussian temperature has a finite negative polynomial-square witness, but
the least witness degree diverges under cooling.  Positively stated:

```text
Every successful Hedenmalm source proof must control the cofinal degree boundary of the
Gaussian-window moment cone; no bounded-degree verification can close the orientation law.  (5)
```

The already formalized source theorem

```text
M_a(0) M_a''''(0)-M_a''(0)^2>0
```

is exactly the first nontrivial unwindowed even moment-Hankel determinant.  It is not a
Gaussian-scale-mixture condition: the latter would incorrectly insert a factor `3` and belongs to
a different moment coordinate.

## Hostile audit and exact scope

1. **Not an RH proof.**  The theorem classifies how a negative Hedenmalm current must survive
   Gaussian cooling.  It does not exclude that current.
2. **Not a finite-section extrapolation.**  `(D)` holds for every continuous `J` with `J(0)>0`,
   including densities that are negative away from zero.  The cofinal degree in `(E)` is essential.
3. **Not a numerical boundary.**  No computed zero, cutoff, fitted constant, or finite estimate
   occurs.  The result is an exact cone equivalence and a qualitative recession law.
4. **Classical parent components.**  Gaussian approximate identities, polynomial density under
   exponential moments, Fourier uniqueness, Gram positivity, and openness of the finite
   positive-definite cone are classical.  The candidate contribution is their exact synthesis
   into the complete-cone invariance plus finite-section/cofinal-defect dichotomy and its
   source-specific Hedenmalm interpretation.
5. **No likelihood-category error.**  The positive theta-tail likelihood measure lives in the
   source-gap coordinate.  It is not substituted for the Fourier orientation measure `J_a`.
6. **No Gaussian-mixture overclaim.**  The correct Fourier moment block has determinant
   `M_a(0)M_a''''(0)-M_a''(0)^2`; the stronger factor-`3` inequality is neither assumed nor
   inferred.

## Literature boundary

- Labouriau, *The Laplace transform and polynomial approximation in L2* (2016), proves polynomial
  density from a Laplace-transform/exponential-tail hypothesis.  This supplies a parent for one
  lemma, not the cooling recession theorem.
- Hamburger/Carleman moment determinacy and the one-dimensional sum-of-squares characterization
  are classical parents for the complete-cone equivalence.
- Targeted searches for Gaussian-damped signed moment cones, minimal negative moment degree under
  cooling, and degree-recession laws found moment-problem and polynomial-density results but no
  statement combining `(A)`--`(E)` or applying it to Hedenmalm's theta current.  This is search
  noncollision, not a priority certificate.

## Lean plan

1. Prove exponential-moment polynomial density for a finite measure from a two-sided exponential
   integrability hypothesis.
2. Prove the signed-density polynomial-square separation theorem.
3. Define the Gaussian-window moment matrix and prove `(A)`--`(C)`.
4. Formalize the diagonal rescaling `(1)`, entrywise dominated convergence `(2)`, and eventual
   finite-section positive definiteness.
5. Define the least defect degree without choice ambiguity and prove cofinal recession.
6. Instantiate the theorem with the Hedenmalm current, prove the parity block decomposition and
   Gaussian-smoothed derivative identity, and connect it to
   `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`.

## Log

- 2026-07-20 -- The Gaussian-scale-mixture conjecture was rejected as a category mismatch: it
  would require the factor-`3` fourth derivative inequality, whereas the actual source theorem is
  exactly the Fourier moment-Hankel determinant with factor `1`.
- 2026-07-20 -- Replaced it by the Gaussian-window complete-cone invariance and defect-recession
  theorem.  Completed the polynomial separation, finite-section scaling, source specialization,
  and hostile audit on paper; promoted to Stage 2 with novelty still unverified.
- 2026-07-24 -- Lean audit of the formalization gate. Corpus already carries plan steps 1--3: the
  Gaussian window `gaussianWindowMeasure` with its finite / open-positive / entire-exponential-moment
  instances (`GaussianWindowPolynomialDensity`, `HedenmalmGaussianHankelRH`), and the full universal
  `(A)`--`(C)` equivalence for any bounded continuous density
  (`CompleteHankelSignCone.completeHankelCone_weightedMoment_iff`, with the algebraic
  square-cone/Hankel bridge `completeHankelCone_iff_momentFunctional_square_nonnegative` and the
  moment-form/Hankel-PD bridge `MomentInnerProduct.positiveMomentForm_iff_momentHankelMatrix_posDef`).
  Formalized this cycle the **positive-definite input** for the cooling law `(D)`: strict
  positive-definiteness of the complete Gaussian-windowed Hankel tower for a nonnegative continuous
  density that is strictly positive at one point
  (`RHTower/GaussianWindowHankelPositiveDefinite.lean`:
  `gaussianWindow_positiveMomentForm_of_nonneg`, `gaussianWindow_momentHankelMatrix_posDef_of_nonneg`).
  This is exactly `G_d` positive definite (the `J = 1` special case, `∫ p(x)^2 exp(-tau x^2) dx > 0`
  for `p != 0`), generalized to arbitrary nonnegative densities positive somewhere; it strengthens the
  corpus PSD<=>(J>=0 a.e.) law to strict PD via `∫ p^2 J dmu > 0` from open-set charging of the
  window and finiteness of a nonzero polynomial's zero set. Unconditional; axioms
  `[propext, Classical.choice, Quot.sound]`. Remaining for `(D)`/`(E)`: the diagonal rescaling
  congruence `(1)`, the entrywise dominated-convergence limit `K_tau -> J(0) G_d` `(2)`, openness of
  the finite PD cone giving eventual PD, and the choice-free least-defect-degree cofinal recession `(E)`.
- 2026-07-24 -- Formalized the two exact scalar laws driving the cooling recession `(D)`/`(E)`, in
  `RHTower/GaussianWindowMomentRescaling.lean` (all unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `weightedMoment_gaussianWindow_rescale` -- the diagonal-congruence factor `(1)` at scalar level:
    the change of variables `x = y / sqrt tau` gives
    `weightedMoment (gaussianWindowMeasure tau) J m = (sqrt tau)⁻¹^(m+1) * ∫ y^m exp(-y^2) J(y/sqrt tau) dy`
    (`withDensity` unfolding + `Measure.integral_comp_mul_left`; holds for every density `J`).
  * `tendsto_gaussianCooledMoment` -- the entrywise Hankel limit `(2)` `K_tau -> J(0) G` at scalar
    level: for bounded continuous `J`, `∫ y^m exp(-y^2) J(y/sqrt tau) dy -> J(0) * ∫ y^m exp(-y^2) dy`
    as `tau -> infinity` (dominated convergence, dominating function `C * ‖y^m exp(-y^2)‖`).
  * supporting `integrable_pow_mul_exp_neg_sq`: every monomial is integrable against `exp(-y^2)`.
  Combined with last cycle's `G_d` positive-definiteness
  (`gaussianWindow_momentHankelMatrix_posDef_of_nonneg`, the `J=1, tau=1` case), the remaining `(D)`
  step is purely finite-matrix: assemble the quadratic form `v^T H_(J,tau,d) v = tau^(-1/2) * w^T K_tau w`
  with `w_i = v_i (sqrt tau)^(-i)`, use the entrywise limit `K_tau -> J(0) G_d` and openness of the
  finite positive-definite cone to get eventual PD; then `(E)` is the choice-free least-defect degree.
- 2026-07-24 -- Built the reusable finite-matrix stability infrastructure for the cooling law `(D)`
  in `HTGeometry/PositiveDefiniteMatrixLimit.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `posDef_coercive` -- a real positive-definite matrix `M` has `∃ μ>0, ∀ x, μ*(x ⬝ᵥ x) ≤ x ⬝ᵥ M *ᵥ x`
    (minimise the continuous quadratic form over the compact unit sphere `{x | x ⬝ᵥ x = 1}` and rescale).
  * `abs_dotProduct_mulVec_le` -- entrywise perturbation control: `|N p q| ≤ ε` gives
    `|x ⬝ᵥ N *ᵥ x| ≤ n*ε*(x ⬝ᵥ x)` (triangle inequality + Cauchy--Schwarz).
  * `posDef_eventually_of_tendsto` -- **positive-definiteness is open under entrywise convergence**:
    a family of Hermitian matrices whose entries converge to those of a positive-definite `M₀` is
    eventually positive definite.  This is exactly the "positive-definite cone is open" step of the
    paper proof of `(D)`.
  These are mathlib gaps (no `PosDef` coercivity or entrywise-limit stability lemma exists upstream).
  Remaining for `(D)`: the matrix-level rescaling congruence `H_(J,tau,d) = (sqrt tau)⁻¹ • (Dτ Kτ Dτ)`
  from `weightedMoment_gaussianWindow_rescale`, the entrywise limit of the cooled Hankel `Kτ -> J(0) G_d`
  from `tendsto_gaussianCooledMoment`, then apply `posDef_eventually_of_tendsto` with
  `M₀ = J(0) • G_d` (positive definite via `gaussianWindow_momentHankelMatrix_posDef_of_nonneg` and
  `Matrix.PosDef.smul`) plus congruence-invariance of PD; then `(E)` is the choice-free least-defect degree.
- 2026-07-24 -- **Formalization gate `(2 -> 3)` complete.**  The whole universal theorem `(A)`--`(E)` and
  its source application are now in Lean, unconditional, axioms `[propext, Classical.choice, Quot.sound]`:
  * `(A)<=>(B)<=>(C)` for any bounded continuous density on the Gaussian window: the corpus generic
    equivalence `CompleteHankelSignCone.completeHankelCone_weightedMoment_iff` instantiated at
    `gaussianWindowMeasure tau` (finite / open-positive / entire-exponential-moment instances all present),
    with the algebraic square-cone/Hankel bridge `completeHankelCone_iff_momentFunctional_square_nonnegative`.
  * Strict positive-definiteness of a nonnegative density's Gaussian Hankel tower
    (`RHTower/GaussianWindowHankelPositiveDefinite.lean`).
  * The two scalar cooling laws -- diagonal-congruence factor `(1)` and entrywise limit `(2)`
    (`RHTower/GaussianWindowMomentRescaling.lean`).
  * Finite-matrix stability -- coercivity and openness of positive-definiteness under entrywise
    convergence (`HTGeometry/PositiveDefiniteMatrixLimit.lean`).
  * Recession law `(D)` `gaussianWindow_momentHankelMatrix_posDef_eventually` and its least-defect-degree
    corollary `(E)` `gaussianWindow_momentHankelMatrix_posDef_eventually_forall_le`
    (`RHTower/GaussianWindowHankelRecession.lean`): for bounded continuous `J` with `J 0 > 0`, every fixed
    finite Gaussian Hankel section is eventually positive definite as `tau -> infinity`, so every finite
    family of sections is eventually simultaneously positive definite (the least defect degree exceeds
    any prescribed `d` cofinally).  `(E)` is stated in the equivalent "all sections up to `d` eventually
    positive definite" form rather than via an explicit choice of least-defect-degree function.
  * The Hedenmalm--theta specialization and its identification with RH were already formalized in the
    corpus (`HedenmalmGaussianHankelRH`, `HedenmalmGaussianHankelApertureWidthSpectrum`).
  Moved to `3-formalized/needs-audit`.
