# Completed local-ratio all-place collapse

- **ID:** `completed-local-ratio-all-place-collapse`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE-D NO-GO (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parent source:** Connes--Consani, *Quasi-inner functions and local factors*,
  [arXiv:2008.10974](https://arxiv.org/abs/2008.10974)

## Statement

For the zeta local factors

```text
gamma_infinity(s)=pi^(-s/2) Gamma(s/2),
gamma_p(s)=(1-p^(-s))^(-1),
rho_v(s)=gamma_v(s)/gamma_v(1-s),
```

every finite product

```text
u_F(s)=rho_infinity(s) product_(p in F) rho_p(s)
```

is quasi-inner on the left critical half-plane.  However, its ordinary all-place completion carries
no zero-orbit index.  More precisely:

1. the product `product_p rho_p(s)` has no nonempty open domain of absolute convergence;
2. the completion-compatible meromorphic regularization is

   ```text
   U_reg(s)=rho_infinity(s) zeta(s)/zeta(1-s)=1;
   ```

3. consequently every window construction which depends functorially only on the regularized
   multiplication symbol has zero off-diagonal corner and Fredholm index zero.

Thus a nontrivial all-place Route D invariant cannot be an ordinary limit of the finite quasi-inner
symbols.  It must be a secondary invariant of the failure of that limit: a renormalization anomaly,
determinant-line defect, or derived-limit class defined before the completed product collapses.

## Proof

For a finite prime `p`,

```text
rho_p(s)=(1-p^(s-1))/(1-p^(-s)).                           (1)
```

Write `sigma=Re(s)`.  If `0<sigma<1/2`, then the denominator in (1) tends to `1` and

```text
|rho_p(s)-1| asymp p^(-sigma).
```

If `1/2<sigma<1`, the same calculation gives

```text
|rho_p(s)-1| asymp p^(-(1-sigma)).
```

Both corresponding prime sums diverge because their exponents are smaller than `1`.  If
`sigma<=0` or `sigma>=1`, the local ratios do not even approach `1` in the required manner, so an
infinite product cannot converge absolutely there.  Every nonempty open subset of the plane contains
a point with `sigma!=1/2`; hence there is no nonempty open domain of absolute convergence.  The
exceptional fixed point `s=1/2`, where every `rho_p(1/2)=1`, does not provide an analytic product
domain.

Put

```text
Lambda(s)=gamma_infinity(s) zeta(s).
```

The completed functional equation is the meromorphic identity

```text
Lambda(s)=Lambda(1-s).                                     (2)
```

The completion-compatible regularization of the finite-place ratio is

```text
product_p^reg rho_p(s)=zeta(s)/zeta(1-s).
```

Therefore, away from the temporary zeros and poles in the displayed quotients,

```text
U_reg(s)
 =gamma_infinity(s)/gamma_infinity(1-s) * zeta(s)/zeta(1-s)
 =Lambda(s)/Lambda(1-s)
 =1.                                                        (3)
```

Equation (3) is an identity of meromorphic functions.  Hence every apparent `0/0` at a reflected
nontrivial zero is removable in the total ratio, and `U_reg` is globally the constant meromorphic
function `1`.

Let `P` be any Hardy polarization.  Multiplication by `U_reg` is the identity, so

```text
(1-P) M_(U_reg) P=0,
P M_(U_reg) P=1_(range P).
```

The first operator has no determinant content and the second has Fredholm index zero.  Any ordinary
window localization that is functorial under equality of multiplication symbols has the same
conclusion.  This proves all three assertions.

## Exact route boundary

The theorem does **not** contradict finite-place quasi-innerness.  Connes--Consani prove compactness
for each finite archimedean-compensated product, and those finite kernels remain nontrivial.  What
fails is promotion by an ordinary all-place symbol limit.

Nor does the theorem rule out a secondary anomaly.  Since the finite product has no open absolute
convergence domain, the sequence of finite quasi-inner compressions need not converge in norm,
Schatten norm, or determinant class to the regularized symbol.  A nontrivial class could in principle
live in precisely that failure of convergence.  Such a construction must prove all of the following:

1. independence of the prime exhaustion;
2. independence of admissible local counterterms;
3. a determinant-compatible window localization;
4. identification of the resulting secondary class with the sign-isotypic, free-reflection-orbit
   divisor; and
5. a source-side quantitative vanishing theorem on a strict post-certificate window.

Without items 1--2 the object is a choice of regularization.  Without item 4 it is only an Euler
product divergence invariant.  Without item 5 it is another exact encoding of the unknown zero
count.

## Route D consequence

- `[CLOSED]` The all-place regularized local-ratio multiplier itself is identically trivial.
- `[CLOSED]` Its Hardy compression, ordinary Fredholm index, and any symbol-local window index cannot
  count free zero orbits.
- `[OPEN CORE]` The only surviving quasi-inner formulation is a **secondary completed-source
  renormalization-anomaly index theorem**.  The anomaly must be constructed before the global
  functional equation collapses the product to `1`.

## Novelty audit

The proof is the completed functional equation plus standard facts about Euler products and
multiplication operators.  It is a useful source-specific no-go, but it is a direct parent-theory
bridge and not new scientific knowledge.

## Lean status

`formal/GaloisForLFunctions/RHTower/CompletedLocalRatioAllPlaceCollapse.lean`
already proves the unconditional globally regularized completed ratio is the
constant unit symbol.  On 2026-08-23,
`formal/GaloisForLFunctions/RHTower/FiniteEulerLocalRatio.lean` added the
exact one-prime Euler-power formula, reflection-inverse identity, and the
fixed-point identity `rho_p(1/2)=1`. It also proves `rho_p(0)=rho_p(1)=0`
and the resulting endpoint failures of absolute convergence. Its targeted
source check, module build, and axiom audit pass with only `propext`,
`Classical.choice`, and `Quot.sound`.

The same module now proves the exact off-line quarter-point identity
`rho_p(1/4)-1=p^(-1/4)+p^(-1/2)` and derives non-summability of its norm
deviations from the prime-power abscissa theorem. This is a certified
interior obstruction, but it is not yet the required arbitrary complex
off-critical-line asymptotic.

By reflection it now also proves the exact `s=3/4` formula and a uniform
`p^(-1/4)/3` lower bound for its norm deviation, hence the corresponding
prime-series non-summability. The all-open-domain theorem still requires a
uniform arbitrary-point comparison.

The no-open-domain absolute-convergence theorem for the ordinary infinite
finite-place product, and the formal Hardy-compression/Fredholm consequences,
are not yet formalized. The card therefore remains in stage 2.
