# Suzuki Neumann-dominated shift-cone obstruction

- **ID:** `suzuki-neumann-dominated-shift-cone-obstruction`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ASYMPTOTIC / CORRECTLY NORMALIZED HERGLOTZ NO-GO / SHIFT SELECTION LAW
- **Scientific status:** `[PAPER-PROVED] [LEAN ALGEBRAIC CORE] [CANDIDATE NOVEL] [NOT RH]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md`
- **Live successor:**
  `../1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`
- **RH used:** no
- **Computation used:** no
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 6 and 8.3.

## Problem

Correct one-sided phase reopens the scalar jump-Pick route.  It does not answer whether every
pair of real shifts `alpha != beta < lambda_a` can produce a normalized Herglotz quotient.  Exact
central threshold is

```text
Phi_norm(alpha,beta) <= c_Xi,
c_Xi=XiC''(0)/XiC(0)<0.                                (1)
```

Direct Neumann contribution is linear in shift and cancels from `Phi_norm`.  Remaining quantity
is affine intercept of normalized Euler--Gamma right-triangle jets.

## Theorem A: universal large-negative deficiency profile

Fix aperture `a>0`.  Put `e_+(x)=e^x`, `e_-(x)=e^(-x)` on `[-a,a]`.  Suzuki's deficiency vectors
are

```text
v_(lambda,+)=(A_a-lambda)^(-1)e_+,
v_(lambda,-)=(A_a-lambda)^(-1)e_-.
```

Since `A_a` is self-adjoint and bounded below, spectral calculus gives unconditionally

```text
(-lambda)(A_a-lambda)^(-1) -> I strongly,
lambda -> -infinity.                                   (2)
```

Therefore `(-lambda)v_(lambda,+)->e_+` and
`(-lambda)v_(lambda,-)->e_-` in `L^2[-a,a]`.

For phase one, compact effective source is distribution

```text
nu_lambda=i(v_(lambda,+)'-v_(lambda,+)
             +v_(lambda,-)'+v_(lambda,-)),             (3)
```

with zero-extension endpoint atoms included.  Interior terms cancel for limiting exponentials.
Distribution derivative of `e^x 1_[-a,a]` contributes
`e^(-a)delta_(-a)-e^a delta_a`; derivative of `e^(-x)1_[-a,a]` contributes
`e^a delta_(-a)-e^(-a)delta_a`.  Hence `(2)--(3)` give

```text
(-lambda)nu_lambda
 -> i*2*cosh(a)*(delta_(-a)-delta_a).                  (4)
```

The same limit follows directly from Suzuki's characteristic formula:

```text
(-lambda)W_lambda(z)
 -> (z-i) integral_(-a)^a e^x e^(izx)dx
    +(z+i) integral_(-a)^a e^(-x)e^(izx)dx
 =4*cosh(a)*sin(a z),                                  (5)

(-lambda)W_lambda'(0) -> 4a*cosh(a).                   (6)
```

No differentiability upgrade of resolvents is hidden: pairing `(3)` with a `C^1` compact test
integrates the distribution derivative by parts and is a bounded `L^2` functional, so strong
convergence in `(2)` suffices.

## Theorem B: normalized Euler--Gamma edge limit

Let

```text
H_g(s)=integral_0^s g(t)dt.
```

Physical right triangle at spectral value zero is

```text
T_(g,R,lambda)(0)=<nu_lambda,H_g(a-y)>.
```

Apply endpoint limit `(4)`.  Since `H_g(0)=0`,

```text
(-lambda)T_(g,R,lambda)(0)
 -> i*2*cosh(a)*H_g(2a).                               (7)
```

Divide `(7)` by `(6)` and apply exact Weyl normalization `q_norm=-i q_phys`:

```text
q_norm,lambda^EG
 -> H_g(2a)/(2a).                                      (8)
```

The direct Neumann law is

```text
q_norm,lambda=q_norm,lambda^EG+(a/2)lambda,
```

and affine sewing annihilates its second term exactly.

## Theorem C: dyadic negative-shift cone violates central Herglotz sign

Choose

```text
alpha_L=-2L,
beta_L=-L.
```

Both are admissible for every sufficiently large `L`, for any finite spectral floor.  If
`q(lambda)->ell` at `-infinity`, their affine zero-intercept is exactly

```text
[beta_L q(alpha_L)-alpha_L q(beta_L)]/(beta_L-alpha_L)
 =2q(-L)-q(-2L) -> ell.                                (9)
```

Combining `(8)--(9)` yields

```text
Phi_norm(-2L,-L) -> H_g(2a)/(2a).                     (10)
```

Suzuki's explicit screw function is continuous and satisfies `g(0)=0`.  Therefore

```text
H_g(2a)/(2a) -> 0,  a -> 0+.                           (11)
```

Since `c_Xi<0`, choose `a>0` small enough that `H_g(2a)/(2a)>c_Xi`.  Equation `(10)` then gives,
for all sufficiently large `L`,

```text
Phi_norm(-2L,-L)>c_Xi.                                 (12)
```

This contradicts necessary Herglotz condition `(1)`.  Hence:

> At every sufficiently small aperture, all sufficiently negative dyadic admissible shift pairs
> produce a normalized scalar jump quotient that is not Herglotz.

The result uses correct physical multiplier `iG_eta`, correct coordinate `eta=-i lambda/2`, and
correct triangle rephasing `-iT_phys`.  It is distinct from retracted mixed-coordinate no-go.

## Strongest positive survivor

Scalar jump positivity, if true for a source-selected pair, must exclude the Neumann-dominated
escape cone.  Auxiliary shifts are not harmless gauges: although Xi-pole coefficients and direct
linear Neumann channel are shift-independent after sewing, source-divisor flux retains nonlinear
resolvent dependence.  A viable construction needs an intrinsic selection law keeping at least
one shift in a bounded spectral window near `lambda_a`, then must prove `(1)` and full Pick
positivity for that selected pair.

Concrete falsifiers for proposed selection laws:

1. any law with `alpha_a=-2L_a`, `beta_a=-L_a`, `L_a->infinity`, at fixed small aperture fails;
2. any law depending only on admissibility and not source flux cannot distinguish the forbidden
   cone;
3. direct Neumann positivity cannot repair failure because its affine intercept is identically
   zero;
4. source gauge changes cancel from normalized jets and cannot change `(10)`.

## Formalization

`formal/GaloisForLFunctions/RHTower/SuzukiLargeNegativeShiftCentralFlux.lean` proves the exact
affine consumer:

```text
suzukiRealAffineZeroIntercept_neg_two_neg_one
tendsto_suzukiDyadicNegativeShiftIntercept_atTop
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero
```

Strong-resolvent endpoint-source limit `(4)`, triangle limit `(8)`, and identification with
Suzuki's explicit `g` remain paper-level because the actual restricted Weil operator and
distributional half-triangle have not been constructed in Lean.

## Novelty audit

Internal corpus contained central intercept, correct one-sided phase, and Neumann cancellation,
but no large-negative resolvent profile, endpoint-atom limit, screw-average law `(8)`, or forbidden
shift cone `(12)`.  Suzuki gives deficiency resolvent equations and ordinary-kernel model but does
not analyze `lambda -> -infinity` or the central Herglotz flux.  Generic strong-resolvent scaling
and endpoint distribution calculus are classical.  Candidate novelty is their exact Suzuki
source synthesis and resulting shift-selection obstruction.  External priority remains
unverified.

## Gates

- [x] correct coordinate and source phase used
- [x] strong-resolvent limit proved on paper
- [x] endpoint distribution and characteristic limits cross-checked
- [x] normalized triangle limit proved
- [x] dyadic affine limit and central contradiction proved
- [x] strongest positive shift-selection survivor extracted
- [x] affine asymptotic core formalized in Lean
- [ ] formalize actual restricted-resolvent and triangle instantiation
- [ ] construct source-selected nonescaping pair with full jump Pick kernel
- [ ] RH

### Lean progress — Theorem A's `(5)` and `(6)` FORMALIZED

The Formalization section records `(4)`, `(5)`, `(8)` as paper-level "because the actual restricted
Weil operator and distributional half-triangle have not been constructed in Lean". That is right for
`(4)` (a strong-resolvent limit of the actual operator) but not for `(5)` and `(6)`: the *limit
object* in `(5)` is an explicit elementary integral identity, and `(6)` differentiates it. Neither
mentions a distribution.

Both are now proved, in `HTGeometry/CompactFourierSineKernel.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `integral_exp_mul_exp_mul_I_symm` : `∫ y in -a..a, exp(c y) exp(I z y) = 2 sinh((c + I z) a)/(c + I z)`.
- `exponentialEdgePair_transform` : **`(5)`'s right-hand side** —
  `(z - I) ∫ e^y e^{Izy} + (z + I) ∫ e^{-y} e^{Izy} = 4 cosh(a) sin(a z)`, for `z ≠ ± I`.
  The mechanism is that `1 + I z = I (z - I)` and `-1 + I z = I (z + I)`, so each shift factor
  cancels its own transform's pole and the two `sinh`s add to `2 I cosh(a) sin(a z)`.
- `deriv_edgePairKernel_zero` : **`(6)`** — the central jet of that kernel is `4 a cosh a`.

So what remains genuinely paper-level in Theorem A is only the *convergence* statement `(4)`: that
`(-lambda) nu_lambda` tends to the endpoint atom pair, which does need the actual resolvent. The
value it converges to, and the normalization `(6)` that `(8)` divides by, are now theorems.

### Lean progress — Theorem B's `(7)` and `(8)` FORMALIZED

Same split as Theorem A. Given the endpoint atom limit `(4)`, neither `(7)` nor `(8)` involves a
distribution: `(7)` evaluates a two-atom **measure** against a continuous primitive, and `(8)` is the
algebra of dividing by `(6)` and applying the Weyl normalization. Both are now proved in
`HTGeometry/SignedCharFunCentralJet.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `integral_endpointAtomPair` : **`(7)`** — pairing `delta_{-a} - delta_a` against `y ↦ H(a - y)`
  gives `H(2a)`, using `H(0) = 0` exactly as the card does. Proof: `integral_dirac` twice.
- `normalizedEdgeRatio` : **`(8)`** — `-I * ((I * 2c * H(2a)) / (4 a c)) = H(2a) / (2a)`. The two
  factors of `I` cancel (this is where `q_norm = -i q_phys` enters) and the edge weight
  `c = cosh a` divides out, leaving the aperture average.

**Revised boundary for this card.**  Of Theorem A and Theorem B, only `(4)` — the strong-resolvent
convergence `(-lambda) nu_lambda -> i 2 cosh(a) (delta_{-a} - delta_a)` — is still paper-level, and
it is the one statement that genuinely needs the restricted Weil operator in Lean. Its limit value
`(5)`, the normalization `(6)`, the pairing `(7)` and the ratio `(8)` are all theorems. The final
gate line "formalize actual restricted-resolvent and triangle instantiation" is therefore now
exactly one item, not four.

### Lean progress — Theorem C's `(11)` FORMALIZED

`eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero` takes
`Tendsto q atBot (nhds 0)` as a **hypothesis** — that is `(10)` together with `(11)`. Of the two,
`(11)` is unconditional real analysis: for Suzuki's continuous screw function with `g(0) = 0`,
`H_g(2a)/(2a) -> 0` as `a -> 0+` because that quotient is the slope at the origin of the primitive,
and the fundamental theorem of calculus identifies it with `g(0)`.

New module `HTGeometry/PrimitiveAverageLimit.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_primitive_div_nhdsNE_zero` : for continuous `g`, `(∫_0^s g)/s -> g 0` as `s -> 0`.
  Proof: the primitive vanishes at `0`, so the quotient *is* `slope` there, and
  `Continuous.integral_hasStrictDerivAt` gives the derivative `g 0`.
- `tendsto_primitive_div_two_mul_nhdsGT_zero` : **`(11)`** — with `g 0 = 0`, the aperture average
  `H_g(2a)/(2a) -> 0` as `a -> 0+`.

So Theorem C's chain now rests only on `(10)` — which is `(8)` combined with `(9)`, and `(9)` was
already formal (`tendsto_suzukiDyadicNegativeShiftIntercept_atTop`). With `(5)`--`(8)` and `(11)`
all proved, the single genuinely open input of this card is `(4)`, the strong-resolvent convergence
of the actual restricted operator.

### Lean progress — the reusable core of `(4)` FORMALIZED

`(4)` is the one genuinely operator-dependent step of this card, and it is shared with four other
cards (`suzuki-boundary-log-nonclock-nonflat-tangent`,
`suzuki-finite-shift-flat-projective-resolvent-holonomy`,
`suzuki-arithmetic-tangent-inverse-moment-holography`,
`suzuki-global-phase-conjugacy-divisor-flow`), all of which park on the unbounded Suzuki operator.
mathlib has `LinearPMap` adjoints but no Friedrichs extension and no spectral theorem for unbounded
self-adjoint operators, so the operator itself stays open.

What can be built now is the analytic step that makes `(2)`/`(4)` a *strong* rather than a norm
limit. In resolvent coordinates the family `(-lambda)(A - lambda)^{-1}` becomes a continuous
functional calculus of the bounded resolvent, and its symbols converge pointwise but **not**
uniformly at the spectral accumulation point `0` — which is exactly why `(2)` is only strong. The
standard bridge is: uniform operator bound, plus norm convergence on a dense set, gives strong
convergence everywhere. That bridge was in neither mathlib nor the corpus.

New module `HTGeometry/StrongConvergenceDense.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_of_dense_of_uniform_bound` : for continuous linear maps uniformly bounded by `C` with
  limit candidate also bounded by `C`, convergence on a dense set implies convergence at every
  point. The `eps/3` argument, stated over an arbitrary `NontriviallyNormedField`.

This is the general-purpose half of `(4)`; what remains is the construction of `A_a` itself and the
identification of the dense set (the range of the resolvent), both of which need the operator.
