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
