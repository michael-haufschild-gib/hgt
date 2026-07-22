# Suzuki causal Weil--Robin Green identity

- **ID:** `suzuki-causal-weil-robin-green-identity`
- **Stage:** 2-fully-proven
- **Type:** RH-FRONTIER REPRESENTATION THEOREM / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `suzuki-causal-hinge-boundary-tail-green-law.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, arXiv:2206.03682v4, Theorem 1.1(1); M. Suzuki,
  arXiv:2606.09096v1, equations (1.3), (2.9)--(2.11), Sections 6 and 8.2--8.3

## Problem

The delayed-hinge theorem proves actual prime atoms are not positive Pick atoms.  Surviving RH
producer must assemble complete prime--Gamma source before sign.  Canonical compound denominator
contains `z^2 XiC`; therefore source theorem should first remove universal `z^-2` screw primitive
and expose completed Weil distribution `K=-g''` plus exact boundary current.

## Theorem A: causal Weil--Robin Green identity `[PAPER-PROVED]`

Let `g` be twice differentiable on positive half-line, or a distributional primitive for which
following integrations are justified by approximation.  Let `K=-g''`, let `v` be integrable and
supported on `[-a,a]`, and define

```text
U(x)=integral_(-a)^a g(x-y)v(y)dy,
W(z)=integral_(-a)^a v(y)exp(i z y)dy,

M_g(z)=integral_0^infinity g(t)exp(i z t)dt,

T_(g,R)[v](z)=integral_(-a)^a v(y)exp(i z y)
  integral_0^(a-y)g(t)exp(i z t)dt dy,

R_g[v](z)=M_g(z)W(z)-T_(g,R)[v](z),

E_K[v](z)=integral_(-a)^a v(y)exp(i z y)
  integral_(a-y)^infinity K(t)exp(i z t)dt dy.          (1)
```

In a half-plane of absolute convergence,

```text
z^2 R_g[v](z)
 =exp(i a z)[i z U(a)-U'(a)]+E_K[v](z).                (2)
```

Equivalently, after `x=t+y`,

```text
E_K[v](z)=integral_a^infinity (K*v)(x)exp(i z x)dx,     (3)
```

so `z^2` turns screw exterior into right exterior of completed Weil distribution plus one Robin
boundary current.

### Proof

For `b>=0`, put

```text
J_b(z)=integral_b^infinity g(t)exp(i z t)dt.
```

Two integrations by parts, with vanishing upper boundary in convergence half-plane, give

```text
J_b(z)
 =-exp(i z b)g(b)/(i z)
  +exp(i z b)g'(b)/(i z)^2
  -1/(i z)^2 integral_b^infinity K(t)exp(i z t)dt.     (4)
```

From one-sided Fubini law,

```text
R_g[v](z)=integral_(-a)^a v(y)exp(i z y)J_(a-y)(z)dy. (5)
```

In first two terms of `(4)`, phase satisfies
`exp(i z y)exp(i z(a-y))=exp(i a z)`.  Their source integrals are `U(a)` and `U'(a)`.
Third is `E_K[v]`.  Multiply by `z^2`, use

```text
-z^2/(i z)=i z,
 z^2/(i z)^2=-1,
-z^2/(i z)^2=1,
```

and obtain `(2)`.  Change variables proves `(3)`.

For Suzuki's source, `g` grows like `exp(t/2)` and theorem holds first in `Im z>1/2`, exactly
same source-native domain as one-sided multiplier.  Piecewise hinge prime terms are covered
distributionally; Gamma series is locally normally convergent away from origin.

## Theorem B: delayed-hinge recovery `[PAPER-PROVED]`

For `g(t)=(t-ell)_+`, one has `K=-delta_ell`.  For `0<=ell<=2a`, set `c=a-ell` and use prior
boundary moments `A_c,B_c,W_[c,a]`.  Directly,

```text
U(a)=A_c,
U'(a)=B_c,
E_K[v](z)=-exp(i z ell)W_[c,a](z).                    (6)
```

Thus `(2)` becomes

```text
z^2 R_(ell,a)
 =exp(i a z)(i z A_c-B_c)-exp(i z ell)W_[c,a](z),     (7)
```

which is exactly `z^2` times delayed-hinge boundary--tail law.  This fixes every sign and proves
distributional extension is source-compatible.

## Theorem C: form-shift locality `[PAPER-PROVED]`

For Neumann primitive `r_0(t)=-|t|/2`, `-r_0''=delta_0`.  Shifted screw kernel

```text
k_lambda=g-lambda r_0
```

has

```text
K_lambda=-k_lambda''=K-lambda delta_0.                (8)
```

For `x>a`, compact source `v` vanishes at `x`, hence `(delta_0*v)(x)=0`.  Therefore causal exterior
in `(3)` is independent of direct form shift:

```text
E_(K_lambda)[v]=E_K[v].                                (9)
```

All explicit shift dependence in denominator-matched exterior lies in source state `v_lambda`
and Robin boundary current

```text
exp(i a z)[i z U_lambda(a)-U_lambda'(a)].              (10)
```

This locates exact midpoint half-gap Neumann debt at boundary, consistently with prior
`-d^2 H_r0(v)` theorem; no critical raw Bianchi bulk is available or needed for its location.

## New scientific conclusion

The collective source requested by previous card is no longer unspecified.  Canonical
denominator-matched split is

```text
completed screw exterior
 = Robin boundary current
 + causal exterior of complete signed Weil distribution.                 (11)
```

Prime, polar, and Gamma terms are already assembled inside `K=-g''`; delayed-hinge sign problem
is not tested separately.  Exact form-shift/halfgap channel lives in Robin current.  This is
precisely geometry compound denominator `z^2 XiC` consumes.

## Corrected open RH core

### `SUZUKI-MARKED-WEIL-ROBIN-CD` `[CONJECTURE]`

For recurrence-selected aperture and admissible midpoint pair, insert actual two-resolvent source
into `(2)`.  Affine-sew Robin currents with marked half-gap tensor and polarize already-completed
causal Weil exterior.  Prove their compound Bezoutian equals positive Green Gram.

This target is source-exact and has three hard falsifiers:

1. treating prime atoms separately violates delayed-hinge sign theorem;
2. dropping Robin current loses exact `d^2` Neumann midpoint debt;
3. replacing completed causal Weil exterior by its positive part assumes RH-equivalent sign.

Proving this CD identity gives compound Pick positivity and existing pole tomography proves RH.
Current theorem is exact representation, not missing positivity proof.

## Novelty audit

Two integrations by parts and Robin Green identities are classical `[BRIDGE]`.  Suzuki papers
relate `g` and `-g''` and construct finite operators, but targeted source and arXiv searches found
no formula matching one-sided exterior, `z^2` compound denominator, exact Robin current, delayed
hinge entry law, and form-shift locality `(9)` in one theorem.  Source-specific synthesis and
frontier localization are `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; external priority unverified.

## Formalization status `[LEAN-PROVED]`

`RHTower/SuzukiCausalWeilRobinGreenIdentity.lean` proves denominator-matching algebra `(2)`,
uniqueness of completed exterior, delayed-hinge recovery `(7)`, and both Xi and compound-denominator
connectors.  Analytic integration and compact-diagonal exterior invariance `(9)` remain
dependency-closed paper theorems; Lean does not encode missing positivity as a hypothesis.

Targeted SOTA build passed `9448/9448`.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean.
