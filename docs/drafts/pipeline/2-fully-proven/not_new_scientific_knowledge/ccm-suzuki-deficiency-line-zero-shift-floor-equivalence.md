# Suzuki's deficiency line reaches zero shift exactly at the RH floor

- **ID:** `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Suzuki's 2026 deficiency-index construction and
  `ccm-negative-spectrum-no-evacuation-law.md`

## Statement

Let `A_a` be Suzuki's self-adjoint operator for the restricted Weil form and let

```text
lambda_0(a)=inf spec A_a.                                  (1)
```

Suzuki's boundary Hilbert space and its symmetric differentiation operator are constructed from

```text
T_(a,lambda)=A_a-lambda I>0,                              (2)
```

which requires

```text
lambda<lambda_0(a).                                      (3)
```

The associated minimal differentiation operator has deficiency indices `(1,1)` and produces an
entire self-adjoint-extension characteristic function with real zeros.

Then:

```text
lambda=0 is admissible for every a>0
 iff lambda_0(a)>0 for every a>0
 iff RH.                                                   (4)
```

More generally, the following are equivalent:

```text
RH,

there exists a function lambda(a) with
  lambda(a)<lambda_0(a) for every a
  and lambda(a)->0 along a cofinal aperture sequence.     (5)
```

Thus Suzuki's positive deficiency line cannot supply the unshifted CCM determinant-line
orientation without already crossing the RH floor.

## Proof

Condition `(2)` is positive exactly under `(3)`. Hence zero shift is allowed precisely when
`lambda_0(a)>0`. Suzuki--Yoshida's localized criterion identifies strict positivity of every
finite-aperture restricted form with RH, proving `(4)`.

Assume the second clause of `(5)`. If `lambda_0(a_0)=-delta<0` at one aperture, nested-domain
monotonicity gives

```text
lambda_0(b)<=-delta for every b>=a_0.                     (6)
```

Condition `lambda(b)<lambda_0(b)` then forces `lambda(b)<-delta` cofinally, contradicting
`lambda(b)->0`. Therefore no negative floor occurs. The localized criterion gives RH.

Conversely, under RH every `lambda_0(a)` is positive, so any negative cofinal function tending to
zero, for example `lambda(a)=-1/(1+a)`, satisfies `(3)`. This proves `(5)`. `QED`

## Positive CCM carrier law

Suzuki's construction supplies an unconditional determinant-line model only below the unknown
floor. A successful CCM proof must therefore carry exactly one of the following stronger resources:

```text
an unshifted Krein/Fredholm determinant line defined without assuming A_a>0,

or

a source-derived cofinal lower barrier lambda(a)<lambda_0(a) with lambda(a)->0.  (7)
```

The second resource already proves RH by `(5)`. The first is the noncircular determinant-line lift
required by `ccm-evans-gram-requires-determinant-line-lift.md`.

Reality of the zeros of Suzuki's shifted characteristic function is therefore not the missing
positivity theorem. It is compatible with either sign of the unshifted Weil floor because the
construction is allowed to move `lambda` below that floor.

## Literature boundary

The deficiency construction and the requirement `lambda<lambda_0(a)` are in
[Suzuki, *Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096),
Theorem 1.5 and Section 6. The cofinal equivalence is the elementary application of the already
proved no-evacuation law. This is route clarification, not new scientific knowledge.

## Lean decision

The analytic restricted-Weil floor and Suzuki boundary Hilbert space are not present in Lean. An
abstract inequality wrapper would not formalize `(4)`, so no Lean file is added.

## Gates

- [x] exact positivity hypothesis behind the deficiency line isolated
- [x] zero-shift admissibility identified with fixed-aperture positivity
- [x] cofinal shifted-line construction proved RH-equivalent
- [x] circular determinant-line shortcut retired
- [ ] construct the unshifted indefinite Fredholm determinant line from the source
- [ ] prove zero spectral flow
- [ ] RH
