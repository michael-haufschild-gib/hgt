# Suzuki's deficiency line reaches zero shift exactly at the RH floor

- **ID:** `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Suzuki's 2026 deficiency-index construction and
  `../../../3-formalized/not_new_scientific_knowledge/ccm/ccm-negative-spectrum-no-evacuation-law.md`

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

## Lean status

**Superseded, 2026-08-03.**  The variational content of `(2)`--`(6)` is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMDeficiencyLineZeroShift.lean`, on the nested-floor layer of
`CCMNestedFloorNoEvacuation.lean` and `CCMCofinalFloorCriterion.lean`.

- `ShiftAdmissible Q N D lam` — the shifted-positivity condition `(2)`, `T_(a,lambda) > 0`, written
  variationally as `lam * ||v||² < QW(v,v)` on the trial domain.
- **`shiftAdmissible_of_lt_floor`** and **`le_floor_of_shiftAdmissible`** — the two unconditional
  halves of `(3)`.  The second needs the trial set to be nonempty: without it the shifted-positivity
  condition is vacuous and every shift passes, so the bound genuinely fails.  That is a sharpening
  of the card, which states `(2) iff (3)` without the caveat.
- **`shiftAdmissible_iff_lt_floor`** — the equivalence `(2) iff (3)` once the floor is **attained**.
  Attainment is exactly the compact-resolvent input that makes `lambda_0(a)` a lowest eigenvalue
  rather than a bare infimum; it is stated as an explicit hypothesis rather than assumed silently.
- **`zero_shiftAdmissible_iff_floor_pos`** — the first equivalence of `(4)`: zero shift is admissible
  at every aperture exactly when every finite-aperture floor is strictly positive.
- `HasCofinalShiftLine` and **`hasCofinalShiftLine_iff_floor_nonneg`** — equation `(5)`: a shift
  function strictly below the floor at every aperture whose values tend to zero along some apertures
  tending to infinity exists **iff** no floor is negative.  The forward direction is the
  no-evacuation argument `(6)` (a negative floor at one aperture pins the shift below `-delta`
  cofinally, contradicting the limit); the backward direction is the explicit line
  `lambda(a) = -exp(-a)`, which is strictly negative everywhere and tends to zero.
- **`not_hasCofinalShiftLine_of_negative_floor`** and
  **`not_hasCofinalShiftLine_restrictedKernel_of_negative_test`** — the retirement of the shortcut:
  one compactly supported test with negative energy destroys every cofinal shifted line.
- `hasCofinalShiftLine_restrictedKernel_iff` — the same equivalence for the concrete restricted
  kernel form `diffBilinForm K v v` with mass `sqMass v = ∫ v²`.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and not theorems of this card: Suzuki's deficiency-index construction and its entire
characteristic function, and the Suzuki--Yoshida localized criterion identifying strict positivity of
every finite-aperture restricted form with RH.  The Lean statements deliver the variational skeleton
— shift admissibility is the floor inequality, and the cofinal shifted line is floor nonnegativity —
with the RH translation left where the card leaves it, in the localized criterion.

## Gates

- [x] exact positivity hypothesis behind the deficiency line isolated
- [x] zero-shift admissibility identified with fixed-aperture positivity
- [x] cofinal shifted-line construction proved RH-equivalent
- [x] circular determinant-line shortcut retired
- [x] Lean: shift admissibility `(2)`--`(3)`, both halves and the attained equivalence
- [x] Lean: zero-shift criterion `(4)` unconditional
- [x] Lean: cofinal shifted-line equivalence `(5)`--`(6)` unconditional, with the explicit line
- [ ] construct the unshifted indefinite Fredholm determinant line from the source
- [ ] prove zero spectral flow
- [ ] RH
