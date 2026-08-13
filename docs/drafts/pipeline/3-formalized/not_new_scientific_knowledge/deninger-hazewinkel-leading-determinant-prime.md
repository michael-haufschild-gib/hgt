# Integral primeness of Hazewinkel's leading Hankel determinant

- **ID:** `deninger-hazewinkel-leading-determinant-prime`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Route:** L — rational-Witt source foundation
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Primary sources:** Hazewinkel, *Operations in the K-theory of endomorphisms* (1983),
  Appendix A.2; Schur-determinant irreducibility infrastructure already formalized from the
  classical Schur-polynomial literature.
- **Statement:** Let `D_n` be the determinant of the universal `n × n` Hankel matrix with
  coefficients `a_0=1`, `a_s=X_{s-1}` for `s>0`. For every `n≥2`, `D_n` is prime in
  `Z[X_0,X_1,...]`. Unconditionally in `n`, `D_n` is prime or a unit; the unit branch consists of
  the degenerate sizes `n=0,1`.

## Goal

Supply the assertion “`D` is prime (easy induction)” used without proof in Hazewinkel Appendix
A.2. The result must live in the integral infinite-variable polynomial ring used before any
specialization, because saturation of the universal determinantal ideal cannot be recovered from
a field-only statement.

## Gates

- [x] 0 → 1 in-progress: exact omitted assertion and its role in saturation isolated
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [x] 2 → 3 formalized: integral theorem and unconditional classification checked in Lean
- [ ] 3 → 4 publication-ready: incorporate into standalone Hazewinkel formalization note

## Paper proof

Fix `n≥2`. Reverse the columns of the leading Hankel matrix. The resulting determinant differs
from `D_n` by the unit sign of the reversal permutation. Under the coordinate identification

```text
a_0 = 1,
a_s = y_(2n-2-s)     for 1≤s≤2n-2,
```

that reversed matrix is the rectangular Schur--Toeplitz matrix for the rectangular partition
`(n-1)^n`. The rectangular Schur determinant is irreducible over `Q`; injective renaming into the
countable variable set and multiplication by a unit preserve primeness. Therefore the scalar
extension `D_n,Q` is prime, hence irreducible, in `Q[X_0,X_1,...]`.

It remains to descend from `Q` to `Z`. Define an integer specialization by

```text
a_0 = 1,
a_(n-1) = 1,
a_s = 0 otherwise.
```

After reversing columns, the specialized Hankel matrix is upper triangular with every diagonal
entry equal to one. Its determinant is therefore a unit (`±1`). If an integer `r` divides every
coefficient of `D_n`, then `r` divides every integer specialization of `D_n`; in particular it
divides this unit. Thus `r` is a unit, so `D_n` is primitive.

Now suppose `D_n=A B` over `Z`. Extending scalars to `Q` makes one of `A_Q,B_Q` a unit because
`D_n,Q` is irreducible. Units in a multivariate polynomial ring over a field are nonzero
constants. Injectivity of `Z→Q` implies the corresponding integral factor was already a constant
integer. Since that constant divides the primitive polynomial `D_n`, it is `±1`. Hence one of
`A,B` is a unit, so `D_n` is irreducible. The infinite-variable polynomial ring over `Z` is a
domain with irreducibles prime, giving the result.

For `n=0` and `n=1`, direct determinant simplification gives `D_n=1`. This proves the premise-free
classification `Prime D_n ∨ IsUnit D_n` for every natural `n`.

## Hostile audit

- **No field-only conclusion:** scalar extension supplies irreducibility input, while explicit
  unit specialization proves integral primitivity and closes Gauss descent.
- **No computed coefficient:** content one follows from a symbolic ring-homomorphism
  specialization and triangular determinant identity.
- **No finite-variable mismatch:** the Schur polynomial is injected into `MvPolynomial ℕ`; prime
  preservation under injective renaming is proved explicitly.
- **No sign gap:** column reversal is tracked as multiplication by the unit permutation sign.
- **Degenerate sizes:** final theorem does not hide an `n≥2` premise; it classifies all sizes by a
  prime-or-unit disjunction.
- **Scientific scope:** this closes literature parity and a formal infrastructure gap. It does not
  prove Hazewinkel saturation or advance the RH core by itself.

## Lean 4 certificate

Module:

```text
GaloisForLFunctions.RHTower.DeningerHazewinkelLeadingPrime
```

Principal declarations:

```text
deningerHazewinkelLeadingDeterminant_prime_of_two_le
deningerHazewinkelLeadingDeterminant_prime_or_isUnit
```

The second declaration is the unconditional capstone. Direct file checking passed with:

```text
lake env lean GaloisForLFunctions/RHTower/DeningerHazewinkelLeadingPrime.lean
```

The module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration. Targeted build

```text
lake build GaloisForLFunctions.RHTower.DeningerHazewinkelLeadingPrime
```

passed after umbrella wiring. `#print axioms` for both declarations reports only Lean/mathlib's
standard `[propext, Classical.choice, Quot.sound]`; no project axiom or admitted proposition
occurs.

## Exact consequence for Hazewinkel

The prime-divisor step in Appendix A.2 is now available integrally: if `D_n` divides a coefficient
product and does not divide the auxiliary factor, it divides the remaining coefficient. The open
frontier is still the saturation theorem

```text
(J_n : D_n) = J_n,
```

specifically the normal-form/independence argument needed to descend a localized relation before
all-stage primeness follows.

## Log

- 2026-08-13 — Schur reversal and integral unit-specialization proof completed.
- 2026-08-13 — formalized over `Z`, including premise-free all-size classification; direct check,
  targeted build, umbrella wiring, and axiom audit passed; moved to Stage 3.
