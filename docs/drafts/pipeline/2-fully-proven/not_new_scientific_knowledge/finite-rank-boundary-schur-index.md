# Finite-Rank Boundary Schur Index

- **ID:** finite-rank-boundary-schur-index
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `finite-rank-one-selector-no-free-lunch.md`,
  `finite-rank-counterterm-kernel-visibility.md`,
  `../../3-formalized/not_new_scientific_knowledge/no-finite-boundary-audit-under-amplification.md`,
  `docs/consolidated/gpt/48.md`
- **Statement:** For an invertible Hermitian bulk form and an invertible
  finite-rank boundary extension, the negative index of the repaired form is
  exactly the negative index of a finite boundary Schur matrix, up to the fixed
  bulk and boundary-base inertias. Thus a semilocal boundary-Weyl proof must
  prove a matrix index theorem, not only a rank-one scalar sign.

## Setup

Let `E` be a finite-dimensional complex vector space. Let `B` be an invertible
Hermitian form on `E`.

Let `V:C^r -> E` be a boundary-channel map, and let `C` be an invertible
Hermitian form on `C^r`. Define the finite-rank boundary extension

`H = B + V C V*`.

Use `kappa_-(A)` for the number of negative eigenvalues of an invertible
Hermitian form `A`, counted with multiplicity.

Define the boundary Schur matrix

`S = -C^{-1} - V* B^{-1} V`.

This sign convention is chosen so that, when `B>0` and `C<0`, positivity of
`H` is equivalent to `S>=0`.

## Theorem

The inertias satisfy

`inertia(H) = inertia(B) + inertia(S) - inertia(-C^{-1})`.

In particular,

`kappa_-(H) = kappa_-(B) + kappa_-(S) - kappa_-(-C^{-1})`.

If `B>0` and `C<0`, then

`kappa_-(H)=kappa_-(S)`.

Therefore, in this common boundary-removal convention, the repaired form is
positive definite if and only if the finite boundary Schur matrix `S` is
positive definite.

Equivalently, with the opposite sign convention

`S_plus = C^{-1}+V*B^{-1}V = -S`,

the same gate is `S_plus<0` when `B>0` and `C<0`.

## Proof

Consider the block Hermitian form on `E direct_sum C^r`

```text
M = [ B    V       ]
    [ V*  -C^{-1} ]
```

Taking the Schur complement of `B`, since `B` is invertible, gives a congruence

`M congruent B direct_sum (-C^{-1}-V*B^{-1}V)`.

Thus

`inertia(M)=inertia(B)+inertia(S)`.

Taking the Schur complement of `-C^{-1}`, since `C` is invertible, gives

`M congruent (B+VCV*) direct_sum (-C^{-1})`.

Therefore

`inertia(M)=inertia(H)+inertia(-C^{-1})`.

Equating the two expressions for `inertia(M)` gives

`inertia(H)=inertia(B)+inertia(S)-inertia(-C^{-1})`.

The negative-index formula is the negative component of the same identity. If
`B>0` and `C<0`, then both `kappa_-(B)` and `kappa_-(-C^{-1})` are zero, so
`kappa_-(H)=kappa_-(S)`.

## Rank-One Shadow

When `r=1`, write `C=(-1/t)` with `t>0` in the boundary-removal convention.
Then

`S = t - v*B^{-1}v`

up to the chosen normalization of the boundary vector. This is the usual scalar
Schur threshold from the rank-one Uvarov/Krein chart.

For `r>1`, the scalar threshold is replaced by the matrix inertia of `S`. A
single channel can be positive while another boundary channel carries a negative
direction. Therefore a rank-one scalar readout can certify the full index only
after a separate theorem proves that no negative direction remains on the
orthogonal or omitted boundary channels.

## Consequence for the RH Route

The corrected semilocal route cannot stop at the first-trivial-zero scalar
`s_d`. A faithful boundary object with pole, first trivial zero, protector-tail,
and finite-place channels must be audited by the matrix Schur index attached to
all source-built channels.

Finite-rank boundary language has two distinct uses:

1. **Static algebra.** At a fixed degree and fixed channel set, the theorem
   reduces the repaired index to the finite Schur matrix `S`.
2. **Source theorem.** The proof still has to construct `B`, `V`, and `C` from
   Euler/Gamma/FE data without zero feeding, prove the correct matrix sign or
   index uniformly in degree/channel scale, and separate fake families by that
   source construction.

Thus this theorem is not an RH proof. It says exactly what a matrix-valued
boundary-Weyl proof must prove once the source-built semilocal carrier has been
constructed.

## Theatre Test

For any semilocal boundary-Weyl proof:

1. What are the boundary channels in `V`?
2. What is the source-built boundary form `C`?
3. Which sign convention is being used for the Schur matrix?
4. Is the proof checking the full matrix inertia of `S`, or only one scalar
   compression?
5. Is the degree/channel-uniform sign supplied by a source theorem rather than
   by finite sampling?

## Gates

- [x] 0 -> 1 in-progress: matrix boundary index gate isolated.
- [x] 1 -> 2 fully-proven: block Schur/Sylvester inertia proof completed.
- [ ] 2 -> 3 formalized: optional finite-dimensional Hermitian Schur theorem.

## Log

- 2026-06-24 -- Codex: created to promote the static finite-rank boundary
  Schur reduction that the semilocal index route now requires.

## 2026-06-24 finite exterior channels do not soften the all-order wall

`finite-prolate-channel-boundary-rh-strength.md` records the all-order consequence for fixed exterior evaluation channels. The Schur matrix gives the static quotient inertia at a fixed degree, but the kernel ideal of any fixed finite exterior channel set still has RH strength.

Thus the matrix Schur theorem is an algebraic coordinate for a source-built boundary object, not a finite-channel shortcut. A proof must control the full source-built channel system uniformly, or prove why the omitted channels and kernel directions carry no negative index.

## 2026-06-24 summable exterior measure boundary case

`summable-exterior-boundary-measure-rh-strength.md` gives the all-order exterior-measure version of the boundary warning. Finite Schur matrices describe fixed finite quotients. A full exterior channel system that is only a finite-total-variation measure still leaves reciprocal atom-isolators visible and remains RH-strength.

Therefore the semilocal matrix/index route must identify a source-built object beyond a summable exterior measure if it is to be non-mirror.

## 2026-06-24 rank-one scalar shadows need kernel exhaustion

`rank-one-scalar-shadow-needs-kernel-exhaustion.md` records the rank-one specialization as a separate guardrail. A positive scalar Schur sign certifies the repaired form only after the boundary kernel is already nonnegative. Otherwise the scalar repairs the visible channel and can leave a negative square in an invisible direction.

Thus the scalar `s_d` is not a faithful index certificate unless the source theorem has already exhausted the omitted or kernel directions. In the multi-channel semilocal route, the replacement is the full boundary Schur matrix and its inertia.
