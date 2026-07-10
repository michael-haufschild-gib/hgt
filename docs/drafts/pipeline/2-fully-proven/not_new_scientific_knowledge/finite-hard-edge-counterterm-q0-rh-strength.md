# Finite Hard-Edge Counterterm Q0 RH Strength

- **ID:** finite-hard-edge-counterterm-q0-rh-strength
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `test-space-closure-q0-visible-rh.md`,
  `reciprocal-seam-admissible-domain-q1.md`,
  `pole-cancellation-not-stieltjes-positive.md`
- **Statement:** Adding an arbitrary finite-jet counterterm at the reciprocal
  hard edge `0` cannot hide an off-line reciprocal atom from the shifted `Q_0`
  test. If the renormalized all-order form is positive, then RH already follows.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

For real polynomials `p`, define the shifted source-aware form

`Q_0[p] = sum_y M_y y p(y)^2`.

Let `m >= 1`. Let `C` be any real quadratic form on `R[y]` such that

`C[p] = 0 whenever p in y^m R[y]`.

This includes the usual case in which `C` depends only on the finite hard-edge
jet

`p(0), p'(0), ..., p^(m-1)(0)`.

Define the finite-counterterm renormalized form

`R_C[p] = Q_0[p] + C[p]`.

## Theorem

If

`R_C[p] >= 0 for every real polynomial p`,

then RH holds.

More generally, for any closed conjugation-invariant set `E subset K`, a
counterterm that vanishes on all polynomials whose restriction to `E` is zero
cannot affect atom-isolation outside `E`. Positivity of the renormalized form
forces every reciprocal atom outside `E` to lie in `R_{>0}`.

## Proof

Assume first that `E={0}` and `C` vanishes on `y^m R[y]`.

Suppose there is a bad reciprocal atom `a in Y`.

If `a` is real and negative, define a continuous conjugation-symmetric function
`h` on `K` by

`h(a)=a^(-m)`, `h=0` on `K \ {a}`.

By the same Mergelyan/symmetrization argument used in
`source-aware-q0-alone-reciprocal-positivity.md`, choose real polynomials
`r_n` uniformly approximating `h` on `K`. Set

`p_n(y)=y^m r_n(y)`.

Then `p_n in y^m R[y]`, so `C[p_n]=0`, and `p_n` converges uniformly on `K` to
the atom-isolator `e_a` with `e_a(a)=1` and `e_a=0` elsewhere. Therefore

`R_C[p_n] = Q_0[p_n] -> M_a a < 0`,

contradicting positivity for all large `n`.

If `a` is non-real, then `conjugate(a)` is also an atom with the same
multiplicity. Choose `zeta in C` such that

`Re(a zeta^2) < 0`.

Define a continuous conjugation-symmetric function `h` on `K` by

`h(a)=zeta/a^m`,
`h(conjugate(a))=conjugate(zeta)/conjugate(a)^m`,
`h=0` elsewhere.

Choose real polynomials `r_n -> h` uniformly on `K` and set `p_n(y)=y^m r_n(y)`.
Again `C[p_n]=0`, and `p_n` converges to the symmetric isolator with values
`zeta` and `conjugate(zeta)` at the conjugate pair. Hence

`R_C[p_n] = Q_0[p_n] -> 2 M_a Re(a zeta^2) < 0`,

contradicting positivity.

Thus no bad atom exists, so every reciprocal atom lies in `R_{>0}`. This is RH.

For the closed-set variant, replace `y^m R[y]` by a test subspace whose uniform
closure contains the atom-isolators for all atoms outside `E` while vanishing on
`E`. The same argument applies because the counterterm is zero on that subspace.

## Consequence for the RH Route

Finite hard-edge renormalization is not an escape from the shifted `Q_0` wall.
A counterterm depending on finitely many data at the accumulation point `0` can
change low-order presentation, finite sections, or unshifted `T_0` bookkeeping.
It cannot repair a negative contribution from an isolated reciprocal atom away
from `0`, because that atom can be isolated by polynomials vanishing to arbitrary
prescribed finite order at `0`.

Therefore a proposed proof of positivity for

`Q_0[p] + finite hard-edge counterterm`

is still RH-strength. Under RH it additionally requires the counterterm itself
to be nonnegative on the hard-edge jet directions; otherwise even RH would not
make the renormalized form positive. But if positivity of the renormalized form
is asserted for all polynomials, the counterterm has not weakened the RH
obligation.

The only possible escape is an infinite-order or nonlocal renormalization whose
closed test space fails to isolate some atoms. That case is exactly the
test-space closure audit: the hidden atoms and their source control must be
identified explicitly.

## Theatre Test

For any hard-edge renormalized positivity argument, ask:

1. Does the counterterm depend only on finitely many jets at `0`?
2. If yes, why does the argument not reduce to this theorem?
3. If no, what is the closed test space after the infinite-order/nonlocal
   renormalization?
4. Which reciprocal atoms can no longer be isolated, and what source theorem
   controls them?

## Gates

- [x] 0 -> 1 in-progress: finite hard-edge counterterm loophole isolated.
- [x] 1 -> 2 fully-proven: complete atom-isolation proof with arbitrary finite
  vanishing order at `0`.
- [ ] 2 -> 3 formalized: optional; follows from polynomial density with finite
  vanishing constraints plus the source-aware `Q_0` atom-isolation theorem.

## Log

- 2026-06-24 -- Codex: created to close the finite hard-edge counterterm route.
  The proof is atom isolation through the ideal `y^m R[y]`.

## 2026-06-24 finite-rank quotient distinction

`finite-rank-counterterm-kernel-visibility.md` explains why the finite hard-edge theorem is stronger than a generic finite-rank statement. A hard-edge finite-jet counterterm vanishes on `y^m R[y]`, and that kernel still contains approximants to every atom-isolator away from `0`. Hence it remains RH-strength.

A general finite-rank counterterm need not have this property. If its quotient evaluates at a bad atom, it can cancel that atom. Therefore finite-rank repairs require an explicit kernel/quotient audit.
