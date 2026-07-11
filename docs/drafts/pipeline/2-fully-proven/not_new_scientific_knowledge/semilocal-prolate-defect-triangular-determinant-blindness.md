# Semilocal prolate defect is triangularly determinant-blind

- **ID:** semilocal-prolate-defect-triangular-determinant-blindness
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE GATEKEEPER (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source input:** the cyclic-pair filtrations and formal prolate operators of
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423v2,
  Sections 2 and 4.3

## Statement

Let `E_n^infinity` and `E_n^P` be the degree-`n` cyclic filtrations for the archimedean and finite
semilocal cyclic pairs. Let `J_P` be the identity on polynomial functions, so

`J_P(E_n^infinity)=E_n^P`.

Put

`B_P=J_P^(-1)N_PJ_P-N_infinity`

on the archimedean polynomial core. Then

`B_P(E_n^infinity) subset E_(n-1)^infinity`                 (1)

for every `n>=0`, with `E_(-1)=0`. Hence `B_P` is locally nilpotent:

`B_P^(n+1)|_(E_n^infinity)=0`.                              (2)

For every finite truncation,

`det(I+z B_P|_(E_n^infinity))=1`.                           (3)

If `B_P` has any compact extension to the completed Hilbert space, that extension is quasinilpotent.
If it has a trace-class extension, its Fredholm determinant is identically trivial:

`det_F(I+zB_P)=1` for every complex `z`.                    (4)

The pulled-back formal prolate naturality defect is `lambda^2B_P`; it has the same conclusions. Thus
the raw defect cannot yield a nontrivial ordinary or Fredholm determinant even though its
ground-state row contains the infinite alternating nonzero tower proved in
`semilocal-all-even-jacobi-prolate-residue-tower.md`.

## Proof

The number operator associated to a cyclic pair acts by `n` on the one-dimensional graded quotient

`E_n/E_(n-1)`.

Indeed its degree-`n` orthonormal polynomial is an eigenvector of eigenvalue `n`, while all lower
orthonormal polynomials lie in `E_(n-1)`. Since `J_P` identifies the polynomial filtrations, both
`J_P^(-1)N_PJ_P` and `N_infinity` induce multiplication by the same scalar `n` on
`E_n^infinity/E_(n-1)^infinity`. Their difference therefore maps `E_n` into `E_(n-1)`, proving (1).
Iteration proves (2), and (3) follows because the finite matrix is strictly triangular.

Now suppose `B_P` extends compactly. Let `Pi_n` be the orthogonal projection onto `E_n^infinity`.
Since `Pi_n` converges strongly to the identity and `B_P` is compact,

`Pi_n B_P Pi_n -> B_P`

in operator norm. Every approximant is finite-rank nilpotent by (2). Nonzero eigenvalues of compact
operators, counted with algebraic multiplicity inside an isolated contour, are stable under sufficiently
small norm perturbations. A nonzero eigenvalue of `B_P` would therefore force a nearby nonzero
eigenvalue of all sufficiently large nilpotent approximants, impossible. Hence the compact extension has
spectrum `{0}` and is quasinilpotent.

For a trace-class extension, the Fredholm determinant is the product over eigenvalues with algebraic
multiplicity. All eigenvalues are zero, giving (4). Equivalently all finite truncation determinants are
one and the trace-class determinant is their canonical limit.

Finally the source formal prolate operators share the multiplication term `-D^2`, which intertwines
`J_P`. Therefore

`J_P^(-1)(W_(lambda,P)J_P-J_PW_(lambda,infinity))=lambda^2B_P`,

and scalar multiplication preserves strict lowering, local nilpotence, quasinilpotence, and determinant
triviality.

## Route consequence

- `[CLOSED]` Determinants of finite Jacobi truncations of the raw grading/prolate naturality defect
  are identically one.
- `[CLOSED]` Declaring the raw defect trace class would not create a determinant invariant; its
  Fredholm determinant would still be one.
- `[PROVED]` Nonzero low-mode or all-mode coefficients do not contradict determinant blindness:
  strictly triangular nilpotent matrices can have many nonzero entries.
- `[OPEN CORE]` A relative resolvent can mix the filtration and need not remain triangular. It is the
  only determinant variant not killed by this theorem, but it requires source-selected closed
  realizations and Schatten estimates.

## Novelty audit

Strict filtration lowering and determinant blindness are standard triangular-operator consequences.
The application decisively removes a Route B shortcut but is derivable from the parent cyclic-pair
filtration, so it is classified as BRIDGE rather than new scientific knowledge.
