# Anticommuting Pauli observer-rank dominance

- **ID:** `anticommuting-pauli-observer-rank-dominance`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / noncommuting exceptional-carrier exclusion
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/observer-spectral-shortcut-action-law.md`
- **Date:** 2026-08-05

## Statement

Let `A` be a finite family of distinct `n`-qubit Pauli words such that every
two distinct members anticommute. Then

\[
 |A|\leq 2n+1.                                      \tag{1}
\]

The bound is sharp as a symplectic statement. For example, the usual binary
Clifford construction gives `2n+1` pairwise anticommuting directions.

Put

\[
 m_{n,q}=\sum_{k=1}^{q}3^k{n\choose k},\qquad
 v_{n,q}=2\sum_{k=1}^{q}{n\choose k}.              \tag{2}
\]

For every `n>=2` and `q>=2`, every such family obeys

\[
 \boxed{|A|+v_{n,q}\leq m_{n,q}.}                  \tag{3}
\]

Consequently the transverse codimension of every pairwise-anticommuting
Pauli carrier inside the full weight-at-most-`q` coefficient space is at
least the exact product-input observer rank:

\[
 m_{n,q}-|A|\geq v_{n,q}.                           \tag{4}
\]

This excludes the canonical noncommuting Clifford/spherical refocusing
mechanism from beating the observer-stationary shortcut exponent.

## Proof of the sharp cardinal bound

Represent Pauli words modulo phase by vectors `v_p` in the binary symplectic
space

\[
 V=\mathbb F_2^{2n}
\]

with alternating form `B`. Anticommutation is exactly

\[
 B(v_p,v_r)=1\quad(p\ne r),
 \qquad B(v_p,v_p)=0.                               \tag{5}
\]

Augment every vector by one coordinate:

\[
 w_p=(v_p,1)\in V\oplus\mathbb F_2.                \tag{6}
\]

We claim that the `w_p` are linearly independent. Suppose

\[
 \sum_{p\in A}c_p w_p=0.                            \tag{7}
\]

The last coordinate gives

\[
 S:=\sum_{p\in A}c_p=0.                             \tag{8}
\]

The first coordinate gives `sum_p c_p v_p=0`. Pairing it with `v_r` and
using `(5)` gives

\[
 0=\sum_{p\in A}c_pB(v_p,v_r)
  =\sum_{p\ne r}c_p=S-c_r=c_r,                     \tag{9}
\]

where subtraction equals addition over `F_2`. Thus every coefficient is
zero. Since `dim(V direct-sum F_2)=2n+1`, linear independence proves `(1)`.

## Observer-codimension comparison

Subtracting the two exact counts in `(2)` gives

\[
 m_{n,q}-v_{n,q}
 =\sum_{k=1}^{q}(3^k-2){n\choose k}.               \tag{10}
\]

When `q>=2`, retaining only the first two nonnegative summands yields

\[
 m_{n,q}-v_{n,q}
 \geq n+7{n\choose2}.                               \tag{11}
\]

For `n>=2`, `choose(n,2)>=n-1`, and hence

\[
 n+7{n\choose2}\geq8n-7\geq2n+1.                 \tag{12}
\]

Combine `(1)` and `(10)`--`(12)` to obtain `(3)` and `(4)`.

## Why this is the relevant noncommuting carrier

For Hermitian Pauli representatives `P_p` satisfying pairwise
anticommutation, every real combination

\[
 K(a)=\sum_{p\in A}a_pP_p
\]

obeys

\[
 K(a)^2=\|a\|_2^2 I.                               \tag{13}
\]

Therefore

\[
 e^{-iK(a)}=
 \cos\|a\|_2\,I-i{\sin\|a\|_2\over\|a\|_2}K(a). \tag{14}
\]

Every sphere with radius in `2 pi Z` is an exact identity-return set. Its
angular dimension `|A|-1` plus its radial recurrence rank `1` gives total
mixed carrier dimension `|A|`. Equation `(4)` shows that even the largest
carrier of this kind cannot lower the Gaussian shortcut exponent below
`v_(n,q)`.

## Hostile audit

1. This theorem covers pairwise anticommuting Pauli spans, not arbitrary
   noncommuting Lie algebras, nonlinear fast-forwardable varieties, or
   unions selected by circuits.
2. It excludes a large exact-refocusing class but does not prove the parent
   observer--spectral shortcut upper bound.
3. Equation `(14)` uses Hermitian Pauli representatives; the symplectic
   cardinal theorem itself is phase-independent.
4. The codimension comparison requires `n>=2` and `q>=2`. One-local dynamics
   remains the known control failure.
5. No novelty claim is authorized before a dedicated literature audit.

## Formalization gate

The proof is finite algebra and exact counting, with no analytic dependency.
Formalize `(1)` and `(3)` before using this carrier exclusion in a paper.
