# Rank-One Scalar Shadow Needs Kernel Exhaustion

- **ID:** rank-one-scalar-shadow-needs-kernel-exhaustion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `uvarov-repair-requires-boundary-kernel-positivity.md`,
  `finite-rank-boundary-schur-index.md`
- **Statement:** A positive rank-one Weyl scalar certifies the full repaired
  positivity only after all directions invisible to the rank-one boundary
  functional are already nonnegative. Otherwise the scalar is only a shadow of
  the faithful index.

## Setup

Let `V` be a finite-dimensional real or complex vector space. Let `A` be a
Hermitian form on `V`, let `beta:V -> C` be a nonzero linear functional, and let
`t>0`. Define the rank-one repaired form

`H=A+t beta^* beta`.

Let

`K=ker beta`.

When `A|_K` is invertible, choose `q in V` with `beta(q)=1` and write

`V=K direct_sum C q`.

With respect to this decomposition,

```text
A = [ B   l ]
    [ l*  a ]
```

where `B=A|_K`. Define the rank-one scalar shadow

`s_beta(t)=a+t-l* B^{-1} l`.

## Theorem

Assume `A|_K` is positive definite. Then

`H>0` if and only if `s_beta(t)>0`.

More generally, if `H>=0`, then necessarily

`A|_K>=0`.

Consequently, a positive scalar shadow cannot certify `H>=0` unless the kernel
condition `A|_K>=0` is also known. The exact finite-dimensional gate is

`H>=0  =>  A|_K>=0`,

and, in the nondegenerate kernel case,

`A|_K>0 and s_beta(t)>0  <=>  H>0`.

Thus a rank-one scalar sign is faithful precisely after the boundary kernel has
no negative direction left for the scalar to miss.

## Proof

If `k in K`, then `beta(k)=0`, so

`H[k]=A[k]`.

Therefore `H>=0` implies `A|_K>=0`.

Assume now that `A|_K=B>0`. In the decomposition
`V=K direct_sum Cq`, the repaired form has matrix

```text
H = [ B      l  ]
    [ l*   a+t ]
```

Since `B>0`, the Schur complement criterion gives

`H>0  <=>  a+t-l* B^{-1} l > 0`,

which is exactly `s_beta(t)>0`.

## Countermodel

The scalar condition alone is insufficient.

Take `V=C^2`, `beta(x,y)=x`, `t=2`, and

`A=diag(-1,-1)`.

Then `K={0} direct_sum C`, and `A|_K=-1` has one negative direction. Choosing
`q=(1,0)`, the scalar shadow is

`s_beta(2)=-1+2=1>0`.

But

`H=A+2 beta^*beta=diag(1,-1)`,

so `H` still has a negative direction. The positive scalar repaired only the
visible coordinate and missed the kernel direction.

## Consequence for the RH Route

In the first-trivial-zero chart, `beta` is evaluation at

`y_*=-4/25`.

The scalar Weyl sign `s_d>0` is therefore a certificate for the full finite
section only after the source proof has established that the boundary kernel

`p(y_*)=0`

carries no negative direction. In semilocal form, the same point is matrix
valued: a single scalar channel can miss negative directions in omitted pole,
protector, or finite-place channels.

Thus the faithful target is the integer index of the completed semilocal
carrier. The scalar `s_d` is a valid compression only when a source theorem
proves kernel exhaustion. Without that theorem, `s_d>0` is compatible with a
remaining negative square.

## Theatre Test

For any proof that cites a positive rank-one scalar:

1. Identify the boundary functional `beta`.
2. Prove `A|_{ker beta}>=0` from source data.
3. If this proof is missing, do not promote the scalar sign to full positivity.
4. If additional channels exist, replace the scalar by the full Schur matrix
   and compute its inertia.

## Novelty And Significance Gate

The proof is Schur-complement algebra. The significant content is its placement:
it blocks the recurring scalar-shadow error in the RH route and forces the proof
back to the completed semilocal integer index.

## Gates

- [x] 0 -> 1 in-progress: scalar-shadow gap isolated from the consolidated
  bridge requirement.
- [x] 1 -> 2 fully-proven: finite-dimensional Schur proof and countermodel
  written.
- [ ] 2 -> 3 formalized: optional Hermitian Schur-complement lemma.

## Log

- 2026-06-24 -- Codex: created to make explicit that `s_d>0` is not a faithful
  index certificate unless the boundary kernel has already been exhausted.

## 2026-06-24 scalar thresholds are not ordered by boundary location

`boundary-weyl-thresholds-have-no-formal-monotonicity.md` records another scalar-shadow failure. Even when two rank-one scalar thresholds are well-defined, their relative size is not determined by the boundary points alone. The positive bulk form controls the dual energies.

Thus a scalar sign at one exterior channel cannot certify a scalar sign at another exterior channel unless a source theorem proves the comparison for the actual bulk form.

## 2026-06-24 Christoffel monotonicity requires a positive bulk

`stieltjes-bulk-exterior-christoffel-monotonicity.md` identifies the case where scalar thresholds do have a valid exterior order: positive moment bulks with support on one side of the boundary interval. The scalar comparison is then a Christoffel-kernel theorem.

For the RH route this comparison is downstream of kernel exhaustion, not a substitute for it. The positive bulk hypothesis must be proved from source data before any scalar threshold order can carry the repair sign.

## 2026-06-24 N1 anatomy does not order scalar thresholds

`n1-signed-bulk-exterior-monotonicity-fails.md` gives an exact signed-moment counterexample: an `N_1` bulk can reverse the expected exterior repair-threshold order. Thus knowing that an unrepaired form has one negative square does not make scalar comparisons faithful across boundary points.

The scalar route still needs the source proof of kernel exhaustion and the Schur sign for the actual boundary channel.
