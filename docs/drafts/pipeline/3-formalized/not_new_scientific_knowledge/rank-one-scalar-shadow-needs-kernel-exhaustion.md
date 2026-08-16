# Rank-One Scalar Shadow Needs Kernel Exhaustion

- **ID:** rank-one-scalar-shadow-needs-kernel-exhaustion
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `../../3-formalized/not_new_scientific_knowledge/uvarov-repair-requires-boundary-kernel-positivity.md`,
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
- [x] 2 -> 3 formalized: `HTGeometry/BoundaryKernelSchurSplit.lean`.

## Log

- 2026-06-24 -- Codex: created to make explicit that `s_d>0` is not a faithful
  index certificate unless the boundary kernel has already been exhausted.

## 2026-06-24 scalar thresholds are not ordered by boundary location

`../../3-formalized/not_new_scientific_knowledge/boundary-weyl-thresholds-have-no-formal-monotonicity.md` records another scalar-shadow failure. Even when two rank-one scalar thresholds are well-defined, their relative size is not determined by the boundary points alone. The positive bulk form controls the dual energies.

Thus a scalar sign at one exterior channel cannot certify a scalar sign at another exterior channel unless a source theorem proves the comparison for the actual bulk form.

## 2026-06-24 Christoffel monotonicity requires a positive bulk

`stieltjes-bulk-exterior-christoffel-monotonicity.md` identifies the case where scalar thresholds do have a valid exterior order: positive moment bulks with support on one side of the boundary interval. The scalar comparison is then a Christoffel-kernel theorem.

For the RH route this comparison is downstream of kernel exhaustion, not a substitute for it. The positive bulk hypothesis must be proved from source data before any scalar threshold order can carry the repair sign.

## 2026-06-24 N1 anatomy does not order scalar thresholds

`../../3-formalized/not_new_scientific_knowledge/n1-signed-bulk-exterior-monotonicity-fails.md` gives an exact signed-moment counterexample: an `N_1` bulk can reverse the expected exterior repair-threshold order. Thus knowing that an unrepaired form has one negative square does not make scalar comparisons faithful across boundary points.

The scalar route still needs the source proof of kernel exhaustion and the Schur sign for the actual boundary channel.

## 2026-08-15 Lean partial formalization

`HTGeometry/FiniteRankCountertermKernelVisibility.lean` formally proves the
card's kernel-exhaustion necessity in reusable real quadratic-form form:
`finiteRankCounterterm_nonneg_on_ker` and
`finiteRankCounterterm_pos_on_ker` show that no rank-one or finite-rank boundary
repair can change an invisible kernel direction. The negative-witness corollary
is `finiteRankCounterterm_no_negative_kernel_witness`.

The card remains Stage 2 because its full complex-Hermitian scalar-shadow
equivalence needs the explicit `ker beta ⊕ Cq` transport and a positive-block
Schur theorem with the card's sign convention; the existing rank-one selector
uses a different scalar and cannot be substituted directly.

## 2026-08-15 Lean split-coordinate Schur closure

`HTGeometry/RankOneScalarShadow.lean` now closes the complex-Hermitian part
after a split coordinate system has been supplied. Its
`rankOneScalarShadowBlock_posSemidef_iff` and
`rankOneScalarShadowBlock_posDef_iff` prove exactly that a positive-definite
kernel block `B` reduces the repaired block to the nonnegative, respectively
strictly positive, scalar `a + t - ell* B⁻¹ ell`. Its principal-block lemmas
formally prove the converse kernel gate, and its literal `Fin 1 ⊕ Fin 1`
counterexample has scalar `1` but is not positive semidefinite.

This is unconditional Lean coverage of the supplied-coordinate theorem. The
card remains Stage 2: it still needs a reusable construction transporting an
arbitrary nonzero complex-linear `beta` to `ker beta ⊕ Cq`, then identifying
the original form with this block form.

## 2026-08-16 Lean closure for an arbitrary boundary functional

`HTGeometry/BoundaryKernelSchurSplit.lean` supplies the missing transport and closes the card for an
arbitrary nonzero complex-linear `beta` on a complex inner product space, with no coordinates given
in advance.

- `exists_kernelRiesz` constructs, from kernel positive definiteness alone, the vector `w in ker beta`
  with `<k, T w> = <k, T q>` for every `k in ker beta`.  It is the coordinate-free `B^{-1} l`:
  `hermitianForm_kernelRiesz_eq` proves `A w = Re <w, T q>`, the card's `l* B^{-1} l`.
- `repairedForm_split` is the congruence transport itself, an identity valid for every `v`:
  `H[v] = A[v - (beta v) . (q - w)] + ||beta v||^2 * s_beta(t)` with `s_beta(t) = a + t - A w`, and the
  first argument ranges exactly over `ker beta`.
- `repairedForm_pos_iff` and `repairedForm_nonneg_iff` are the card's equivalence
  `A|_K > 0 and s_beta(t) > 0 <=> H > 0` in both the definite and the semidefinite form.
- `hermitianForm_nonneg_on_ker` and `hermitianForm_pos_on_ker` are the necessity gate `H >= 0 => A|_K >= 0`
  in the complex-Hermitian setting.
- `shadow_scalar_not_faithful` is the card's countermodel, formalized on `C^2` with `T = -1`,
  `beta (x, y) = x` and `t = 2`: the Schur scalar is `1 > 0` while the repaired form takes the value
  `-1` on the invisible direction `e_1`.  The kernel Riesz vector there is `0` (`shadowProj`), so the
  split identity applies verbatim and the failure is exactly the missing kernel positivity.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
