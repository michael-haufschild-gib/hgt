# Boundary Weyl Thresholds Have No Formal Monotonicity

- **ID:** boundary-weyl-thresholds-have-no-formal-monotonicity
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `two-boundary-rank-one-nontransfer.md`;
  `pole-budget-does-not-imply-uvarov-repair.md`;
  `rank-one-scalar-shadow-needs-kernel-exhaustion.md`;
  entropy move `monotone`
- **Statement:** Distinct rank-one boundary functionals have no formal Weyl
  threshold order. A positive bulk form can make either boundary channel cheaper
  or more expensive to repair. Therefore pole-to-first-trivial-zero monotonicity
  is not available without an additional source theorem.

## Setup

Let `V` be a finite-dimensional complex vector space. Let

`alpha,beta:V -> C`

be two nonzero linear functionals that are not scalar multiples. For a positive
definite Hermitian form `B` on `V`, write

`E_B(alpha)=alpha B^{-1} alpha^*`

for the dual energy of the boundary functional. The rank-one form

`B - t alpha^* alpha`

is positive semidefinite exactly when

`t <= 1/E_B(alpha)`.

Thus `tau_B(alpha)=1/E_B(alpha)` is the Schur/Weyl threshold at `alpha`.

## Theorem

For any positive numbers `r_alpha` and `r_beta`, there exists a positive
definite Hermitian form `B` on `V` such that

`E_B(alpha)=r_alpha`

and

`E_B(beta)=r_beta`.

Consequently, for the two Weyl thresholds

`tau_B(alpha)=1/r_alpha`, `tau_B(beta)=1/r_beta`,

there is no formal inequality in either direction. The threshold at `beta` can
be smaller than, equal to, or larger than the threshold at `alpha`.

## Proof

Since `alpha` and `beta` are not scalar multiples, they are linearly independent
in `V^*`. Extend them to a basis

`alpha, beta, eta_3, ..., eta_n`

of `V^*`.

Define a positive definite Hermitian form `G` on `V^*` by declaring this basis
orthogonal and setting

`G(alpha,alpha)=r_alpha`,

`G(beta,beta)=r_beta`,

and

`G(eta_j,eta_j)=1`

for every remaining basis vector.

Every positive definite Hermitian form `G` on `V^*` is the inverse dual form of
a unique positive definite Hermitian form `B` on `V`. For this `B`,

`E_B(alpha)=G(alpha,alpha)=r_alpha`

and

`E_B(beta)=G(beta,beta)=r_beta`.

The Schur-complement threshold claim follows from the standard rank-one
criterion:

`B - t alpha^* alpha >= 0`

if and only if

`1 - t alpha B^{-1} alpha^* >= 0`,

which is exactly `t <= 1/E_B(alpha)`.

## Polynomial Boundary Specialization

Take

`V=C[y]_{<=1}`,

`alpha=e_{-4}`,

and

`beta=e_{-4/25}`.

These functionals are independent by `two-boundary-rank-one-nontransfer.md`.
The theorem therefore applies to the pole boundary and the first-trivial-zero
boundary already in degree one.

For example, choosing

`r_alpha=1`, `r_beta=100`

makes the first-trivial-zero threshold one hundred times smaller than the pole
threshold. Choosing

`r_alpha=100`, `r_beta=1`

reverses the comparison. Both choices come from positive definite bulk forms.

## Consequence For The RH Route

A monotone pole-to-Uvarov proof would try to argue:

1. the pole channel at `y=-4` is controlled;
2. the first-trivial-zero channel at `y_*=-4/25` lies between the pole and the
   hard edge in a preferred order;
3. the Weyl threshold therefore moves in the useful direction.

The theorem shows that step 3 has no formal content. Boundary location alone
does not order the Schur threshold. The order is a property of the source-built
bulk form, not of the two exterior points.

Thus a source proof may still prove a true monotonicity statement for the actual
completed explicit-formula carrier. But that statement must use zeta-specific
source structure: Euler/local-factor orientation, Gamma normalization,
functional-equation coupling, or a completed semilocal index theorem. It cannot
come from rank-one Weyl algebra alone.

## Theatre Test

For any proof that transports sign from one exterior boundary point to another:

1. Which positive bulk form defines the dual energies?
2. What source theorem proves the claimed ordering of
   `E_B(e_a)` and `E_B(e_b)`?
3. Is the ordering still true after replacing the bulk form by another positive
   form with the same rank-one boundary vocabulary?
4. If not, the argument is a source theorem only if it names the zeta-specific
   structure preventing the countermodel above.

## Source Boundary

This theorem is finite-dimensional linear algebra; the real symmetric variant
is the same argument with real dual forms. It proves no positivity for zeta and
no zero localization. Its role is to prevent boundary monotonicity language
from replacing the missing source-built Schur/index theorem.

## Gates

- [x] 0 -> 1 in-progress: monotone pole-to-Uvarov shortcut isolated.
- [x] 1 -> 2 fully-proven: dual-energy prescription proves threshold
  non-ordering.
- [x] 2 -> 3 formalized: `RHTower/BoundaryWeylThresholdNonMonotone.lean`.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after entropy
  selected `monotone`. The card blocks the move from pole-channel control to
  first-trivial-zero repair by a presumed boundary-threshold order.

## 2026-06-24 Stieltjes bulk restores a conditional monotonicity

`stieltjes-bulk-exterior-christoffel-monotonicity.md` records the positive case excluded from this countermodel. If the bulk form is a positive moment form whose support lies to one side of the compared exterior boundary points, then the Christoffel kernel diagonal is monotone on the exterior interval.

Thus the correct split is: arbitrary positive bulk forms have no boundary-threshold order, while source-built Stieltjes bulks do. The latter helps only after the source proof has already built the positive bulk.

## 2026-06-24 signed moment N1 counterexample

`../../3-formalized/not_new_scientific_knowledge/n1-signed-bulk-exterior-monotonicity-fails.md` strengthens the nonmonotonicity warning inside the moment category. Even a one-negative-square signed moment form with support to the right of the compared exterior points can reverse the pole-to-first-trivial-zero threshold order.

Therefore the missing source theorem cannot be weakened from positive Stieltjes bulk to `N_1` anatomy. The `N_1` signature must be accompanied by kernel exhaustion or a source-specific monotonicity theorem.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/BoundaryWeylThresholdNonMonotone.lean`
(namespace `RHTower`), wired into the `GaloisForLFunctions.RHTower` umbrella.

| Paper statement | Lean declaration |
|---|---|
| the basis-extension step (a vector normalized for one functional and killed by the other) | `exists_dual_vector` |
| the realizing positive definite bulk form | `boundaryBulkForm`, `boundaryBulkForm_nonneg`, `boundaryBulkForm_pos` |
| `E_B(alpha) = r_alpha`, `E_B(beta) = r_beta` | `boundaryBulkForm_at_u`, `boundaryBulkForm_at_w` |
| the rank-one Schur criterion `B - t alpha^* alpha >= 0 <=> t <= 1/E_B(alpha)` | `boundaryThreshold_alpha`, `boundaryThreshold_beta` |
| the full non-ordering theorem | `boundaryWeylThreshold_not_monotone` |

The dual energy is carried in its variational form: `B - t alpha^* alpha >= 0` is the pointwise
inequality `t ||alpha v||^2 <= B v`, and the theorems say exactly that this holds iff
`t <= 1/r_alpha` (resp. `1/r_beta`). Since `r_alpha` and `r_beta` are arbitrary positive reals,
either threshold can be the smaller one — for instance `(r_alpha, r_beta) = (1, 100)` and
`(100, 1)` — which is the card's conclusion.

The card's basis extension `alpha, beta, eta_3, ...` is realized by the two dual vectors `u`, `w`
and the residual projection `v - alpha(v) u - beta(v) w`; `exists_dual_vector` supplies them from
the non-proportionality hypothesis.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
