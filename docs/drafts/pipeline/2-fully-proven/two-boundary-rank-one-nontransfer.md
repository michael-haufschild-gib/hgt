# Two Boundary Rank-One Nontransfer

- **ID:** two-boundary-rank-one-nontransfer
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `docs/consolidated/revision01/formulas.md` formulas 182--185,
  `zero-fed-uvarov-repair-tautology.md`, and `no-boundary-selection-of-zeta.md`
- **Statement:** The pole rank-one channel at `y=-4` and the first-trivial-zero
  Uvarov channel at `y=-4/25` are distinct finite-degree boundary functionals.
  Positivity or cancellation on one boundary kernel does not transfer to the other
  without an additional change-of-boundary theorem.

## Goal

Prevent a conflation between two useful rank-one coordinates:

1. the archimedean source split
   `H^A_d=R^A_d-4 u_{-4}u_{-4}^*`, whose negative channel is evaluation at
   the pole image `y=-4`;
2. the Uvarov/protector split
   `H^0_d=H^-_d+a_*u_*u_*^*`, whose repair channel is evaluation at the first
   trivial-zero point `y_*=-4/25`.

Both are rank-one boundary charts, but they are not the same chart.

## Theorem

Let `a` and `b` be distinct complex numbers and let

`V_d = C[y]_{<=d}`

with `d>=1`. Define evaluation functionals

`e_a(p)=p(a)`, `e_b(p)=p(b)`.

Then:

1. `e_a` and `e_b` are not scalar multiples.
2. The rank-one Hermitian forms `e_a^*e_a` and `e_b^*e_b` have different
   kernels.
3. A statement restricted to `ker e_a` gives no formal implication on `ker e_b`,
   and conversely.

In particular, for `a=-4` and `b=-4/25`, the pole channel and the first-trivial-zero
channel are algebraically distinct for every `d>=1`.

## Proof

Since `a != b` and `d>=1`, the polynomial

`p_a(y)=y-a`

belongs to `V_d` and satisfies

`e_a(p_a)=0`, while `e_b(p_a)=b-a != 0`.

Similarly,

`p_b(y)=y-b`

satisfies `e_b(p_b)=0` and `e_a(p_b)=a-b != 0`.

Thus `ker e_a` and `ker e_b` are different hyperplanes. If `e_a` and `e_b` were
scalar multiples, their kernels would agree; hence they are not scalar multiples.
The kernels of the rank-one forms `e_a^*e_a` and `e_b^*e_b` are exactly
`ker e_a` and `ker e_b`, respectively, so the rank-one forms also have different
kernels. The non-implication claim follows from the same witnesses: `p_a` kills
the `a`-boundary and is visible to the `b`-boundary, while `p_b` does the reverse.

## Consequence for the RH Route

Formula 184 gives the archimedean split

`Q_arch[p] = -4 p(-4)^2 + sum_{j>=1} (2j+1/2)^(-2) p(-(2j+1/2)^(-2))^2`.

Its rank-one negative channel is evaluation at the pole image `y=-4`. Therefore
any calculation on the pole-orthogonal slice `p(-4)=0`, or any cancellation along
the vector `u_i=(-4)^i`, controls the pole channel only.

The first-trivial-zero Uvarov chart instead uses the boundary point

`y_* = -(5/2)^(-2) = -4/25`.

The theorem shows that these boundary functionals already differ in degree one:
`p(y)=y+4` kills the pole channel but not the first-trivial-zero channel, while
`p(y)=y+4/25` kills the first-trivial-zero channel but not the pole channel.

Thus a proof may use both charts, but it must not slide between them. A valid
transfer needs an explicit change-of-boundary theorem connecting the pole-channel
Loewner budget to the first-trivial-zero Schur/Uvarov scalar. Without that theorem,
pole cancellation and first-trivial-zero repair are separate coordinates.

## Source Boundary

This theorem is elementary finite-dimensional algebra. It claims no progress on
RH. Its value is a guardrail for the source-built landscape program: rank-one
language alone does not identify which boundary is carrying the sign.

## Gates

- [x] 0 -> 1 in-progress: boundary-channel conflation isolated.
- [x] 1 -> 2 fully-proven: finite evaluation-functional proof written.
- [ ] 2 -> 3 formalized: optional; a short Lean theorem about evaluation
  functionals on degree-one polynomials would suffice.

## Log

- 2026-06-24 -- Codex: created while auditing the archimedean source split against
  the first-trivial-zero Uvarov chart. The exact finite witness is the pair of
  linear polynomials `y+4` and `y+4/25`.

## 2026-06-24 boundary threshold monotonicity is not formal

`boundary-weyl-thresholds-have-no-formal-monotonicity.md` strengthens this boundary separation from kernels to Schur thresholds. Even after a positive bulk form is chosen, the dual energies of two independent boundary functionals can be prescribed independently by changing the bulk metric.

Thus the pole channel at `y=-4` and the first-trivial-zero channel at `y=-4/25` are not ordered by their exterior locations alone. Any useful monotonicity between them must be proved from the actual source-built carrier, not from rank-one boundary algebra.
