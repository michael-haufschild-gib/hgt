# Pole Budget Does Not Imply Uvarov Repair

- **ID:** pole-budget-does-not-imply-uvarov-repair
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `two-boundary-rank-one-nontransfer.md`,
  `finite-rank-one-selector-no-free-lunch.md`, and formulas 182--185 in
  `docs/consolidated/revision01/formulas.md`
- **Statement:** A finite form may have exactly the pole-channel structure
  "positive bulk minus one rank-one pole boundary" and still fail every fixed
  first-trivial-zero Uvarov repair. Therefore pole-channel Loewner budget alone
  cannot imply the first-trivial-zero Schur sign.

## Goal

Strengthen the boundary nontransfer guardrail from distinct functionals to an
actual finite countermodel. The question is whether the pole-channel structure

`positive bulk - c e_{-4}^* e_{-4}`

can by itself force positivity after adding the first-trivial-zero atom

`t e_{-4/25}^* e_{-4/25}`.

It cannot.

## Theorem

Let `V` be a finite-dimensional complex vector space, and let `alpha, beta: V -> C`
be nonzero linear functionals that are not scalar multiples. Fix any `t>0`.
Then there is a Hermitian form `A` on `V` such that:

1. `A` has exactly one negative square.
2. `A` is positive definite on `ker alpha`.
3. For some `c>0`, `A` can be written as

   `A = R - c alpha^* alpha`

   with `R` positive definite.
4. The beta-repaired form

   `A + t beta^* beta`

   is not positive semidefinite.

For `V=C[y]_{<=d}`, `d>=1`, `alpha=e_{-4}`, and `beta=e_{-4/25}`, this gives a
finite pole-budget form whose pole kernel is positive but whose first-trivial-zero
repair fails.

## Proof

Because `alpha` and `beta` are not scalar multiples, `alpha` is nonzero on
`ker beta`. Choose `q in ker beta` with `alpha(q)=1`.

Since `alpha(q)=1`, every `v in V` has a unique decomposition

`v = lambda q + k`, with `k in ker alpha`.

Choose any positive definite Hermitian form `B` on `ker alpha`, and define

`A(lambda q+k) = -|lambda|^2 + B(k,k)`.

Then `A` is positive definite on `ker alpha`, and it has exactly one negative
square, represented by the `q` direction.

Moreover, in this decomposition `alpha(lambda q+k)=lambda`. For any `c>1`, set

`R = A + c alpha^* alpha`.

Then

`R(lambda q+k) = (c-1)|lambda|^2 + B(k,k)`,

so `R` is positive definite and `A=R-c alpha^*alpha`.

Since `q in ker beta`,

`(A+t beta^*beta)(q) = A(q) + t |beta(q)|^2 = -1`.

Thus the beta-repaired form is not positive semidefinite.

For the polynomial specialization, take

`q(y) = (y+4/25)/((-4)+4/25)`.

Then `q(-4/25)=0` and `q(-4)=1`, so the abstract construction applies to the
pole and first-trivial-zero evaluation functionals.

## Consequence for the RH Route

Formula 184 gives an actual archimedean pole-budget decomposition. That exact
decomposition is valuable, but the theorem shows what it cannot do by itself:
the formal structure

`positive bulk - one pole evaluation square`

does not force positivity after a different rank-one repair at `y=-4/25`.

Therefore a source-built proof cannot stop at:

1. archimedean pole channel identified;
2. pole-orthogonal budget positive;
3. Gamma atom at the first trivial zero named.

It must also prove a genuine source theorem connecting the specific zeta prime
finite part to the first-trivial-zero boundary scalar. In finite algebra, the
negative direction can be chosen invisible to the `y=-4/25` repair while remaining
fully visible to the pole channel. The zeta proof must rule out exactly that
invisible-negative-direction scenario by using more than pole-budget structure.

## Source Boundary

This is a countermodel to a proof pattern, not a statement about the actual zeta
form. It claims no RH progress. Its role is to force any pole-to-Uvarov transfer
to carry real source content: Euler/local-factor orientation, the completed
explicit formula, or another non-equivalent rigidity principle.

## Gates

- [x] 0 -> 1 in-progress: finite pole-to-Uvarov implication isolated.
- [x] 1 -> 2 fully-proven: countermodel written.
- [ ] 2 -> 3 formalized: optional finite-dimensional Hermitian form theorem.

## Log

- 2026-06-24 -- Codex: created after the two-boundary nontransfer guardrail. The
  witness polynomial is `q(y)=(y+4/25)/((-4)+4/25)`, which is invisible to the
  first-trivial-zero boundary but visible to the pole boundary.

## 2026-06-24 pole-to-Uvarov monotonicity is not formal

`boundary-weyl-thresholds-have-no-formal-monotonicity.md` adds the threshold version of this countermodel. For two independent boundary functionals, a positive bulk form can make either Schur threshold larger. Therefore pole-channel control cannot be transported to the first-trivial-zero channel by a presumed monotone boundary order.

A zeta proof may still establish a source-specific boundary monotonicity theorem, but it must use the completed explicit-formula carrier itself. The finite pole-budget form does not supply it.

## 2026-06-24 Stieltjes bulk monotonicity is conditional

`stieltjes-bulk-exterior-christoffel-monotonicity.md` gives the legitimate monotone comparison that this countermodel lacks. For a positive moment bulk supported to the right of the pole and first-trivial-zero boundary points, the Christoffel threshold at the nearer boundary point is larger.

This does not rescue pole-budget transfer by itself. It says exactly what extra theorem is needed: the relevant positive Stieltjes bulk must be source-built before the comparison is invoked.

## 2026-06-24 N1 signed moment monotonicity is insufficient

`../../3-formalized/not_new_scientific_knowledge/n1-signed-bulk-exterior-monotonicity-fails.md` gives a signed-moment version of the pole-to-Uvarov failure. Even an `N_1` moment bulk supported to the right of both `-4` and `-4/25` can reverse the repair-threshold order between those two boundary points.

Thus pole-to-Uvarov transfer cannot be rescued by saying that the unrepaired carrier has exactly one negative square. The proof still needs a source-built positivity or monotonicity theorem for the actual completed carrier.

## 2026-06-24 positive Stieltjes bulk still does not make the first atom enough

`../../3-formalized/not_new_scientific_knowledge/positive-stieltjes-pole-plus-first-atom-insufficient.md` gives the Stieltjes-bulk version with the actual pole and first-trivial-zero masses. A positive atomic bulk on `{0,1,2}` minus `4e_{-4}^*e_{-4}` has exactly one negative square, and adding `(4/25)e_{-4/25}^*e_{-4/25}` is still indefinite.

Thus the obstacle is not only arbitrary positive bulk geometry. The formal archimedean pattern `positive bulk - pole + first atom` is insufficient without the prime-source residual or another completed source theorem.
