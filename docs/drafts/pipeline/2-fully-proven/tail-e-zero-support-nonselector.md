# Tail-E Zero Support Is Not a Source Selector

- **ID:** tail-e-zero-support-nonselector
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-selector guardrail
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`;
  `shifted-reciprocal-moments-determine-divisor.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** If the protector Hankel tail `E` is represented by a finite
  signed measure `mu_E` supported on the shifted reciprocal zero support, then
  the full tail sequence is faithful to that signed measure. Therefore
  identifying `E=mu_E` is anatomy of the zero-side chart, not an independent
  source selector for RH.

## Setup

Let `X` be a compact countable subset of `C` with connected complement. In the
protector situation, think of

`X={a_*+y_rho : rho a nontrivial zero} union {a_*}`,

where `y_rho=-(rho-1/2)^(-2)` and `a_*=4/25`. The point `a_*` is the hard-edge
accumulation point.

Let `mu` be a finite complex measure supported on `X`, and define its moments

`e_n(mu)=int_X x^n dmu(x)`, `n>=0`.

A Hankel tail attached to `mu` is the infinite matrix

`E_mu=(e_{i+j}(mu))_{i,j>=0}`.

The real signed case is included by viewing signed measures as complex
measures. If the support is real, the same proof may use Stone-Weierstrass in
place of Mergelyan.

## Theorem

Let `mu` and `nu` be finite complex measures supported on `X`. If

`e_n(mu)=e_n(nu)` for every `n>=0`,

then `mu=nu`.

Consequently, the all-order Hankel tail `E_mu` determines `mu`.

## Proof

Set `eta=mu-nu`. The moment hypothesis gives

`int_X x^n d eta(x)=0`

for every `n>=0`, hence

`int_X p(x) d eta(x)=0`

for every polynomial `p`.

Because `X` is compact and `C \ X` is connected, Mergelyan's theorem gives
uniform density of polynomials in `C(X)`. Since `eta` is finite, the functional

`f |-> int_X f d eta`

is continuous on `C(X)`. It vanishes on the dense subspace of polynomial
restrictions, so it vanishes on all of `C(X)`. By the Riesz representation
theorem, `eta=0`.

Thus `mu=nu`. The Hankel tail determines every moment because `e_n=E_{0n}`.
Therefore the all-order tail determines the representing measure.

## Application To The Protector Tail

The bridge-theorem consolidation records three facts about the protector split:

1. `E` is Hankel: `E_{ij}=e_{i+j}`.
2. `E=mu_E`, conditional on the source-defined Jacobi part in the
   finite-part construction.
3. Computations demote `mu_E` to the seam Hankel shadow of the Krein signed
   measure `sigma=nu'-a_* delta_{y_*}`; Davenport-Heilbronn shares the tail
   behavior, while the gate is the repair sign/index.

The theorem above explains why that demotion is forced. Once the support is the
shifted reciprocal zero support and the all-order Hankel tail is known, the tail
has recovered the signed measure in that zero-side coordinate. It is a faithful
chart of the measure, not a softer source condition.

So there are two legitimate uses of `E`:

1. **Finite-part anatomy.** Prove that a source-defined seam finite part has a
   Hankel boundary tail and identify it with `mu_E`.
2. **Coordinate transfer.** Use `E` after an independent source theorem has
   already built the carrier and proved the repair/index sign.

The illegitimate use is:

`E has the right shifted-zero support or all-order moments; therefore the source
landscape selected RH.`

That step has merely moved into a faithful zero-side chart. The missing theorem
remains the source-built boundary/index inequality.

## Consequence For The RH Route

The tail route fails the theatre test if it stops at `E=mu_E`.

The reason is not numerical weakness. The reason is logical type: `E=mu_E`
identifies a representation of the signed zero-side measure. A landscape proof
must instead show that Euler/Gamma/functional-equation source data force the
completed boundary repair before reciprocal-zero positivity or support
localization is read.

Equivalently, a proof using the tail must still discharge rows A6--A7 of
`source-selector-repair-obligation-ledger.md`:

`source data => kernel/channel exhaustion + full Schur/index sign`.

The protector tail may be part of that carrier, but it is not the selector.

## Theatre Test

For any proposed proof through `E` or `mu_E`, ask:

1. Is `mu_E` constructed from source data before the zero support is used?
2. Does the argument prove the boundary/index sign, or only identify the tail?
3. Which fake family is rejected before evaluating `kappa_-`, `s_d`, or the
   Hankel cone?
4. If a warm prompt asking for `E=mu_E` recovers the same route, what remains
   beyond the known finite-part anatomy?

If the answer to `2` is "only identify the tail", the proof has not moved the
RH wall.

## Source Boundary

This card uses compact moment determinacy only. It proves no positivity for
zeta and no zero localization. Its role is to prevent the protector tail from
being promoted from source anatomy to a source selector.

## Gates

- [x] 0 -> 1 in-progress: `tail-E` selected by entropy and audited against the
  bridge consolidation.
- [x] 1 -> 2 fully-proven: measure-determinacy proof written and applied to the
  protector Hankel tail.
- [ ] 2 -> 3 formalized: optional compact-moment determinacy wrapper.

## Log

- 2026-06-24 -- Codex: created under the private anti-theatre pass after the
  `tail-E` entropy selection. The result records that the tail is a
  zero-faithful signed-measure chart, not an independent RH proof mechanism.
