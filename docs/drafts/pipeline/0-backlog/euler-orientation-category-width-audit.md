# Euler Orientation Category-Width Audit

- **ID:** euler-orientation-category-width-audit
- **Stage:** 0-backlog
- **Type:** route audit / source-axiom scope guardrail
- **Source:** `source-selector-repair-obligation-ledger.md`,
  `no-boundary-selection-of-zeta.md`,
  `finite-rank-one-selector-no-free-lunch.md`
- **Statement:** Euler/local-factor orientation is not automatically a
  zeta-specific repair theorem. If stated broadly, it proves a GRH-class
  theorem for every object satisfying the same source axioms. If narrowed to
  conductor-one `Q`, it selects the function but still does not prove the
  semilocal repair/index sign.

## Scope Lemma

Let `A` be a list of source axioms and let `P(F)` be the repaired semilocal
index conclusion for an object `F`, for example:

`kernel/omitted-channel exhaustion + full Schur/index sign`.

If a proof uses only the axioms `A` to prove `P(F)`, then it proves `P(F)` for
every object satisfying `A`.

Therefore an `L_src` proof has two choices:

1. State `A` broadly, using Euler products, positive local factors, completed
   functional equations, and source finite parts. Then the result is a
   broad GRH-style theorem for the whole source category covered by `A`.
2. Narrow `A` to conductor-one, trivial character, pole normalization, and the
   rank-one `Q` Gamma boundary. Then `A` may identify `zeta`, but the repair
   conclusion `P(zeta)` still has to be proved separately.

There is no third option in which a broad Euler-orientation slogan is
zeta-specific while also carrying the repair/index sign.

## Category Tests

Any proposed Euler-orientation theorem must answer these scope tests before it
is treated as progress on RH:

| Test object | If it satisfies the axioms | If it is excluded |
|---|---|---|
| primitive Dirichlet `L` | The theorem is a GRH statement for that conductor and character. | The axiom list must name the conductor/character exclusion as source data. |
| Dedekind `zeta_K` | The theorem is a GRH statement for that field. | The axiom list must name the archimedean signature or arithmetic source mismatch. |
| Davenport-Heilbronn | The axioms are too weak, because FE costume is passing without Euler/local-factor orientation. | The exclusion must be lack of positive Euler/local-factor orientation, not off-line zeros. |
| reversed-prime/sign-fake | Scalar shadows are too weak if it passes. | The exclusion must be wrong prime-source orientation, not later `kappa_-` or Hankel failure. |

## Consequence For The Repair Ledger

This audit sharpens rows A3--A7 of
`source-selector-repair-obligation-ledger.md`.

Euler/local-factor orientation can be a genuine source input only after its
category width is declared. A broad version must be prepared to prove the same
semilocal index theorem across the declared `L`-function class. A narrow version
must explain why the narrowing is source data and not a post-hoc way to avoid
category tests.

After the scope is fixed, the live repair obligation is unchanged:

`source data => kernel/omitted-channel exhaustion + full Schur/index sign`.

## Kill Conditions

Kill or downgrade an Euler-orientation proof sketch if:

1. it claims to be zeta-specific but uses only axioms shared by a larger
   `L`-function class;
2. it narrows to `zeta` by degree-one/conductor-one classification and then
   treats that as a proof of the repair sign;
3. it excludes Davenport-Heilbronn by zero locations rather than source data;
4. it excludes sign-fakes by a target positivity test rather than prime-source
   orientation;
5. it uses the words "Euler product" where the proof actually needs the full
   semilocal Schur/index theorem.

## Status

This is a scope guardrail, not an RH proof. It prevents the source route from
confusing three different claims:

1. source typing identifies a class;
2. conductor/character/boundary data identify `zeta` inside that class;
3. the semilocal repair/index theorem proves the RH-bearing sign.

Only the third claim can carry the RH content.

## Log

- 2026-06-24 -- Codex: created after the repair ledger to make the category
  width of Euler/local-factor orientation explicit.
