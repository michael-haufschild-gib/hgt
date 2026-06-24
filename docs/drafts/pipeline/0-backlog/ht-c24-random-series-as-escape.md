# Random-series almost-sure escape — random analytic functions are a.s. HT and handle-free

- **ID:** ht-c24-random-series-as-escape
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C24
- **Statement:** A random analytic function with i.i.d. continuous coefficients is HT almost surely and, more strongly, a.s. avoids every finite symbolic handle from any prechosen countable menu (difference, recurrence, transform, algebraic-functional).

## Goal
Establish **probability-one escape** from all finite handles — the measure-theoretic form of largeness. Door: independent, experiment-friendly evidence stream for "constraint, not flow".

## Door grade (hint)
**Genuinely-new flavour (measure-theoretic).** A nonzero polynomial identity cuts a measure-zero condition on random coefficients; countable menu ⇒ a.s. avoidance.

## Approach
For each fixed `P`, `{coeffs : P(f)≡0}` is a positive-codimension (measure-zero) analytic condition on the coefficient vector; countable union stays null ⇒ a.s. HT. Pin convergence + continuity hypotheses. Methods: 8 similar objects, 11 run experiments, 17 change representation.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C24; C22/C23 (topological/perturbative largeness).

## Log
- 2026-06-20 — created in 0-backlog from bucket C24.

## Professor proof attempt — Gaussian finite-jet version, 2026-06-23

[PROVED-HERE CANDIDATE; novelty not cleared]

**Theorem candidate.** Let `Ω ⊂ C` be a connected domain. Let `F` be an `O(Ω)`-valued random holomorphic function such that, for every finite set of distinct points `z_1,...,z_r ∈ Ω` and every jet order `m`, the joint jet vector

`J(F) = (j^m F(z_1),...,j^m F(z_r)) ∈ (C^{m+1})^r`

has an absolutely continuous law with respect to Lebesgue measure and full support. Then `F` is hypertranscendental over `C(z)` almost surely.

This covers nondegenerate Gaussian analytic functions whose finite jet covariance matrices are nonsingular.

**Proof.** Use the same expanded finite-support indexing as C22. After denominator clearing, every algebraic differential equation over `C(z)` is a finite `C`-linear relation among expanded differential monomials

`M(z,Y_0,...,Y_m)=z^k ∏_{i=0}^m Y_i^{α_i}`.

For each finite support `S={M_1,...,M_r}`, let `L_S` be the event that the analytic functions `M_j(z,j^m F(z))` are linearly dependent in `O(Ω)`. The algebraic-differential locus over `C(z)` is contained in the countable union of the `L_S`.

As in C22, for each support `S` there exist distinct base points `z_1,...,z_r` such that

`Δ((v_{i,l})) = det(M_j(z_i,v_{i,0},...,v_{i,m}))_{i,j}`

is a nonzero polynomial in the finite jet variables. If `F ∈ L_S`, then `Δ(J(F))=0`. Since `J(F)` has an absolutely continuous full-support law and the zero set of a nonzero polynomial has Lebesgue measure zero, `P(F∈L_S)=0`. Countability of supports gives probability zero for the union. Therefore `F` is HT over `C(z)` almost surely.

**Why this is not C22 verbatim.** C22 proves topological largeness (comeager) in `O(Ω)`. This proves measure-one escape for any holomorphic random-function law with nondegenerate finite jets. It replaces Baire nowhere-density by finite-dimensional absolute continuity.

**Theatre test / novelty risk.** The proof is short once C22 is known, and may be a routine Gaussian-polynomial-zero corollary rather than a new theorem. A quick web source check did not find the exact phrase/result for Gaussian analytic functions and differential algebraic equations, but absence from search is weak evidence. Promote only if agents agree that the finite-jet nondegeneracy formulation is a non-mechanical, consequence-bearing C24 theorem rather than the measure analogue of C22.

## 2026-06-24 Haiku promotion note -- finite-jet nondegenerate random holomorphic laws

A standalone theorem card has been created at
`../2-fully-proven/random-holomorphic-functions-are-ht-a-s.md`.

The promoted theorem: if an `O(Omega)`-valued random holomorphic function has absolutely continuous finite-jet
laws at every finite set of distinct points and every finite jet order, then it is HT over `C(z)` almost surely.
The planar Gaussian entire function satisfies the hypothesis, so it is HT over `C(z)` almost surely.

Proof mechanism: count finite expanded differential-monomial supports; for each support choose finite jet points
whose evaluation determinant is a nonzero polynomial; absolute continuity makes that determinant vanish with
probability zero; countable union kills all ADE supports.

Status: proof complete, novelty/significance audit still required. Broad genericity is source-adjacent to
van den Dries/Rubel/Malgrange, but targeted searches did not find the exact random-holomorphic almost-sure HT
statement.

## 2026-06-24 audit downgrade -- correct folklore/bridge, not new knowledge

The promoted theorem in `../2-fully-proven/random-holomorphic-functions-are-ht-a-s.md` is proof-correct under
joint finite-jet absolute continuity, but the novelty grade is downgraded to **FOLKLORE / BRIDGE**. The mechanism
is the direct countable-union-of-null-sets argument after reducing ADEs over `C(z)` to countably many finite
expanded monomial supports.

Citation hygiene: `math/0412354` was checked and does not appear to contain the claimed Baire/meagreness twin; it
is background for differential transcendence methods, not the topological genericity citation. Keep the van den
Dries/Rubel/Malgrange source risk open.

This card remains useful as an anti-theatre and largeness guardrail. It is not a significant new theorem about
HT by the project gate.
