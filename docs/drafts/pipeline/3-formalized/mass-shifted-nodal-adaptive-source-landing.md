# Mass-shifted nodal adaptive source landing

- **Status:** FORMALISED IN LEAN 4
- **Route:** mass-shifted spectral face / Route U
- **Target:** source-first arithmetic producer
- **Opened:** 2026-08-12

## Conjecture under attack

For a real polynomial amplitude `p` and shifted-Xi moment functional `L_y`, put

\[
 A=L_y(p^2),\qquad B=L_y(pXp),\qquad
 Q_{y,p}=A\,Xp-Bp.
\]

Then `Q_{y,p}` is the division-free degree-one admission of the `p²`-reweighted source:

\[
 L_y(pQ_{y,p})=0,
 \qquad
 L_y(pXQ_{y,p})=A L_y((Xp)^2)-B^2.
\]

At `y=w²`, `w>1/2`, the second identity is the base-one completed mixed-amplitude aggregate.
Its frozen-admission derivative is minus the literal rational--Gamma-minus--von-Mangoldt
bilinear source selected from `(p,Q_{y,p})` before reflection aggregation. For nodal amplitudes
`p=X^m prod_(r in R)(X-r)`, nonnegativity of these landings is equivalent to RH.

## Hostile checks

- Not a fixed reporter: `Q_{y,p}` depends nonlinearly on source moments and on admitted `p`.
- Not an orientation map: target theorem identifies completed arithmetic formation and derivative.
- No sign is manufactured: RH remains equivalent to, not proved by, landing nonnegativity.
- Existing general bilinear source module supplies arithmetic connector but does not state this
  adaptive degree-one admission, its exact Turan landing, or nodal RH reduction.

## Required Lean closure

1. Define division-free adaptive successor from corpus moment primitives.
2. Prove orthogonality and exact mixed Turan landing.
3. Prove completed aggregate and literal arithmetic source identities.
4. Bridge resolvent `xiPolyMoment` to shifted real moment functional.
5. Prove nodal landing criterion equivalent to RH.
6. Wire umbrella; direct Lean, axiom, lint, and targeted module-build audits.

## Paper proof

Write `C=L_y((Xp)^2)`. Bilinearity gives

\[
 L_y(pQ)=A B-B A=0,
 \qquad
 L_y(pXQ)=A C-B^2.
\]

Expanding the successor energy gives

\[
 L_y(Q^2)=A(A C-B^2).
\]

The generic bounded atomic-source bridge identifies

\[
 \bigl(L_y(X^kp^2):\mathbb C\bigr)=\operatorname{xiPolyMoment}(p,k,y).
\]

For the coefficient packet of `pQ`, the base-one completed aggregate is `L_y(pXQ)`.
At `y=w²`, completed-source formation splits it before reflection aggregation into the
rational--Gamma continuum formation minus the von-Mangoldt labelwise formation, using one common
adaptive radial kernel.

For actual moving admission define source rates `S_A=-A'`, `S_B=-B'`, `S_C=-C'`.
Bilinear source expansion and product differentiation give

\[
 \mathcal A_{\rm bil}(p,Q)=A S_C-BS_B,
 \qquad
 D'=-(\mathcal A_{\rm bil}+S_AC-S_BB).
\]

Thus exact admission connection is retained.

New nodal descent gives

\[
 RH\iff \forall R,m,\ \mathcal L_w^\sharp
   \left(X^m\prod_{r\in R}(X-r)\right)\ge0.
\]

New rational-node density reduces this to countable family indexed by
`(j,m,c : Fin j → ℚ)`.

## Novelty audit

- Corpus search found general diagonal and bilinear completed-source connectors, nodal resolvent
  descent, and rational-node density, but no source-selected degree-one successor, exact Turan
  mixed landing, moving connection law, or arithmetic nodal RH criterion.
- This is project-level new synthesis. External priority remains unverified.
- No sign is inferred from equivalence. Remaining theorem is cumulative covariant source sign or
  its forced collision with existing hard-boundary alternatives.

## Lean status

Module:
`RHTower.XiShiftedNodalAdaptiveArithmeticSourceLanding`.

Direct `lake env lean` passes. Umbrella import added. Targeted module build passes
(`12122` cached/transitive jobs). Axiom audit of ten capstones reports only `propext`,
`Classical.choice`, and `Quot.sound`. Placeholder scan and `git diff --check` pass.

Repository-wide `scripts/formal_tools.py lint` currently fails only on concurrently added,
unrelated unreachable Bourgain/Sieve/HTGeometry modules; it does not report this module. New
module itself is umbrella-wired and placeholder-free.

## Log

- 2026-08-12 — conjectured source-selected division-free successor and proved paper identities.
- 2026-08-12 — hostile audit retained moving-admission connection rather than freezing it.
- 2026-08-12 — combined nodal and rational-node descent with literal completed arithmetic landing.
- 2026-08-12 — formalized all capstones, wired umbrella, passed direct Lean, targeted build, axiom,
  placeholder, and diff audits.
