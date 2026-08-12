# Mass-shifted nodal adaptive source landing

- **Status:** IN PROGRESS
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
