# Mass-shifted tied-power global-budget orientation no-go

- **ID:** `mass-shifted-tied-power-global-budget-orientation-no-go`
- **Status:** Formalized in Lean 4
- **Route:** mass-shifted spectral face, §9.3 exact open core
- **Novelty:** `[NOVELTY UNVERIFIED]`

## Conjecture attacked

Perhaps the local tied-power countermodels disappear after imposing the strongest currently useful
scalar constraints of the completed central Xi source: the exact sector and radius bounds, the
corpus interval for the zeroth moment, the first-moment upper bound, and the global transverse
orientation-energy cap.

## Exact failure

Take three copies of each four-atom cloud

\[
 Z_+=\{11,9,10+i,10-i\},\qquad
 Z_-=\{11+i,9+i,9-i,11-i\},
\]

and scale every atom by `a=1/2880`.  For

\[
 s_k^\pm=3\operatorname{Re}\sum_{z\in Z_\pm}(az)^{k+1}
\]

the visible moments agree:

\[
 s_0^\pm={1\over24},\qquad
 s_1^\pm={1\over6912},\qquad
 s_2^\pm={1\over1990656}.
\]

Hence both sources determine the same positive singular size-two Hankel face, with monic null
polynomial `P=X-1/288`.  Every atom is conjugation paired and satisfies

\[
 84^2|z|^2<85^2(\Re z)^2,\qquad 41^2|z|^2<4.
\]

The scalar completed-source budgets also hold exactly:

\[
 {1\over25}<s_0^\pm<{29\over625},\qquad
 s_1^\pm<{1\over5000},
\]

and, writing `E=3 sum (Im z)^2`,

\[
 E_+={1\over1382400}<{1\over150000},\qquad
 E_-={1\over691200}<{1\over150000}.
\]

Nevertheless the first unseen Krein crossings are

\[
 [P,XP]_+={1\over5733089280000}>0,
 \qquad
 [P,XP]_-=-{1\over1433272320000}<0.
\]

Both multiplicity-three clouds also inherit the complete complex Möbius tied-power differential
hierarchy.  All claims are exact rational identities; no numerical computation is used.

## Positive survivor

The zeroth/first trace windows and total transverse energy remain separate marginals.  Even when
combined with local atom geometry, conjugation, exact transport, and the full current singular
face, they do not encode the incidence between the completed Euler--Gamma source and the null
polynomial.  A viable sign theorem must use a mixed source/null-line law, not another scalar budget.

This is the precise useful content extracted from `docs/notes.md`: conditioning must constrain
joint realizability.  Matching more independent invariants does not recover the hidden affine
extension class.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.TiedPowerGlobalBudgetOrientationNoGo`
- Capstone: `HTGeometry.tiedPowerGlobalBudgetOrientationNoGo`
- Exact geometry, conjugation, moment, energy, singular-face, remainder, and transport theorems are
  unconditional.
- Module is wired into `GaloisForLFunctions.HTGeometry`.

## Route consequence

This does not refute completed-Xi orientation.  It refutes derivations using only the listed scalar
completed-source bounds together with already formalized local tied-power data.  Remaining open
core is strict positive orientation of first surviving factorial-Volterra rung from a genuinely
mixed Euler--Gamma incidence identity.
