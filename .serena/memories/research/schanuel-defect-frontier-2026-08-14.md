# Schanuel defect frontier (2026-08-14)

Mission: unconditional Lean proof of Schanuel; active goal remains open.

## Corrected formal frontier
- Stage n=1 is unconditional Hermite–Lindemann, not open.
- Added `schanuelExtractionAt_one` to `formal/GaloisForLFunctions/RHTower/SchanuelStageWitnesses.lean`, importing `ExpAlgebraicTranscendental`.
- Source check and targeted `lake build GaloisForLFunctions.RHTower.SchanuelStageWitnesses` pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Global lint remains red only on unrelated pre-existing unreachable FieldOne/Suzuki/HTGeometry modules.
- Card: `docs/drafts/pipeline/2-fully-proven/schanuel-stage-one-hermite-lindemann.md`.

## Internal/external frontier
- First open stage is n=2.
- Even two algebraically independent logarithms of algebraic numbers remain unknown.
- Ax solves differential equation, not isolated numerical values.
- Dasgupta–Kakde MCC/fewnomial program is limited to logarithms of algebraic numbers; (w)=>(m)/(m') remains open even at 2x2/four exponentials.
- Generic powers and almost-all tuple theorems do not reach explicit/essential values.
- Kirby: essential counterexamples lie in countable `ecl^C(emptyset)`.

## New paper theorems / normal form
1. Defect lattice injection:
   For Q-LI x_i, y_i=exp x_i, K=Qbar(x,y), epsilon_i=dy_i/y_i-dx_i, the map Z^n -> Omega_{K/Qbar} is injective.
   Proof: if ds=dw/w in a finitely generated function field, pole orders force s,w constants; Hermite–Lindemann contradicts w=exp s for nonzero rational combination.
2. Algebraic-coefficient independence:
   epsilon_i are Qbar-linearly independent.
   Proof: algebraic constant relation defines invariant differential eta vanishing on locus V. Translate by Qbar point; group products stabilize at proper H with eta|H=0. Split H_a x H_m. Torus character lattice expresses coefficient vector in algebraic combination of integer characters, giving Q-LI logarithms of algebraic numbers; Baker contradicts additive algebraic coset relation.
3. Stage-two normal form:
   hypothetical counterexample has td K=1, unique epsilon_2=rho epsilon_1, rho transcendental (indeed K finite over Qbar(rho)), and rho exponentially algebraic via Kirby. For algebraic basepoint q on normalized curve:
   integral_q^p epsilon_i = X_i(q)-log Y_i(q)+2pi i k_i.
   Trace/norm loses exp under conjugation; generic-power results exclude exactly this exponentially algebraic slope.

Cards:
- `docs/drafts/pipeline/2-fully-proven/schanuel-logarithmic-differential-defect-lattice.md`
- `docs/drafts/pipeline/2-fully-proven/schanuel-defects-algebraic-coefficient-independent.md`
- `docs/drafts/pipeline/2-fully-proven/schanuel-stage-two-defect-slope-normal-form.md`
- DCD sufficient conjecture returned to backlog: `docs/drafts/pipeline/0-backlog/schanuel-defect-coefficient-descent.md`.

## Exact remaining wall
Need descent from Qbar-linear independence of defect forms to K-linear independence. On log-algebraic slice this is algebraic independence of logarithms, so valuations/formal differential arguments alone cannot close it. A stage-two counterexample is defect-saturated: Omega has K-dim 1 and annihilator of defect span is zero, so Ax cannot manufacture a nonzero exponential derivation. Any next attack must retain chosen exp branch under arithmetic specialization; trace, conjugation, tangent lifts erase it.