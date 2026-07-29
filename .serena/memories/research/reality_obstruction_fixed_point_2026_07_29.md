# Reality–obstruction fixed-point frontier (2026-07-29)

Mission remains: derive/certify one source law from which quantum theory, spacetime, matter, and all four forces follow.

## New universal conjecture

Card: `docs/drafts/pipeline/1-in-progress/reality-obstruction-fixed-point-law.md`.

Headline: **There is only one possible physics: every universe is a shadow of the same unfinished law.**

Law: `R ≃ Comp_src^{+,†,∇}(Ob(R))`: reality is the unique positive differential completion of its own impossibilities. This is conjectural. Non-tautology firewall requires independently defined obstruction/completion, no dimension/signature/group/particles/constants baked in, minimal universal property, source-faithful equivalence, and a new dimensionless prediction.

Typed interpretation: left coefficient shadow = causal/gravity candidate; right coefficient shadow = quantum/gauge candidate; linking transfer = matter; source derivative-envelope growth = time. Candidate novelty is only source reconstruction + unique nonhorizontalizable fixed point + derivation of 3+1 and SM algebra/dynamics/prediction.

## Two killed bridges

1. `finite ternary presentation => differential closure` is false. Fixed 1D TRO `X_z = C P` can carry `D(z)=Gamma(z)P`; fiberwise ternary closure does not constrain parameter derivation. Card: `docs/drafts/pipeline/5-failed/finite-ternary-presentation-implies-differential-closure.md`. Positive survivor: finite derivation-invariant carrier => finite linear differential law (already Lean-proved in FiniteObservableKoopmanBoundary, FiniteLinearStateDifferentialEscape, FiniteGeneratorDifferentialEscape). Missing primitive is source-selected ternary connection.

2. Literal connection uniqueness is false. On `C` with `[x,y,z]=x conj(y) z`, every `δ_λ(z)=i λ z` is a distinct ternary derivation and is invisible to infinitesimal reciprocal square. Card: `docs/drafts/pipeline/5-failed/source-data-uniquely-determines-ternary-connection.md`. Positive survivor: compatible connections form a torsor; invisible vertical stabilizer is candidate gauge freedom. Exact Lean formalization is pending.

## Hostile parent correction

Pluta–Russo prove all TRO derivations are spatial. Connection affine spaces/gauge stabilizers and NCG curvature are prior. Connes already derives gauge transformations as a subgroup of diffeomorphisms. Baez–Schwahn (arXiv:2606.15235, June 2026) derive SM gauge group as stabilizer intersection in `H_2(C) ⊂ H_3(C) ⊂ H_3(O)`.

Corpus already formalized `same-qubit-weak-lorentz-overlap-no-go.md`: weak SU(2) acts nontrivially on the same H2(C) Lorentz corner, so internal weak and external Lorentz actions cannot be the same action. Corpus also found observable and matter SM embeddings are nonconjugate. Fixed-point program must derive two distinct coefficient actions and nonconjugate transport; “gauge = stabilizer” is not novelty.

## Exact Lean survivor

New module: `formal/GaloisForLFunctions/HTGeometry/ReciprocalSquareCharacteristicPolynomial.lean`.

Over any commutative star ring, for rectangular `D : Matrix m n R`, `card m <= card n` gives
`charpoly(Dᴴ*D) = X^(card n-card m) * charpoly(D*Dᴴ)`, and reverse for opposite dimension order. Also proved coefficient shift, forced low-coefficient vanishing, equal-dimension equality, and complex specializations.

Direct `lake env lean GaloisForLFunctions/HTGeometry/ReciprocalSquareCharacteristicPolynomial.lean` passed. Targeted `lake build GaloisForLFunctions.HTGeometry.ReciprocalSquareCharacteristicPolynomial` passed `8655/8655`. Axiom audit: exactly `[propext, Classical.choice, Quot.sound]` for all declarations. Card promoted to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/reciprocal-square-characteristic-polynomial-law.md` with `[REDISCOVERED]` status.

Module deliberately imports Mathlib only because unrelated concurrent work left upstream `EventInvolutionComplement.lean` failing. Global lint currently red due dozens of unrelated new modules unreachable from umbrellas; this module is imported by `HTGeometry.lean` and absent from failure list. Do not claim corpus-wide lint green until concurrent migration settles.

## Next exact frontier

Formalize 1D phase-derivation no-go, then classify kernel of reciprocal observation: if two source-compatible ternary connections induce identical derivatives on all calibrated reciprocal coefficient observables, is their difference necessarily a spatial stabilizer derivation? Main physics frontier remains source selection of the connection torsor and nonconjugate observable/matter transport.