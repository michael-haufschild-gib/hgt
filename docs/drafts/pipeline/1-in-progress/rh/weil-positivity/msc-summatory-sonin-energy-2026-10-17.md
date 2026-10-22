# MSC summatory source: Sonin energy comparison

Status: in progress; requested energy comparison remains unproved. Frontier map is read-only.

## Objective and scope

Prove the genuine Sonin energy comparison for the fixed arithmetic source and logarithmic tangent constructed in `SquarefreeDiscrepancyHilbertTransport` and `HedenmalmSquarefreeSummatoryConormalTransport`. Work from Lean corpus only; no web, external novelty audit, numerical experiment, added arithmetic premise, or full build.

## Plan

1. Identify the exact Sonin operator, energy, source norm, and singular graph normalization in the current corpus.
2. State and attack exact candidate comparisons. Keep conjecturing after failures; distinguish ordinary projection contractivity from the missing completed graph comparison.
3. Complete a dependency-closed paper proof before formalization. If an obstruction is proved, extract and audit its strongest positive survivor.
4. Formalize and audit targeted modules with `lake --old env lean`; inspect axioms in a temporary file, wire umbrellas, refresh index, run lint, and clean owned scratch files.

## Established inputs

- Fixed source h0=E(exp t) exp(-t/2)/(1+t)^2 and genuine clock tangent h1=-t h0 belong to L2 on the positive logarithmic ray.
- One analytic evaluation family K_s=(1+t)^2 exp(-(s-1/2)t) recovers M(s) and M'(s), Re s>1/2. The density channel reconstructs the original squarefree partition and derivative; interval readouts recover all squarefree coefficients.
- The exact MSC conormal and Xi multiplicities are preserved. No Sonin energy comparison was established by that construction.
- `GammaSewnMobiusXiWardSourceNonexpansiveNoGo` proves that the original literal-source graph has gain 1/(2|epsilon|) at the base aperture. `MobiusGammaXiSingularGraphNormalLanding` proves contraction only before inversion of the full normal factor. Neither statement automatically settles the new summatory source plane.
- `SoninCofinalGlobalEulerCarrier` already gives asymptotically isometric moving-shell transport. Repackaging that universal theorem alone would not prove the requested completed graph comparison.

## Conjecture log

1. Ordinary contractivity of a Sonin projection supplies the requested completed-source energy comparison: rejected as insufficient. It omits division by the source overlap and the graph-to-anti-causal incidence.
2. The source-derived factors in the summatory Fisher numerator cancel the singular Euler-normal gain on the fixed source/tangent plane: under investigation. The old unit-vector counterexample concerns a different source norm and cannot simply be reused.
3. Apply the already contractive inward Sonin corner and use cofinal incidence: insufficient. `SoninContractiveComplexHardyIncidence` supplies the actual norm-one corner and Gamma-scale scalar convergence in the safe Euler chamber. It does not bound the completed strict-right Ward column by the source Gram after inverse-overlap division. Replacing the original vectors by admitted summatory vectors does not supply this missing inequality.
4. Dominate the signed discrepancy by its absolute value: false as a critical contraction. `SquarefreeDiscrepancyCriticalGap.exists_uniform_absolute_gap` and `eventually_one_lt_absoluteResponse` show that discarding signs introduces a fixed positive gap and the absolute response exceeds one near the critical exponent. This is an existing exact arithmetic obstruction, not a new no-go theorem.
5. Use ordinary Fourier/Plancherel positivity in the logarithmic coordinate as the Sonin comparison: insufficient. `SoninLogCoordinateScattering` identifies the actual Sonin Fourier constraint with an involutive Mellin-scattering operator, not the ordinary logarithmic Fourier transform. The physical scattering channel must be retained.
6. Transfer through the complete CHMD graph energy identity: insufficient. `CHMDGraphDivisorPairing` retains the signed zero pairing and both polar products. `CHMDDoobSourceGraph.sourceEnergy_add_two_mass` gives sourceEnergy = graphNorm^2 - 2*sourceMass. Graph admission alone does not determine this sign. The source-domain and signed-energy identification for the squarefree pair are also not proved.

## Exact existing endpoint

The four-unit MSC Ward endpoint in `GammaSewnMobiusXiWardCofinalBoundaryLift` is

    4 G(w) - r(w) r(w)^* >= 0

for every finite packet with Re w_i>0, where G_ij=1/(w_i+conj(w_j)) and r_i=`continuedXiAntiCausalWardResponse w_i`. This is `ContinuedXiWardFourUnitBoundaryLiftLaw`, not a newly introduced receiver. The corpus already proves this endpoint equivalent to RH. That equivalence does not prove or refute the endpoint.

The squarefree Hilbert construction proves a different Gram fact: its own evaluation vectors have a positive Gram and reproduce the scalar partition and derivative. No identity or inequality identifies that Gram, after the singular quotient and complementary-channel subtraction, with the required four-unit Ward defect. A proof of ordinary projection contraction would not discharge this step.

## Open core

Construct a bridge preserving the complete signed arithmetic source that establishes the four-unit Ward defect above, or a genuinely equivalent source-derived Sonin/Weil sign. Inverse-overlap control, the complementary channel, or the desired sign cannot be supplied as assumptions. No dependency-closed proof of this bridge was obtained; no new Lean theorem or RH claim is made.

## Corpus audit

Five documented research queries were run, including deep searches for Sonin source/tangent energy, singular graph comparison, signed discrepancy positivity, and full signed Weil energy, plus lexical exploration. Completed deep requests reported complete inventories and `partial=false`, but semantic coverage was unavailable and coverage snapshots could lag the current generation. Relevant declarations and their proof bodies were read directly. Broad proposed transfers were checked against their actual hypotheses; none supplied the missing sign.

Only this research card and a cross-session memory were added for this follow-up. Existing Lean source and the frontier map were not modified. No full build, numerical experiment, external search, or new conditional receiver was used. The route is not retired.
