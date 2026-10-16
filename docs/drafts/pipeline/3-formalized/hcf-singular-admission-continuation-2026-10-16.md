# HCF: continuation through singular admission coordinates

Status: formalized and audited, 2026-10-16.

## Corpus starting point

Actual heat normal blocks, all-time inertia/census, Toda identities and exact contact orders are already formalized. The complete prime–Gamma source sign remains open. New work must not restate these results, add a receiver, or improve a bound.

## Conjecture loop

1. Test universal simple crossing or monotone finite-section inertia. The available heat-moment differential structure does not justify either claim: the exact normal-block orders allow higher contacts. Do not assume transversality.
2. Investigate whether canonical monic admission polynomials have a removable projective singularity at every positive heat time, with an explicitly determined limiting polynomial and exact denominator cancellation. This would replace coordinates that divide by vanishing Hankel determinants with a canonical continuation.

## Dependency-closed proof under formalization

For a normal block with regular heads n and n+d, write P_N(t) for canonical monic admission. The proposed exact law is

`(t-a)^k P_(n+k)(t) -> (d-1).descFactorial k * P_n(a)` for `0 <= k < d`, with coefficientwise analytic continuation.

1. Every coefficient is meromorphic: Cramer's rule expresses it as a quotient of analytic moment determinants.
2. Differentiating orthogonality and using the heat moment recursion leaves only the previous admission direction. The subleading coefficient equals `logDeriv Delta_N` by the terminal-border determinant derivative. Thus `P_N' = (logDeriv Delta_N)' P_(N-1)` wherever adjacent heads are regular.
3. The existing exact multiplicity `M_k=k(d-k)` makes the cancelled connection coefficient `(t-a)^2 (logDeriv Delta_(n+k))'` analytic with value `-M_k`.
4. A meromorphic primitive of a function whose `(k+1)`-scaled germ extends analytically has a k-scaled analytic extension. Its value is minus the derivative's cancelled value divided by k. This statement includes zero coefficient values.
5. Inducting through the block gives `C_k=(d-k) C_(k-1)` and hence `C_k=(d-1).descFactorial k`. At coefficient n, the limiting value is nonzero, establishing exact polynomial pole order and a unique projective limit, not merely an upper bound.

Actual-source capstone discharges analyticity, isolated regularity, block existence and multiplicity from the HCF corpus. No positivity or transversality premise remains.

## Structural result

Conjecture 2 succeeds. Static normal-block geometry allowed a whole kernel `P_n q`, potentially of dimension greater than one. The moving heat admission selects the specific line `P_n`, with the explicit falling-factorial multiplier above. This identifies the direction approached at simultaneous singularities and replaces undefined monic transport coordinates with an analytic nonzero projective chart.

Lean forced a stronger scalar ingredient: antidifferentiation must preserve analytic cancellation even when the cancelled coefficient is zero. `scaledAnalyticGerm_of_deriv` proves this, so no coordinate genericity is hidden in the polynomial theorem. Monicity then certifies exact pole order using the coefficient at degree n.

New modules:
- `HTGeometry/HankelHeatAdmissionFlow.lean`: Cramer analyticity, subleading logarithmic derivative and forced admission direction.
- `HTGeometry/MeromorphicPolePrimitive.lean`: analytic pole cancellation, including zero leading coordinates, exact-order detection and logarithmic-derivative residues.
- `RHTower/XiGaussianHeatAdmissionContinuation.lean`: actual heat connection, exact block continuation, exact pole and analytic nonzero projective extension.

The complete prime–Gamma source sign and the no-transition selection remain open. No RH equivalence or positivity receiver was added.

## Verification

- All three focused `lake --old build +Module:olean` builds passed. Unchanged dependencies were replayed, not rebuilt.
- Final direct `lake env lean` audits passed without output or warnings for all three new source modules.
- Mathlib API-name scratch audit passed.
- Ten `#print axioms` checks, including all actual capstones, returned only `[propext, Classical.choice, Quot.sound]`.
- Both theorem-area umbrellas import the new modules; no umbrella or full build was run.
- Global `scripts/formal_tools.py lint` failed only on 11 unrelated modules missing from their umbrellas: `CHMDComplexJumpGraph`, `CHMDComplexWeilForm`, `HerglotzRieszUnsymmetrized`, `PaperThetaArithmeticHolomorphy`, `PaperThetaArithmeticWeilCalculus`, `PaperThetaUniformCutControl`, `CanonicalProductSubquadraticType`, `CauchySlopeRemainder`, `EvenHermitianAxisMultiplicity`, `EvenHermitianCanonicalFactor`, `EvenHermitianSpectralFactor`. No errors referenced the three new modules.
- No numerical experiments, admitted proofs, added axioms, heartbeat increases, commits or pushes.
- Owned search results, build/lint logs and Lean audit scratch files were removed. No owned build or search process remains.

## Constraints

Use current Lean corpus and documented search only. No web, old research markdown, numerical experiments, added axioms or heartbeat changes. Actual capstone must take only intrinsic time/rank inputs. Foreground focused builds; final direct Lean audits, axiom audit, umbrella wiring, lint and owned-scratch cleanup.
