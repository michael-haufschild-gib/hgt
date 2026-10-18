# Divisor-six stability and the next successor gap

- **ID:** bvi-six-mode-stability-and-quarter-gap-2026-10-18
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** Variance away from divisor six is at most twice the defect in half-decorrelation; deleting the six-mode improves the sharp upper covariance ratio to one quarter.

## Motivation

The exact covariance cone shows that unrestricted universal quadratic improvements are
impossible. The next question is which arithmetic restriction genuinely strengthens the
inequality. The field guide singles out divisor six, but its existing inequality theorem
does not establish the complete equality classification or a quantitative stability estimate.

## Corpus evidence

- `SuccessorEnergyRigidityAndParityStability` classifies the negative endpoint and proves
  its stability, but does not classify the positive half-decorrelation endpoint.
- `ExactSuccessorMomentRegionAndUniversalInequalities` provides symbolic coordinate
  realization and proves that unrestricted improvements cannot hold.
- Corpus search locates `GaloisForLFunctions.HTGeometry.totient_le_two_iff` in
  `HTGeometry/CrystallographicRestriction.lean`: positive integers with totient at most two
  are exactly `1,2,3,4,6`.
- Renew the search before implementation; source-only discoveries require Lean verification.

## Candidate mechanism

For `e≥2`, `e≠6`, conjecture

`φ(e) ≤ 2(φ(e)-2μ(e))`.

Outside `1,2,3,4,6`, evenness and the crystallographic classification give `φ(e)≥4`;
then `μ(e)≤1` suffices. At `2,3,4`, the Möbius value is nonpositive.
Thus, writing `V=Σ_{e≥2}φ(e)Y(e)²` and `C=Σ_{e≥2}μ(e)Y(e)²`,

`Σ_{e≥2,e≠6}φ(e)Y(e)² ≤ 2(V-2C)`.

Consequences to prove and audit:

1. Half-decorrelation equality iff every nonconstant coordinate except `Y(6)` vanishes.
2. A quantitative distance estimate to the divisor-six extremizer space.
3. If `Y(6)=0`, then `4C≤V`.
4. The quarter bound and stability constant are sharp: the pure divisor-ten mode has
   `φ(10)=4`, `μ(10)=1`, hence `V=4t²`, `C=t²`.

Use the existing symbolic finite inverse for witnesses, not numerical enumeration.
Do not count the already advertised uniqueness claim alone as a new contribution;
the target is the stronger stable classification and sharp next gap.

## Gates

- [ ] Renew prior-research and dependency audit.
- [ ] Complete paper proof and endpoint witnesses.
- [ ] Unconditional Lean capstones, named-module check, axiom audit.
- [ ] Wiring, index refresh, lint, contribution assessment.

Not counted toward the 250-contribution goal.
