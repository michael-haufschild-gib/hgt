# Prime/Gamma wall--Xi Gamma-six correction clock

- **ID:** route-p-prime-gamma-wall-xi-gamma-six-correction-clock
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PROVED HERE]` `[NOVELTY UNVERIFIED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]`
- **Source:** prime/Gamma wall Fredholm coherence, theta-cusp prime--archimedean moments, and opposite Gamma-six cyclic Stokes boundaries
- **Statement:** On every aperture `d ≥ 1`, one unique positive Gamma-six source clock makes opposite-boundary curvature equal the complete quadratic Malgrange correction and yields an entire correction log giving wall/Xi contact through order two.

## Goal

Construct required positive even correction from independent source-horizontal irregular Stokes data, rather than merely infer its necessity from Xi/wall mismatch. This closes quadratic landing only; full Fredholm coefficient law and divisor control remain open.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, corpus and literature audit
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted Lean check and new-declaration axiom audit
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact candidate

Put

`c_Xi = normalizedPrimeArchMoment(0)/2`,

`P_Xi = normalizedPrimeArchMoment(1)/normalizedPrimeArchMoment(0)^2`,

`G_d = P_wall(d) - P_Xi`, and

`κ_d = c_Xi sqrt(G_d)`.

For `d ≥ 1`, `P_wall(d)` is real and `G_d>0`. Let

`E_d(t) = sourceHorizontalGammaSixUnitOppositeBoundaryCurvature(κ_d t)`.

Then `κ_d>0`, `E_d(0)=0`, `E_d'(0)=0`, and

`E_d''(0) = A_d''(0) = 2 c_Xi^2 G_d`,

where `A_d` is the first-jet-normalized wall--Xi Malgrange correction log. Moreover, `κ_d` is the unique positive real clock with this second jet.

Its canonical complexification

`H_d(z)=2(cosh(κ_d z)-1)`

is entire and has jets `(0,0,2κ_d²)`. Therefore

`log D_d(c_Xi z)+H_d(z)`

and `canonicalXiSeamLog(z)` agree at orders zero, one, and two.

## Approach

1. Use `P_wall(d)=coherence(d)/2` to eliminate complex-phase ambiguity.
2. Use explicit source inequalities `P_Xi<9/80<P_wall(d)` for `d≥1`.
3. Apply exact Gamma-six opposite-boundary law `2(cosh a-1)`; its first jet vanishes and second jet is `2`.
4. Scale by `κ_d`; `Real.sq_sqrt` gives exact quadratic match.
5. Prove positive-clock uniqueness from equality of squares.

## Hostile audit

- **Jet parity/order:** cubic negative renormalized current is third-order and cannot supply this even second jet. Rejected as direct landing.
- **Complex phase:** for `d>0`, wall projective jet is exactly a real coherence expectation divided by two. No imaginary remainder survives.
- **Circularity:** `normalizedPrimeArchMoment 0,1` have explicit theta-cusp source formulas; wall coherence is prime/Gamma source data. No Xi zero or RH premise enters.
- **Gauge:** first jet already fixes scalar time normalization; Gamma-six energy is zero and first-order flat at neutral character.
- **Tautology risk:** clock is not an arbitrary fitted complex coefficient. It is the unique positive real clock in the fixed unit Gamma-six opposite-boundary source model. This establishes quadratic incidence, not full tau equality.

## Literature audit

- Bertola constructs locally analytic Malgrange/Fredholm tau sections and explains line-bundle gauge freedom: <https://arxiv.org/abs/1703.00046>.
- Bertola derives monodromy/Stokes-parameter variational formulas; corrigendum noted: <https://arxiv.org/abs/0902.4716>, <https://arxiv.org/abs/1601.04790>.
- Desiraju gives a six-ray irregular Painleve-II Fredholm tau depending on Stokes parameters: <https://arxiv.org/abs/2008.01142>.
- Its--Lisovyy--Prokhorov treat extended monodromy data and connection constants: <https://arxiv.org/abs/1604.03082>.
- Audit found no prime/Gamma arithmetic clock, completed-Xi landing, or this paired-curvature identity. Absence is an audit inference, not a priority claim.

## Dependency-closed paper proof

Fix `d≥1`. Existing cold-wall separation gives

`P_Xi < 9/80 < Re P_wall(d)`.

For positive aperture, exact Fredholm coefficient evaluation gives

`P_wall(d) = coherence(d)/2`,

so `P_wall(d)` is real. Hence `G_d=P_wall(d)-P_Xi>0`. Since `c_Xi>0`, `κ_d=c_Xi sqrt(G_d)>0` and

`κ_d^2 = c_Xi^2 G_d`.

The first-jet-normalized Malgrange correction theorem gives

`A_d''(0)=2 c_Xi^2 G_d=2κ_d^2`.

The fixed Gamma-six opposite-boundary source law is

`E_d(t)=2(cosh(κ_d t)-1)`.

Direct differentiation yields `E_d(0)=0`, `E_d'(0)=0`, and `E_d''(0)=2κ_d^2`. Therefore `E_d''(0)=A_d''(0)` as a complex value; reality above rules out an omitted phase component.

If another positive clock `λ` has the same Gamma-six second jet, then `2λ^2=2κ_d^2`. Thus `(λ-κ_d)(λ+κ_d)=0`. Positivity excludes `λ+κ_d=0`, so `λ=κ_d`. ∎

Finally, complexify the fixed boundary law as `H_d(z)=2(cosh(κ_d z)-1)`. Entire differentiation gives `H_d(0)=H_d'(0)=0` and `H_d''(0)=2κ_d²=A_d''(0)`. Since `A_d=canonicalXiSeamLog-log D_d(c_Xi·)` and `A_d'(0)=0`, adding `H_d` to the wall log gives exact Xi contact at orders zero, one, and two. No logarithm product identity or branch extension is required. ∎

## Formal certificate

- **Module:** `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock.lean`
- **Exact landing:** `iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_eq_gammaSixCorrectionEnergy_secondJet`
- **Positive-clock uniqueness:** `routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock_eq_of_pos_of_secondJet_eq`
- **Capstone:** `routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionQuadraticLanding`
- **Analytic correction:** `routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog`
- **Two-jet contact:** `routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_twoJetContact`
- **Verification:** direct module check passed. All seventeen public theorems created by this module depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- **Lint:** module is reachable and clean. Repository lint remains nonzero only for unrelated reachability failures.
- **Remaining open core:** construct coefficient-faithful higher even Gamma-six/Stokes corrections and prove their full Fredholm series equals the wall--Xi correction germ; quadratic landing alone does not control Malgrange divisor.

## Log

- 2026-08-25 — direct cubic-current identification rejected by jet order and sign.
- 2026-08-25 — exact Gamma-six correction-clock candidate formed; internal source and external literature audits completed.
- 2026-08-25 — promoted to 2-fully-proven after reality, positivity, source-purity, gauge, and uniqueness audits closed.
- 2026-08-25 — promoted to 3-formalized after targeted Lean verification and seven-declaration axiom audit.
- 2026-08-25 — entire Gamma-six correction log formalized; corrected wall/Xi logarithmic tau germs now have exact contact through order two. Ten new declarations axiom-audited without rechecking prior seven.
