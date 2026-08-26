# BM partner discriminant and radiation-faithfulness no-go (2026-08-26)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPartnerPoleDiscriminant.lean`, imported by `RHTower.lean`.

Proved:
- Exact first variation of squared FE–Schwarz BM pole separation: `D'(0)=2[-i(Re rho-1/2)](v_FE-v_S)`.
- At critical-line coincidence, `D'(0)=0`.
- Stronger punctured quadratic law: `D(c)/c^2 -> (v_FE-v_S)^2`; unequal velocities force quadratic exceptional-point opening.
- Symmetry-compatible all-order higher response gives reflected/conjugated critical copies one common analytic pole germ.
- Any injective full radiation record keeps off-line FE–Schwarz partner outputs distinct; collapse of an off-line pair forces radiation-map noninjectivity.

Conjecture loop failures:
1. Exceptional-point collision does not annihilate resonances; it preserves contour multiplicity.
2. Uniform global contour coercivity is not supplied by arbitrary analytic higher response and is undermined by QNM pseudospectral migration.
3. Same-sign Krein protection fails: FE–Schwarz partners have opposite signatures, the collision-permitted class.
4. Optical positivity does not fix raw discriminant direction because Jost/temporal phase remains free.

Interpretation: deterministic symmetry-faithful local Einstein–Teukolsky dynamics cannot select RH by erasing off-line BM sectors. Faithful radiation preserves resolved bad doublets; collapsing them necessarily loses information into an invisible/orthogonal channel. Remaining physical core is an actual nonlinear radiation/admission theorem deciding whether horizon projection is injective on FE–Schwarz orbits or quantifying its orthogonal-helicity kernel. Either result must be derived from gauge-fixed Einstein–Teukolsky dynamics, not generic KMS/passivity.

Verification: target Lean compile passed. `#print axioms` for all new declarations gives only `[propext, Classical.choice, Quot.sound]`. Global `formal_tools.py lint` found only unrelated pre-existing/concurrent umbrella reachability failures; new module is reachable. No git/docs/ledger edits. Scratch files removed.