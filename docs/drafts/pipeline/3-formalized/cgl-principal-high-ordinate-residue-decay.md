# CGL principal high-ordinate residue decay

- **ID:** cgl-principal-high-ordinate-residue-decay
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Chen--Gupta--Li, arXiv:2507.08296v2, Section 12.1, equation (12.1)
- **Statement:** The principal zero-detector residue is bounded uniformly in conductor and strip abscissa by `(X+1) C |t|^N exp (-pi |t| / 2)`, hence is below every fixed threshold at sufficiently large ordinate.

## Goal
Close the high-ordinate half of CGL's sole principal Mellin-residue obligation with no RH, zero-density, or caller-supplied analytic premise.  Keep the genuinely separate low-ordinate principal zero census explicit.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp`, targeted Lean check green, new declarations axiom-clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use the exact residue identity already formalized in `ChenGuptaLiPrincipalContour.lean`.  Bound the finite Möbius detector at `1` by `X+1` and the principal Euler residue by `1`.  The delicate uniformity as `Re rho` approaches `1` is obtained from
`Gamma(1-rho) = Gamma(2-rho)/(1-rho)`: on `|Im rho| >= 1`, the denominator has norm at least `|Im rho|`, while `2-Re rho` lies in the fixed compact strip `[1,3/2]`.  Apply the corpus Gamma vertical-strip estimate there and polynomial--exponential decay for the threshold consequence.

## Proof

**[PROVED HERE]** Put `w = 1-rho`.  Since `1/2 <= Re rho < 1`, one has `0 < Re w <= 1/2`, while `1 <= |Im rho|` gives `1 <= |Im w| <= ‖w‖`.  The Gamma recurrence gives

`‖Gamma(w)‖ <= ‖Gamma(w+1)‖`.

Now `1 <= Re(w+1) <= 3/2`, so the uniform vertical-strip theorem bounds the right side by `C |Im rho|^N exp(-pi |Im rho|/2)`.  The detector mollifier contributes at most `X+1`.  Every real Euler factor `1-1/p` belongs to `[0,1]`, so their product has norm at most one.  Multiplication with the exact principal residue identity proves the stated estimate.  Polynomial growth times the strict exponential tends to zero, giving a conductor-uniform threshold `T(X,eta)` and the contrapositive: residue size at least `eta` forces `|Im rho| < T`.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/ChenGuptaLiPrincipalHighOrdinate.lean`.

- `cglPrincipalLFunctionResidue_norm_le_one`
- `exists_cglPrincipalPole_Gamma_norm_le_polyExp`
- `cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp`
- `cglPrincipalRegularizedMellinFactor_at_principalPole_eventually_lt`
- `cglPrincipalRegularizedMellinFactor_large_forces_bounded_ordinate`

Targeted source check passed.  `#print axioms` for all five declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.  Formal lint reports no task-caused error; two unrelated pre-existing `HTGeometry` umbrella reachability errors remain.

## Frontier effect

The high-ordinate principal residue in CGL Section 12.1 is closed.  The separate smoothed coefficient-tail truncation is now closed in `ChenGuptaLiClassITailGeometricBound.lean`. Still open and not conflated with either theorem: quantitative low-ordinate principal zero census and safe-line integral-tail truncation needed for the complete Class-I/Class-II alternative.

## Log
- 2026-08-23 — created in 1-in-progress after exact comparison with CGL Section 12.1.
- 2026-08-23 — `[PROVED HERE]` and formalized; moved to 3-formalized after targeted Lean and axiom checks.
