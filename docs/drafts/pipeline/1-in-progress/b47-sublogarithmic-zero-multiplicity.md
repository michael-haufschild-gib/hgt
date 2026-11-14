# Sublogarithmic multiplicity of zeta zeros

- **ID:** b47-sublogarithmic-zero-multiplicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1311/route-obstacles.md`, S4, B47; exact target in `docs/reports/review-0611/obstacles-summary.md`, B47.
- **Statement:** For every `ε > 0`, eventually every critical zeta zero `ρ = 1/2 + iγ` satisfies `m(ρ) ≤ ε log |γ|`, unconditionally, from an input not reducible to size bounds. The same assertion for all nontrivial zeros is a stronger target.

## Proven inputs and open step

- `SquareRootThreshold.mult_le_log_zeta` gives `m(ρ) ≤ 40 log(180 |Im ρ|)`.
- `NodalGeometryOfTheDeBruijnFlow.exists_mult_le_log` gives critical multiplicity `≤ (3300/9991 + ε) log X`. Its frequency estimate comes from energy doubling and size bounds at a fixed positive horizon; it does not make the coefficient tend to zero.
- `ConjugateDiagonalGeometry.exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect` gives `H(γ) ≤ C log|γ|/loglog|γ| + 4 Eγ((1/4)loglog|γ|)`, where `H` counts the entire horizontal fibre. The all-height estimate `Eγ((1/4)loglog|γ|) = o(log|γ|)` is not supplied.
- `PrimeTorusTheory.NonAlignmentAtEveryLargeHeight` controls finite-word multiplicity and prime phases. No implication from large zeta multiplicity to the forbidden alignment has been identified.

The two displayed multiplicity bounds from `SquareRootThreshold` and `ConjugateDiagonalGeometry` pass `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`, using `lake --old env lean`. No proof of the sublogarithmic target is supplied.

## Heat collision test

High critical multiplicity does not force forward nonreal branches. The sign is `∂t H = −∂z² H`: an order-`m` real zero has forward profile `Q_m(w) = e^(−D²)w^m`, with `m` simple real roots. The nonreal profile is backward, at negative time when the base is `0`; positive-time finiteness does not constrain it.

The existing positive survivor is a real-gap bound `g² ≤ (24/(m+1) + ε)t`: `CollisionsBlowUpToHermiteProfiles.blowup_forward`, `card_profileRoots`, `exists_zero_near_root_forward`, `exists_close_zeros_forward`. Its validity radius depends on the zero, with no lower bound reaching the horizon `t ≍ 1/log γ`. Even at that horizon, `m ≍ log γ` gives `g² ≍ 1/log²γ`, compatible with known spacing. A uniform gap-opening rate `ω(1/log γ)` near every initial collision would be new input.

## Derivative cancellation and reciprocal integrability

Low zeta jets give exact paired-eta moment cancellations (`pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity`). Positivity alone does not convert them into prime-phase alignment: `ArithmeticPositiveDuality.PositiveAnnihilator.exists_arbitrary_multiplicity_near_unit_mass` supplies positive Dirichlet polynomials with constant coefficient `1`, arbitrary zero order, and nonconstant mass arbitrarily close to `1`. Multiplying zeta by eta or finite Euler factors preserves the jets by Leibniz; an independent arithmetic constraint remains missing.

A precise alternative target is local integrability of `|ζ(1/2+it)|^(−p(T))` on every high unit interval, with `p(T) log T → ∞`. At an order-`m` zero the exact integrability threshold is `mp(T)<1`. Off-line Blaschke removal preserves this boundary modulus (`TheDerivativeReadsTheBlaschkeFactor.exists_blaschke_quotient`), but supplies no reciprocal moment bound. For the formal coefficients of `ζ^(−α)`, the prime coefficients equal `−α`, so their critical square sum diverges for every `α>0`. Neither a deterministic coefficient-to-boundary transfer nor the required local reciprocal integrability has been proved.

The exact arithmetic receiver criterion is `TransHorizonIncidenceMechanics.receiverBounded_logPowerCosine_iff_all`: the weight `d^(−1/2) cos(γ log d)(log d)^k` has bounded energy precisely when all zeta jets through `k` vanish. Its centered prefix is `A_c(n)=−Σ_{d≤n}c(d){n/d}−nΣ_{d>n}c(d)/d`, and its energy is `Σ A_c(n)²/[n(n+1)]`. Polynomial localization at one finite arithmetic scale supplies only finite energy; every finitely supported weight already has bounded receiver. A contradiction requires a quantitative lower bound across growing scales, with the polynomial normalization and its bounded-energy constant controlled. That lower bound remains unproved.

## Positive strip test

The formalized [positive strip test](../3-formalized/zeta-sech-strip-multiplicity.md)
gives `m(1/2+iγ) ≤ (3/(8π)+ε)log|γ|` and the stronger uniform envelope

`m(β+iγ) ≤ [(3/(8π))cos((4π/3)(β−1/2))+ε]log|γ|`.

The weighted horizontal-fibre theorem uses the corpus quasi-RH strip,
fixed-line sublogarithmic logarithmic derivatives, and positive sech residues.
It gives sublogarithmic multiplicity on the outer boundaries `β=1/8,7/8`.
All stated consequences are Lean-certified with only `propext`,
`Classical.choice`, and `Quot.sound`. The critical-line coefficient remains
positive, so B47 remains open.

## Gates

The formalized [local compensation theorem](../3-formalized/zeta-large-critical-multiplicity-local-compensation.md)
shows that `m≥c log T` at a critical zero forces `Ω_c(log T)` actual off-line
zero copies within a fixed height distance and a fixed positive horizontal depth.
Its exact finite inequality, Gaussian asymptotic, and final counting statement
pass Lean with standard axioms only. Excluding these configurations remains open.

- [x] Exact target and existing bounds identified.
- [ ] Independent all-height arithmetic or geometric input proved.
- [ ] Dependency-closed proof of the displayed zeta statement.
- [ ] Lean formalization, module check, transitive axiom audit.
