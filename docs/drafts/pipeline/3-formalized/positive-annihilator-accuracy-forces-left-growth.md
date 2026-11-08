# Positive annihilator accuracy forces left growth

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `logs/aal-conjecture-loop-2026-11-07.md`, Metatheorem 341.
- **Lean:** `ArithmeticPositiveDuality/PositiveAnnihilatorAccuracyForcesLeftGrowth.lean`.

For a positive two-prime Dirichlet polynomial `P(s)=1+Σ a_n n^(−s)`, supported on `n=2^u 3^v>1`, put `H(σ)=Σ a_n n^(−σ)`. If `P(β+iγ)=0`, then for `σlo<β<σhi`,

`1≤H(β)≤H(σhi)^θ H(σlo)^(1−θ)`, where `θ=(β−σlo)/(σhi−σlo)`.

Thus `H(σhi)≤ε`, `ε>0`, forces

`H(σlo)≥ε^(−(β−σlo)/(σhi−β))`.

The formal proof uses the literal multivariate polynomial evaluation, the triangle inequality, finite Hölder interpolation, and logarithms. No analytic continuation assumption is introduced.

## Exact boundary and sharpness

The worklog's strict inequality `H(β)>1` is false in general. The exact identity is

`H(β)−1=Σ a_n n^(−β)(1+cos(γ log n))`.

Consequently `H(β)=1` precisely when every supported nonconstant phase has cosine `−1`. The positive binomial `Pβ(s)=1+2^(β−s)` vanishes at `ρβ=β+iπ/log 2`, has `H(β)=1`, and attains the left-growth bound exactly with `ε=H(σhi)`. This is an explicit Dirichlet-polynomial zero; no claim that `ρβ` is a zeta zero is made.

## Actual zeta zeros

Every finite set of actual ξ-zeros, with arbitrary prescribed multiplicities, admits a positive two-prime polynomial with constant coefficient one, the prescribed vanishing orders, and `|P(s)−1|<ε` throughout `Re s≥1`. The same polynomial satisfies the proved lower mass bound to the left of each prescribed zero. This combines the existing existence theorem with the exact cost, without assuming AAL or any distribution hypothesis on zeta zeros.

## Certificates

- `one_le_dirichletTailMass_of_zero`
- `dirichletTailMass_eq_one_iff_phases`
- `root_forces_tail_sandwich`
- `annihilator_accuracy_forces_left_growth`
- `exists_xi_zero_annihilator_with_left_growth`
- `exists_positive_annihilator_of_unit_tail_mass`
- `sharpBinomial_attains_left_growth`

Direct `lake --old env lean` audit passes without warnings. All seven capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. The module is umbrella-wired. The strict worklog claim is replaced by an exact equality classification and a sharp growth law; AAL remains undecided. The formalized multiplicity and frequency-span refinements are in `the-unit-mass-boundary-of-positive-annihilators.md`.
