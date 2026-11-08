# Unit-cell density of rational zero relocation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `logs/aal-conjecture-loop-2026-11-07.md`, Cycle 318.
- **Statement:** A nontrivial normalized rational relocation has a signed continuous integer-measure defect whose leading term on every large unit cell is a Bernoulli polynomial.

## Exact candidate

For distinct actual zeta zeros `r_j` and partial-fraction coefficients `a_j`, put

`R(s)=1+Σ_j a_j/(s-r_j)`,
`f(Y)=Σ_j a_j Y^(r_j-1) Σ_{1≤n≤Y} n^(-r_j)`.

When `R(1)=1` and `Σ_j a_j=0`, set `A=Σ_j a_j r_j`. The proposed limits are

`N² f(N) → -A/12`,
`N² f(N+1/2) → A/24`.

For conjugation-symmetric data and real `A≠0`, these give opposite signs in every sufficiently large unit cell. The stronger uniform candidate is

`f(Y)=-(A/2) B₂({Y})Y^(-2)+O(Y^(-3))`.

## Source construction to discharge

With two distinct positive critical-line ordinates `γ₁,γ₂`, take

`D(s)=((s-1/2)²+γ₁²)((s-1/2)²+γ₂²)`,
`R(s)=1+c s(s-1)/D(s)`.

This preserves reflection, reality, `R(0)=R(1)=1`, and has quadratic trace `A=c`. Its poles cancel against actual zeta zeros; no simplicity assumption is needed.

An explicit target avoids a root-collision existence argument. For `γ₁,γ₂>1`, write

`a=γ₁²`, `b=γ₂²`, `h=√((a+1/4)(b+1/4)+1/16)`,
`γ=√(h-5/16)`, `ρ=3/4+iγ`, `c=2h-a-b-3/4`.

Then `γ>0`, `c<0`, and the quartet polynomial for `ρ` is exactly `D(s)+c s(s-1)`. The sign follows from

`((a+b+3/4)/2)²-h²=(a-b)²/4+(a+b)/8+1/64>0`.

The corresponding density therefore has proposed limits `N²f(N)→-c/12>0` and `N²f(N+1/2)→c/24<0`. These explicit algebraic identities and the Mellin transform still require Lean proofs.

## Mechanism and limits

Euler–Maclaurin gives the density from exact unit coefficients. The `ζ(r_j)` terms vanish; normalization removes the constant term, and the vanishing residue sum removes the `Y⁻¹` term. The next term is the periodic Bernoulli function. This audits the worklog's integrable-defect claim and identifies its local support obstruction. It is not an AAL contradiction.

## Status

Corpus audit located `ZetaEulerMaclaurinArbitraryOrder`, `IntegrableDefectsAtUnitDensityAreRigid`, and the unconditional Hardy critical-line census. `ArithmeticPositiveDuality/TheUnitCellTraceOfZeroRelocation.lean` is being developed; no capstone is checked yet. The uniform remainder, half-integer limit, concrete relocation, and Mellin-transform identity remain unformalized.
