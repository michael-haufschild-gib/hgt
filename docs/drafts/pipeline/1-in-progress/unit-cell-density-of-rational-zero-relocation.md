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

The corresponding density has proposed limits `N²f(N)→-c/12>0` and `N²f(N+1/2)→c/24<0`. The algebraic identities are checked in `NormalizedQuartetRelocation.lean`, including strict negativity of `c` and both endpoint values; their transitive axioms are the three standard Lean axioms.

This quartet does not satisfy the worklog's additional normalization `R′(1)=0`: its derivative is `c/D(1)<0`, now checked by `normalizedRelocation_deriv_one_neg`. No claim about a construction satisfying all three endpoint conditions follows from this example.

Stronger algebraic candidate: for any single quartet, `R(1)=1` forces its quadratic trace `A≤0`; equality forces `Re ρ=1/2` and `γ₁²=γ₂²=(Im ρ)²`. Writing `δ=Re ρ−1/2`, `a=γ₁²`, `b=γ₂²`, the exact identity is

`4(B+A/4)=A²+A(8δ²+2(a+b)+1)+16δ⁴+8δ²(a+b)+(a−b)²`.

Normalization makes the left side zero. Every off-line single-quartet move therefore has `A<0`. The classification remains to be formalized.

## Mechanism and limits

Euler–Maclaurin gives the density from exact unit coefficients. The `ζ(r_j)` terms vanish; normalization removes the constant term, and the vanishing residue sum removes the `Y⁻¹` term. The next term is the periodic Bernoulli function. This audits the worklog's integrable-defect claim and identifies its local support obstruction. It is not an AAL contradiction.

## Status

The algebraic quartet, uniform Bernoulli remainder, and literal Mellin identity have passed Lean checking, with only `propext`, `Classical.choice`, and `Quot.sound`. Their modules are `NormalizedQuartetRelocation.lean`, `TheUnitCellTraceOfZeroRelocation.lean`, and `PowerSumDensitiesAndRationalMellinFactors.lean`.

`NormalizedRelocationHasASignedDensity.lean` also passed direct checking without warnings. Its assumption-free existential capstone constructs the donors from Hardy's theorem and proves the literal density's opposite signs; `exists_quartetDensity_inverse_square_bound` supplies the global decay bound.

`TheNormalizedRelocationDensityHasZeroMass.lean` now proves absolute integrability, zero total mass, and fixed-width sign bands: eventually `N²f(N+θ)≥−c/48` for `0≤θ≤1/12`, and `N²f(N+θ)≤c/48` for `1/3≤θ≤2/3`. Its Mellin transform is holomorphic on `Re s>−1` and satisfies `D(s)M(s)=cs(s−1)ζ(s)`, interpreted at `s=1` using the entire pole unit. Evaluating at zero proves the mass identity. All five capstones pass direct checking without warnings and use only the three standard axioms.

Derivative jumps and the general endpoint classification remain under formalization. Actual AAL remains undecided.
