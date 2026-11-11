# The Li ladder as damped comb tails

- **ID:** A82
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Target

Realize every paired Li coefficient as a limit of normalized comb forms of finite tails.
For degree `n`, the undamped tail profile is the Laguerre polynomial
`P_n(x)=Σ_{k<n} binom(n,k+1)(−x)^k/k!`, with coefficients `P_n(log(N/m))`.
The flat tail is `n=1`.

## Damped approximation

Use `g_{n,ε}(x)=1_{x>0} exp(−(1/2+ε)x) P_n(x)`, with `ε>0`.
Its Fourier transform at the spectral point corresponding to `ρ` is
`1−(1−1/(ρ+ε))^n`. The reflected factor uses `1−ρ+ε`.
As `ε↓0`, their product tends to the paired Li summand.

Both shifted denominator norms are at least `|Im ρ|>4`, for every real shift.
The finite geometric-series identity bounds the product by
`(2^n−1)²/|Im ρ|²`, summable over zero copies. Dominated convergence therefore gives
`W(g_{n,ε})→xiLiPaired(n)`.

For fixed `ε>0`, multiply by the smooth plateau on `(0,R)` with transition width `1/R`.
Writing the damped polynomial profile as `g`, let
`B=sup_{x≥0}|g(x)|exp(x/2)` and `D=∫₀∞|g′(x)|exp(x/2) dx`; both are finite.
The plateau has total variation at most `2`, so every truncated profile has weighted
derivative integral at most `2B+D`. Integration by parts gives the uniform transform
bound `(2B+D)/|Im ρ|`. Dominated convergence passes through the zero sum as `R→∞`.
Reflect and translate the compact profile by `R+log 4`, placing its support in
`(log 4,R+log 4)`. At degree point `m`, its argument is `log(M/m)`, where
`M=4 exp(R) N`; division by `sqrt(m)` gives the common normalization `1/sqrt(M)`
times the damped polynomial and cutoff. The compact smooth sampling theorem
then realizes each approximant as a limit of finite comb forms. A diagonal choice gives
one sequence of finite tails for each `n`.

## Lean

Three modules contain the full argument:

- `TheDampedLiTailsReachTheLiCoefficients.lean`: damping removal by summable domination; direct check passed.
- `SmoothTruncationPreservesTheDampedTail.lean`: compact cutoffs, weighted variation and Fourier convergence; direct check passed.
- `TheLiCoefficientsAreLimitsOfCombTails.lean`: Laguerre profile bounds, multiplicity-preserving spectral transfer,
  comb sampling and diagonal sequence `exists_liCombTail_sequence`; direct check passed.

These files are in `HodgeTheoryOfAFixedPart/`. The diagonal uses `ε_m=1/(m+1)`,
`R_m≥m+1`, `N_m≥m` and converges to `Re xiLiPaired(n)`.
`RHTower.suzukiLiWeilForm_eq_xiLiPaired` already identifies the limiting coefficient.
This route proves a damped iterated limit; convergence of the raw polynomial tail requires
an additional uniform truncation estimate.
