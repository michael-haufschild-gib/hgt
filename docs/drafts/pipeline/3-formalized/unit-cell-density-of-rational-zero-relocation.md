# Unit-cell density of rational zero relocation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `logs/aal-conjecture-loop-2026-11-07.md`, Cycle 318.
- **Statement:** Actual critical-line donor zeros give an integrable signed relocation density with zero mass, a uniform Bernoulli profile, exact integer derivative jumps, and a negative first gap preserved by every finite ordinary Dirichlet filter with constant coefficient one.

## Construction

Hardy's theorem supplies `1<γ₁<γ₂` with `ζ(1/2+iγ_j)=0`. No RH or simplicity assumption is used. Put

`D(s)=((s−1/2)²+γ₁²)((s−1/2)²+γ₂²)`,
`h=√((γ₁²+1/4)(γ₂²+1/4)+1/16)`,
`η=√(h−5/16)`, `ρ=3/4+iη`, `c=2h−γ₁²−γ₂²−3/4`.

Then `η>0`, `c<0`, and the symmetric quartet multiplier is exactly
`R(s)=1+c s(s−1)/D(s)`, with `R(0)=R(1)=1` and `R(ρ)=0`.

For `r_γ=1/2+iγ`, define

`p_γ(Y)=Im(Y^(r_γ−1) Σ_(1≤n≤Y) n^(−r_γ))/γ`,
`f(Y)=c((γ₂²+1/4)p_γ₂(Y)−(γ₁²+1/4)p_γ₁(Y))/(γ₂²−γ₁²)`.

## Proven identities

1. For `Re s>1`, `∫_1^∞ Y^(−s)f(Y)dY=ζ(s)(R(s)−1)`. The literal power-sum Mellin identities hold even without donor-zero assumptions.
2. With `B₂(θ)=θ²−θ+1/6`, there is `C≥0` such that eventually, uniformly for `0≤θ<1`,
   `|N²f(N+θ)+c B₂(θ)/2|≤C/N`.
   Thus `f(Y)=O(Y^(−2))`, `N²f(N)→−c/12`, and `N²f(N+1/2)→c/24`.
3. Eventually, `N²f(N+θ)≥−c/48` for `0≤θ≤1/12`, and `N²f(N+θ)≤c/48` for `1/3≤θ≤2/3`.
4. `f∈L¹(1,∞)`, `∫f=0`, and `∫f(Y)/Y dY=R′(1)=c/D(1)<0`.
5. Adjacent cell values agree; their derivatives at integer `n≥1` differ by exactly `c/n²`.
6. There is `0<ε≤1` with `f<0` on `(1,1+ε)`. For every finite `S⊆{2,3,…}` and arbitrary real coefficients `a_n`,
   `f(Y)+Σ_(n∈S) a_n f(Y/n)/n=f(Y)` whenever `Y<2`.
   Hence this negative interval survives every such filter, including signed filters. The local first-gap law needs no donor-zero assumption.

## Proof mechanism

Euler–Maclaurin and a uniform quadratic expansion of `(1+θ/N)^(s−1)` give the Bernoulli remainder. Vanishing donor zeta values identifies these regularized kernels with the literal floor sums. Inverse-square decay makes the Mellin integral holomorphic on `Re s>−1`; the identity theorem extends

`D(s)M(s)=cs Z(s)`, where `Z(s)` is the entire continuation of `(s−1)ζ(s)`.

Evaluation at zero and one gives the two moment identities. Adding the next integer changes the complex kernel by `1/n`, which has zero imaginary part, while its slope changes by `(s−1)/n²`. This proves gluing and the exact derivative jump. The first cell therefore starts at zero with slope `c`; nonconstant integer dilations sample the zero region below one.

## Endpoint rigidity and positive survivor

For any single quartet, let `δ=Re ρ−1/2`, `η=Im ρ`, `a=γ₁²`, `b=γ₂²`,
`A=2(η²−δ²)−a−b`, and `B=(η²+δ²)²−ab`. These are its quadratic and constant centered numerator differences. The identity

`4(B+A/4)=A²+A(8δ²+2(a+b)+1)+16δ⁴+8δ²(a+b)+(a−b)²`

shows that `R(1)=1` forces `A≤0`. Equality holds exactly when `Re ρ=1/2` and `γ₁²=γ₂²=(Im ρ)²`. Every off-line single quartet therefore has `R′(1)<0` and a positive vertical limit `t²(R(σ+it)−1)→−A>0`.

Thus simultaneous `R(1)=1`, `R′(1)=0` is impossible for a single off-line quartet. The surviving invariant connects endpoint slope, inverse moment, vertical trace, Bernoulli profile, and integer derivative jumps. This does not exclude larger globally normalized constructions or establish the worklog's higher-order moment-matching claims. Actual AAL remains undecided.

## Lean certificates

All modules are in `formal/GaloisForLFunctions/ArithmeticPositiveDuality/` and imported by its umbrella.

| Module | Principal certificate |
|---|---|
| `NormalizedQuartetRelocation.lean` | `normalizedRelocation_polynomial`, `normalizedRelocation_deriv_one_neg` |
| `TheUnitCellTraceOfZeroRelocation.lean` | `exists_uniform_quartetCellDefect_remainder` |
| `PowerSumDensitiesAndRationalMellinFactors.lean` | `mellin_quartetDensity` |
| `NormalizedRelocationHasASignedDensity.lean` | `exists_normalizedRelocation_signed_density` |
| `TheNormalizedRelocationDensityHasZeroMass.lean` | `exists_integrable_signed_quartet_density`, `eventually_quartetDensity_sign_bands` |
| `TheIntegerJumpsOfRelocationDensities.lean` | `quartetCellDefect_derivative_jump` |
| `EndpointNormalizationForcesANegativeQuartetTrace.lean` | `quartet_quadratic_eq_zero_iff_of_endpoint`, `quartet_deriv_one_neg_of_endpoint` |
| `TheFirstIntegerGapDetectsRelocation.lean` | `exists_normalizedRelocation_first_gap_obstruction` |

All eight direct `lake --old env lean` checks pass without warnings. Audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
