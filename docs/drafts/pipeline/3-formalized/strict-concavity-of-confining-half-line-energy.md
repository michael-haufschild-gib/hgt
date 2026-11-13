# Strict curvature of the confining half-line energy

- **Stage:** 3-formalized
- **Target:** B16, B17; the shape of the margin as confinement varies.
- **Statement:** For `t>0`, `μ(t)=criticalHalfLineGroundEnergy(1/t)` is strictly concave. No normalized profile minimizes at two different ratios. The eighth-exponential mass of a normalized minimizer strictly decreases as `t` increases.

## Corpus connection

`criticalHalfLineFullEnergy_change_ratio` makes the energy of each fixed profile affine in the confinement coefficient. Actual-domain attainment is available in `CriticalHalfLineEnergyBranch`. Concavity follows by evaluating an intermediate-parameter minimizer at the two endpoints.

Equality would make that profile minimize at both endpoints. Quadratic variation gives the full weak equations `B_a(F,G)=λ(a)∫FG`. Subtracting them forces `(exp(-8u)-c)F(u)` to annihilate all smooth compactly supported tests on the negative half-line. Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` identifies this locally integrable function with zero. Strict monotonicity of the exponential confines the support of `F` to at most one point, contradicting unit square mass.

## Paper proof

Write `m(F)=∫F²`, `W(F)=∫F²exp(-8u)`, `K=criticalAliasCoefficient 1>0`. The exact dependence is `E_{1/t}(F)=E_1(F)+K(t-1)W(F)` for positive `t`. Actual-domain attainment supplies a unit minimizer at every positive parameter.

**Weak equation.** For a minimizer `F` at ratio `R`, the nonnegative form `Q_R(G)=E_R(G)-λ(R)m(G)` vanishes at `F`. Expanding `Q_R(F+cG)` gives `2cB+c²A≥0` for every real `c`, with `A=Q_R(G)≥0` and `B=B_R(F,G)-λ(R)∫FG`. Substitution `c=-B/(A+1)` gives `-(A+2)B²≥0`, hence `B=0`. This proves the weak equation against every actual-domain profile.

**No common minimizer.** Suppose the same unit profile minimizes at distinct positive ratios `R,S`. Subtracting the weak equations and the mixed-energy parameter identity gives

`∫G(u)[(a(R)-a(S))exp(-8u)-(λ(R)-λ(S))]F(u)du=0`

for every actual-domain `G`. The coefficient `a(R)-a(S)` is nonzero because `a(R)=K/R` and `K>0`.

Every smooth compact test supported in `u<0` belongs to the actual domain: compactness gives ordinary and exponential integrability, and the corpus's `C²` compact-support Gamma estimate gives full Gamma integrability. The bracketed function times `F` is locally integrable. Smooth-test duality therefore makes it zero almost everywhere on the negative half-line. Its scalar factor has at most one zero, by injectivity of the exponential. A singleton has zero Lebesgue measure, so `F=0` almost everywhere there; the support condition gives zero on the rest of the line. This contradicts `m(F)=1`.

**Strict concavity.** Let `x≠y` be positive and let `α,β>0` with `α+β=1`. A minimizer `F` at `αx+βy` satisfies

`μ(αx+βy)=αE_{1/x}(F)+βE_{1/y}(F)≥αμ(x)+βμ(y)`.

Equality would make both nonnegative endpoint energy deficits zero, since both weights are positive. Thus `F` would be a common minimizer at the distinct ratios `1/x,1/y`, already excluded. The inequality is strict.

**Strict mass response.** For `0<x<y`, choose unit minimizers `F_x,F_y`. The variational comparisons give

`K(y-x)W(F_y)≤μ(y)-μ(x)≤K(y-x)W(F_x)`.

Equality at either endpoint would again produce a common minimizer. In particular `W(F_y)<W(F_x)`. This order law is independent of any choice of signs or representatives.

## Lean status

All three modules passed final plain source audits without warnings, with exactly `propext`, `Classical.choice`, and `Quot.sound`, and are wired into the umbrella:

- `ConfiningHalfLineWeakEquation`: the actual-domain weak equation and admissibility of compact smooth negative-support tests.
- `ConfiningHalfLineGroundStateSeparation`: `halfLineEnergyMinimizer_ratio_unique` excludes a common normalized minimizer at distinct positive ratios.
- `ConfiningHalfLineGroundEnergyCurvature`: `confiningHalfLineGroundEnergy_strict_jensen` proves strict concavity, and `halfLineEnergyMinimizer_exponential_mass_strict_antitone` proves strict mass response.

Polar nonvanishing is not implied by concavity alone.
