# Logarithmic excess under strong half-line confinement

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B16, B17; quantitative shape of the actual variational margin.
- **Statement:** For `a=criticalAliasCoefficient R` tending to infinity, the unit-mass ground energy is `a+log a+O(1)`. Every normalized minimizer satisfies `c/a≤W(F)-1≤C/a` for fixed positive constants.

## Corpus connection

`CriticalHalfLineEnergyBranch` attains the literal full-energy floor and supplies a reflected tilted spline supported in `[-1,0]`. `BiScaleUncertainty.exists_sourceRescale_logarithmic_energy_bound_of_support` gives coefficient-one logarithmic normalized archimedean cost for its dilates.

For a normalized negative-support profile, `W-1=∫F²(exp(-8u)-1)` controls its tail mass. Cauchy–Schwarz bounds the correlation at displacement `x>0` by the square root of the mass below `-x`. Integrating this correlation deficit against the positive singular archimedean kernel gives a lower bound `-log(W-1)-O(1)`. Balancing it with `a(W-1)` yields the logarithmic excess.

## Paper proof

Write `m(F)=∫F²`, `W(F)=∫F²exp(-8u)`, `J(F)=biScaleLevyEnergy(F)`, and `cΓ=2·gammaHardyPhaseRate(0)`.

**Actual-domain identity.** For every actual-domain profile, Gamma integrability transfers under the linear change of Fourier variable to integrability of `gammaHardyPhaseRate(2πξ)|Fourier(F)(ξ)|²`. Ordinary L¹ and L² membership are part of the domain. The corpus's general `integral_archSymbol_mul_normSq_fourier_eq` and `lintegral_archLevyDirichlet_ne_top` therefore give finite jump energy and `archForm(F)=cΓm(F)+levyEnergy(F)`. The jump integrand is measurable because `(x,u)↦(F(u)-F(u+x))²` is measurable and integration preserves measurability. Expanding the square, using L² product integrability and translation invariance, identifies `levyEnergy(F)=J(F)`. Thus no smoothness or compact-support assumption is needed.

**Exponential defect and correlation.** If `m(F)=1`, then `δ=W(F)-1>0`: the integrand `F(u)²(exp(-8u)-1)` is nonnegative and strictly positive wherever `u<0` and `F(u)≠0`; zero integral would contradict unit mass. At displacement `x>0`, negative support restricts the correlation integral to `u≤-x`. Cauchy–Schwarz and translation invariance give its square at most the square mass in that tail. The exponential defect bounds this tail by `δ/(exp(8x)-1)≤δ/(8x)`.

**Logarithmic lower cost.** If `0<δ<8`, put `r=δ/8<1`. The corpus lemma `archLevySinhWeight_ge_exp_neg_half_div` gives `w(x)≥exp(-x/2)/x≥1/x-1/2`. For `r≤x≤1`, this and the correlation bound imply

`(1-autocorr(F,x))w(x)≥1/x-sqrt(r)x^(-3/2)-1/2`.

The nonnegative full Lévy integral dominates its integral over `[r,1]`, hence

`J(F)≥-log r-2(1-sqrt r)-(1-r)/2≥-log δ-5/2`.

For `δ≥8`, the same final bound follows from `J(F)≥0`. The inequality therefore holds throughout the actual unit domain.

**Arithmetic remainder.** Put `S(F)=exponentialSourceMass(F)`. Existing weighted estimates give `|primeSum(F)|≤2V S(F)` and `coshHalfMoment(F)²,sinhHalfMoment(F)²≤J₀ S(F)`, where `V` and `J₀=∫exp(-|u|)` are fixed nonnegative constants. Thus, for `C=2V+2J₀`,

`|E_R(F)-archForm(F)-aW(F)|≤C S(F)≤C(m(F)+W(F))`.

Combining the unit-mass identities gives a fixed `B≥0` with

`E_R(F)≥a+(a-C)δ-log δ-B`.

For `a≥2C+2`, put `p=a-C≥a/2>0`. The inequality `log z≤z-1` at `z=pδ` gives `pδ-log δ≥1+log p`. Consequently `λ(R)≥a+log a-O(1)`.

**Matching upper cost.** Take the reflected tilted spline `g`, a compact `C²` source supported in `[-1,0]`, with square mass `m>0`. Its correlation has a finite positive support radius `D`. For `a≥max(D,1)`, normalize the dilation

`G_a(u)=sqrt(a/m) g(au)`.

It has unit mass, belongs to the actual domain, and is supported in `[-1/a,0]`. Scalar multiplication preserves normalized Lévy energy. The coefficient-one dilation theorem gives `J(G_a)≤log a+C_g`. Also `W(G_a)≤exp(8/a)`. The elementary bound `exp t-1≤t exp t` implies `a(W(G_a)-1)≤8exp(8)` for `a≥1`. The arithmetic remainder is uniformly bounded because `W(G_a)` is bounded. Testing the variational floor with `G_a` gives `λ(R)≤a+log a+O(1)`.

**Minimizing mass scale.** For a normalized minimizer, combine the preceding upper bound with the lower bound retaining `δ`. With `z=pδ`, this gives `z-log z≤Q` for one fixed `Q≥1`, since `log(a/p)≤log 2`. Positivity of `z` implies `z≥exp(-Q)`. Applying `log(z/2)≤z/2-1` also gives `z≤2(Q+log 2+1)`. Since `a/2≤p≤a`, there are fixed `c,C'>0` with `c≤aδ≤C'`. These bounds hold for every sign choice and representative of the minimizing line.

## Lean status

`criticalHalfLineGroundEnergy_strong_confinement` proves the stated energy and exponential-excess bounds, uniformly over every normalized minimizer at sufficiently large confinement strength.

All six `CausalReflection` modules pass final plain source audits and are wired: `ActualHalfLineLevyEnergy`, `ConfiningHalfLineArithmeticBounds`, `HalfLineConfinementCorrelation`, `HalfLineConfinementLogarithmicCost`, `HalfLineConfinementDilation`, and `ConfiningHalfLineStrongLimit`. Their audited final declarations depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.

The result does not identify a limiting renormalized energy or rescaled profile. Those are separate conjectures.
