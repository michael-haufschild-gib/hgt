# Universal soft logarithmic confinement limit

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B16, B17; identify the limiting variational problem behind the confining margin. Review-1311 A158 identifies this written closure for verification; limiting-profile attainment remains separate.
- **Statement:** After subtracting `a+log a`, the actual ground energy converges to a fixed half-line logarithmic variational floor. Rescaled minimizers approach this floor, with `a(W-1)→1` and `a∫(-u)F(u)²du→1/8`.
- **Status:** Complete. All eighteen supporting modules pass final plain source audits with exactly `propext`, `Classical.choice`, and `Quot.sound`; all are wired. Counted as one contribution. Limiting-profile attainment and polar charge remain open.

## Corpus connection

`gammaHardyPhaseRate_eq_log_reference_fourier` decomposes the actual Gamma symbol into a logarithmic reference and a bounded convolution remainder. `gammaHardyPhaseRate_sub_log_conductor_tendsto_zero` fixes its high-frequency normalization. `SuzukiSmallApertureGroundAsymptotic` transfers a uniformly controlled rescaled form to an actual Rayleigh infimum on a fixed interval.

The strong-confinement route supplies a different geometry: actual half-line minimizers have bounded `a(W-1)`. Rescaling by `x=-au` suggests a linear confining potential `8x`. The global affine variational comparison supplies both secant bounds for the minimizing exponential mass.

## Limiting form

Let `U` consist of measurable real profiles `f`, zero on `[0,∞)`, belonging to `L¹∩L²`, with finite absolute logarithmic Fourier energy and `∫f(u)²exp(-βu)du<∞` for some `β>0`. Restrict to square mass one. Set

`Q(f)=∫ log|ξ|·|Fourier(f)(ξ)|² dξ+8∫(-u)f(u)²du`.

Let `μ` be its Rayleigh infimum. The limit is `λ(R)-a(R)-log a(R)→μ` as `a(R)→∞`. The literal corpus asymptotic gives `2·gammaHardyPhaseRate(2πaξ)-log a→log|ξ|` for nonzero `ξ`, fixing this normalization. No attainment of the limiting infimum is claimed.

## Paper proof

Write `D_b f(u)=sqrt(b)f(bu)`, `M(f)=∫(-u)f(u)²du`, and `L(f)=∫log|ξ|·|Fourier(f)(ξ)|²dξ`. The Fourier transform uses the corpus's `2π` normalization. Put `k=criticalAliasCoefficient 1>0` and parameterize the actual floor by `ν(a)=λ(k/a)`, so its literal confinement coefficient is `a`.

**Domain and scaling.** An exponential square moment gives finite first moment, since `βt≤exp(βt)` for `t≥0`. Fourier dilation and change of variables give unit-mass preservation, `M(D_bf)=M(f)/b`, and `L(D_bf)=L(f)+log b`. Absolute logarithmic integrability is preserved by the same formula and the triangle inequality. An exponential moment at `β` becomes one at `bβ`; hence `U` is invariant under every positive dilation.

Every actual-domain profile belongs to `U`. Near frequency zero its Fourier transform is bounded by its L¹ norm, and `|log|ξ||` is integrable on a bounded interval. Away from zero, the corpus's Gamma-symbol asymptotic bounds the logarithmic weight by a constant plus the absolute Gamma symbol. Actual Gamma integrability and Plancherel therefore give absolute logarithmic integrability. Conversely, continuity and the same asymptotic bound the absolute Gamma symbol by `C+|log|ξ||`. Thus `D_a f` belongs to the actual domain for every sufficiently large `a`, whenever `f∈U`: choose `aβ≥8` for its exponential moment.

**Concentration removes the prime and pole terms.** For a unit actual-domain profile put `δ=W(F)-1`. At every `h>0`, pointwise comparison on `u≤-h` gives

`(1-exp(-8h))∫_{u≤-h}F(u)²exp(-8u)du≤δ`.

The lower weighted mass `S(F)=∫F²exp(2|u|)` is at most `W(F)`. For `δ≤1`, let `F_h=1_{[-h,0)}F`. Then `S(F),S(F_h)≤2` and `S(F-F_h)≤δ/(1-exp(-8h))`. These indicators preserve the weighted L² domain. Fix `0<h<log 2`. The corpus theorem `primeSum_eq_zero_of_width_lt` gives `primeSum(F_h)=0`, and `abs_primeSum_sub_le` gives

`|primeSum(F)|≤4sqrt(2)V·sqrt(δ/(1-exp(-8h)))`.

For either polar kernel `ψ=cosh(u/2)` or `sinh(u/2)`, weighted Cauchy–Schwarz bounds the near and far pairings separately. Since `(exp(-|u|)ψ(u))²≤exp(-|u|)≤1`, with `J₀=∫exp(-|u|)`,

`|∫Fψ|²≤4h+2J₀δ/(1-exp(-8h))`.

First choose `h` small, then `δ` small. Both polar squares tend to zero uniformly on these profiles. Therefore the full remainder `A(F)=-primeSum(F)+2coshHalfMoment(F)²-2sinhHalfMoment(F)²` tends to zero uniformly as `δ↓0`. No smoothness or sign of `F` is used.

**First moment controls low-frequency mass.** If `g∈L¹∩L²` has unit square mass and `∫|u|g²≤M₀`, split it at `|u|=H>0`. The inside part has L¹ norm squared at most `2H`; the outside part has square mass at most `M₀/H`. The pointwise Fourier L¹ bound, Plancherel, and `|z+w|²≤2|z|²+2|w|²` give, for `η>0`,

`∫_{|ξ|≤η}|Fourier(g)(ξ)|²dξ≤8ηH+2M₀/H`.

Choosing `H` first and then `η` shows that this spectral mass tends uniformly to zero. No uniform L¹ bound on the whole profile is assumed.

**Uniform lower comparison of the Gamma symbols.** Set `σ(ξ)=2gammaHardyPhaseRate(2πξ)` and `e_a(ξ)=σ(aξ)-log a-log|ξ|`. The corpus asymptotic and evenness give `σ(ξ)-log|ξ|→0` as `|ξ|→∞`; continuity and this asymptotic also give `σ≥-B` for a fixed `B≥0`. Given `ε>0`, choose `T≥1` such that `|σ(z)-log|z||≤ε` for `|z|≥T`. For nonzero `ξ` outside `[-T/a,T/a]`, `e_a≥-ε`; inside, `e_a≥-B-log T`. The preceding low-frequency estimate proves

`liminf_{a→∞} inf_g ∫e_a(ξ)|Fourier(g)(ξ)|²dξ≥0`,

where the infimum ranges over unit profiles in `U` with `M(g)≤M₀`. The single frequency zero is null. For each fixed `f∈U`, the same integral tends to zero: `e_a→0` off zero, and for `a≥1` its absolute value is bounded by `C+|log|ξ||`. The latter bound follows by separating `a|ξ|≥T` and `a|ξ|≤T`; in the second region `log|ξ|≤log(a|ξ|)≤log T`. Dominated convergence applies by the definition of `U`.

**Fixed trials.** For fixed `f∈U`,

`a(W(D_af)-1)=∫a(exp(-8u/a)-1)f(u)²du→8M(f)`.

For domination choose an exponential moment at `β` and `a≥16/β`. With `t=-u≥0`, the inequalities `exp z-1≤z exp z` and `βt/2≤exp(βt/2)` bound `a(exp(8t/a)-1)` by `(16/β)exp(βt)`. The pointwise limit is the derivative of the exponential at zero. Consequently the defect tends to zero, the arithmetic remainder vanishes, and Fourier scaling gives

`E_a(D_af)-a-log a→Q(f)`.

**The limiting infimum is finite.** A normalized reflected compact spline supplies a unit member of `U`. The verified strong-confinement estimate gives `ν(a)≥a+log a-K` for all sufficiently large `a`. Comparing it with each fixed trial and taking the preceding limit gives `Q(f)≥-K` throughout the unit class. Its Rayleigh set is therefore nonempty and bounded below, defining a finite real `μ`.

**Matching variational limits.** Testing with any unit `f∈U` gives `limsup(ν(a)-a-log a)≤Q(f)`; approximation of the infimum gives the upper bound `μ`. For the reverse inequality take any actual normalized minimizer `F_a`, whose existence is already proved for every positive ratio, and put `g_a=D_{1/a}F_a`. The verified exponential-excess bound gives `aδ(F_a)≤C`. Since `exp(8t)-1≥8t`, one has `M(g_a)=aM(F_a)≤C/8`. Also `g_a∈U`. The exact decomposition is

`ν(a)-a-log a = Q(g_a) + [aδ(F_a)-8M(g_a)] + ∫e_a|Fourier(g_a)|² + A(F_a)`.

The bracket is nonnegative, the symbol remainder has a uniform lower bound tending to zero, and the arithmetic remainder tends uniformly to zero. Since `Q(g_a)≥μ`, this proves the lower limit `μ`. Moreover the same identity forces both nonnegative quantities `Q(g_a)-μ` and `aδ(F_a)-8M(g_a)` to tend uniformly to zero over all minimizing profiles.

**Virial scale.** Affine dependence of the full form on strength gives, for every fixed `b>1` and every minimizer at strength `a`,

`[ν(ba)-ν(a)]/((b-1)a)≤W(F_a)≤[ν(a)-ν(a/b)]/((1-1/b)a)`.

The convergent renormalized energy therefore gives

`log b/(b-1)+o(1)≤aδ(F_a)≤log b/(1-1/b)+o(1)`.

The elementary bounds `1-1/b≤log b≤b-1` put the limiting lower bound above `1/b` and the upper bound below `b`. Letting `b↓1` proves `aδ(F_a)→1`, uniformly over all minimizers. The vanishing potential-linearization error then gives `M(g_a)=aM(F_a)→1/8`. Every comparison is independent of the sign and representative of the minimizing line.

## Lean status

Eighteen modules pass plain source audits with exactly `propext`, `Classical.choice`, and `Quot.sound`; all are wired:

- `HalfLineConfinementTail`: weighted-tail control and `8M(F)≤W(F)-m(F)`.
- `WeightedSourceTruncation`, `WeightedSourceLocalizedPairing`: indicator closure, exact restricted masses, and localized weighted Cauchy–Schwarz.
- `HalfLineTerminalTruncation`, `HalfLineConfinementPoleDecay`: uniform disappearance of the full prime-and-pole remainder as unit-profile excess tends to zero (`exists_arithmeticRemainder_small_of_excess`).
- `HTGeometry/HardyBoundary/FourierFirstMomentWindow`: bounded physical first moment excludes uniform spectral concentration at zero.
- `ConfiningGammaSymbol`: exact logarithmic normalization, global lower bound, uniform dilation majorant, and transfer of Gamma integrability between Fourier normalizations.
- `ConfiningGammaSpectralLimit`: vanishing integrated remainder on fixed logarithmic profiles and uniform lower comparison under a bounded first moment.
- `HTGeometry/HardyBoundary/UnitaryRealDilation`: mass preservation, first-moment scaling, and weighted physical/Fourier changes of variables with integrability transfer.
- `HTGeometry/HardyBoundary/LogarithmicFourierDomain`: integrability of the logarithmic singularity at zero and two-way comparison with logarithmically growing symbols.
- `HTGeometry/HardyBoundary/LogarithmicFourierDilation`: absolute logarithmic domain invariance and the exact signed-energy scaling law.
- `SoftLogarithmicHalfLineDomain`: actual-domain inclusion, invariance under positive dilation, and eventual recovery of the actual Gamma domain after compression.
- `ConfiningPotentialLimit`: compression linearizes the exponential excess to eight times the physical first moment, by an exponential-moment majorant.
- `ConfiningFixedTrialLimit`: exact dilated Gamma decomposition and convergence of every fixed unit trial's renormalized full energy to the logarithmic-plus-linear form.
- `ConfiningLogarithmicFloor`: the limiting Rayleigh set is nonempty and bounded below; fixed trials give the uniform eventual upper comparison with its infimum.
- `ConfiningRescaledEnergy`: exact minimizing energy decomposition, nonnegative potential error, and a uniform lower bound tending to zero for the combined spectral and arithmetic remainder.
- `ConfiningLogarithmicLimit`: convergence of the renormalized ground energy to the universal floor, with uniform vanishing of both logarithmic energy excess and potential-linearization error for all minimizers.

- `ConfiningVirialLimit`: affine secants force `a(W-1)→1`; the potential error then gives scaled first moment `1/8`. `universal_softLogarithmic_confinement_limit` assembles all four uniform conclusions.

The final theorem has no added analytic premises. Its plain source audit is warning-free. No olean is generated for the final module because no written leaf imports it.
