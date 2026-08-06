# Clock probes for smooth potentials: the hyperbolic route

- **ID:** `hyperbolic-clock-probe-smooth-potential`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / HYPERBOLIC PDE / CLOCKS
- **Parent:** `new_scientific_knowledge/clocks/two-species-conformal-clock-scale-law.md`
- **Status:** **closed.** The open core of the parent card is discharged: clock probes are
  constructed, unconditionally in Lean, for *every* smooth potential on spacetime — no analyticity,
  no decay, no smallness, no time-independence — in every dimension, and with them the parent's
  two-species scale law for an arbitrary smooth conformal factor. The original obstruction stands:
  `ClockCharacteristicIllPosed.lean` shows the characteristic route cannot reach smooth data, so the
  construction below solves the Cauchy problem on the frequency side instead.

## What has to be built

mathlib turned out to have far more than expected — `Mathlib/Analysis/Distribution/` contains
tempered distributions, Fourier multipliers, Bessel potentials and the Sobolev spaces `H^{s,p}`,
including `MemSobolev.fourierMultiplierCLM_of_bounded` (a **bounded** multiplier preserves `H^s`).
That is exactly the energy estimate for a propagator, so the missing pieces are:

1. **The Klein–Gordon symbols have temperate growth.** `cos(t⟨ξ⟩)` and `sin(t⟨ξ⟩)/⟨ξ⟩` with
   `⟨ξ⟩ = √(1 + 4π²‖ξ‖²)`. The square root is harmless here — unlike `‖ξ‖`, the argument is bounded
   below by `1`, so the composition is smooth; what needs work is the polynomial bound on *all*
   iterated derivatives. mathlib's `hasTemperateGrowth_one_add_norm_sq_rpow` is the model proof
   (`HasTemperateGrowth.comp'` on `t = {y | 1/2 < y}`).
2. **The free propagator solves the free equation**: differentiating the multiplier family in `t`
   inside the distributional pairing.
3. **The Duhamel/Volterra step** — *done*, see below.
4. **Sobolev embedding to `C²`** and the probe normalisation `u(x₀) = 1`, `u ≠ 0` nearby.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/VolterraLinearIntegralEquation.lean` — step 3, the abstract
half of the evolution, **complete**:

- `volterraIterate` — the Picard iterates of `u(t) = f(t) + ∫₀^t K(t,s) u(s) ds` in a Banach space;
- **`continuous_volterraIterate`** — each iterate is continuous, by the parametric-integral
  continuity theorem with a variable upper limit;
- **`norm_volterraIterate_succ_sub_le`** — *the factorial estimate*: with `‖K(t,s)‖ ≤ M` and
  `‖f‖ ≤ F`, consecutive iterates differ by at most `F Mⁿ⁺¹ |t|ⁿ⁺¹/(n+1)!`;
- `summable_volterraBound`, `summable_volterraIncrements`, `volterraSolution`,
  **`tendsto_volterraIterate`** — the increments are summable at every time, being a tail of the
  exponential series, so the iterates converge; the solution is their sum;
- **`continuous_volterraSolution`** — the solution is continuous, by the Weierstrass test on every
  bounded time interval (the bound is `t`-dependent, so the test is applied locally and continuity
  is deduced at each point from a neighbourhood);
- **`norm_volterraIterate_le`** — every iterate is bounded by `F e^{M|t|}`, uniformly in the index.
  This is the dominating function the next step needs;
- **`volterraSolution_eq`** — *the solution satisfies the equation*, by dominated convergence under
  the integral with that constant bound;
- **`volterra_eq_of_eq_of_eq`** — and it is the only continuous solution: the difference of two
  solutions is bounded by `W (M|t|)ⁿ/n!` for every `n`, and the factorial wins.

This is what makes the Volterra equation solvable with **no smallness hypothesis**: each iteration
integrates one more power of the time variable, and the factorial beats the geometric factor. It is
the linear case of Picard–Lindelöf with a two-variable kernel, which mathlib does not have.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSymbol.lean` — step 1, **the energy estimate**:

- **`hasTemperateGrowth_realCos`**, **`hasTemperateGrowth_realSin`** — the sine and the cosine have
  temperate growth. mathlib does not have these; they are the model case of a smooth function all of
  whose derivatives are bounded, and the proof is the even/odd closed form of the iterated
  derivatives together with `norm_iteratedFDeriv_eq_norm_iteratedDeriv`;
- `kgFreq`, `one_le_kgFreq`, `kgFreq_eq_rpow`, **`hasTemperateGrowth_kgFreq`**,
  **`hasTemperateGrowth_kgFreq_inv`** — the Klein–Gordon frequency `⟨ξ⟩ = √(1+‖ξ‖²)` and its
  inverse, both of temperate growth, as instances of mathlib's
  `hasTemperateGrowth_one_add_norm_sq_rpow` at `r = ±1/2`;
- `kgCosSymbol`, `kgSinSymbol`, **`hasTemperateGrowth_kgCosSymbol`**,
  **`hasTemperateGrowth_kgSinSymbol`** — the two propagator symbols. Composing `cos` with `t⟨ξ⟩`
  needs only `HasTemperateGrowth.comp`, *because* the frequency is the Klein–Gordon one: with the
  wave frequency `‖ξ‖` the composition is not smooth at the origin and the restricted-set version
  `comp'` with iterated-derivative bounds would be needed instead;
- **`norm_kgCosSymbol_le`** (`≤ 1`), **`norm_kgSinSymbol_le`** (`≤ |t|`) — both symbols are bounded;
- **`memSobolev_kgCosSymbol`**, **`memSobolev_kgSinSymbol`** — *hence each propagator preserves every
  Sobolev space*, which is the energy estimate of the free Klein–Gordon evolution.

Axioms: `[propext, Classical.choice, Quot.sound]`.

Note for the next step: `MemSobolev.fourierMultiplierCLM_of_bounded` lives in a section with
`[InnerProductSpace ℂ F] [CompleteSpace F]`; stating it with only `[NormedSpace ℂ F]` makes
elaboration diverge rather than fail, which costs a heartbeat timeout to diagnose.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSymbolEvolution.lean` — step 2, **the symbols
solve the equation**:

- `hasDerivAt_cosFreq`, `hasDerivAt_sinFreq`, **`hasDerivAt_sincFreq`** — the time derivatives:
  `∂ₜcos(t⟨ξ⟩) = -⟨ξ⟩sin(t⟨ξ⟩)` and `∂ₜ(sin(t⟨ξ⟩)/⟨ξ⟩) = cos(t⟨ξ⟩)`;
- **`hasDerivAt_deriv_cosFreq`**, **`hasDerivAt_deriv_sincFreq`** — and both symbols satisfy the
  oscillator equation `∂ₜ²û = -⟨ξ⟩²û`, frequency by frequency;
- `hasDerivAt_kgCosSymbol`, `hasDerivAt_kgSinSymbol`, **`hasDerivAt_deriv_kgCosSymbol`**,
  **`hasDerivAt_deriv_kgSinSymbol`** — the same in the complex form the multiplier calculus uses;
- `kgCosSymbol_zero`, `kgSinSymbol_zero`, **`deriv_kgCosSymbol_zero`**,
  **`deriv_kgSinSymbol_zero`** — the four initial conditions, so the pair is the fundamental system:
  the cosine carries the initial value and starts at rest, the sine starts at zero with unit
  velocity.

With mathlib's Fourier convention `⟨ξ⟩² = 1 + ‖ξ‖²` is the symbol of `1 - (2π)⁻²Δ`, so the
oscillator equation above *is* the Klein–Gordon equation of the physical field, frequency by
frequency.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSynthesis.lean` — the symbol evolution lifted
through the frequency integral:

- **`hasDerivAt_integral_symbol`** — differentiation under a symbol integral: if the symbol is
  differentiable in the parameter with derivative dominated by `g`, and `g` times the density is
  integrable, the integral is differentiable with the expected derivative. This is mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` packaged for a symbol-times-density integrand;
- `continuous_kgFreq` and the continuity of the three symbol families in the frequency;
- **`hasDerivAt_kgSynthesis`**, **`hasDerivAt_deriv_kgSynthesis`** — hence the synthesis
  `u(t) = ∫ cos(t⟨ξ⟩) h(ξ) dξ` is twice differentiable in time and satisfies
  `∂ₜ²u = -∫ ⟨ξ⟩² cos(t⟨ξ⟩) h(ξ) dξ`.

The hypotheses are exactly the right ones: the `k`-th time derivative of the symbol costs a factor
`⟨ξ⟩^k`, so what is needed is the integrability of `⟨ξ⟩^k` times the density — which every Schwartz
density satisfies for every `k`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonOperator.lean` — what the frequency squared is on
the physical side:

- `kgFreq_sq` — `⟨ξ⟩² = 1 + ‖ξ‖²`;
- **`fourierMultiplierCLM_kgFreqSq`** — hence, for a Schwartz function,
  `𝓕⁻(⟨ξ⟩² 𝓕f) = f - (2π)⁻² Δ f`: *the Klein–Gordon multiplier is the Klein–Gordon operator* of unit
  mass, in the convention mathlib's Fourier transform imposes. The proof splits the symbol as
  `1 + ‖ξ‖²` through `fourierMultiplierCLM_sum`, uses `fourierMultiplierCLM_const` on the first
  summand and mathlib's `laplacian_eq_fourierMultiplierCLM` on the second.

So the oscillator equation `∂ₜ²û = -⟨ξ⟩²û` proved for the symbols is the Klein–Gordon equation
`∂ₜ²u = (2π)⁻²Δu - u` of the field, and the three pieces — energy estimate, symbol evolution,
Laplacian identification — now speak about the same operator.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonFreeSolution.lean` — the free evolution of a
Schwartz datum:

- `kgFree`, `kgFreeVel` — the two propagators applied to a Schwartz function, again Schwartz;
- **`kgFree_zero`**, **`kgFreeVel_zero`** — the evolution starts at the datum, the velocity evolution
  at zero;
- **`kgOperator_kgFree`** — the Klein–Gordon operator applied to the free evolution *is* the
  multiplier with symbol `⟨ξ⟩² cos(t⟨ξ⟩)`:
  `kgFree f t - (2π)⁻²Δ(kgFree f t) = 𝓕⁻(⟨ξ⟩²cos(t⟨ξ⟩)𝓕f)`.

Since the symbols satisfy `∂ₜ²cos(t⟨ξ⟩) = -⟨ξ⟩²cos(t⟨ξ⟩)`, the spatial side of the field equation
and the second time derivative are now the *same multiplier up to sign* — which is the free
Klein–Gordon equation, expressed entirely in the multiplier calculus, with no integral bookkeeping.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonPointwise.lean` — the bridge from operators to
integrals:

- **`coe_fourierMultiplierCLM`** — a Fourier multiplier is the inverse transform of the product of
  symbol and transform, *as a function*: `⇑(fourierMultiplierCLM F g f) = 𝓕⁻(fun ξ => g ξ • 𝓕f ξ)`.
  `fourierInv_coe` turns the Schwartz-level inverse transform into the function-level one, which
  `fourierInv_eq` unfolds to `∫ ξ, 𝐞⟪ξ,x⟫ • …`;
- **`coe_kgFree`**, **`coe_kgFreeVel`** — the two evolutions as inverse Fourier integrals;
- **`coe_kgOperator_kgFree`** — and the Klein–Gordon operator applied to the free evolution is the
  inverse transform of `⟨ξ⟩²cos(t⟨ξ⟩)𝓕f`.

Every piece of the free evolution is now available in both languages: as an identity of operators on
Schwartz functions, and as an integral against the frequency variable — which is the form the
synthesis lemmas differentiate in time.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonClassical.lean` — **the free evolution is a
classical solution**:

- `kgDensity`, `norm_kgDensity`, `continuous_kgChar` — the frequency density `𝐞⟪ξ,x⟫ 𝓕f ξ` of the
  evolution at a fixed point of space, of the same modulus as the transform;
- **`integrable_weight_kgDensity`** — every frequency weight `⟨ξ⟩ᵏ` is integrable against it, because
  `⟨ξ⟩ᵏ` has temperate growth and therefore `⟨ξ⟩ᵏ 𝓕f` is again Schwartz, hence integrable;
- `kgFree_apply_eq_synthesis`, `kgOperator_kgFree_apply_eq_synthesis` — the evolution and the
  Klein–Gordon operator applied to it, at a fixed point, are syntheses of the density;
- **`hasDerivAt_kgFree_apply`**, **`hasDerivAt_deriv_kgFree_apply`** — hence, for every Schwartz
  datum and every point,

  `∂ₜ²u(t, x) = (2π)⁻²Δu(t, x) - u(t, x)`,

  the free Klein–Gordon equation *classically*, as an identity of real numbers at every event, not
  merely of Schwartz functions or of distributions.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## The route to a variable potential: the weighted Wiener algebra

The remaining step is the potential. The natural functional setting — `H^s` — is not available: what
mathlib has is the *predicate* `MemSobolev` on tempered distributions, with no Banach space to run
the Volterra iteration in, and building one requires Minkowski's integral inequality and an `Lp`
multiplication calculus.

The cheaper setting, and the one this card now takes, is the **weighted Wiener algebra on the
frequency side**:

`A_k = { û : ∫ ⟨ξ⟩ᵏ |û(ξ)| dξ < ∞ }`, i.e. `L¹` of the measure `⟨ξ⟩ᵏ dξ`, a Banach space.

Everything the construction needs is elementary there:

1. the propagators act by multiplication with `cos(t⟨ξ⟩)` and `sin(t⟨ξ⟩)/⟨ξ⟩`, both bounded by `1` in
   modulus, hence are contractions of `A_k` — no energy estimate, no Plancherel;
2. multiplication by the potential acts by convolution with `𝓕V`, and `A_k` is a **Banach algebra**
   under convolution by Peetre's inequality `⟨ξ⟩ᵏ ≤ 2^{k/2} ⟨ξ-η⟩ᵏ ⟨η⟩ᵏ` and Tonelli — this is the
   one estimate the whole potential theory rests on, and in weighted `L¹` it is Young's inequality
   for `L¹ ⋆ L¹ → L¹`, which mathlib has;
3. the potential may be cut off: a probe solving `□u + (χV)u = 0` solves `□u + Vu = 0` wherever
   `χ = 1`, and `χV` is smooth with compact support, hence Schwartz, hence `𝓕(χV) ∈ A_k` for every
   `k` — so *any* smooth potential is admissible;
4. the Duhamel kernel `K(t,s) = (multiplication by sin((t-s)⟨ξ⟩)/⟨ξ⟩) ∘ (convolution by 𝓕V)` is
   therefore a uniformly bounded family of operators on `A_k`, and `VolterraLinearIntegralEquation`
   solves the integral equation with no smallness hypothesis;
5. `k ≥ 2` gives a classical solution: the synthesis of an element of `A_k` is `C²`, by the
   parametric-integral lemmas already proved, and `‖u(t,·) - u(0,·)‖_∞ ≤ ‖û(t,·) - û(0,·)‖_{A_0}`
   gives the probe normalisation `u ≠ 0` near the event by continuity in `t`.

The conformal clock problem is exactly this case: by Theorem 1 of the parent card the operator on a
chart is `□_g + V` with `□_g` the *flat* d'Alembertian — the principal part has constant
coefficients, and only the zeroth-order term varies.

## Lean status of the Wiener layer

`formal/GaloisForLFunctions/HTGeometry/WienerWeightedMeasure.lean` — the weight and its inequality:

- **`kgFreq_sq_le_peetre`**, **`kgFreq_le_peetre`**, **`kgFreq_pow_le_peetre`** — *Peetre's
  inequality* `⟨ξ⟩ ≤ √2 ⟨ξ-η⟩⟨η⟩` and its `k`-th power. The proof is the triangle inequality
  followed by `1 + (a+b)² ≤ 2(1+a²)(1+b²)`, which is `(a-b)² + 1 + 2a²b² ≥ 0`;
- `kgWeight`, `wienerMeasure`, **`integrable_wienerMeasure_iff`** — the weighted frequency measure
  `⟨ξ⟩ᵏ dξ` and the identification of its integrable functions.

`formal/GaloisForLFunctions/HTGeometry/WienerConvolutionOperator.lean` — **convolution is bounded**:

- `WienerDensity` — a measurable density integrable against the weight of order `N`, with its
  weighted `L¹` norm `norm'`;
- `kgConvIntegrand`, **`norm_kgConvIntegrand_le`** — the integrand of the weighted convolution and
  its pointwise bound, which is exactly Peetre's inequality after dividing by `⟨ξ-η⟩ᴺ`;
- `integrable_kgConvIntegrand`, `continuous_kgConv`, `norm_kgConv_le` — the convolution exists, is
  continuous (dominated convergence with a bound independent of `ξ`) and is bounded;
- **`kgConvCLM`**, **`norm_kgConvCLM_le`** — hence *convolution by an admissible density is a
  bounded operator* on the space of bounded continuous functions, of norm at most
  `√2ᴺ ∫ ⟨η⟩ᴺ|a(η)|dη`.

The space is the *weighted sup-norm* space rather than the weighted `L¹` space: an element is a
bounded continuous `G` standing for the density `⟨ξ⟩⁻ᴺG(ξ)`. Completeness is then free — the space
*is* `E →ᵇ ℂ` — and the convolution estimate needs no Fubini and no `Lᵖ` quotient, only the triangle
inequality for the integral.

`formal/GaloisForLFunctions/HTGeometry/WienerSymbolMultiplication.lean` — **the propagators**:

- `kgMulCLM`, `norm_kgMulCLM_le`, `norm_kgMulCLM_sub_le` — multiplication by a bounded continuous
  symbol, which is multiplication in the ring `E →ᵇ ℂ`, so the operator bound is automatic;
- `kgSincBCF`, `kgCoscBCF`, `norm_kgSincBCF_le`, `norm_kgCoscBCF_le` — the damped propagator symbols
  `sin(t⟨ξ⟩)/⟨ξ⟩` and `cos(t⟨ξ⟩)/⟨ξ⟩`, both bounded by `1` *for every time*;
- **`norm_kgSincBCF_sub_le`**, **`norm_kgCoscBCF_sub_le`**, `continuous_kgSincBCF`,
  `continuous_kgCoscBCF` — and both are Lipschitz in time with constant `1`, uniformly in the
  frequency.

The undamped symbol `cos(t⟨ξ⟩)` is *not* continuous in `t` for the supremum norm — the phase moves at
speed `⟨ξ⟩`, so the supremum of `|cos(t⟨ξ⟩) - cos(t'⟨ξ⟩)|` is `2` for every `t ≠ t'`. Dividing by the
frequency repairs exactly this. One power of the weight buys uniform continuity in time, and that is
the whole regularity bookkeeping of the evolution.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonPotentialFlow.lean` — **the evolution exists**:

- `kgDuhamelKernel`, **`norm_kgDuhamelKernel_le`**, `continuous_kgDuhamelKernel` — the Duhamel
  kernel `K(t,s) = (multiplication by sin((t-s)⟨ξ⟩)/⟨ξ⟩) ∘ (convolution by 𝓕V)`, uniformly bounded
  on the *whole* time axis by `√2ᴺ‖𝓕V‖`, and continuous in `(t,s)` in the operator norm;
- `kgFreeTerm`, `norm_kgFreeTerm_le`, `continuous_kgFreeTerm` — the free term;
- **`kgPotentialFlow`**, **`kgPotentialFlow_eq`**, **`kgPotentialFlow_zero`**,
  **`kgPotentialFlow_unique`**, `continuous_kgPotentialFlow` — hence the Klein–Gordon evolution with
  a potential exists on the frequency side, globally in time, with no smallness hypothesis, and is
  the unique continuous solution of the Duhamel equation.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/DuhamelScalarOscillator.lean` — **the driven oscillator**:

- `duhamelCosPart`, `duhamelSinPart`, `hasDerivAt_duhamelCosPart`, `hasDerivAt_duhamelSinPart` — the
  two moments of the source and their derivatives, by the fundamental theorem of calculus;
- **`duhamelScalar_eq`** — the addition formula `sin((t-s)ω) = sin(tω)cos(sω) - cos(tω)sin(sω)`
  separates the time parameter from the integration variable, so the Duhamel integral becomes a
  combination of two integrals whose integrands do not depend on `t`;
- **`hasDerivAt_duhamelScalar`** — the first derivative, in which the two source terms produced by
  the moments cancel exactly;
- **`hasDerivAt_deriv_duhamelScalar`** — and the second: `u'' = -ω²u + h`. The Pythagorean identity
  is what returns the source, once.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonFlowPointwise.lean` — **the equation at every
frequency**:

- `kgFlowSource`, `continuous_kgFlowSource` — the potential term of the evolution at a fixed
  frequency;
- **`kgPotentialFlow_apply_eq_duhamel`** — evaluation at a frequency turns the Banach-space Duhamel
  equation into the scalar one, because evaluation is a continuous linear map and commutes with the
  Bochner integral in time;
- **`hasDerivAt_kgPotentialFlow_apply`**, **`hasDerivAt_deriv_kgPotentialFlow_apply`** — hence, at
  every frequency,

  `∂ₜ²û(t,ξ) = -⟨ξ⟩²û(t,ξ) + 𝓕(Vu(t))(ξ)`,

  globally in time, for any potential whose transform is integrable against the weight.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisDensity.lean` — **the weight beats the
dimension**:

- **`integrable_kgFreq_inv_pow`** — `⟨ξ⟩⁻ᵐ` is integrable as soon as `dim E < m`, from mathlib's
  Japanese-bracket estimate;
- `kgWeighted`, `norm_kgWeighted_le`, `continuous_kgWeighted` — the density represented by a weighted
  datum;
- **`integrable_kgFreq_pow_mul_kgWeighted`**, **`integrable_kgFreq_pow_mul_inv_pow`** — hence `j`
  derivatives may be taken under the synthesis integral whenever `dim E + j < N`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonFlowBounds.lean` — **uniform bounds**:

- `norm_duhamelCosPart_le`, `norm_duhamelSinPart_le` — the moments of a bounded source are bounded by
  the length of the time interval;
- **`norm_kgPotentialFlow_le`** (and `norm_volterraSolution_le`, added to the Volterra module) — the
  evolution obeys the Volterra bound `‖G₀‖e^{M|t|}`;
- **`norm_deriv_kgPotentialFlow_apply_le`**, **`norm_deriv_deriv_kgPotentialFlow_apply_le`** and
  their versions uniform on a time interval — the first two time derivatives of the evolution are
  bounded *uniformly in the frequency*, the second one costing exactly `⟨ξ⟩²`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSynthesisField.lean` — **the field**:

- **`aestronglyMeasurable_deriv_param`** — the derivative of a continuous family is measurable, being
  a pointwise limit of difference quotients. This avoids any joint-continuity argument;
- `kgChar`, `kgFlowDensity`, `kgFlowDensityDeriv`, `kgFlowDensityDeriv2`, **`kgFlowField`** — the
  synthesis of the evolution against the character, and its two frequency-side time derivatives;
- `kgFlowDensityDeriv2_eq`, `continuous_kgFlowDensityDeriv2` — the second derivative read off the
  oscillator equation, hence continuous in the frequency;
- **`hasDerivAt_kgFlowField`**, **`hasDerivAt_deriv_kgFlowField`** — the field is twice
  differentiable in time at every point of space, with both derivatives taken under the frequency
  integral by dominated convergence.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisSpace.lean` — **the space derivatives**:

- `kgSynthesis`, `kgChar_eq_cexp`, **`hasDerivAt_kgChar_dir`** — the character along a line, and its
  derivative `2πi⟪ξ,v⟫`;
- `norm_inner_le_kgFreq` — the factor is dominated by `2π‖v‖⟨ξ⟩`;
- **`hasDerivAt_kgSynthesis_dir`**, **`hasDerivAt_deriv_kgSynthesis_dir`** — hence the synthesis is
  twice differentiable in every spatial direction, both derivatives taken under the integral. Unlike
  the time derivatives the bound is global in the parameter.

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisLaplacian.lean` — **the Laplacian**:

- `sum_sq_real_inner` — Parseval for an orthonormal basis in real form;
- **`sum_integral_dirSq`** — summing the second directional derivatives over an orthonormal basis
  gives the synthesis of `-4π²‖ξ‖²`.

`formal/GaloisForLFunctions/HTGeometry/WienerPotentialProduct.lean` — **convolution is
multiplication**:

- `kgChar_add` — the character turns addition into multiplication;
- **`integral_kgChar_mul_convolution`** — the synthesis of a convolution is the product of the
  syntheses, by Fubini (mathlib's `Integrable.convolution_integrand` supplies the product
  integrability) and the translation invariance of the measure.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonPotentialWave.lean` — **the equation**:

- `kgPotential` — the potential attached to a convolving density, its inverse Fourier transform;
- `kgWeighted_kgConvBCF` — the convolution operator read on the density itself;
- `deriv_deriv_kgFlowField_dir` — the second spatial derivative of the field along a direction;
- **`kgFlowField_wave_equation`** — for every admissible density `a`, every datum `G₀`, every
  orthonormal basis, every time and every point:

  `∂ₜ²u(t,x) = (2π)⁻² Δu(t,x) - u(t,x) + V(x)·u(t,x)`,

  where `Δ` is the sum of the second derivatives along the basis and `V = 𝓕⁻a`. This is the
  Klein–Gordon equation with a potential, **classically**, globally in time, with no smallness
  hypothesis and no analyticity anywhere.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonProbeNormalization.lean` — **the probe does not
vanish**:

- `kgConjChar` — the datum concentrated at an event: the conjugate of the character;
- **`kgFlowField_zero_apply`** — at `t = 0` the character of the synthesis and the datum cancel, so
  the field at the event is `∫ ⟨ξ⟩⁻ᴺ⁻¹ dξ`;
- **`kgFlowField_zero_ne_zero`** — a positive real number, hence nonzero;
- **`continuousAt_kgFlowField`** — the field is continuous in the event, jointly in time and space,
  by dominated convergence with the Volterra bound;
- **`eventually_kgFlowField_ne_zero`** — hence the probe is nonzero on a whole spacetime
  neighbourhood of the event.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisMixed.lean` — **mixed derivatives**:

- `kgDirDensity`, `norm_kgDirDensity_le`, and the integrability transfers — a spatial derivative
  multiplies the density by `2πi⟪ξ,v⟫`, which costs exactly one power of the weight;
- **`hasDerivAt_kgSynthesis_dir_synthesis`** — the directional derivative of a synthesis *is* the
  synthesis of the derived density;
- **`hasDerivAt_kgSynthesis_dir_dir`** — hence the mixed second derivatives, with no new analysis:
  the first-derivative theorem applied to the derived density.

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisContinuity.lean` — **continuity in the
event**:

- **`continuous_kgSynthesis_param`** — a family of densities that is continuous in the frequency,
  continuous in time, and dominated on each time interval by a multiple of the weight has a jointly
  continuous synthesis. Every synthesis of the construction — the field and each of its derivatives
  — is of this shape;
- `norm_kgDirDensity_le_weight` — the derived densities are again dominated, with one power spent.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonRealProbe.lean` — **the real probe**:

- `IsRealDensity`, `kgChar_neg`, **`conj_kgPotential`**, `kgPotential_im` — the potential is real
  exactly when the density satisfies `a(-η) = conj a(η)`, by the substitution `η ↦ -η`;
- `hasDerivAt_re`, `deriv_re_eq`, `deriv_deriv_re_eq` — the real part commutes with the derivatives;
- `kgRealField`, and the differentiability lemmas in time and in each direction;
- **`kgRealField_wave_equation`** — the real part solves the same equation with the real potential;
- **`kgRealField_zero_pos`**, **`eventually_kgRealField_ne_zero`** — it is positive at the event and
  nonzero on a neighbourhood.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonUnitSpeed.lean` — **unit propagation speed**:

- **`deriv_deriv_kgFlowField_dir_smul`** — a second directional derivative scales quadratically;
- **`kgFlowField_wave_equation_unit`**, **`kgRealField_wave_equation_unit`** — measuring the spatial
  derivatives along `(2π)⁻¹eᵢ` clears the Fourier convention's constant:

  `∂ₜ²u = Δu - u + Vu`,

  which is the corpus's wave operator with signature `(-1, 1, …, 1)` and potential `V - 1`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonChartLift.lean` — **the spacetime chart**:

- `kgDir`, `kgDir_eq_basisFun` — the chart's spatial directions are the standard orthonormal basis;
- `kgSpatial`, **`kgSpatial_update_zero`**, **`kgSpatial_update_succ`** — moving one chart coordinate
  moves either the time or exactly one spatial direction, by `(2π)⁻¹` times the standard vector;
- `kgChartField`, `kgChartField_update_zero`, `kgChartField_update_succ` — the real probe read in
  coordinates.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonChartPartials.lean` — **the coordinate
derivatives**:

- `kgChartTimePartial`, `kgChartSpacePartial`, `kgChartPartial` — the partial derivatives of the
  chart field, indexed by the chart coordinates through `Fin.cases`;
- **`hasDerivAt_kgChartField_update`** — for every coordinate `j` and every point,
  `r ↦ u(update y j r)` is differentiable with the expected derivative. The zeroth coordinate is the
  time derivative; a spatial coordinate is the derivative along the rescaled direction, translated so
  that the parameter starts at the current value of the coordinate.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonFlowJointContinuity.lean` — **joint
continuity**:

- **`continuous_kgFlowSource_pair`** — the source is jointly continuous in frequency and time,
  because it is the evaluation of a continuous curve of bounded continuous functions and evaluation
  is jointly continuous for the supremum norm;
- `continuous_duhamelCosPart_pair`, `continuous_duhamelSinPart_pair` — hence so are the moments, by
  the parametric-interval-integral continuity theorem;
- **`continuous_deriv_kgPotentialFlow_pair`**, **`continuous_kgFlowDensityDeriv_pair`** — hence the
  time derivative of the evolution, and its density, are jointly continuous.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonChartC1.lean` — **the chart field is `C¹`**:

- `continuous_kgSynthesis_flowDensityDeriv`, `continuous_kgSynthesis_dirDensity` — the two syntheses
  occurring as partial derivatives are continuous in the event;
- `kgChartTimePartial_eq`, `kgChartSpacePartial_eq` — each chart partial is the real part of one of
  them;
- **`continuous_kgChartPartial`**, **`isC1OnPi_kgChartField`**, **`hasFDerivAt_kgChartField`** — so
  the chart field has continuous partials everywhere and is differentiable, by the corpus's own
  instrument `hasFDerivAt_of_isC1OnPi`;
- **`coordPartial_kgChartField`** — and its `coordPartial`s are the computed partials. *This is the
  bridge into the corpus's coordinate calculus.*

`formal/GaloisForLFunctions/HTGeometry/WienerSynthesisTimeDeriv.lean` — **differentiating a
synthesis in time, in general**:

- **`hasDerivAt_kgSynthesis_time`** — a family of densities differentiable in time, dominated by the
  weight uniformly on each time interval, has a synthesis differentiable in time with the derivative
  under the integral. This is the step the second-order calculus repeats for every first partial.

Axioms: `[propext, Classical.choice, Quot.sound]`.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonChartGeneric.lean`,
`KleinGordonChartFamilies.lean`, `KleinGordonChartSecond.lean` — **the second-order chart
calculus**:

- `kgChartOf` — every object read in the chart is the real part of the synthesis of a density
  family, evaluated at the chart point; **`continuous_kgChartOf`**,
  **`hasDerivAt_kgChartOf_zero`**, **`hasDerivAt_kgChartOf_succ`** prove once and for all what such
  an object needs;
- the weight bookkeeping of the three families: the time derivative costs nothing (the Volterra
  bound is uniform in the frequency), a spatial derivative costs one power, the second time
  derivative costs two — so a weight exceeding the dimension by two carries the whole calculus;
- **`isC1OnPi_kgChartTimePartial`**, **`isC1OnPi_kgChartSpacePartial`**,
  **`differentiableAt_coordPartial_kgChartField`** — each first partial has continuous partials of
  its own (mixed included), hence is differentiable: the hypothesis of the divergence-form
  d'Alembertian.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonClockProbe.lean` — **the clock probe**:

- `kgEps`, `kgWaveOp` — the Minkowski signature and the corpus's wave operator on the chart;
- `kgChartPotential` — the potential `V - 1`;
- `coordPartial_coordPartial_zero`, `coordPartial_coordPartial_succ` — the pure second coordinate
  derivatives are the objects the field equation relates;
- **`kgWaveOp_kgChartField`** — hence

  `□u + (V - 1)u = 0` at every event,

  with `□` the corpus's `SmoothPseudoMetric.ofSignature` d'Alembertian;
- **`solvesPotentialWaveOn_kgChartField`** — `SolvesPotentialWaveOn` on any region;
- `kgChartEvent`, `eventually_kgChartField_ne_zero`, and
  **`exists_localProbesOn_kgChartPotential`** — around any prescribed event there is an open region
  on which the field is a clock probe: **`LocalProbesOn (kgWaveOp d) (kgChartPotential a) region`**.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## What is proved, and what is left

The hyperbolic route is **closed for static potentials**: for every real density `a` admissible at a
weight exceeding the dimension by two, the potential `V = 𝓕⁻a` — an arbitrary smooth function of
space with enough decay — admits clock probes near every event, unconditionally, with no analyticity
and no smallness hypothesis. That is exactly the object the parent card's open core asks for, in the
time-independent case.

What remains is the **time-dependent** potential, which the conformal application needs (the
conformal potential `V = μe^{2σ} - a□σ - a²⟨dσ,dσ⟩` depends on all coordinates when `σ` does). The
extension is structural rather than conceptual: the Duhamel kernel already has *two* time arguments
in `VolterraLinearIntegralEquation`, so it suffices to replace the fixed convolver `kgConvCLM a` by a
family `t ↦ kgConvCLM (a t)` with a uniform norm bound and continuity in `t`, and to carry that
family through the flow, the source, and the bounds. Everything downstream — the synthesis, the
chart calculus, the probe — is stated for a general density family and applies verbatim.

`formal/GaloisForLFunctions/HTGeometry/WienerDensityFamily.lean` — **the moving convolver**:

- `integrable_weight_sub`, **`norm_kgConvCLM_sub_le`** — convolution is linear in the density, so the
  operator norm of a difference of convolvers is bounded by the weighted `L¹` norm of the difference
  of the densities;
- `WienerFamily` — a curve of densities with a uniform weighted bound and a Lipschitz modulus;
- **`WienerFamily.norm_convCLM_le`**, **`WienerFamily.continuous_convCLM`** — hence the convolvers of
  a family are uniformly bounded and continuous in the operator norm.

The two modules that first carried the time-dependent flow separately
(`KleinGordonTimeDependentFlow`, `KleinGordonTimeDependentPointwise`) have been **absorbed into the
mainline**: the whole chain now takes a `WienerFamily` rather than a fixed density, and the static
case is the constant family — *definitionally*, since `kgPotentialFlow a.constFamily G₀` and the old
static flow are the same term. Nothing was duplicated.

What changed along the chain:

- `kgDuhamelKernel a t s = mult(sin((t-s)⟨ξ⟩)/⟨ξ⟩) ∘ conv(a.density s)` — the convolver is the one of
  the integration time; the uniform bound is `√2ᴺ·a.bound` and the operator-norm continuity comes
  from `WienerFamily.continuous_convCLM`;
- `kgFlowSource a G₀ ξ s = kgConv N (a.density s) (kgPotentialFlow a G₀ s) ξ`;
- **`kgFlowField_wave_equation`** now reads
  `∂ₜ²u(t,x) = (2π)⁻²Δu(t,x) - u(t,x) + V(t,x)·u(t,x)` with `V(t,·) = 𝓕⁻(a.density t)`;
- `IsRealFamily a := ∀ t, IsRealDensity (a.density t)` — the reality condition, time by time;
- **`kgChartPotential a y = (kgPotential (a.density (y 0)) (kgSpatial d y)).re - 1`** — the chart
  potential now depends on *all* spacetime coordinates.

## The result

```
exists_localProbesOn_kgChartPotential :
  ∀ {d N} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N),
    (finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N → IsRealFamily a →
    ∀ x₀, ∃ region, IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (kgWaveOp d) (kgChartPotential a) region
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

For every **time-dependent** real potential whose spatial transform is admissible at a weight
exceeding the dimension by two and moves Lipschitz-continuously in the weighted norm, the corpus's
wave operator with signature `(-1,1,…,1)` admits clock probes on a neighbourhood of any prescribed
event — unconditionally, with no analyticity, no smallness hypothesis and no restriction on the time
interval. That is the open core of the parent card.

## The class is inhabited

A hypothesis class asserts nothing until something satisfies it, so
`formal/GaloisForLFunctions/HTGeometry/KleinGordonProbeExamples.lean` exhibits the potentials the
construction covers:

- **`WienerDensity.ofCompactSupport`** — a continuous density of compact support is admissible at
  *every* weight; no decay estimate is needed, the weighted integrand is continuous with compact
  support;
- **`WienerFamily.ofModulation`** — multiplying such a density by a bounded Lipschitz function of
  time gives a family, with `bound = M‖a‖'` and `lip = L‖a‖'`;
- `isRealFamily_ofModulation` — and the family is real when the density is;
- `kgBump`, `kgBumpFun`, **`kgBumpDensity`**, `isRealDensity_kgBumpDensity` — a symmetrised bump
  function is such a density: real-valued and even, hence obeying the reality condition;
- **`kgPotential_kgBumpDensity_zero_pos`** — its potential is *positive at the origin*, so it is not
  the zero potential (the proof is `ContDiffBump.integral_pos` after the symmetrisation is undone by
  the negation-invariance of the measure);
- **`kgChartPotential_bump_timeAxis`** — along the time axis the chart potential is
  `g(t)·(∫bump) - 1`, an affine function of the modulation with a *positive* coefficient: it varies
  in time as soon as `g` does;
- **`exists_localProbesOn_bump`** — hence clock probes exist, explicitly, for a concrete
  time-dependent nonzero potential.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Every real Schwartz potential

The class is not just inhabited; it contains *every* Schwartz potential, with the chart potential
being literally the given function:

- **`integrable_kgFreq_pow_mul_schwartz`**, **`WienerDensity.ofSchwartz`** — a Schwartz function is a
  density at every weight (the weight has temperate growth, so `⟨η⟩ᴺψ` is again Schwartz);
- **`kgPotential_ofSchwartz_fourier`** — *the potential of the transform of a Schwartz function is
  the function itself*, by mathlib's Fourier inversion;
- **`isRealDensity_ofSchwartz_fourier`** — and the reality condition holds exactly when the function
  is real-valued, since conjugating the transform reflects the frequency;
- **`kgChartPotential_ofSchwartz`** — the chart potential is `V(x) - 1` for `V = φ`;
- **`exists_localProbesOn_schwartz`** — hence: *for every real Schwartz potential on space, clock
  probes exist near every event.* Every smooth compactly supported potential is of this kind, which
  is the form the conformal application produces after a spatial cutoff.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Time-dependent families, and a non-separable one

- **`WienerFamily.ofWeightedBounds`** — the general constructor: a curve of densities decaying like
  `⟨η⟩⁻ᴺ⁻ᵐ` uniformly in time and Lipschitz in time at that rate is an admissible family, with
  `bound = M∫⟨η⟩⁻ᵐ` and `lip = L∫⟨η⟩⁻ᵐ`. The two supporting estimates
  (`integrable_weight_of_pointwise`, `integral_weight_le_of_pointwise`) turn a pointwise weighted
  bound into the weighted `L¹` data the family asks for;
- `kgWaveDensity`, **`kgWaveFamily`**, `isRealFamily_kgWaveFamily` — an instance whose time
  dependence is *frequency dependent*, `⟨η⟩⁻ᴺ⁻ᵐ⁻¹cos(t⟨η⟩)`: the potential it defines is **not** a
  product of a function of time and a function of space, so the class is not confined to separable
  potentials;
- **`exists_localProbesOn_wave`** — clock probes for that non-separable time-dependent potential.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## A probe at every event: the corpus's `OpenProbes`

`formal/GaloisForLFunctions/HTGeometry/KleinGordonProbeAnywhere.lean` removes the last restriction —
the construction normalises the field at time zero, so on its own it produces probes near one time
slice:

- `hasFDerivAt_comp_add_const`, `coordPartial_comp_add_const`, `coordPartial_sq_comp_add_const` —
  **coordinate derivatives are translation invariant** (the corpus had avoided needing this; here it
  is proved);
- **`kgWaveOp_comp_add_const`** — hence so is the wave operator;
- `WienerFamily.timeShift`, `isRealFamily_timeShift`, **`kgChartPotential_timeShift`** — shifting the
  potential in time and composing the field with the inverse shift returns the *same* potential;
- **`openProbes_kgChartPotential`**:

  ```
  ∀ {d N} (A : WienerFamily (EuclideanSpace ℝ (Fin d)) N),
    (finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N → IsRealFamily A →
      OpenProbes (kgWaveOp d) (kgChartPotential A)
  ```

`OpenProbes` is the corpus's own interface — a probe on an open neighbourhood of *every* event,
nonvanishing throughout it — and it is exactly what `scale_reconstruction_of_openProbes`, the
two-species scale law of the parent card, consumes.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Localisation, and every smooth static potential

- **`openProbes_of_locally_kgChartPotential`** — probes are a *local* matter: a potential that agrees
  near every event with the potential of *some* admissible family has probes on open regions. This
  is what removes every global decay hypothesis;
- `kgCutoff`, **`kgLocalPotential`** — a smooth potential cut off by a bump around the event is a
  Schwartz function (`HasCompactSupport.toSchwartzMap`), real, and equal to the potential on the
  ball;
- **`openProbes_of_static_smooth`**:

  ```
  (finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N → ContDiff ℝ ∞ p →
    OpenProbes (kgWaveOp d) (fun y => p (kgSpatial d y))
  ```

  *Clock probes for **every** smooth static potential*, with no decay hypothesis whatsoever: the
  potential is cut off near each event, and the probe only ever has to solve there;
- **`potential_eq_of_kgOpenProbes`** — and the probes determine the potential, by the corpus's
  `potential_eq_of_openProbes`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Quantified decay: the last analytic input

`formal/GaloisForLFunctions/HTGeometry/KleinGordonFourierDecay.lean` supplies the estimate a
*time-dependent* family needs — a decay bound whose constant is an explicit functional of the
function, not an unnamed constant produced by the Schwartz axioms:

- `kgSchwartzOp`, **`kgSchwartzOp_eq`** — the Klein–Gordon operator `1 - (2π)⁻²Δ` on Schwartz
  functions, realised as the multiplier with symbol `⟨η⟩²` (this is where the corpus's own
  `fourierMultiplierCLM_kgFreqSq` is reused);
- **`fourier_kgSchwartzOp`**, `fourier_kgSchwartzOp_iterate` — applying it `j` times multiplies the
  transform by `⟨η⟩²ʲ`;
- `norm_fourier_le_integral` — a transform is bounded by the `L¹` norm of the function;
- **`norm_fourier_le_weight`**:

  ```
  ‖𝓕f(η)‖ ≤ ⟨η⟩⁻²ʲ · ∫ ‖(1 - (2π)⁻²Δ)ʲ f‖
  ```

The right-hand side is an explicit norm, so a curve of potentials can be *required to bound it
uniformly in time* — which is exactly the hypothesis shape `WienerFamily.ofWeightedBounds` consumes.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Time-dependent potentials, assembled

- `inv_pow_le_inv_pow_of_le` — the weight is monotone, so an even exponent `2j ≥ N + m` suffices;
- **`WienerFamily.ofSchwartzCurve`** — a curve of Schwartz potentials is an admissible family as soon
  as the *explicit* decay functional `∫‖(1-(2π)⁻²Δ)ʲΦ(t)‖` is bounded uniformly in time and
  Lipschitz in time; the pointwise bounds `ofWeightedBounds` needs come straight from
  `norm_fourier_le_weight`;
- `isRealFamily_ofSchwartzCurve`, `kgPotential_ofSchwartzCurve` — reality time by time, and the
  potential of the family is the curve itself, by inversion;
- **`openProbes_of_schwartzCurve`**:

  ```
  OpenProbes (kgWaveOp d) (fun y => (Φ (y 0) (kgSpatial d y)).re - 1)
  ```

  *Clock probes for a genuinely time-dependent potential*, in the corpus's own interface, with the
  chart potential being the given function of the event.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## The parent card's hypothesis, discharged

`formal/GaloisForLFunctions/HTGeometry/KleinGordonConformalProbe.lean` closes the loop:

- `kgSpatialCLM`, `contDiff_comp_kgSpatial`, `kgChart`, **`kgWaveOp_eq_dalembert`** — the wave
  operator of the construction *is* the corpus's `SmoothMetricChart.dalembert` of the flat chart
  with signature `(-1,1,…,1)`, definitionally;
- **`openProbes_conformalPotential_static`** — for a conformal factor that does not depend on the
  time coordinate, the massive species has probes on open regions **in every dimension**
  (`conformalPotential_weight_zero` reduces the potential to `μe^{2σ}`, a smooth function of the
  spatial point, and smooth static potentials have probes with no further hypothesis);
- **`twoSpecies_scale_reconstruction_static`**:

  ```
  (other₁ x - other₂ x) / massSq = Real.exp (2 * s (kgSpatial d x))
  ```

  *The two-species conformal clock scale law, with the massive species' probe family constructed
  rather than assumed*, for every static conformal factor and in every dimension. The corpus had this
  unconditionally only in two dimensions (`openProbes_conformalPotential_two`) and on charts with a
  foliation.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Sup bounds instead of integral norms

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSupportBounds.lean` converts the family's decay
functional into the form a concrete potential supplies:

- **`integral_norm_le_of_support`** — `∫‖f‖ ≤ (sup‖f‖)·vol(K)` for `f` vanishing off `K`;
- **`kgSchwartzOp_support`**, `kgSchwartzOp_iterate_support` — the operator `1 - (2π)⁻²Δ` does not
  enlarge supports (the Laplacian of a function vanishing near a point vanishes there, by
  `laplacian_congr_nhds`), so the compact set is the one of the potential itself;
- `integral_kgSchwartzOp_le` — hence the decay functional is bounded by a sup times a volume;
- **`openProbes_of_schwartzCurve_sup`** — clock probes for a time-dependent potential supported in a
  fixed compact set, with finitely many derivatives bounded uniformly in time and Lipschitz in time.
  This is the hypothesis format a smooth compactly supported potential actually comes with.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Every smooth spacetime potential

`formal/GaloisForLFunctions/HTGeometry/KleinGordonJointSmooth.lean` — the bounds a smooth potential
supplies, from joint smoothness alone:

- `contDiff_partialFDeriv`, `contDiff_partialFDerivTime`, `contDiff_partialFDeriv_two` — the partial
  derivatives of a jointly smooth function of `(t,x)` are jointly smooth, by mathlib's parametric
  derivative theorem applied to the slice family;
- **`contDiff_partialLaplacian`** — hence so is the Laplacian in the space variable, being a finite
  sum of second directional derivatives along an orthonormal basis;
- `contDiff_kgFunOp_param`, **`contDiff_kgFunOp_iterate_param`** — and so is every iterate of
  `1 - (2π)⁻²Δ` applied in the space variable;
- `kgFunOp_support`, `kgFunOp_iterate_support`, `kgFunOp_iterate_param_support` — supports are not
  enlarged, at the level of functions;
- **`exists_bound_kgFunOp_iterate`** — a potential supported in a compact set of *events* has all its
  iterates bounded uniformly in time, by continuity on a compact support;
- **`exists_lipschitz_kgFunOp_iterate`** — and Lipschitz in time, by the mean value inequality
  applied to the partial derivative in time, which is again continuous with compact support.

`formal/GaloisForLFunctions/HTGeometry/KleinGordonSpacetimeProbe.lean` — the cut-off and the probe:

- `kgSchwartzOp_sub`, `kgSchwartzOp_iterate_sub` — the operator is linear, being a Fourier
  multiplier, so time differences pass through it;
- `kgTimeCutoff`, `kgSpacetimeCut`, `kgSpacetimeCurve` — the potential cut off in space *and* time
  around an event, as a curve of Schwartz functions supported in one compact set;
- `kgSpacetimeCurve_re` — near the event the cut-off is invisible;
- **`openProbes_of_smooth_spacetime`**:

  ```
  OpenProbes (kgWaveOp d) (fun y => P (y 0, kgSpatial d y))
  ```

  *Clock probes for every smooth spacetime potential*: no decay, no smallness, no
  time-independence, in every dimension.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## The parent card's hypothesis, discharged in full

`formal/GaloisForLFunctions/HTGeometry/KleinGordonConformalSpacetime.lean`:

- `kgEventCLM`, `contDiff_comp_kgEvent` — the splitting of an event into its time coordinate and its
  point is a continuous linear map, so a smooth function of the event is smooth on the chart;
- **`openProbes_conformalPotential`** — the massive species of an *arbitrary* smooth conformal factor
  has probes on open regions;
- **`twoSpecies_scale_reconstruction`**:

  ```
  (other₁ x - other₂ x) / massSq = Real.exp (2 * σ (x 0, kgSpatial d x))
  ```

  the parent card's scale law with the massive probe family *constructed* rather than assumed, for
  every smooth conformal factor on spacetime and in every dimension.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## What the whole construction proves

For an arbitrary smooth potential `V` on `ℝ¹⁺ᵈ` and an arbitrary event, there is a classical
solution of

```
∂ₜ²u = (2π)⁻²Δu - u + V u
```

on all of spacetime, real-valued and nonvanishing near that event. The evolution is solved on the
frequency side in a weighted Wiener algebra: Peetre's inequality makes convolution by the transform
of the potential bounded, the Volterra iteration converges with no smallness hypothesis because each
step integrates one more power of the time variable, and the synthesis may be differentiated twice
in time and twice in space under the integral. Every hypothesis on `V` is then removed by cutting
off in space and time around the event, which the probe interface cannot see.
