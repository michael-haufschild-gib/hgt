# The logarithmic de Rham complex and the Poincaré residue, as sheaves

- **ID:** `log-de-rham-residue-sheaf`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE
- **Parents:** `deninger-pro-log-stein-kummer-residue-square`,
  `deninger-strict-pro-log-collar-trace-kernel`

## Why

Both analytic deninger cards record the same three obstructions: "no Stein theory, no coherent-sheaf
cohomology and no logarithmic de Rham complex".  Two of the three are stale.  The corpus now proves
**Cartan's theorem B** on `ℂ^n` and on `(ℂ^×)^n` (`deningerHolomorphic_ext_eq_zero`,
`_punctured`), and for free analytic sheaves of finite rank (`deningerFree_ext_eq_zero_punctured`);
it has sheaf cohomology as `Ext` out of the free abelian sheaf on an open set, acyclic resolutions,
fine sheaves and partitions of unity; and it has the acyclicity and filtered passage that
`(12)`--`(14)` of the residue-square card asks for, in the form
`deningerAcyclicOn_of_filtration`, `deningerFiltration_sections_surjective` and the three
direct-limit exactness theorems.

What is genuinely missing is the third: the logarithmic de Rham complex of a chart with a smooth
divisor, and the Poincaré residue as a morphism of sheaves.

## What is to be built

On the split chart of the residue-square card, `W × ℂ` with divisor `D = W × {0}`, a logarithmic
`k`-form is uniquely `α + (dz/z) ∧ β` with `α` a holomorphic `k`-form and `β` a holomorphic
`(k-1)`-form, and the Poincaré residue is `β|_{z=0}`.

1. The presheaf of logarithmic forms on the chart, and its sheaf condition, by the corpus's local
   predicate machinery.
2. The residue as a morphism of sheaves onto the pushforward of the forms of the divisor.
3. The residue sequence `0 → Ω^k → Ω^k(log D) → i_* Ω^{k-1}_D → 0` and its exactness.
4. Acyclicity of the terms, from Cartan's theorem B for free sheaves already proved, and the
   filtered passage already proved.

## The algebraic form, and why it is a tensor product

The local structure "every logarithmic form is uniquely `α + (dz/z) ∧ β`" says exactly that the
logarithmic algebra is the ordinary one with **one closed generator of degree one and vanishing
square adjoined**.  Adjoining such a generator is tensoring with the exterior algebra on a free
module of rank one, and the corpus owns both halves already: `tensorCDGA`, the tensor product of two
commutative differential graded algebras, and `exteriorModuleCDGA`, the exterior algebra of a module
graded by its exterior powers.  So the logarithmic algebra needs no new construction — only the
observation that above degree one the exterior powers of a rank-one module vanish, which is what
makes the tensor product have exactly two nonzero bidegrees in each degree: the ordinary forms and
the ones carrying `d log z`.

## Status

Landed: `formal/GaloisForLFunctions/HTGeometry/LogDeRhamAlgebra.lean`.  Axiom audit for all five
declarations: `propext, Classical.choice, Quot.sound`.

- `exteriorPower_rank_one_eq_bot` — **`⋀^j R = 0` for `j ≥ 2`**: a wedge of two elements of `R` is a
  multiple of the square of the class of `1`, which the exterior algebra kills.
- `logCDGA` — **the logarithmic de Rham algebra**, as a commutative differential graded algebra.
- `logCDGAUnit`, `logInclusion` — its unit and the inclusion of the ordinary forms.
- `logDlog` — **the class of `d log z`**, the adjoined generator, in degree one.

- `exteriorιₗ`, `exteriorOneToBase`, `exteriorOneEquiv` — **the first exterior power of a module is
  the module itself**.  mathlib has the alternating-map correspondence but not this instance of it;
  the inverse is the class of a vector, and the round trips are the one-argument case of the
  correspondence.
- `logResidue` — **the Poincaré residue**: the component at the bidegree carrying the adjoined
  generator, read through that identification.
- `logResidue_inclusion` — an ordinary form has no residue.
- `exteriorPower_rank_one_subsingleton`, `tensorProduct_eq_zero_of_subsingleton_right`,
  `logCarrier_high_eq_zero` — **a logarithmic form has only two nonzero bidegrees**: every component
  of exterior degree at least two vanishes.  This is the structural fact that makes the residue
  sequence exact.

- `logResidue_surjective` — **the residue is onto**: the form `x ∧ d log z` has residue `x`.
- `exteriorZeroOne`, `exteriorZeroToBase`, `exteriorZero_eq_smul_one`, `exteriorZeroEquiv` — **the
  zeroth exterior power is the ring**, every element being a multiple of the unit.
- `logResidueEquiv`, `logZeroEquiv`, `logZeroEquiv_symm`, `logResidue_eq_zero_iff` — **exactness of
  the residue sequence** `0 → Ω^• → Ω^•(log D) → Ω^{•-1} → 0`: a logarithmic form has no residue
  exactly when it is an ordinary form.  The proof is the two-bidegree structure: everything of
  exterior degree at least two vanishes, the bidegree carrying the generator is killed by the
  hypothesis, and what is left is the ordinary bidegree.

- `logResidueEquiv_map_d`, `logResidue_d` — **the residue commutes with the differential**, so it is
  a morphism of complexes.  No sign appears: the logarithmic differential has no component
  differentiating the adjoined generator, because that generator is closed, so the right half of the
  tensor differential vanishes identically.

Remaining: the passage from the algebra to the sheaf, which the corpus's local-predicate machinery
supports.  The algebraic content of `(6)`--`(7)` of the residue-square card — the logarithmic
complex, the unique expression `α + (dz/z) ∧ β`, the Poincaré residue `β`, and the residue sequence
— is complete.

## The sheaf layer: what is built

The passage from the algebra to the sheaf is the ideal sequence of a coordinate divisor,
`0 → O --·z--> O --restrict--> i_* O_D → 0`, from which the residue sequence for `k`-forms is
obtained by taking the direct sum over the `k`-subsets of the coordinates: on a subset not
containing the last direction the sequence is the identity, on one containing it the sequence above.

Landed, axiom audit `propext, Classical.choice, Quot.sound` for every declaration:

- `formal/GaloisForLFunctions/HTGeometry/DbarCoordinateProduct.lean` — `dzbarAt_mul`, **the Leibniz
  rule for the antiholomorphic derivative**, from the product rule for the Fréchet derivative and
  the complex homogeneity of the antiholomorphic Wirtinger functional; `dzbarAt_coord`, a
  coordinate is holomorphic; `coordSetForm` and **`setDbar_coordSetForm`**: multiplying a form by a
  coordinate commutes with the Dolbeault operator.
- `formal/GaloisForLFunctions/RHTower/DeningerDivisorInclusion.lean` — `deningerDivisorMap`,
  appending a zero last coordinate; its injectivity, continuity, and the fact that it commutes with
  updating an earlier coordinate; **`dzbarAt_comp_divisorMap`**: the antiholomorphic derivatives
  restrict to the divisor, which is a definitional consequence of that commutation;
  `deningerDivisorPullback` and `setDbar_deningerDivisorPullback`.
- `formal/GaloisForLFunctions/RHTower/DeningerStructureSheafMaps.lean` — **`deningerCoordMul`**,
  multiplication by a coordinate as an endomorphism of the sheaf of holomorphic functions;
  **`deningerDivisorInclusion`**, the divisor as a map of spaces; **`deningerDivisorRestrict`**,
  restriction to the divisor as a morphism to the direct image of the structure sheaf of the
  divisor; **`deningerCoordMul_comp_restrict`**, the composite vanishes; and
  **`deningerCoordMul_mono`**: multiplication by a coordinate is a monomorphism, because a form it
  kills vanishes off the coordinate's zero set and hence, being continuous, on it too.
- `formal/GaloisForLFunctions/RHTower/DeningerDivisorExtension.lean` — `deningerChopMap`, forgetting
  the last coordinate, with the two computations of the antiholomorphic derivatives of a function
  pulled back along it; **`deningerDivisorRestrict_locallySurjective`** and
  **`deningerDivisorRestrict_epi`**: off the divisor the trace of a small neighbourhood is empty, so
  the zero section works, and on the divisor a local model of the given function read through the
  map forgetting the last coordinate is a holomorphic extension.

## What is left, and exactly what it is

Exactness of `0 → O --·z--> O --restrict--> i_* O_D → 0` in the middle.  That is the statement that
**a holomorphic function vanishing on a coordinate hyperplane is divisible by that coordinate** —
the Nullstellensatz for a smooth divisor, in the one case that is needed.  It is a genuine theorem
of several complex variables, and the corpus does not have it.

The route that fits the corpus's tools: for `f` holomorphic near a point of the divisor and
vanishing on it, put
\[
 u(x)=\frac1{2\pi i}\oint_{|\zeta|=r}\frac{f(x_1,\dots,x_n,\zeta)}{\zeta(\zeta-x_{n+1})}\,d\zeta .
\]
For each `ζ` on the circle the integrand is complex Fréchet differentiable in `x`, so
`hasFDerivAt_integral_of_dominated_loc_of_lip` — which mathlib states over an `RCLike` field, so
over `ℂ` — makes `u` complex differentiable, hence analytic by `DifferentiableOn.analyticOnNhd`,
hence a section of the structure sheaf by `analyticOnNhd_of_dzbarAt_eq_zero` read backwards.  The
identity `x_{n+1}·u = f` is the one-variable Cauchy formula applied to `ζ ↦ f(x',ζ)/ζ`, which is
holomorphic on the disc because `f` vanishes at `ζ = 0`.

With that in hand the residue sequence is the direct sum of `C(n,k-1)` copies of the ideal sequence
and `C(n,k) - C(n,k-1)` copies of the identity, its terms are free analytic sheaves of finite rank
and so acyclic by `deningerFree_ext_eq_zero`, and steps 1--4 of this card are closed.

## The division: the quotient is written down

`formal/GaloisForLFunctions/HTGeometry/HolomorphicCoordinateDivision.lean`.  Axiom audit
`propext, Classical.choice, Quot.sound`.

The circle-integral route above is not needed.  The quotient has a closed form: contracting the last
coordinate to zero along a segment and integrating the last partial derivative,

    u(x) = ∫₀¹ (∂ₙ₊₁ f)(x₁,…,xₙ, t·xₙ₊₁) dt,

and `xₙ₊₁·u = f` is the fundamental theorem of calculus along that segment — the constant term is
`f` at the endpoint on the divisor, which vanishes by hypothesis.

- `coordContract` — the contraction of the last coordinate, as a complex linear map;
  **`coordContract_mem_ball`**: it preserves a polydisc *centred on the divisor*, because the last
  coordinate of the centre is zero and the contraction only shortens the last coordinate's distance
  to it.  This is why the statement is local at a point of the divisor.
- `hasDerivAt_coordContract` — the contraction is an affine path with constant velocity
  `Pi.single (last) xₙ₊₁`.
- `lastCoordDeriv`, `coordDivQuotient` — the last partial derivative and the quotient.
- `coordDeriv_analyticOnNhd` — the last partial derivative of an analytic function is analytic,
  since `fderiv` of an analytic function is analytic and evaluation is continuous linear.
- `hasDerivAt_comp_coordContract`, `continuousOn_coordDeriv_path` — the chain rule along the path
  and the continuity that makes the integral exist.
- **`coordDivQuotient_mul`** — `xₙ₊₁ · u = f` on the whole polydisc.

**What is left on this card**: that `u` is holomorphic.  It is a parametric integral over `[0,1]` of
a family of holomorphic functions, so this is one application of
`hasFDerivAt_integral_of_dominated_loc_of_lip`: the Lipschitz bound is the supremum of
`‖fderiv (coordDeriv f)‖` on a compact sub-polydisc, uniform in `t` because the contraction is a
contraction; the derivative family is continuous in `t`, hence measurable.  With `fderiv ℝ u`
computed as `∫₀¹ fderiv ℝ (F · t)`, the antiholomorphic derivatives of `u` vanish because the
antiholomorphic Wirtinger functional is continuous linear and so commutes with the integral, and
each integrand is holomorphic.  Then `analyticOnNhd_of_dzbarAt_eq_zero` makes `u` analytic and the
residue sequence is exact.

### The parametric-integral step, written out

`coordContract` and its two structural lemmas for that step are landed too:
`coordContract_eq` writes the contraction as `coordDrop + t • coordKeepLast`, so it is continuous
— indeed affine — in the parameter as a map into the space of continuous linear maps;
`continuous_coordContract` is that continuity; and **`coordContract_dist_le`** is that the
contraction does not increase distances, for a parameter in `[0,1]`.

The remaining application of `hasFDerivAt_integral_of_dominated_loc_of_lip` (with `𝕜 = ℂ`, which
the lemma allows since it is stated over an `RCLike` field, so the derivative comes out complex
linear and no `∂̄` argument is needed) then needs, with `μ = volume.restrict (Ioc 0 1)`,
`s = ball c ρ` for some `dist x₀ c < ρ < r`, and
`F' t = (fderiv ℂ (coordDeriv f) (coordContract t x₀)).comp (coordContract t)`:

- the Lipschitz bound: `C = sup ‖fderiv ℂ (coordDeriv f)‖` on `closedBall c ρ`, finite by
  compactness and the continuity of the derivative of an analytic function; then
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the ball and `coordContract_dist_le`
  give `‖F x t − F y t‖ ≤ C‖x − y‖` uniformly in `t`;
- measurability of `F x` and of `F'`: both are **continuous on `Icc 0 1` only** — the contraction
  leaves the polydisc for a parameter outside `[0,1]` — so the route is
  `ContinuousOn.aestronglyMeasurable` against `μ`, not `Continuous.aestronglyMeasurable`;
- integrability of `F x₀` and of the constant bound: continuity on a set of finite measure.

Then `coordDivQuotient f` is complex differentiable on the polydisc, hence analytic, hence a section
of the structure sheaf, and `deningerCoordMul` composed with it recovers the given section — which
is exactness of the ideal sequence in the middle, and with it the residue sequence.

## The division theorem: proved

**`exists_analyticOnNhd_coord_mul`** in
`formal/GaloisForLFunctions/HTGeometry/HolomorphicCoordinateDivision.lean`.  Axiom audit
`propext, Classical.choice, Quot.sound`.

> A holomorphic function on a polydisc centred on the divisor of the last coordinate, vanishing on
> that divisor, is that coordinate times a holomorphic function on the same polydisc.

The quotient is `coordDivQuotient`, the segment integral above.  Its holomorphy is
`coordDivQuotient_differentiableAt`: one application of
`hasFDerivAt_integral_of_dominated_loc_of_lip` at `𝕜 = ℂ`, with

- `s = ball c ρ` for `dist x₀ c < ρ < r`, so `closedBall c ρ` is a compact subset of the polydisc;
- the bound `C = sup ‖fderiv ℂ (lastCoordDeriv f)‖` on that compact ball, and the Lipschitz estimate
  `‖F x t − F y t‖ ≤ C‖x − y‖` from `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` together
  with `coordContract_dist_le` — uniform in `t`, which is the hypothesis that would fail for any
  non-contracting path;
- measurability of the integrand and of the derivative family through
  `ContinuousOn.aestronglyMeasurable` on `Ioc 0 1`, the derivative family being continuous by
  `ContinuousOn.clm_comp` out of `continuous_coordContract` and the continuity of the derivative of
  an analytic function.

Passing from complex differentiability on the polydisc to analyticity is the corpus's own
several-variable statement `analyticAt_of_differentiableOn` — mathlib's
`DifferentiableOn.analyticOnNhd` is one variable only.

**What is left on this card**: only the bookkeeping that turns this into exactness of the sheaf
sequence — read a section of the structure sheaf killed by the restriction as an analytic function
on a polydisc, divide, and read the quotient back as a section, which is the local-model machinery
already used for `deningerDivisorRestrict_locallySurjective`.

## The ideal sheaf, and the one statement left

`formal/GaloisForLFunctions/RHTower/DeningerDivisorIdeal.lean`.  Axiom audit
`propext, Classical.choice, Quot.sound`.

Exactness of `0 → O --·z--> O --restrict--> i_* O_D → 0` in the middle is now a *factorisation*
question rather than a gluing one.  The sections vanishing on the divisor are cut out by a
**pointwise** condition, so they form a subsheaf `deningerVanishSheaf` by the corpus's local-predicate
machinery, and:

- `deningerVanishIncl_comp_restrict` — a section vanishing on the divisor restricts to zero;
- `deningerVanishPred_of_restrict_eq_zero` — conversely a section killed by restriction vanishes on
  the divisor, because restriction is evaluation at the divisor's points and every point of the
  domain lying on the divisor is in the image of its parametrisation (this is where the divisor's
  domain has to be the full preimage);
- `deningerVanishKernelLift`, **`deningerVanishIncl_isKernel`** — so the ideal sheaf *is* a kernel of
  restriction, by the same "same underlying map, corestricted" device the corpus uses for the
  closed forms;
- `deningerCoordMulVanish`, `deningerCoordMulVanish_comp`, `deningerCoordMulVanish_mono` — and
  multiplication by the coordinate factors through it, monomorphically.

**The one statement left** is that `deningerCoordMulVanish` is an epimorphism, i.e.
`TopCat.Presheaf.IsLocallySurjective (deningerCoordMulVanish Ω).1`.  Then it is mono and epi in an
abelian category, hence an isomorphism; composing the inverse with the kernel lift discharges
`KernelFork.IsLimit.ofι` for `deningerCoordMul`, and `ShortComplex.exact_of_f_is_kernel` closes the
sequence.

Its proof, with every input already built:

1. take the local model `g` of the section on an open `N`, and put `W = N ∩ deningerAmb U`;
2. `g ∅` is *globally* smooth (`SmoothSetForm` is global) and its antiholomorphic derivatives vanish
   on `W` (`deningerDivisorModel_dzbar_eq_zero`, which is stated for an arbitrary dimension and so
   applies with `n := n+1`), so `analyticOnNhd_of_dzbarAt_eq_zero_on` makes it analytic on `W`;
3. pick a ball `B = ball c₀ R ⊆ W` at `c₀ = x`.  If `x` lies on the divisor the ball is *centred on
   it*, which is what `coordDivQuotient_analyticOnNhd` needs, and `u₀ = coordDivQuotient (g ∅)`;
   otherwise shrink `B` to avoid the divisor and take `u₀ = g ∅ / z_last`, analytic because the
   denominator does not vanish.  Either way `z_last · u₀ = g ∅` on `B`;
4. the section is `y ↦ u₀ y` on `V = deningerRestrictOpen Ω (ball c₀ (R/3)) ⊓ U`, and its *global*
   smooth model is `ψ · u₀` for a `ContDiffBump c₀` with `rIn = R/3`, `rOut = R/2` — the corpus
   already uses `ContDiffBump` on `Fin n → ℂ` in `exists_polydisc_bumps`, so the instance is there.
   Global smoothness is smoothness on `B` and on the complement of the bump's support, two opens
   that cover;
5. its `∂̄` vanishes because `ψ ≡ 1` near each point of `V` and `u₀` is complex differentiable there.

### The epi: all four inputs built

`exists_local_coord_quotient`, `deningerQuotientModel`, `deningerQuotientModel_smooth`,
`deningerQuotientModel_eq_of_mem` and `setDbar_deningerQuotientModel` are landed in
`DeningerDivisorIdeal.lean`.  What is left is only their assembly into

    theorem deningerCoordMulVanish_locallySurjective (Ω) :
        TopCat.Presheaf.IsLocallySurjective (deningerCoordMulVanish Ω).1

following `deningerDivisorRestrict_locallySurjective` line for line: take the model `g` on `N`, put
`Wset = N ∩ deningerAmb U`, get `dzbarAt (g ∅) j = 0` there from
`deningerDivisorModel_dzbar_eq_zero` (instantiated at dimension `n+1`) and hence
`AnalyticOnNhd ℂ (g ∅) Wset` from `analyticOnNhd_of_dzbarAt_eq_zero_on`; get the vanishing of `g ∅`
on the divisor from the section's own vanishing through the model; feed both to
`exists_local_coord_quotient` at the centre `x`; take
`V = deningerRestrictOpen Ω (ball x (R/3)) ⊓ U` and the section `y ↦ u y`, whose model is
`deningerQuotientModel x R hR u` — smooth by `deningerQuotientModel_smooth`, equal to `u` on the
smaller ball by `deningerQuotientModel_eq_of_mem`, and `∂̄`-closed by
`setDbar_deningerQuotientModel`.  The identity `z_last · u = g ∅ = h` on `V` is `humul` composed
with the model equality.

Then `deningerCoordMulVanish` is mono and epi, hence iso; its inverse after
`deningerVanishKernelLift` discharges `KernelFork.IsLimit.ofι` for `deningerCoordMul`, and
`ShortComplex.exact_of_f_is_kernel` gives the short exact ideal sequence — and with it the residue
sequence and steps 1--4 of this card.
