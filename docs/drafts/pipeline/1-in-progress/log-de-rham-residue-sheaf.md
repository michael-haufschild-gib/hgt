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
