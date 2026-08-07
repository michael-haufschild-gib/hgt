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
