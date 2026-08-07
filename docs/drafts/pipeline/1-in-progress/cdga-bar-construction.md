# The bar construction of an augmented commutative differential graded algebra

- **ID:** `cdga-bar-construction`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE
- **Parents:** `cdga-module-derived-tensor-layer`,
  `deninger-derived-rank-quotient-universal-property`,
  `deninger-selective-positive-cell-h0-preservation`,
  `deninger-character-shape-formality`

## Why

Three deninger cards record the same remaining gap in the same words: "the `E_∞` coherence, the bar
construction and its spectral sequence".  The corpus's substitute for `E_∞` is the commutative
differential graded model, which is now complete — free algebras on degree-one generators, relative
tensor products of algebras over a base, semi-free resolutions, flatness and derived base change.
The bar construction is the one object of that model still missing, and it is what the cards use to
pass from the underived shadow to the connectivity statements.

## What is to be built

Let `A` be a unital commutative differential graded algebra over `R` with an augmentation
`ε : A → R`, and let `Ā = ker ε` be the augmentation ideal.  Assume `A` connected, that is `Ā`
concentrated in degrees `≥ 1`, so that the shift `sĀ` with `(sĀ)^n = Ā^{n+1}` stays in
nonnegative degrees.  The bar construction is

    B(A) = ⨁_{k ≥ 0} (sĀ)^{⊗ k}

with the differential `d = d_int + d_bar`, where `d_int` is the internal differential of `Ā` with the
sign of the shift and `d_bar` multiplies adjacent factors.

## Steps

1. **The augmentation ideal as a non-unital algebra.**  `augIdealCarrier` and `augIdealModule` are
   built; what is missing is the multiplication `Ā^a → Ā^b → Ā^{a+b}` and its bilinearity,
   associativity, graded commutativity and Leibniz rule.  `[LANDED]`
2. **The shift of the ideal**, `(sĀ)^n = Ā^{n+1}`, with the induced differential and the sign.
3. **The iterated tensor power** `(sĀ)^{⊗k}`, by recursion on `k` using the corpus's
   `TensorCarrier`, which is already a product over the decompositions of the degree and therefore
   the direct sum in each degree.
4. **The total object** `⨁_k (sĀ)^{⊗k}` in each degree.
5. **The two differentials** and `d² = 0`.
6. **The augmentation and the counit**, and the comparison `B(A) → R`.

## Status

Steps 1--3 landed; axiom audit for every declaration below is `propext, Classical.choice, Quot.sound`
or less.

- `formal/GaloisForLFunctions/HTGeometry/CDGAAugmentationIdealAlgebra.lean` — `augIdealMul` with
  bilinearity, `augIdealMul_assoc`, `augIdealMul_comm`, `augIdealMul_leibniz`: **the augmentation
  ideal is a commutative differential graded algebra without a unit.**
- `formal/GaloisForLFunctions/HTGeometry/CDGAGroundModule.lean` — `zeroComplexModule`: **a cochain
  complex is a differential graded module with zero action**, over any algebra.  This is the device
  that makes the whole module layer — in particular the tensor product with its Koszul sign —
  available for plain complexes, without building a second tensor product.  The first attempt went
  through modules over `groundCDGA` with the scalar action in degree zero; that forces a transport
  along `0 + b = n` into every axiom, and the zero action avoids all of it while giving the same
  tensor product, since `tensorD` never reads the action.
- `formal/GaloisForLFunctions/HTGeometry/CDGACochain.lean` — `Cochain`, a complex packaged with its
  instances so that complexes can be produced by recursion (the `DGStage` pattern);
  `Cochain.tensor`, **the tensor product of complexes**, whose differential squares to zero for
  free; `Cochain.ground`; `augIdealShift`, **the shift of the augmentation ideal**, degree `n` being
  degree `n + 1` of the ideal with the differential negated; and `barPower`, **the `k`-fold tensor
  power of the shifted ideal**, by recursion on `k`.

## What step 5 needs that does not exist yet

The bar differential maps `(sĀ)^{⊗(k+1)} → (sĀ)^{⊗k}` and *raises* the total degree by one, since
multiplying two shifted elements of degrees `a` and `b` gives an element of `Ā` in degree
`a + b + 2`, which is degree `a + b + 1` after the shift.  So it is the multiplication
`sĀ ⊗ sĀ → sĀ`, a map of degree one, applied in the first two slots.  The corpus's `tensorMapLeft`
tensors a *degree-zero* morphism with the identity; what is needed is the same for a degree-one map,
with the sign that the Koszul convention forces.  That is the next object to build.
