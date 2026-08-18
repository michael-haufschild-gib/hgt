# Borel's rank theorem, formalized: the programme

- **ID:** `borel-rank-formalization-programme`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (multi-session)
- **Serves:** `deninger-algebraic-cyclotomic-milnor-amplitude` — its **only** remaining input
- **Supersedes:** the route table of `garland-formalization-programme` (audited unsound 2026-08-18)
- **Created:** 2026-08-18

## Target

For a number field `K`,
\[
 K_2(\mathcal O_K)\otimes\mathbb Q=0,
\]
equivalently the degree-two tame kernel is torsion.  This is Borel's rank computation in the only
form the parent card needs, equivalently Garland's 1971 finiteness theorem.

## Why this is now the *only* target

Two audits fixed the picture:

1. `k2-rank-divisibility-firewall` proves, unconditionally and in Lean, that **no combination of
   finite-coefficient statements can give the rank** — the mod-`m` theory is blind to a uniquely
   divisible summand — and that **finite generation is exactly what restores decidability**
   (`isTorsion_of_fg_of_no_int_quotient`).
2. The card's second alleged blocker, its `(4)`, **does not exist**: the corpus already owns the
   `E_∞` layer in its commutative-differential-graded model (`deninger-character-shape-formality` at
   stage 3, the 79-module CDGA stack, `derivedBaseChange_zigZag`, `freeExteriorCDGAHom`,
   `relTensorCDGA`).  `RHTower.deningerAlgebraicMilnorAmplitude` now states the whole card with the
   tame-kernel statement as its single hypothesis.

So the parent card is exactly one classical theorem from stage 3.

## The route: integral finiteness first, then a mod-`m` bound

```
K₂(𝒪_S) ⊗ ℚ = 0
  ⇐ [F] K₂(𝒪_S) finitely generated        ← the integral input the firewall demands
      ⇐ H₂(SL_n(𝒪_F), ℤ) finitely generated
          ⇐ SL_n(𝒪_F) acts on a contractible complex, cocompactly, with FINITE stabilizers
              ⇐ Ash's well-rounded retract        ← geometry of numbers, NOT analysis
  ⇐ [M] |K₂(𝒪_S)/m| bounded
      ⇐ Merkurjev–Suslin / Tate: K₂(F)/m ≅ H²(F, μ_m^{⊗2})
      ⇐ finiteness of the étale H² with finite coefficients
```

Layer F is the half that is *not* analytic: the well-rounded retract is built from minimal vectors of
lattices, and its cocompactness is Minkowski/Mahler finiteness.  That is the reason this route is
chosen over Borel's own symmetric-space argument, which needs continuous cohomology of Lie groups,
van Est, and Borel–Serre.

## Layer F — progress

### F1. Minimal vectors of a lattice `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/LatticeMinimalVectors.lean` (wired into the `HTGeometry`
umbrella; axiom audit `propext, Classical.choice, Quot.sound`).

```text
discreteSubmodule_isClosed          a discrete ℤ-submodule of a normed space is closed
finite_lattice_inter_of_bounded     ** it meets every bounded set in a finite set **
exists_minimal_norm                 ** a nonzero discrete submodule has a shortest nonzero vector **
```

These are the objects the retract is made of: a lattice is *well-rounded* when its shortest vectors
span, and the well-rounded locus is the complex on which `SL_n(𝒪)` acts with finite stabilizers.
mathlib has `IsZLattice`, `Zspan.setFinite_inter` for the span of a basis, and
`Metric.finite_isBounded_inter_isClosed`; what it does not have is the statement for an arbitrary
discrete submodule, nor the existence of a shortest vector, both of which are proved here.

### F2. Well-roundedness and FINITE STABILIZERS `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/LatticeWellRounded.lean` (wired; axiom audit
`propext, Classical.choice, Quot.sound`).

```text
IsLatticeMinimum, exists_isLatticeMinimum   the length of a shortest nonzero vector, and that it
                                            exists
latticeMinimalVectors                       the shortest vectors
latticeMinimalVectors_finite                ** finite **
latticeMinimalVectors_nonempty              nonempty at the minimum
IsWellRounded                               the shortest vectors span
mapsTo_latticeMinimalVectors                a lattice isometry permutes them
eq_of_eqOn_latticeMinimalVectors            they determine a linear map on a well-rounded lattice
finite_latticeIsometry_of_wellRounded       ** THE ISOMETRY GROUP OF A WELL-ROUNDED LATTICE IS
                                               FINITE **
```

The last is step 4 of the plan and one of the two geometric inputs of the whole layer: it is exactly
why the action on the well-rounded retract has **finite stabilizers**, hence why the equivariant
chain complex is finitely generated over `ℤΓ`, hence why `H_i(Γ, ℤ)` is a finitely generated abelian
group.  The proof is the elementary one — a lattice isometry permutes the finitely many shortest
vectors, and on a well-rounded lattice those span, so the isometry is determined by the permutation,
giving an injection of the isometry group into a finite set of maps.

### Next bricks in Layer F

1. **Mahler/Minkowski compactness**: the set of unimodular lattices with minimum bounded below is
   compact — the *cocompactness* input, the second geometric half.
2. The well-rounded retract itself: the deformation of the space of lattices onto the well-rounded
   locus, and its contractibility.
3. The equivariant cell structure, and the passage `finitely many orbits + finite stabilizers ⟹
   `ℤ` has a resolution by finitely generated `ℤΓ`-modules ⟹ `H_i(Γ, ℤ)` finitely generated`.
4. `H₂(SL_n(𝒪)) → K₂(𝒪)`: Matsumoto, the universal central extension, and homological stability.

## Layer M — not started

Merkurjev–Suslin in weight two, or Tate's class-field-theoretic proof for number fields, followed by
the finiteness of `H²_ét(𝒪_S, ℤ_p(2))`.  By the firewall this layer is *permitted* only in the
presence of Layer F; on its own it can prove nothing about the rank.

## Log

- 2026-08-18 — Programme opened after the `(4)` correction reduced the parent card to a single
  input.  Layer F started: minimal vectors of a lattice.
