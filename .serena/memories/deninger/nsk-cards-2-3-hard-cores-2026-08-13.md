# Deninger NSK cards 2 and 3: what actually blocks stage 3 (2026-08-13)

## Card 2 `deninger-algebraic-cyclotomic-milnor-amplitude`
Remaining headline `(1)`: `K_q^M(F) ⊗ ℝ = 0` for `F/ℚ` algebraic, `q ≥ 2`.

REDUCTION NOW FORMALIZED (unconditional, compiles clean):
- `HTGeometry/MilnorKGrading.lean` — `torsionAddSubgroup`, `milnorClassDeg_split`,
  **`milnorKDeg_mem_torsion_of_two`**: degree `2+k` of `MilnorKDeg F` is torsion once degree two
  is.  (Built on the corpus's pre-existing graded Milnor K-theory `MilnorKDeg` /
  `MilnorSymbolDeg` / `milnorMul` in `HTGeometry/MilnorKGradedRing.lean` +
  `MilnorWittWittComparison.lean` — do NOT rebuild a grading, it already exists.)
- `HTGeometry/MilnorKFunctoriality.lean` — `milnorUnitMap`, `milnorKPreMap`, **`milnorKMap`**
  (field hom ⇒ Milnor ring hom), `milnorKMap_symbol`, `milnorSymbol_mul_torsion_of_map`,
  **`milnorSymbol_mul_torsion_of_subfield`**.
Both wired into `HTGeometry.lean`.

REMAINING CORE (classical, deep): *every length-two Milnor symbol of a number field is torsion*.
Equivalent (via tame symbols into the finite residue fields) to the tame kernel being torsion —
Tate/Garland finiteness, equivalently Borel's rank computation.  Mathlib has no algebraic
K-theory, no localization sequence, no Borel regulator.  Note `ℚ̄` does NOT help: `K_2` of an
algebraically closed field is generally nonzero (uniquely divisible, Suslin); `K_2(ℚ̄) = 0` only
because it is the colimit of the number-field groups.  So the number-field theorem is unavoidable.
Item `(4)` additionally needs `E_∞`-algebra homotopy theory.

## Card 3 `deninger-selective-positive-cell-h0-preservation`
All one-categorical content already landed earlier (π₀ graded shadow, equivariant descent,
principal conormal, Kähler line).  Remaining: free `E_∞`-algebra on a 1-connective object, the
homotopy pushout and its `π₀` formula, `DAC_DERIVED_RANK_QUOTIENT_PI0`, and the Milnor–Witt
fundamental class with determinant twist and Gysin map.  None of ∞-categories, `E_∞`-ring spectra,
or motivic/MW sheaf theory exists in mathlib.

POSSIBLE HONEST INTERMEDIATE for card 3: formalize the positive-cell `π₀` theorem in a concrete
model — connective chain complexes, where `H₀(A ⊗^L_R k) ≅ H₀A ⊗_{H₀R} H₀k` is provable from
right-exactness — rather than in an ∞-category.  The card asks for the ∞-categorical statement, so
this would be a model-level surrogate, not the card's theorem.
