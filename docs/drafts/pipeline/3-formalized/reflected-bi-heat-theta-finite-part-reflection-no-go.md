# Reflected bi-heat theta finite-part reflection no-go

- **ID:** RBH-TFPR
- **Stage:** 3-formalized
- **Type:** SOURCE-LEVEL NO-GO AND EXACT EIGENSPACE DECOMPOSITION
- **Frontier-map policy:** read only

## Theorem

For every admissible reflected bi-heat datum `P`, let `P.reflect` replace `z`
by `1-z` and preserve heat scale `x`.  Then:

1. factor swap plus lattice transpose leaves every regulated pair sum unchanged;
2. canonical theta-pole finite part satisfies
   `reflectedBiHeatFinitePart P.reflect = reflectedBiHeatFinitePart P`;
3. reflection is an involution, and every scalar source splits exactly into
   reflection-even and reflection-odd projections;
4. after adding arbitrary source `A`, reflection defect of completed finite part
   is exactly twice odd projection of `A`.

Therefore canonical finite part descends to reflection quotient and cannot
orient an off-wall divisor.  Any source-level wall orientation must enter
through a nonzero reflection-odd augmentation.

## Corpus basis

- `ReflectedBiHeatThetaResidue` proves exact theta pole and canonical finite-part
  limit but did not analyze `z ↦ 1-z`.
- `AsymmetricHeatDoubleSum` exposes pair term with complementary Dirichlet
  orders and additive heat coefficient.
- `heatCoeff_neg` makes lattice transpose compatible with factor swap.
- Mandatory corpus search found no pair-sum or finite-part reflection theorem.

## Paper proof

Complementary-order reflection swaps left and right Dirichlet orders.  Swapping
lattice indices sends heat difference `m-n` to its negative, while
`heatCoeff_neg` preserves heat weight; commutativity swaps remaining factors.
Product commutation therefore reindexes full `tsum` to itself.  Reflection also
preserves theta-pole coefficient because it preserves `x`.  Both reflected and
unreflected pole-subtracted sums are thus same function and have canonical
one-sided limits; Hausdorff limit uniqueness identifies finite parts.

Off wall, reflection changes real part of `z`, giving a distinct datum with same
finite part.  Standard involutive even/odd projections split arbitrary source.
Finite-part evenness cancels canonical terms in augmented reflection defect,
leaving exactly twice odd projection.

## Formal theorem package

- `ReflectedBiHeatDatum.reflect_reflect`
- `asymmetricHeatPairTerm_swap`
- `reflectedBiHeatPairSum_reflect`
- `reflectedBiHeatFinitePart_reflect`
- `ReflectedBiHeatDatum.reflect_ne_of_re_ne_half`
- `reflectedBiHeatFinitePart_noninjective_at_offWall`
- `reflectedBiHeatSource_eq_evenPart_add_oddPart`
- `reflectedBiHeatSourceEvenPart_reflect`
- `reflectedBiHeatSourceOddPart_reflect`
- `reflectedBiHeatAugmentedFinitePart_sub_reflect`
- `reflectedBiHeatAugmentedFinitePart_reflect_eq_iff_oddPart_eq_zero`

## Provisional literature audit

Primary literature checked on zeta regularization and Epstein reflection
formulas records general functional-equation symmetry, but search found no
theorem identifying this complementary-order additive-heat double sum's
canonical regulator finite part under factor swap, nor its exact source
eigenspace obstruction.  Priority claim remains provisional pending expert
review.

## No-go closure

- **Exact killing theorem/mechanism:** canonical regulated pair sum and theta
  finite part are reflection-even; every off-wall datum has distinct reflected
  partner with identical finite part.
- **Strongest positive survivor:** exact reflection-even/odd source
  decomposition; completed orientation defect is twice odd projection.
- **New insight:** source route must manufacture antisymmetry; canonical theta
  renormalization contributes none.  Search for wall orientation can be reduced
  exactly to odd source subspace.
- **Status:** dependency-closed paper proof and Lean theorem module complete.

## Audit

- Module:
  `GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartReflectionNoGo`
- Direct `lake env lean` check passed.
- Targeted `lake build` passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired; full umbrella build intentionally not run.

## Log

- 2026-08-27 — conjecture frozen after corpus and provisional literature audit.
- 2026-08-27 — pair-sum invariance, canonical finite-part no-go, off-wall
  noninjectivity, and exact odd-source survivor formalized; moved to stage 3.
