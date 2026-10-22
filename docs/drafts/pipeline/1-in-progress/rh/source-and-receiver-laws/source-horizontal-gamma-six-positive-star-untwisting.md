# Source-horizontal Gamma-six positive-star untwisting

- **ID:** `source-horizontal-gamma-six-positive-star-untwisting`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / PRODUCER OPEN
- **Source:** `rh-current-frontier-map.md`; integral Cartier Gamma producer; covariant cyclic Stokes producer
- **Statement:** One literal cyclic Hermitian square detects and forces Gamma-six holonomy untwisting; producing its physical positivity for every Xi divisor remains exactly RH-strength.

## Goal

Untwist the unconditional covariant boundary `t-exp(a)` to the fixed Deninger boundary `t-1`
without erasing prime labels, divisor multiplicity, or reflection orientation.

## Conjecture loop

1. **Adams/Frobenius power coherence forces untwisting.** `[FALSIFIED AS PRODUCER]` Existing
   one-sided framed power transport has exact curvature
   `chi(m)(m-1)(1-chi(n))`; its vanishing is already equivalent to neutral grade. Power-map
   coherence therefore cannot be imported into the physical frame unconditionally.
2. **Covariant Stokes flatness itself untwists.** `[FALSIFIED]` Every real grade is covariantly
   flat. Lean now contains the explicit counterexample `a=1`, which is covariantly flat but reads
   the canonical Hermitian square strictly negatively.
3. **Source-star positivity on the minimal square untwists.** `[PROVED]` For cyclic generator `t`,
   physical evaluation sends

   ```text
   (t⁻¹-1)(t-1)  ↦  -2(cosh(a)-1).
   ```

   Existing Gamma curvature proves the right side nonpositive, with equality only at `a=0`.
   Hence nonnegativity on this single source square forces holonomy one. No global positivity cone,
   trace, completion, or all-test-function Weil criterion is needed for the consumer theorem.

## Lean status

Module:

`formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixPositiveStarUntwisting.lean`

Main declarations:

- `sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare`
- `sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare_nonneg_iff`
- `sourceHorizontalGammaSixIntegralHermitianSquare_eq_quadraticGhost`
- `sourceHorizontalGammaSixPhysicalStarPositive_iff_sourceUntwisting`
- `sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_starPositive`
- `sourceZeroGammaSixCyclicPhysicalCharacter_fixedStokesFlat_of_starPositive`
- `exists_covariantStokesFlat_without_positiveStarUntwisting`
- `deningerXiFullIntegralGammaProducer_quadraticGhost_nonpos`
- `deningerXiFullIntegralGammaProducerStarPositive_iff_descends`
- `everySourceHorizontalGammaSixPhysicalStarPositive_iff_riemannHypothesis`

## Exact open producer

Construct, for every retained Xi divisor, a genuine source/Gamma natural landing of the literal
cyclic/integral Laurent source into a positive star receiver whose state equals the physical
Gamma character on the one canonical Hermitian square. Ordinary Hellinger/Gauss positivity is not
enough: corpus identifies it with the opposite sign, namely positive paired curvature. Required
law must prove star preservation or positive-state provenance before scalar evaluation, not append
nonnegativity as a hypothesis.

## No-go closure

- **Exact killing theorem/mechanism:** Covariant flatness allows arbitrary positive holonomy;
  Adams coherence in the physical one-sided frame is equivalent to the desired conclusion.
- **Strongest positive survivor:** One-square positive-star law is sufficient and minimal; full
  integral quadratic ghost is precisely that square, with multiplicity and prime clock retained.
- **New insight:** Quadratic ghost is not merely an unwanted nonlinear residue. It is the source
  Hermitian square on which physical Gamma evaluation reverses the canonical positive sign.
  Untwisting is therefore a star-compatibility problem, not another boundary-exactness problem.
- **Status:** Consumer theorem formalized unconditionally. Positive-star producer remains open;
  global existence is formally equivalent to RH and is not claimed.

## Meyer modular reinterpretation

The genuine Xi-selected Meyer/Koszul reporter closes the coefficient comparison.  For every
retained divisor `rho` and prime `p`, Lean now proves

```text
fullIntegralGammaGhost(rho,p)
  = -multiplicity(rho) * (norm(chi_p(rho)) - norm(chi_p(rho))⁻¹)^2,
```

where `chi_p(rho)` is the already-constructed prime-flow eigencharacter of the nonzero Meyer
reporter.  Hence all following pointwise statements are equivalent:

1. full integral ghost is nonnegative;
2. Meyer modular norm imbalance vanishes;
3. Meyer prime character has unit norm;
4. cyclic Gamma-six covariant boundary untwists to fixed Deninger boundary;
5. retained divisor lies on critical line.

This is a real source-class transition: integral Cartier ghost is negative square of Meyer
modular imbalance, not merely another theorem sharing critical-line endpoint.

Canonical Abelian-zeta-gas GNS does not produce missing balance.  Its Toeplitz generator satisfies
`W*V=1` but `V*W != 1`; positive-temperature Gibbs state distinguishes `V*W` from unit.  Lean
therefore proves no ring landing can send Laurent generator and inverse to canonical gas
isometry/coisometry.  Required receiver must be bilateral before Toeplitz compression, and its
state must retain Meyer character coefficient.  Merely invoking GNS positivity is falsified.

Formal module:

`formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixMeyerModularUntwisting.lean`

## Gates

- [x] 0 → 1 in-progress: exact source element, sign law, falsifiers, and producer typed
- [ ] 1 → 2 fully-proven: construct genuine source-positive/star-preserving landing
- [ ] 2 → 3 formalized: formalize that landing and derive unconditional RH
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-16 — Adams and flatness conjectures falsified; minimal Hermitian-square untwisting and
  multiplicity-faithful sign obstruction formalized in Lean.
- 2026-08-16 — Proved exact integral-Cartier/Meyer modular norm-square identity and direct Meyer
  unitarity untwisting theorem.  Falsified canonical positive-temperature gas GNS producer by
  proper-isometry and Laurent-landing obstructions.
