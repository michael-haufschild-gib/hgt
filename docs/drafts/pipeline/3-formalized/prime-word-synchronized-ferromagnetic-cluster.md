# Prime-word synchronized ferromagnetic clusters

- **ID:** prime-word-synchronized-ferromagnetic-cluster
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** live `RHTower` support-marker and centered-prime-field APIs; Lee--Yang / ferromagnetic-cluster bridge
- **Statement:** `[BRIDGE]` Evaluating a squarefree prime-word support marker at the centered prime Lee--Yang fields gives the field monomial of a synchronized ferromagnetic cluster; every zero of `1 +` that monomial, and every zero of a finite product of nonempty cluster blocks, has zero imaginary part.

## Goal

Turn the existing multivariate prime-support marker into a reusable zero-localized Lee--Yang block for every finite prime-word support.  The result must retain the full support incidence that scalar support-cardinality jets lose, extend the existing one-prime and two-prime blocks to arbitrary finite supports, and expose a finite-product consumer usable elsewhere in the Lean corpus.  It does not identify the completed source with such a product and therefore does not prove RH.

## Gates

- [x] 0 -> 1  in-progress: exact definitions exist in the live corpus, the statement is source-pure after centered-field evaluation, and the proof reduces to an exact norm identity
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3  formalized: Lean theorem names recorded, target build green, axiom audit and formal lint pass
- [ ] 3 -> 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For a finite support `P`, define the synchronized-cluster field monomial by
`M_P(z) = product_{p in P} p^(z - 1/2)` and its two-state partition block by
`Z_P(z) = 1 + M_P(z)`.  First prove that `M_P` is exactly the evaluation of
`primeWordSquarefreeMarker` at `centeredPrimeLeeYangField`.  Then use the existing
single-prime norm law to obtain
`norm (M_P(z)) = exp ((sum_{p in P} log p) * im z)`.
If `P` is nonempty, the logarithmic sum is positive; hence `Z_P(z) = 0` forces
the norm to be one and therefore `im z = 0`.  Finally pass the conclusion through
`Finset.prod_eq_zero_iff` to finite products of nonempty prime-word cluster blocks.

## Proof `[PROVED HERE]`

Let `L_P = sum_{p in P} log p`.  Multiplicativity of the complex norm and the existing centered
prime-field identity give

`norm (M_P(z)) = product_{p in P} exp (log(p) * im(z)) = exp (L_P * im(z))`.

If `P` is nonempty, every prime in `P` is greater than one, so every `log p` is positive and hence
`L_P > 0`.  If `Z_P(z) = 1 + M_P(z) = 0`, then `M_P(z) = -1`, so its norm is one.  Injectivity of
the real exponential gives `L_P * im(z) = 0`; positivity of `L_P` forces `im(z) = 0`.  For an empty
support the block is the constant `2`, so it has no zero.

For a prime word `w`, generic multivariate-polynomial evaluation sends each variable `X_p` to the
centered prime field at `p`; therefore the squarefree marker evaluates to the product over exactly
`primeWordSupport w`, which is `M_(support w)`.  Finally, if a finite product of nonempty word blocks
vanishes, `Finset.prod_eq_zero_iff` selects a vanishing factor, and the preceding argument applies.

The analytic specialization is support-faithful, not merely zero-localized.  At `z = I`, direct
evaluation gives `centeredPrimeLeeYangField p I = p`, so `M_P(I)` is the ordinary squarefree product
of the primes in `P`.  The exponent of a prime `p` in that product is exactly the indicator of
`p ∈ P`; unique factorization therefore makes `P ↦ M_P(I)` injective.  Consequently two prime-word
marker evaluations at `I` are equal exactly when their complete distinct-prime supports are equal.
In particular, this analytic specialization still separates the explicit singleton/doubled word
pair that every binary signing character identifies.

## Physics provenance

- T. D. Lee and C. N. Yang, *Statistical Theory of Equations of State and Phase Transitions. II*,
  Physical Review 87 (1952), 410--419, DOI `10.1103/PhysRev.87.410`.
- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model. I. Introduction and relation to
  other models*, Physica 57 (1972), 536--564, DOI `10.1016/0031-8914(72)90045-6`.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin--Kasteleyn--Swendsen--Wang
  representation and Monte Carlo algorithm*, Physical Review D 38 (1988), 2009--2012,
  DOI `10.1103/PhysRevD.38.2009`.

The first source supplies the circle-zero geometry for ferromagnetic Ising partition functions;
the latter two supply the exact common-spin cluster interpretation.  The Lean theorem uses only
the resulting finite two-state block and proves its zero geometry directly.

## Downstream application target

- Give `PrimeSupportMultivariateLiftMarker` a generic commutative-ring evaluation theorem.
- Connect that marker directly to `PrimeLeeYangPolydisk.centeredPrimeLeeYangField`.
- Export an arbitrary finite-product zero-localization theorem from `RHTower.lean`.
- Reuse the block in source-factorization arguments only when an exact factorization into these support blocks is available; do not treat the physics interpretation as that missing comparison.

## Lean certificate

- `GaloisForLFunctions.RHTower.eval₂Hom_primeWordSquarefreeMarker`
- `RHTower.primeLeeYangLog_pos`
- `RHTower.centeredPrimeLeeYangField_I`
- `GaloisForLFunctions.RHTower.eval₂Hom_primeWordSquarefreeMarker_centeredPrimeLeeYangField`
- `GaloisForLFunctions.RHTower.norm_synchronizedPrimeClusterField`
- `GaloisForLFunctions.RHTower.synchronizedPrimeClusterPartition_zero_im`
- `GaloisForLFunctions.RHTower.factorization_primeSupportProduct`
- `GaloisForLFunctions.RHTower.primeSupportProduct_injective`
- `GaloisForLFunctions.RHTower.synchronizedPrimeClusterField_I_injective`
- `GaloisForLFunctions.RHTower.primeWordSynchronizedClusterPartition_eq_one_add_markerEval`
- `GaloisForLFunctions.RHTower.centeredPrimeLeeYangMarkerEval_I_eq_iff_support_eq`
- `GaloisForLFunctions.RHTower.centeredPrimeLeeYangMarkerEval_I_separates_parityBlindWords`
- `GaloisForLFunctions.RHTower.primeWordSynchronizedClusterPartition_zero_im_of_ne_nil`
- `GaloisForLFunctions.RHTower.primeWordSynchronizedClusterEnsemblePartition_zero_im`

Verification on 2026-07-14:

- Target build passed: `8567/8567` jobs.
- `RHTower` umbrella build passed once at `10086/10086` jobs before the support-faithfulness
  extension.  After that extension the target rebuilt green; a fresh umbrella attempt failed only
  in the unrelated concurrently edited `PrimeArchCofinalHausdorffDiagonalRH.lean`.
- Axiom audit for all listed declarations: `[propext, Classical.choice, Quot.sound]` only.
- `scripts/formal_tools.py lint` passed.
- Generated formal index refreshed; `git diff --check` passed.

## Open core

The completed source has not been proved to factor into synchronized-cluster blocks.  Sums or interacting mixtures of the blocks are not controlled by the finite-product theorem.  The result supplies a support-sensitive library primitive and an exact sufficient condition, not the missing completed-source comparison.

## Log

- 2026-07-14 -- Created in `1-in-progress` after eliminating already-saturated KMS and scalar Rayleigh routes; selected because it gives an exact consumer for the live multivariate support marker.
- 2026-07-14 -- Paper proof completed and formalized in `PrimeWordSynchronizedCluster.lean`; promoted to `3-formalized` after target and umbrella builds, axiom audit, formal lint, index, and whitespace checks passed.
- 2026-07-14 -- Added the `z = I` support-faithfulness theorem and used it to separate the corpus's explicit parity-blind word pair after centered Lee--Yang specialization; target build, axiom audit, lint, index, and diff checks passed.
