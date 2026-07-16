# Complex modal Hankel boundary for ringdown observations

- **ID:** `complex-modal-hankel-ringdown-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean target)
- **Register:** `[BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`

## Theorem

Let `K` be a field and let an observed sequence be a finite modal packet

```text
m(n) = sum_(a < d) weight(a) * node(a)^n.
```

Then its `(d+1) x (d+1)` Hankel determinant is zero.  In particular this applies over `C`, where
sampled black-hole quasinormal modes and damped neutron-star oscillations have complex nodes.
Conversely, one nonzero complex Hankel determinant excludes every exact modal presentation of the
corresponding width.

The nontrivial positive statement is exact mode counting.  If all `d` nodes are distinct and all
weights are nonzero, then

```text
det H_d = det(Vandermonde(node))^2 * product_a weight(a) != 0,
det H_(d+1) = 0.
```

Thus the first singular leading block occurs exactly one size above the number of active modes in
the noiseless model.

For the completed prime--Gamma moving complex moments, a nonzero determinant at a base point
therefore excludes a finite complex quasinormal-mode model there.  At the functional-equation
center, RH supplies nonvanishing in every size, so every fixed finite complex modal width is
excluded under RH.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/FiniteModalHankelRank.lean` proves:

- `algebraicHankelMatrix`;
- `finiteModalSequence` and `FiniteModalWidthAtMost`;
- `algebraicHankelMatrix_mulVec_nodePolynomial_eq_zero`;
- `det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero`;
- `det_algebraicHankelMatrix_succ_eq_zero_of_finiteModalWidthAtMost`;
- `not_finiteModalWidthAtMost_of_det_ne_zero`;
- `algebraicHankelMatrix_finiteModalSequence_eq_vandermonde`;
- `det_algebraicHankelMatrix_finiteModalSequence`;
- `det_algebraicHankelMatrix_finiteModalSequence_ne_zero`;
- `finiteModalSequence_exact_hankel_mode_count`.

`formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaComplexModalBoundary.lean` proves:

- `CompletedMovingComplexModalWidthAtMost`;
- `completedMovingComplexHankelMatrix_eq_algebraicHankelMatrix`;
- `completedMovingComplexHankelDet_eq_zero_of_modalWidthAtMost`;
- `not_completedMovingComplexModalWidthAtMost_of_det_ne_zero`;
- `not_completedMovingComplexModalWidthAtMost_one_half_of_riemannHypothesis`.

## Corpus delta

`FiniteSpectralHankelRank.lean` proves the boundary only for real masses and real nodes.  The new
theorem is field-generic and therefore covers damped/oscillatory complex frequencies directly.
The RHTower consumer composes with `completedMovingComplexHankelDet_one_half` and the existing
strict central Hankel determinant theorem.

## Physics provenance

- M. Giesler, M. Isi, M. Scheel, and S. Teukolsky, *Black hole ringdown: the importance of
  overtones*, arXiv:1903.08284.  Ringdown inference uses finite superpositions of quasinormal
  overtones.
- S. Bhagwat, X. Jimenez Forteza, P. Pani, and V. Ferrari, *Ringdown overtones, black hole
  spectroscopy, and no-hair theorem tests*, arXiv:1910.08708.  Spectroscopy resolves frequencies
  in a finite overtone superposition.
- P. Bosch, S. R. Green, and L. Lehner, *Nonlinear effects in the black hole ringdown:
  absorption-induced mode excitation*, arXiv:2112.11168.  The quasinormal contribution is a sum of
  residues `C_n exp(-i omega_n t)`; finite observational models truncate this modal response.
- Z.-Y. Zheng et al., *Non-radial oscillations and gravitational wave emission of hybrid neutron
  stars*, arXiv:2303.07086.  Neutron-star gravitational-wave asteroseismology is organized by mode
  frequencies and damping times.
- K. Hornbostel, G. P. Lepage, C. T. H. Davies, R. J. Dowdall, H. Na, and J. Shigemitsu, *Fast Fits
  for Lattice QCD Correlators*, arXiv:1111.1363.  Lattice-QCD correlators are fitted by finite sums
  of exponentials; the exact Vandermonde determinant and first-singular-block law give the
  corresponding noiseless active-state count over the same value interface.
- B. Blossier, M. Della Morte, G. von Hippel, T. Mendes, and R. Sommer, *On the generalized
  eigenvalue method for energies and matrix elements in lattice field theory*, arXiv:0902.1265.
  Increasing the interpolating-field family separates additional energy levels, matching the
  positive rank-growth side of the modal Hankel law.

## RH boundary

The theorem is not a source of RH positivity.  It strengthens route exclusion and hypothesis
discharge: a finite complex resonance or QNM ansatz cannot realize a completed-source moment
sequence once the corresponding determinant is known nonzero.  Under RH, the exclusion holds at
all widths; proving such nonvanishing independently of RH would be actual forward progress.

## Gates

- [x] existing real spectral and state-space boundaries audited
- [x] complex QNM observational form isolated from spacetime evolution
- [x] field-generic Hankel theorem proved in Lean
- [x] complex moving prime--Gamma consumer proved in Lean
- [x] targeted verification and axiom audit

## Verification

- one combined scratch proof passed before source insertion;
- one serialized targeted build of the deepest RHTower module was run because its `.olean` was
  absent and cached its single new HTGeometry dependency;
- both touched source files pass direct `lake env lean` checks;
- the four audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
- the exact determinant and mode-count declarations use the same three standard axioms;
- the lint gate reports neither new module as unreachable; the current repo-wide lint remains
  blocked by unrelated modules being added concurrently without umbrella imports;
- no numerical computation, full build, or self-concurrent Lean build was run.
