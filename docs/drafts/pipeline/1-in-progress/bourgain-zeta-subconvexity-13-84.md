# Bourgain critical-line subconvexity exponent 13/84

- **ID:** `bourgain-zeta-subconvexity-13-84`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean target)
- **Source:** J. Bourgain, *Decoupling, exponential sums and the Riemann zeta
  function*, JAMS 30 (2017), 205--224, DOI 10.1090/jams/860.
- **Statement:** `[LITERATURE]` For every `ε > 0` there are `C > 0` and `T ≥ 1`
  such that, for every real `t` with `T ≤ |t|`,
  `‖riemannZeta (1/2 + t*I)‖ ≤ C |t|^(13/84+ε)`.

## Goal

Produce a dependency-closed, unconditional Lean theorem matching Bourgain's
critical-line bound. No spacing, decoupling, exponential-sum, or approximate
functional-equation estimate may enter as a hypothesis of the final declaration.

## Gates

- [x] 0 → 1 in-progress: exact asymptotic statement, primary source, dependency
  graph, and current Lean wall identified.
- [ ] 1 → 2 fully-proven: transcribe and audit a dependency-closed paper proof,
  including every theorem imported by Bourgain from earlier literature.
- [ ] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and
  `#print axioms` pass.
- [ ] 3 → 4 publication-ready: source crosswalk and Lean certificate.

## Exact dependency ledger

1. `[LITERATURE]` Bourgain Theorem 1: multilinear decoupling for a
   non-degenerate curve in `R^4`. The proof imports planar curve decoupling and
   multilinear Fourier-restriction estimates.
2. `[LITERATURE]` Bourgain Theorem 2 and Corollary 3: the twelfth-power mean
   value `A₆ ≪ N^(6+ε)`, then the first-spacing estimate.
3. `[LITERATURE]` Section 3: Poisson/cubic localization, six-fold convolution,
   Bombieri--Iwaniec double large sieve, and Huxley's resonance-curve
   second-spacing estimate produce Theorem 4.
4. `[LITERATURE]` Section 4: Theorem 4 plus older exponent-pair bounds gives the
   uniform short exponential-sum estimate (3.19).
5. `[LITERATURE]` Classical approximate functional equation, partial summation,
   and dyadic dissection turn (3.19) into exponent `13/84`.

## Internal corpus audit

- `[CORPUS]` `ZetaVerticalSqrtBound.norm_riemannZeta_le_sqrt_norm_add_two_half`
  gives only square-root-scale growth.
- `[CORPUS]` first- and second-derivative van der Corput integral estimates are
  formalized in `VanDerCorput*.lean`.
- `[CORPUS]` `ZetaAFETransfer.zeta_norm_le_afe` is an unconditional
  Euler--Maclaurin transfer, not the symmetric height-dependent AFE.
- `[CORPUS]` `FourthMomentDiagonal.fourthMoment_bounded` retains its explicit
  off-diagonal double sum.
- `[LOCAL-RESEARCH] [PAPER-PROVED]`
  `hardy-critical-line-moment-anchor.md` contains a dependency-closed smooth
  symmetric AFE proof. This is also the first reusable Bourgain dependency and
  therefore enters Lean first.
- `[OPEN CORE]` After the smooth AFE, no analytic `L^p` decoupling,
  Bombieri--Iwaniec double large sieve, or Huxley second-spacing theorem exists
  in the corpus or current mathlib.

## Formalization order

1. Smooth symmetric AFE at conductor scale.
2. Partial-summation and dyadic reduction from uniform short logarithmic
   exponential sums to a critical-line zeta exponent.
3. Exponent-pair bounds used outside Bourgain's new estimate.
4. Double large sieve and Huxley second-spacing theorem.
5. Bourgain `A₆` mean value via curve decoupling.
6. Assemble the unconditional `13/84+ε` theorem and audit axioms.

## Log

- 2026-07-25 — primary paper and current Lean corpus audited. Route opened in
  Stage 1. Smooth symmetric AFE selected as first dependency because its complete
  paper proof already exists in the Stage-2 Hardy card and it is independently
  required by Bourgain Section 4.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]` partial summation and dyadic reduction
  closed in `BourgainPartialSummation.lean`, `BourgainDyadicDissection.lean`,
  and `BourgainZetaReduction.lean`. The exact critical-line Dirichlet polynomial
  is now connected to blockwise logarithmic phase sums and to the unconditional
  Euler--Maclaurin zeta transfer. Target builds, representative axiom audits,
  umbrella wiring, and formal lint pass. Smooth conductor-length AFE remains
  the first open analytic dependency.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]` Gaussian smooth-AFE contour
  infrastructure closed in six `SmoothAFEGaussian*.lean` modules: explicit
  vertical Gaussian majorants on every nonzero line, positive-abscissa
  invariance, entire divided-difference regularization, reciprocal contour
  limits, and exact unit residue across zero. Representative axiom audits use
  only `[propext, Classical.choice, Quot.sound]`. The remaining Stage-2 AFE
  core is now the zeta Dirichlet-series interchange, functional-equation
  reflection, and uniform Gamma-ratio/Stirling estimate; no Bourgain
  decoupling or spacing estimate has yet been discharged.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]`
  `SmoothAFEZetaMellin.lean` closes the absolute-half-plane zeta expansion:
  explicit `p`-series/Gaussian bounds prove vertical integrability of
  `ζ(s+w)x^w exp(w²)/w` for `1 < Re(s)+c`, termwise integrability of the
  Dirichlet series, summability of integral norms, and the justified
  integral/`tsum` interchange. Remaining smooth-AFE core is coefficient
  identification with the canonical cutoff, contour shift of `ζ(s+w)`,
  functional-equation reflection, and uniform Gamma-ratio control.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]`
  `SmoothAFEZetaDirichletExpansion.lean` identifies every termwise Mellin
  integral with the canonical Gaussian cutoff and proves the exact identity
  `A_c(s,x)=∑_{n≥1}n^{-s}V(n/x)` whenever `c>0` and
  `1<Re(s)+c`. The open smooth-AFE core is now the residue-bearing zeta
  contour shift, functional-equation reflection, and uniform Gamma-ratio
  estimate.
- 2026-07-25 — `[CORPUS] [LEAN-PROVED]`
  `BourgainLogExponentPair.hasLogExponentPair_zero_one` supplies the exact
  uniform-subinterval interface for the trivial pair `(0,1)`, using
  unimodularity and the triangle inequality. `[LITERATURE]` Bourgain's JAMS
  paper proves the `13/84` zeta exponent through its `A₆` first-spacing
  theorem, Bombieri--Iwaniec/Huxley second spacing, and older exponent-pair
  bounds; it does not make the current deep gap disappear by a direct
  elementary specialization. `[OPEN CORE]` The exact declaration
  `HasLogExponentPair (13/84) (55/84)` still requires formalizing that
  decoupling/spacing chain. No stronger corpus theorem currently supplies it.
