# Moving a transform zero preserves the Weil form

- **ID:** R0411-ZERO-MOVE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A smooth source supported in `[-r,r]`, whose Fourier transform vanishes at
  `κ`, admits a source at the same aperture with that transform zero moved to `conj(κ)` and
  with unchanged Weil form for every zero configuration.

## Exact statement

Let `r ≥ 0`, `f ∈ C∞_c([-r,r])`, and `F = paperFT f`, with `F(κ)=0`.
There exists `h ∈ C∞_c([-r,r])`, with transform `H`, such that

\[
 H(\bar\kappa)=0,\qquad
 (z-\kappa)H(z)=(z-\bar\kappa)F(z),\qquad
 W_Z(h,h)=W_Z(f,f)
\]

for every `z ∈ ℂ` and every zero configuration `Z`. No positivity assumption is needed.

## Proof

Compact division gives a smooth source `g` at the same aperture with
`F(z)=-i(z-κ)G(z)`, where `G=paperFT g`. Set `h=g'+i·conj(κ)g`.
Differentiation preserves support and gives `H(z)=-i(z-conj(κ))G(z)`.
Both diagonal Weil summands equal

\[
 (z-\kappa)(z-\bar\kappa)G(z)\overline{G(\bar z)}.
\]

The summands therefore agree term by term, hence so do their weighted sums.
The polynomial transform identity also holds at its removable point.

## Lean

Module: `CanonicalSystemOfTheWindowTower/MovingATransformZeroPreservesTheWeilForm.lean`.

- `pointImage_annihilate_conj`: equality of individual summands.
- `weilForm_annihilate_conj`: equality of full forms after conjugating a differential factor.
- `exists_same_aperture_zero_move`: source existence, support, transform identity, and form equality.

Final `lake --old env lean` check passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

This establishes zero-moving on the smooth compact core. Completion and canonical-system
realization of the actual pre-contact Weil spaces remain open.
