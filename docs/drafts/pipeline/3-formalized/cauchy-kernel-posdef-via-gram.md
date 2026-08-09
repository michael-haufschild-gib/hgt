# The half-plane Cauchy kernel is positive definite, via mathlib's Gram theory

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## What the corpus had

`RHTower/GammaSewnMobiusXiWardHardyNonexpansive.lean` defines
`rightHalfPlaneHardyCauchyGram w i j = 1/(wᵢ + conj wⱼ)` and proves it hermitian and **positive
semidefinite**, the latter by an explicit boundary-integral computation (a feature map, a quadratic
integrand, two integrability lemmas, and an integral evaluation).

## What this adds

`BaezDuarteDetectorGram.inner_bdDetector_eq_cauchyGram` had already identified that matrix as the Gram
matrix of the Mellin detector vectors of the Nyman--Beurling carrier. `RHTower/BaezDuarteDetectorIndependence.lean`
turns the identification into a matrix equation and pushes it through mathlib's Gram theory
(`Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`, which the corpus was not using):

* `rightHalfPlaneHardyCauchyGram_eq_gram` — `rightHalfPlaneHardyCauchyGram w = Matrix.gram ℂ (detectors)`.
  With this, `Matrix.posSemidef_gram` reproves the corpus's PSD theorem in one line, and the corpus's
  hermitian theorem is `Matrix.isHermitian_gram`.  (I did not delete the corpus's integral proof: importing
  the Mellin carrier into that widely-used module would be a bad structural trade.  The identification is
  now a theorem rather than a docstring remark.)
* `linearIndependent_bdDetector` — **the detectors at distinct points of `Re s < ½` are linearly
  independent.**  Proof: a vanishing combination, paired with a further detector, is the partial-fraction
  identity `∑ᵢ aᵢ/(cᵢ − t) = 0` for every `t` in the half-plane, with `cᵢ = 1 − conj sᵢ` distinct and
  `Re(cᵢ − t) > 0` so no denominator vanishes.  Clearing denominators gives a polynomial vanishing on an
  infinite set, hence the zero polynomial; evaluating it at `cₖ` isolates `aₖ`.
* **`rightHalfPlaneHardyCauchyGram_posDef` — the Cauchy kernel at *distinct* points with `Re w > 0` is
  positive definite**, via `Matrix.posDef_gram_iff_linearIndependent`.  This is new: the corpus had only
  semidefiniteness.
* `det_rightHalfPlaneHardyCauchyGram_ne_zero` — hence nonsingular.  This is the nonvanishing of the Cauchy
  determinant obtained *without* the determinant formula, which mathlib does not have.
* `linearIndependent_bdDetector_zeros` — the instance at distinct zeta zeros in the right half of the
  strip.

All `#print axioms` clean.

## Why it matters

Two things, one structural and one for the route.

**Structural.** A bespoke integral computation in the corpus is an instance of a general theorem about Gram
matrices. That is the cheapest kind of audit win: the general fact was already available in mathlib and the
corpus was not connected to it. The connection also hands the Cauchy matrix mathlib's whole Gram toolkit
(submatrix behaviour, the operator-norm inequality `‖f‖²·gram − gram∘f ⪰ 0`, the determinant criterion).

**Route.** For the Nyman--Beurling floor of `BaezDuarteDetectorGram.bdTarget_dist_floor_orthonormal` this
says the many-zero bound is *nondegenerate*: `n` distinct zeros give `n` linearly independent detectors, so
an orthonormal family of full size `n` exists inside their span and every zero contributes a strictly
positive amount to the floor. Before this, the floor was stated for whatever orthonormal family one could
produce, with no guarantee that a hypothetical second zero adds anything.
