# FZZ puncture two-channel Plücker classification

- **ID:** FZZ-P-TCPC
- **Stage:** 3-formalized
- **Type:** MATRIX CLASSIFICATION / NO-GO SURVIVOR
- **Parent:** FZZ-P
- **Frontier-map policy:** read only; no edit made

## Exact result

Let `(p,q) ≠ (0,0)` be an internal row, `(c₀,c₁)` the affine puncture source's
on-shell row, and `(d₀,d₁)` its transverse-slope row.  A nonzero amplitude
`(a₀,a₁)` can satisfy the internal kernel equation

`p a₀ + q a₁ = 0`

and carry an FZZ affine-channel point mode at target energy `E` if and only if

`q c₀ - p c₁ = 0` and `q d₀ - p d₁ ≠ 0`.

Thus occurrence is exactly Plücker alignment of the internal and on-shell rows,
together with Plücker transversality of the internal and slope rows.  The
criterion is independent of `E` unless the dynamics itself gives the rows
nontrivial energy dependence.

## Paper proof

Existing affine-channel classification says a point mode is equivalent to

`a₀ c₀ + a₁ c₁ = 0` and `a₀ d₀ + a₁ d₁ ≠ 0`.

For the forward direction, combine the first equation with the internal-row
kernel equation.  Since `(a₀,a₁)` is nonzero, elimination of either nonzero
coordinate gives `q c₀-p c₁=0`.  If also `q d₀-p d₁=0`, elimination with either
nonzero coordinate of `(p,q)` forces `a₀d₀+a₁d₁=0`, contradiction.

For the reverse direction, choose the canonical internal-kernel amplitude
`(a₀,a₁)=(q,-p)`.  It is nonzero because the internal row is nonzero.  Its
on-shell collective is the first Plücker minor and its slope collective is the
second, proving the affine point-mode conditions.

## No-go closure and positive survivor

- If internal and slope rows are aligned, no point mode survives.
- Canonical data `(p,q,c₀,c₁,d₀,d₁)=(1,0,1,0,0,1)` realizes a point mode for
  every real target energy.
- Therefore unconstrained two-channel matrix mixing cannot be the zeta-selective
  content.  Remaining positive burden is dynamical: derive energy-dependent rows
  from the GFZZ/Feshbach operator and prove their two Plücker minors vanish and do
  not vanish exactly on the required zeta set.

This is stronger than a negative result: it isolates the exact determinant
invariant any viable two-channel completion must control.

## Hostile review

- No spectral conclusion is inferred from arbitrary fitted rows.
- Nonzero internal row and nonzero amplitude are explicit.
- Transversality is essential; dropping it admits zero source slope and destroys
  the point mode.
- Energy independence of the abstract criterion is exposed, not hidden.
- Result does not claim the physical GFZZ operator realizes the required minors.

## Novelty audit (2026-08-27)

Corpus search found affine finite-channel source classification, rank-one box
models, fractional thresholds, and weighted-source rigidity, but no internal-row
or Plücker classification.  Primary-literature searches covering rank-one
Friedrichs thresholds, two-channel Feshbach `R`-matrix models, and structured
continua found no exact FZZ-puncture theorem with this alignment/transversality
criterion.  Priority remains provisional pending expert review.

Primary comparison sources:

- arXiv:math/0604277, *The threshold effects for a family of Friedrichs models*
- arXiv:cond-mat/0601542, two-channel Feshbach `R`-matrix analysis
- arXiv:0802.3808, structured-continuum Fano/Feshbach model

## Lean realization

Module:
`GaloisForLFunctions.RHTower.FZZCigarPunctureTwoChannelPluckerClassification`

Theorems:

- `fzzPunctureAffineCollectiveOnShell_two`
- `fzzPunctureAffineCollectiveSlope_two`
- `fzzPunctureTwoChannelInternalRowPointMode_iff`
- `not_fzzPunctureTwoChannelInternalRowPointMode_of_slope_aligned`
- `fzzPunctureCanonicalTwoChannelInternalRowPointMode`

Verification:

- direct `lake env lean` passed
- targeted module `lake build` passed
- exported theorem axiom audit passed: only standard Mathlib axioms
- imported by `GaloisForLFunctions.RHTower`
