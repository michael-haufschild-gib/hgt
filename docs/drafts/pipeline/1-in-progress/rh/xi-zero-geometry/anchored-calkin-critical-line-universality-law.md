# Anchored Calkin critical-line universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_essentialNorm_decay`: pointwise cofinal
  charge-scaled Calkin decay kills the first-prime seam.
- `orbitwiseFirstPrimeSeamCharge_eq_zero_iff`: the first-prime seam vanishes exactly on the
  critical line.
- `firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff`: each anchored
  commutator is compact exactly when its two prime seam charges agree.
- `orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half`: every single prime seam is faithful to the
  critical line.
- `xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff`: the calibrated Hurwitz boundary seam has the
  same open-strip zero fibre.

Existing global theorems quantify only over Xi divisor support. Reading the pointwise source
statements together exposes a divisor-independent four-chart classification on the whole open
strip.

## Universal law

For every positive aperture and every point in the open critical strip, the following are
equivalent: cofinal decay of the charge-scaled anchored commutator essential norm; compactness of
every anchored `{2,q}` commutator; vanishing of the calibrated prime-two Euler/Hurwitz boundary
seam; and `Re rho = 1/2`.

## Paper proof

Cofinal decay kills the first-prime seam and hence forces the critical line. On the line every
prime seam vanishes, so all anchored commutators are compact and their essential norms are zero;
unbounded primes give cofinal decay. Conversely, compactness at every partner prime gives cofinal
zero essential norm and therefore the line. The calibrated boundary-seam equivalence supplies the
fourth chart. No numerical computation is used.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.AnchoredCalkinCriticalLineUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
