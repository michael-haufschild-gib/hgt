# Gamma factorial tail/covariant-residue universality law

## Status

Paper proof closed.  Lean connector written; exact module check deferred to final dependency build.

## Theorem-first source

- `tendsto_gammaFactorialScaledPolygamma_even_finiteTail` identifies the order-`2r+2` factorial
  microscope tail as `-(2r+1)!`.
- `norm_gammaPoleCovariantTopResidueValue_eq_factorial_pow_mul_factorial` identifies the norm of
  the grade-`j` covariant top residue at pole branch zero as `j!`.

Whole-corpus search found no theorem relating the analytic tail and covariant residue frame.

## Universal law

For every `r` and every nonzero microscope coordinate `x`, the even finite-tail limit at order
`2r+2` equals the negative norm of the grade-`2r+1` intrinsic covariant top residue at the initial
Gamma pole.

## Paper proof

The finite-tail theorem gives limit `-(2r+1)!`.  Substitute branch `0`, ambient jet order
`2r+1`, and top grade `j = 2r+1` into the covariant tensor law.  Its norm is
`(0!)^(2r+1) (2r+1)! = (2r+1)!`.  Replacing the factorial in the first identity by this exact norm
proves the claim.

## Lean status

- Module:
  `GaloisForLFunctions.HTGeometry.GammaFactorialTailCovariantResidueUniversalityLaw`
- Theorem:
  `GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm`
- Current blocker: cached object file for
  `GaloisForLFunctions.HTGeometry.GammaFactorialJetConnectionTensorLaw` does not exist.  Under the
  build discipline, dependency construction is reserved for final `lake build <module>` audit.

## Novelty audit

Pending literature audit after theorem-generation phase.  Corpus audit is negative.
