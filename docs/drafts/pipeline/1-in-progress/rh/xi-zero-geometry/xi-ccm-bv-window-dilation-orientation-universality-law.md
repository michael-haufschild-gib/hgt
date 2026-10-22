# Xi CCM BV-window dilation orientation universality law

## Status

In progress — paper proof and Lean source complete; exact check deferred until final dependency
audit because `XiCCMMultiObservableDivisorUniversalityLaw` has no cached object file.

## Theorem-first provenance

- `RHTower/BVPrimeWindowDilationOrientation.lean`
  - `mellinTransform_argumentDilation`
  - `mellinTransform_argumentExpansion`
  - `weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul`
  - `polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul`
  - `continuedSourceResidueValue_argumentDilation`
  - `continuedSourceResidueValue_argumentExpansion`
  - `continuedSourceResidueOrientation_pos_iff`
  - `tendsto_argumentDilation_expansion_continuedSource_residues`
- `RHTower/XiCCMMultiObservableDivisorUniversalityLaw.lean`
  - `xiRightZero_ccmMultiObservableDivisorUniversalCertificate`

## Universal law

At every right Xi divisor copy, one compact BV prime window noncensoring the divisor generates two
complete nine-observable tomography packets under every integer dilation `r > 1`: one from forward
argument dilation and one from inverse dilation.  Both normalized packets recover the same Xi
multiplicity, but their raw actual residues acquire opposite Mellin characters
`r^(ρ-1/2)` and `r^(1/2-ρ)`.  Their forward-minus-inverse squared residue norm is therefore strictly
positive.

For the same pair, before analytic continuation, finite prime windows and complete
prime-archimedean polar coefficients obey literal square-index decimation `n ↦ r²n`.  The local
off-critical divisor orientation is thus the continued image of an exact finite source action,
while normalization erases that action and preserves universal multiplicity tomography.

## Paper proof

The Mellin scaling identities show that nonvanishing of the original window at the shifted divisor
implies nonvanishing of both dilated windows because positive-real complex powers never vanish.
Apply the nine-chart tomography theorem to each window.  The residue-character identities give the
opposite raw characters, and positivity of the Xi multiplicity makes the base residue nonzero.
Since a right divisor has `Re ρ > 1/2`, the exact orientation sign theorem gives strict positivity.
The two finite square-index laws and the punctured residue-limit theorem apply to the same source
pair directly.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/XiCCMBVWindowDilationOrientationUniversalityLaw.lean`.

Full source check is deferred solely because imported
`GaloisForLFunctions.RHTower.XiCCMMultiObservableDivisorUniversalityLaw.olean` is absent; no
dependency build was run before final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the dilation/decimation/orientation source law and the nine-chart normalized tomography law as
separate terminal modules, but no theorem proving that one finite dilation pair simultaneously
produces two universal tomographies and a strictly oriented raw-residue discriminator.
