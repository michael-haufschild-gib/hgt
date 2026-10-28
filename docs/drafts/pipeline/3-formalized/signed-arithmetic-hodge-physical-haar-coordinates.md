# Actual source coordinates are the normalized Haar readouts

Let U embed the complete logarithmic-cell Hilbert space into whole-line L2,
using the existing cell embedding followed by extension by zero. U is an
isometry and U*U=1. For every compact real bounded-variation source f,
the (j,a) detail coordinate of U*f is exactly the complex lift of
the actual normalized Haar readout c(j,a).

Extension by zero intertwines every nonnegative half-line shift with literal
whole-line translation. At every dyadic level j>=0, the normalized cell-basis
vector therefore has waveform haarProfile(a)(x-j log 2)/sqrt(haarMass(a)).
The physical inner product, exact profile integral and positive mass prove
the coordinate identity. No identification of the entire continuous source
space with the cell completion is assumed.

Lean: `SignedArithmeticHodgeTheory/DyadicHaarCoordinatesReadTheOriginalSource.lean`.
Capstones: `norm_wholeLineLogCellEmbedding`,
`wholeLineLogCellEmbedding_adjoint_self`,
`halfLineExtend_haarAtom_pow_coeFn`,
`sqrt_mass_wholeLineLogCellOrbit_coeFn`,
`physicalLogCellCoordinates_detail`.
Final individual no-olean audit passes. Printed capstone dependencies contain
only `propext`, `Classical.choice`, `Quot.sound`.
