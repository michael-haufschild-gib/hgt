/-
The finite compression fires on a concrete crossing operator: §1 tower → §8 Hodge compression.

`seam_hodge_compression_finite` (in `SeamFiniteHodge`) compresses the flat supertrace onto the harmonic
projection for *any* odd square-zero differential.  Its hypotheses — `d² = 0` and a grading `Γ` making
`d` odd — are exactly the structure a seam crossing operator carries (`SeamCrossingMatrix`):
`crossOp_sq_zero` and `grade_crossOp_odd`.  So the compression is not merely an abstract lemma awaiting a
differential; it fires on the concrete §1 crossing operator.

`crossOp_compression` instantiates it: for the crossing differential `d = crossOp M r` with grading
`Γ = gradeOp M r`, and *any* operator `R` commuting with the crossing, the whole-complex supertrace
equals the supertrace on the crossing's harmonic block,
`superTrace Γ R = superTrace Γ (R · P)` with `P = seamHarmonicProj (crossOp M r)`.  This welds the
Hilbert–Schmidt crossing tower (§1, `crossOp_energy_law`) to the McKean–Singer Hodge compression (§8) on
a single concrete object — the finite construction realized, not hypothesized.
-/
import GaloisForLFunctions.RHTower.SeamCrossingMatrix
import GaloisForLFunctions.RHTower.SeamFiniteHodge

noncomputable section

namespace RHTower

open Matrix

/-- **The Hodge compression fires on a concrete crossing operator.**  For the crossing differential
`d = crossOp M r` (square-zero, `crossOp_sq_zero`) with grading `Γ = gradeOp M r` (odd on it,
`grade_crossOp_odd`), and any `R` commuting with the crossing, the flat supertrace compresses onto the
crossing's harmonic projection: `superTrace Γ R = superTrace Γ (R · seamHarmonicProj d)`.  The §1
crossing tower and the §8 compression meet on one concrete object. -/
theorem crossOp_compression (M r : ℕ) (R : Matrix (Fin M) (Fin M) ℂ)
    (hR : R * crossOp M r = crossOp M r * R) :
    superTrace (gradeOp M r) R
      = superTrace (gradeOp M r) (R * seamHarmonicProj (crossOp M r)) :=
  seam_hodge_compression_finite (gradeOp M r) R (crossOp M r)
    (crossOp_sq_zero M r) (grade_crossOp_odd M r) hR

end RHTower
