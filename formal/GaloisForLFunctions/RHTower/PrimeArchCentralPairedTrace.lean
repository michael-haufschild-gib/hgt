import GaloisForLFunctions.RHTower.PrimeArchCentralPairedDiagonalSourceBarrier
import GaloisForLFunctions.RHTower.PrimeArchLineConjSummation

/-!
# Central Route-Q sign for the literal continued source trace

The atomwise source barrier and absolute line-conjugate summation yield the sector sign of the
actual continued prime--Gamma reciprocal-square trace.
-/

open Complex

namespace RHTower

noncomputable section

/-- The actual continued prime--Gamma reciprocal-square trace has nonnegative sector phase on
the central Route-Q band. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_nonneg_central
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 ≤ (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    exact (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzim hzimUpper hzeta]
  exact centralPaired_tsum_im_nonneg_of_lineConj_pairs
    (xiReciprocalSquareResolventTerm z)
    (summable_xiReciprocalSquareResolventTerm hXi)
    (fun q =>
      xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_central
        z hzre hzreUpper hzim q hXi)

end

end RHTower
