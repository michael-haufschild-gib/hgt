import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion

/-!
# Prime--archimedean clocks require unbounded spectral dimension

The general finite-spectral Hankel obstruction is applied here to the normalized prime--Gamma
moment source.  At any fixed width `d`, local approximation of every finite source block would
force the source Hankel determinant of size `d + 1` to vanish.  Consequently:

* one nonzero determinant excludes that width;
* RH excludes every fixed width, because it makes every leading source determinant positive;
* every RH-compatible finite-clock approximation necessarily uses dimensions tending beyond every
  fixed bound.

This is a route constraint, not an RH proof: it identifies the dimension growth that any successful
finite-clock approximation must contain.
-/

namespace RHTower

noncomputable section

/-- The prime--archimedean source is locally approximable by real spectral clocks whose number of
observable lines is bounded once and for all by `d`.  Signed masses and arbitrary real nodes are
allowed, so failure of this property also excludes all positive/KMS subclasses of width `d`. -/
def PrimeArchFixedSpectralWidthLocalClosure (d : ℕ) : Prop :=
  HTGeometry.FixedSpectralWidthLocalClosure d normalizedPrimeArchMoment

/-- The source-side matrix and the general HTGeometry moment matrix are the same finite value
observable. -/
theorem primeArchSourceMomentHankelMatrix_eq_momentHankelMatrix (n : ℕ) :
    primeArchSourceMomentHankelMatrix n =
      HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n := by
  ext i j
  rfl

/-- A fixed-width local prime--archimedean clock forces the first Hankel determinant beyond that
width to vanish. -/
theorem det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure
    {d : ℕ} (h : PrimeArchFixedSpectralWidthLocalClosure d) :
    (primeArchSourceMomentHankelMatrix (d + 1)).det = 0 := by
  rw [primeArchSourceMomentHankelMatrix_eq_momentHankelMatrix]
  exact HTGeometry.det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure h

/-- A single nonzero source determinant discharges the negation of a fixed spectral-width
approximation hypothesis. -/
theorem not_primeArchFixedSpectralWidthLocalClosure_of_det_ne_zero
    {d : ℕ} (hdet : (primeArchSourceMomentHankelMatrix (d + 1)).det ≠ 0) :
    ¬ PrimeArchFixedSpectralWidthLocalClosure d := by
  intro h
  exact hdet
    (det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure h)

/-- Width zero is excluded unconditionally by the already-proved positivity of the first source
determinant. -/
theorem not_primeArchFixedSpectralWidthLocalClosure_zero :
    ¬ PrimeArchFixedSpectralWidthLocalClosure 0 := by
  apply not_primeArchFixedSpectralWidthLocalClosure_of_det_ne_zero
  simpa using ne_of_gt det_primeArchSourceMomentHankelMatrix_one_pos

/-- **RH dimension-growth law.**  Under RH no uniformly bounded number of observable spectral
lines can approximate all finite prime--archimedean source blocks. -/
theorem not_primeArchFixedSpectralWidthLocalClosure_of_riemannHypothesis
    (hRH : RiemannHypothesis) (d : ℕ) :
    ¬ PrimeArchFixedSpectralWidthLocalClosure d := by
  apply not_primeArchFixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt
    ((primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH) (d + 1))

end

end RHTower
