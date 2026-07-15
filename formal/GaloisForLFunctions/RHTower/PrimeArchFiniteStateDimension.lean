import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank
import GaloisForLFunctions.RHTower.PrimeArchFiniteSpectralDimension

/-!
# Prime--archimedean clocks require unbounded hidden-state dimension

The finite-spectral dimension obstruction is strengthened from diagonal spectral responses to
arbitrary real finite-dimensional linear state-space responses.  At every fixed hidden dimension
`d`, local approximation of all finite normalized prime--Gamma moment blocks would force the
source Hankel determinant of size `d+1` to vanish.

Thus one nonzero determinant excludes that hidden dimension unconditionally, and RH excludes every
fixed dimension.  The conclusion covers finite hidden Markov, weighted-automaton, linear recurrent,
and finite transfer-matrix architectures after their scalar response is placed in the standard
`output ⬝ᵥ A^n *ᵥ input` form.  It is a dimension-growth constraint, not an RH proof.
-/

namespace RHTower

noncomputable section

/-- The prime--archimedean source is locally approximable by scalar responses of real linear
state-space models whose hidden dimension is bounded once and for all by `d`. -/
def PrimeArchFixedStateSpaceDimensionLocalClosure (d : ℕ) : Prop :=
  HTGeometry.FixedStateSpaceDimensionLocalClosure d normalizedPrimeArchMoment

/-- The older fixed spectral-width hypothesis implies the stronger state-space approximation
hypothesis at the same dimension. -/
theorem primeArchFixedStateSpaceDimensionLocalClosure_of_fixedSpectralWidth
    {d : ℕ} (h : PrimeArchFixedSpectralWidthLocalClosure d) :
    PrimeArchFixedStateSpaceDimensionLocalClosure d :=
  HTGeometry.fixedStateSpaceDimensionLocalClosure_of_fixedSpectralWidthLocalClosure h

/-- A fixed-dimensional local prime--archimedean state-space realization forces the first Hankel
determinant beyond that dimension to vanish. -/
theorem det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure
    {d : ℕ} (h : PrimeArchFixedStateSpaceDimensionLocalClosure d) :
    (primeArchSourceMomentHankelMatrix (d + 1)).det = 0 := by
  rw [primeArchSourceMomentHankelMatrix_eq_momentHankelMatrix]
  exact HTGeometry.det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure h

/-- One nonzero source determinant rules out every real `d`-state linear realization, not only a
diagonal finite-spectrum clock. -/
theorem not_primeArchFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
    {d : ℕ} (hdet : (primeArchSourceMomentHankelMatrix (d + 1)).det ≠ 0) :
    ¬ PrimeArchFixedStateSpaceDimensionLocalClosure d := by
  intro h
  exact hdet
    (det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure h)

/-- Hidden dimension zero is excluded unconditionally. -/
theorem not_primeArchFixedStateSpaceDimensionLocalClosure_zero :
    ¬ PrimeArchFixedStateSpaceDimensionLocalClosure 0 := by
  apply not_primeArchFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  simpa using ne_of_gt det_primeArchSourceMomentHankelMatrix_one_pos

/-- **RH hidden-dimension growth law.**  Under RH no uniformly bounded finite-state linear,
hidden-Markov, transfer-matrix, or recurrent realization can approximate all finite source
observation blocks. -/
theorem not_primeArchFixedStateSpaceDimensionLocalClosure_of_riemannHypothesis
    (hRH : RiemannHypothesis) (d : ℕ) :
    ¬ PrimeArchFixedStateSpaceDimensionLocalClosure d := by
  apply not_primeArchFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt
    ((primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH) (d + 1))

end

end RHTower
