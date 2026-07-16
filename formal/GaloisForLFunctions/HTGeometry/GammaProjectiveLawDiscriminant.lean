import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial

/-!
# The actual Gamma function has a projective law discriminant

Place the Gamma function on a two-dimensional space of possible one-dimensional laws.  A law
`A = (a,b)` observes Gamma along the ray `s ↦ a s`; the second coordinate is a transverse law
which does not act on this observable.  Hölder's theorem and unconditional argument-scaling
invariance show that the observation is hypertranscendental exactly when `a ≠ 0`.

Thus the actual Gamma function, not merely its divisor, has one exact projective differential-
dependence horizon.  This is an instantiation of the pretemporal directional-law idea; the result
is a consequence of Hölder's theorem and is not itself claimed as the new curvature theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- Gamma observed along the one-dimensional law selected by `A = (a,b)`. -/
def gammaDirectionalObservation (A : ℂ × ℂ) : ℂ → ℂ :=
  fun s ↦ Complex.Gamma (A.1 * s)

/-- The actual Gamma ray is hypertranscendental exactly when the selected law has nonzero
longitudinal component. -/
theorem hypertranscendental_gammaDirectionalObservation_iff (A : ℂ × ℂ) :
    Hypertranscendental (gammaDirectionalObservation A) ↔ A.1 ≠ 0 := by
  constructor
  · intro hHT hzero
    apply hHT
    have hconst := differentiallyAlgebraic_const (Complex.Gamma 0)
    have hfun : gammaDirectionalObservation A = fun _ ↦ Complex.Gamma 0 := by
      funext s
      simp [gammaDirectionalObservation, hzero]
    rw [hfun]
    exact hconst
  · intro hnonzero
    simpa [gammaDirectionalObservation] using
      (hypertranscendental_gamma_affine hnonzero 0)

/-- Law directions along which the actual Gamma observation is differentially algebraic. -/
def gammaDirectionalDependenceSet : Set (ℂ × ℂ) :=
  {A | DifferentiallyAlgebraic (gammaDirectionalObservation A)}

/-- **Exact Gamma law horizon.**  The directional differential-dependence set of Gamma is the
single central hyperplane on which the longitudinal derivation component vanishes. -/
theorem gammaDirectionalDependenceSet_eq_longitudinalKernel :
    gammaDirectionalDependenceSet = {A | A.1 = 0} := by
  ext A
  change DifferentiallyAlgebraic (gammaDirectionalObservation A) ↔ A.1 = 0
  have hHT := hypertranscendental_gammaDirectionalObservation_iff A
  simpa [Hypertranscendental] using not_congr hHT

/-- The exact Gamma dependence horizon is projective: nonzero common rescaling of a law does not
change membership. -/
theorem smul_mem_gammaDirectionalDependenceSet_iff
    (c : ℂ) (hc : c ≠ 0) (A : ℂ × ℂ) :
    c • A ∈ gammaDirectionalDependenceSet ↔
      A ∈ gammaDirectionalDependenceSet := by
  rw [gammaDirectionalDependenceSet_eq_longitudinalKernel]
  simp only [Set.mem_setOf_eq, Prod.smul_fst, smul_eq_mul]
  exact mul_eq_zero.trans (or_iff_right hc)

end

end GaloisForLFunctions.HTGeometry
