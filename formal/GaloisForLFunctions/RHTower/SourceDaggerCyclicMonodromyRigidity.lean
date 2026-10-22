import GaloisForLFunctions.RHTower.Deninger.DeningerOneSidedFramedMateCurvatureTransgression
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Source--dagger cyclic monodromy rigidity

A degree-one cyclic source has rotation square equal to the identity.  If a
nonzero source atom lands equivariantly in a paracyclic boundary whose
rotation square is scalar monodromy, retained cyclicity forces that scalar
to be one.

For the Deninger half-density boundary, the scalar is the mate gain
`exp ((2 * re s - 1) * log n)`.  Thus a nonzero equivariant atom at any
integer clock `n ≥ 2` forces `re s = 1/2`.  Applying this on every Xi divisor
fibre proves RH.  The final theorem is a consumer: it does not construct the
source-first equivariant landing or its non-erasure property.
-/

open Complex

namespace RHTower

noncomputable section

/-- Gauge-normalized degree-one mixed source-inverse/analytic-dagger
rotation.  Its square is the half-density mate gain. -/
def sourceDaggerNormalizedDegreeOneRotation
    (n : ℕ) (s : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (z.2, (deningerHalfDensityMateGain n s : ℂ) * z.1)

/-- The target rotation is paracyclic: its degree-one monodromy is exactly
the Deninger half-density mate gain. -/
theorem sourceDaggerNormalizedDegreeOneRotation_sq
    (n : ℕ) (s : ℂ) (z : ℂ × ℂ) :
    sourceDaggerNormalizedDegreeOneRotation n s
        (sourceDaggerNormalizedDegreeOneRotation n s z) =
      (deningerHalfDensityMateGain n s : ℂ) • z := by
  ext <;> simp [sourceDaggerNormalizedDegreeOneRotation]

/-- **Retained-cyclicity rigidity.** A nonzero atom transported from a
degree-one cyclic source into a scalar-monodromy paracyclic target forces
trivial target monodromy. -/
theorem retainedCyclicity_forces_monodromy_one
    {S : Type*} (rotate : S → S) (land : S → ℂ × ℂ)
    (targetRotate : ℂ × ℂ → ℂ × ℂ) (delta : ℂ)
    (hsource : ∀ x, rotate (rotate x) = x)
    (hintertwine : ∀ x, land (rotate x) = targetRotate (land x))
    (htarget : ∀ z, targetRotate (targetRotate z) = delta • z)
    {x : S} (hnonzero : land x ≠ 0) :
    delta = 1 := by
  have hfixed : delta • land x = land x := by
    rw [← htarget (land x), ← hintertwine, ← hintertwine, hsource]
  have hzero : (delta - 1) • land x = 0 := by
    rw [sub_smul, one_smul, hfixed, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hnonzero)

/-- A nonzero equivariant source atom at one nontrivial integer clock forces
the critical half-density line. -/
theorem re_eq_half_of_sourceDaggerCyclicLanding
    {S : Type*} (rotate : S → S) (land : S → ℂ × ℂ)
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ)
    (hsource : ∀ x, rotate (rotate x) = x)
    (hintertwine : ∀ x,
      land (rotate x) =
        sourceDaggerNormalizedDegreeOneRotation n s (land x))
    {x : S} (hnonzero : land x ≠ 0) :
    s.re = 1 / 2 := by
  have hgainC : (deningerHalfDensityMateGain n s : ℂ) = 1 :=
    retainedCyclicity_forces_monodromy_one rotate land
      (sourceDaggerNormalizedDegreeOneRotation n s)
      (deningerHalfDensityMateGain n s : ℂ)
      hsource hintertwine
      (sourceDaggerNormalizedDegreeOneRotation_sq n s)
      hnonzero
  have hgain : deningerHalfDensityMateGain n s = 1 := by
    exact_mod_cast hgainC
  rw [deningerHalfDensityMateGain] at hgain
  have hexp := (Real.exp_eq_one_iff _).mp hgain
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  rcases mul_eq_zero.mp hexp with hre | hnlog
  · linarith
  · exact False.elim (ne_of_gt hlog hnlog)

/-- **RH consumer.** One fixed cyclic source atom, retained nontrivially and
equivariantly by the mixed source--dagger landing on every Xi divisor fibre,
forces the Riemann hypothesis.  The landing and its atomic non-erasure are
explicit hypotheses, not constructed here. -/
theorem riemannHypothesis_of_sourceDaggerCyclicAtomicLanding
    {S : Type*} (rotate : S → S) (atom : S) (n : ℕ) (hn : 2 ≤ n)
    (land : XiDivisorSupport → S → ℂ × ℂ)
    (hsource : ∀ x, rotate (rotate x) = x)
    (hintertwine : ∀ rho x,
      land rho (rotate x) =
        sourceDaggerNormalizedDegreeOneRotation n (rho : ℂ)
          (land rho x))
    (hnonzero : ∀ rho, land rho atom ≠ 0) :
    RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  intro rho
  apply (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2
  exact re_eq_half_of_sourceDaggerCyclicLanding rotate (land rho) hn
    (rho : ℂ) hsource (hintertwine rho) (hnonzero rho)

end

end RHTower
