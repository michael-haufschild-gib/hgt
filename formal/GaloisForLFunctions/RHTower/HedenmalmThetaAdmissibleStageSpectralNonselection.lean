import GaloisForLFunctions.HTGeometry.TraceZeroNonrealDivisorDensity
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion

/-!
# Actual theta approximation axioms do not select real finite divisors

The signed theta completion chooses each finite stage using four recorded properties: finite
support, Hilbert--Schmidt regularity, prescribed approximation accuracy, and zero diagonal trace.
Those properties are spectrally nonselective.

At every requested accuracy, the arbitrary-target density theorem supplies another admissible
stage having an explicit nonreal ordinary Fredholm zero. This does not say the fixed
`Classical.choice` stage has a nonreal divisor. It proves that its recorded specification cannot
yield real-divisor or modewise Green-neutrality theorems. A successful replacement must record an
additional theta-arithmetic flag or boundary law.
-/

open Complex Matrix

namespace RHTower.HedenmalmThetaSource

open HilbertSchmidt GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every theta approximation accuracy admits a finite-support traceless source stage satisfying
the existing stage specification but carrying a nonreal ordinary Fredholm divisor. -/
theorem exists_thetaSourceSignedApproximationProperty_nonrealDivisor (k : ℕ) :
    ∃ (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) (z : ℂ),
      ThetaSourceSignedApproximationProperty k SK ∧
      ((1 : Matrix ↥SK.1 ↥SK.1 ℂ) - z • blockMatrix SK.2 SK.1).det = 0 ∧
      z.im ≠ 0 := by
  have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨s, K', z, hsupp, hHS, hclose, htrace, hdet, him⟩ :=
    exists_finiteSupport_traceZero_nonrealDivisor_close
      isHS_neg_thetaKernelMatrix hε
  exact ⟨⟨s, K'⟩, z, ⟨hsupp, hHS, hclose, htrace⟩, hdet, him⟩

/-- Closed source-specific nonselection certificate: every current approximation fibre contains a
stage with a nonreal divisor. -/
theorem thetaSourceSignedApproximationProperty_spectrally_nonselective :
    ∀ k : ℕ,
      ∃ (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) (z : ℂ),
        ThetaSourceSignedApproximationProperty k SK ∧
        ((1 : Matrix ↥SK.1 ↥SK.1 ℂ) - z • blockMatrix SK.2 SK.1).det = 0 ∧
        z.im ≠ 0 :=
  exists_thetaSourceSignedApproximationProperty_nonrealDivisor

end

end RHTower.HedenmalmThetaSource
