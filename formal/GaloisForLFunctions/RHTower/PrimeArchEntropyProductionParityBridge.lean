import GaloisForLFunctions.RHTower.PrimeArchEntropyProductionResponseRH

/-!
# Parity bridge for entropy-production passive responses

The completed prime--Gamma source is odd under centered negative conjugation.  Directed
prime-only passive carriers fail its fixed-point test at `I / 4`.  In contrast, a Hermitian
finite KMS entropy-production stage has reversal-symmetric intensity.  This module proves its
literal response has the same oddness and negative-conjugation covariance, hence zero real
component at the source's fixed comparison point.  This is a compatibility result only: no
source-value or thermodynamic convergence assertion is made here.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Hermitian entropy-production intensities pair every transition with its reverse, so their
finite passive response is exactly odd in the centered spectral coordinate. -/
theorem finiteKMSEntropyProductionTransitionPassiveResponse_neg
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (z : ℂ) :
    HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy (-z) =
      -HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy z := by
  exact HTGeometry.finiteTransitionPassiveResponse_neg _ energy
    (finiteKMSEntropyProductionTransitionIntensity_symm β energy amplitude hHermitian) z

/-- The same finite response obeys the literal centered negative-conjugation covariance carried
by the completed prime--Gamma source. -/
theorem finiteKMSEntropyProductionTransitionPassiveResponse_negConj
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (z : ℂ) :
    HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy
          (-(starRingEnd ℂ) z) =
      -(starRingEnd ℂ) (HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy z) := by
  rw [finiteKMSEntropyProductionTransitionPassiveResponse_neg β energy amplitude hHermitian,
    ← HTGeometry.finiteTransitionPassiveResponse_conj]

/-- `I / 4` is fixed by centered negative conjugation.  Therefore every Hermitian
entropy-production finite stage has the exact source-compatible real-part normalization there. -/
theorem finiteKMSEntropyProductionTransitionPassiveResponse_re_eq_zero_at_I_div_four
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) :
    (HTGeometry.finiteTransitionPassiveResponse
      (finiteKMSEntropyProductionTransitionIntensity β energy amplitude) energy
      (Complex.I / 4)).re = 0 := by
  have h := finiteKMSEntropyProductionTransitionPassiveResponse_negConj
    β energy amplitude hHermitian (Complex.I / 4)
  have hfixed : (-(starRingEnd ℂ) (Complex.I / 4)) = Complex.I / 4 := by
    have hfour : (starRingEnd ℂ) (4 : ℂ) = 4 :=
      map_natCast (starRingEnd ℂ) 4
    rw [map_div₀, hfour]
    simp only [Complex.conj_I]
    ring
  rw [hfixed] at h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

end

end RHTower
