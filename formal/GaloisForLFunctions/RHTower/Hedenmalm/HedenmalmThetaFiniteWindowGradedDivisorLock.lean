import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGradedTraceDivisorLock

/-!
# Finite-window graded theta-source divisor lock

The first Newton trace window already blocks every finite graded or Krein repair of the theta
source.  Exact signed traces only through the total even rank force the cross-multiplied
superdeterminant identity.  If the even divisor is real, every source divisor is therefore real.

This strictly weakens the previous full graded-lift interface: the odd determinant may have poles,
no trace identity above the finite Newton window is required, and neither metric adjointness nor
coercive escape enters the divisor argument.  The latter fields are retained to show that they do
not create a loophole.

The module also proves that a finite pole-free odd sector has zero power trace in every positive
degree.  Such a sector cannot carry even the quadratic signed trace needed for coefficient-faithful
polarization.
-/

open Complex Matrix Finset
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite pole-free determinant sector has no positive-degree power trace. -/
theorem trace_pow_eq_zero_of_det_one_sub_smul_ne_zero_fin {n : ℕ}
    (O : Matrix (Fin n) (Fin n) ℂ)
    (hdet : ∀ z : ℂ,
      ((1 : Matrix (Fin n) (Fin n) ℂ) - z • O).det ≠ 0) :
    ∀ m : ℕ, 0 < m → (O ^ m).trace = 0 := by
  obtain ⟨U, T, hU1, hU2, hT, hOT⟩ := exists_schur_triangulation n O
  have hdiag : ∀ i, T i i = 0 := by
    intro i
    by_contra hi
    have hprod : ∏ j, (1 + (-(T i i)⁻¹) * T j j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [neg_mul, inv_mul_cancel₀ hi]
      norm_num
    have hformula :=
      det_one_add_smul_eq_prod hU2 hT hOT (-(T i i)⁻¹)
    have hzero :
        ((1 : Matrix (Fin n) (Fin n) ℂ) - (T i i)⁻¹ • O).det = 0 := by
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) - (T i i)⁻¹ • O =
          1 + (-(T i i)⁻¹) • O by module]
      rw [hformula]
      exact hprod
    exact hdet _ hzero
  intro m hm
  rw [trace_pow_eq_sum_diag hU1 hU2 hT hOT]
  simp [hdiag, ne_of_gt hm]

end

end GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Minimal graded/Krein polarization interface.  Only the finite Newton trace window and reality
of the even divisor are retained; no pole-free odd sector is assumed. -/
structure ThetaSourceFiniteWindowRealGradedPolarization where
  oddRank : ℕ → ℕ
  odd : (k : ℕ) → Matrix (Fin (oddRank k)) (Fin (oddRank k)) ℂ
  even : (k : ℕ) →
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  signedTrace : ∀ k m : ℕ,
    m ≤ Fintype.card (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) →
      ((even k) ^ m).trace - ((odd k) ^ m).trace =
        ((thetaSourceKreinFiniteMatrix k) ^ m).trace
  realDivisor : ∀ k : ℕ, ∀ z : ℂ,
    ((1 : Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
        (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ) -
      z • even k).det = 0 → z.im = 0
  polarization : (k : ℕ) →
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  metricAdjoint : ∀ k : ℕ,
    polarization k * even k = (even k)ᴴ * polarization k
  coerciveEscape : ∀ k : ℕ,
    (polarization k)ᴴ * polarization k =
      ((((k : ℝ) + 1) ^ (2 : ℕ) : ℝ) : ℂ) • 1

/-- First total-rank signed trace window already forces the exact cross-multiplied
superdeterminant identity. -/
theorem thetaSourceFiniteWindowRealGradedPolarization_det_factor
    (L : ThetaSourceFiniteWindowRealGradedPolarization) (k : ℕ) (z : ℂ) :
    ((1 : Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (L.oddRank k))
        (↥(thetaSourceSignedCutoff k) ⊕ Fin (L.oddRank k)) ℂ) -
      z • L.even k).det =
        thetaSourceSignedOrdinaryDet k z *
          ((1 : Matrix (Fin (L.oddRank k)) (Fin (L.oddRank k)) ℂ) -
            z • L.odd k).det := by
  unfold thetaSourceSignedOrdinaryDet
  exact graded_signedTrace_preservation_le_forces_det_factor
    _ _ _ (L.signedTrace k) z

/-- A real-divisor graded polarization preserving only the finite Newton window already proves
RH.  Pole-freeness, all-degree traces, metric adjointness, and coercive escape are not used. -/
theorem riemannHypothesis_of_thetaSourceFiniteWindowRealGradedPolarization
    (L : ThetaSourceFiniteWindowRealGradedPolarization) : RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
  intro k z hz
  have hsource : thetaSourceSignedOrdinaryDet k z = 0 := by
    unfold thetaSourceKreinChiralXiCandidate at hz
    exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne
  apply source_realDivisor_of_graded_signedTrace_le_realDivisor
    (thetaSourceKreinFiniteMatrix k) (L.odd k) (L.even k)
    (L.signedTrace k) (L.realDivisor k)
  exact hsource

/-- Closed finite-window lock: either RH holds or no such weakened polarization exists. -/
theorem riemannHypothesis_or_no_thetaSourceFiniteWindowRealGradedPolarization :
    RiemannHypothesis ∨
      IsEmpty ThetaSourceFiniteWindowRealGradedPolarization := by
  by_cases h : Nonempty ThetaSourceFiniteWindowRealGradedPolarization
  · left
    exact riemannHypothesis_of_thetaSourceFiniteWindowRealGradedPolarization h.some
  · right
    exact ⟨fun L => h ⟨L⟩⟩

end

end RHTower.HedenmalmThetaSource
