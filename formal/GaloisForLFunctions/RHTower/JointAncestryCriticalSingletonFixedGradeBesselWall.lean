import GaloisForLFunctions.HTGeometry.RankOneHilbertSchmidt
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.RHTower.JointAncestryAmplifiedPrimePoissonSuperselection

/-!
# JAS critical singleton fixed-grade Bessel wall

The critical prime-Poisson mean of the singleton character at `p` has modulus `p⁻¹ᐟ²`.
Consequently the singleton characters cannot be the bounded synthesis image of the orthonormal
prime basis: applying the adjoint to the constant vector would put the divergent prime harmonic
sequence in `ell²`.

This obstruction survives multiplication by any fixed actual nonzero completed-theta grade and
injection into any one coordinate of the countable JAS amplification. Thus countable multiplicity
can help prime-support completion only through genuinely mixed prime--grade incidence; repeating
one grade cannot do so.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The `L²` class of the singleton coordinate character at prime `p` in the critical
prime-Poisson state. -/
def criticalPrimeSingletonCharacterL2 (t : ℝ) (p : Nat.Primes) :
    PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num) :=
  ContinuousMap.toLp 2
    (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) ℂ
    (infiniteTorusFourier (Finsupp.single p 1))

/-- Constant-one observer in critical prime-Poisson `L²`. -/
def criticalPrimePoissonOneL2 (t : ℝ) :
    PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num) :=
  ContinuousMap.toLp 2
    (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) ℂ
    (1 : C(PrimeTorus, ℂ))

/-- The constant observer reads the exact critical prime-Poisson singleton moment. -/
theorem inner_criticalPrimePoissonOne_singletonCharacter
    (t : ℝ) (p : Nat.Primes) :
    inner ℂ (criticalPrimePoissonOneL2 t) (criticalPrimeSingletonCharacterL2 t p) =
      primePoissonParameterValue (1 / 2 : ℝ) t p := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℂ (((criticalPrimePoissonOneL2 t :
        PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x)
        (((criticalPrimeSingletonCharacterL2 t p :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x)
        ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) =
        ∫ x, infiniteTorusFourier (Finsupp.single p 1) x
          ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num) := by
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (1 : C(PrimeTorus, ℂ)),
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier (Finsupp.single p 1))] with x hx1 hx2
      have hx1' : (((criticalPrimePoissonOneL2 t :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x) = 1 := by
        simpa only [criticalPrimePoissonOneL2, ContinuousMap.one_apply] using hx1
      have hx2' : (((criticalPrimeSingletonCharacterL2 t p :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x) =
          infiniteTorusFourier (Finsupp.single p 1) x := by
        simpa only [criticalPrimeSingletonCharacterL2] using hx2
      rw [hx1', hx2']
      simp [RCLike.inner_apply]
    _ = primePoissonParameterValue (1 / 2 : ℝ) t p := by
      rw [integral_infiniteTorusFourier_primePoissonMeasure]
      simp [circlePoissonFourierMoment]

/-- No bounded synthesis sends the orthonormal prime basis to all critical singleton
prime-Poisson characters. -/
theorem not_exists_criticalPrimeSingletonCharacterSynthesis (t : ℝ) :
    ¬ ∃ T : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
        PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num),
      ∀ p, T (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
        criticalPrimeSingletonCharacterL2 t p := by
  rintro ⟨T, hT⟩
  have hsum := (HTGeometry.ellTwoCoordinateBasis Nat.Primes).summable_norm_inner_sq
    (T.adjoint (criticalPrimePoissonOneL2 t))
  have hnorm : ∀ p : Nat.Primes,
      ‖inner ℂ (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)
        (T.adjoint (criticalPrimePoissonOneL2 t))‖ =
        ‖primePoissonParameterValue (1 / 2 : ℝ) t p‖ := by
    intro p
    rw [T.adjoint_inner_right, hT]
    rw [← inner_conj_symm, RCLike.norm_conj]
    rw [inner_criticalPrimePoissonOne_singletonCharacter]
  have hsumParameter : Summable (fun p : Nat.Primes =>
      ‖((primePoissonParameter (1 / 2 : ℝ) t (by norm_num) p :
        CirclePoissonParameter) : ℂ) - 0‖ ^ 2) := by
    simpa only [hnorm, coe_primePoissonParameter, sub_zero] using hsum
  have hwall := (summable_normSq_primePoissonParameter_zero_iff
    (1 / 2 : ℝ) t (by norm_num)).mp hsumParameter
  norm_num at hwall

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Actual singleton prime character weighted by one fixed completed-theta grade. -/
def jointAncestryCriticalPrimeThetaSingletonPayload
    (t : ℝ) (r : ℕ) (p : Nat.Primes) : JASCriticalPrimePoissonL2 t :=
  (‖jointAncestryCompletedThetaGradeL2 r‖ : ℂ) •
    criticalPrimeSingletonCharacterL2 t p

/-- Fixed-grade amplification of the actual completed-theta singleton prime packet. -/
def jointAncestryCriticalPrimeThetaFixedGradeSingletonPacket
    (t : ℝ) (r : ℕ) (p : Nat.Primes) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single r (jointAncestryCriticalPrimeThetaSingletonPayload t r p)

/-- A bounded Hilbert completion of all prime singleton packets inside one fixed theta grade. -/
def JASCriticalPrimeThetaFixedGradeSingletonSynthesis (t : ℝ) (r : ℕ) : Prop :=
  ∃ T : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
      L2Amplification ℕ (JASCriticalPrimePoissonL2 t),
    ∀ p, T (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      jointAncestryCriticalPrimeThetaFixedGradeSingletonPacket t r p

/-- No fixed completed-theta grade admits bounded synthesis of all critical singleton prime
characters. Thus diagonal completion can survive only by genuinely mixing prime and grade. -/
theorem not_JASCriticalPrimeThetaFixedGradeSingletonSynthesis (t : ℝ) (r : ℕ) :
    ¬ JASCriticalPrimeThetaFixedGradeSingletonSynthesis t r := by
  rintro ⟨T, hT⟩
  let c : ℂ := (‖jointAncestryCompletedThetaGradeL2 r‖ : ℂ)
  have hc : c ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (jointAncestryCompletedThetaGradeL2_ne_zero r))
  let T0 : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
      JASCriticalPrimePoissonL2 t :=
    c⁻¹ • ((l2Coordinate (H₁ := JASCriticalPrimePoissonL2 t) r).comp T)
  apply not_exists_criticalPrimeSingletonCharacterSynthesis t
  refine ⟨T0, ?_⟩
  intro p
  simp only [T0, smul_apply, ContinuousLinearMap.comp_apply,
    hT, jointAncestryCriticalPrimeThetaFixedGradeSingletonPacket,
    l2Coordinate_single_same, jointAncestryCriticalPrimeThetaSingletonPayload, c]
  rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]

end

end RHTower
