import GaloisForLFunctions.RHTower.JointAncestryCriticalSingletonFixedGradeBesselWall

/-!
# JAS critical mixed prime--grade incidence

A bounded synthesis of critical singleton prime characters into a countably graded carrier forces
the critical prime mass in every grade fiber to be square-summable. This is the exact residual
obstruction left after adding Hilbert multiplicity: collisions inside one grade retain the common
prime-Poisson mean and its harmonic accumulation.

The obstruction has a concrete positive boundary. Assign each prime its own grade via the canonical
prime enumeration. The resulting packet family is orthonormal and therefore has an explicit
isometric synthesis. Countable grading repairs the singleton Bessel wall precisely when it records
prime incidence rather than repeating a common grade.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Every critical singleton prime character has unit `L²` norm. -/
theorem norm_criticalPrimeSingletonCharacterL2 (t : ℝ) (p : Nat.Primes) :
    ‖criticalPrimeSingletonCharacterL2 t p‖ = 1 := by
  have hsq : ‖criticalPrimeSingletonCharacterL2 t p‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : ((criticalPrimeSingletonCharacterL2 t p :
        PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) =ᵐ[
          primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)]
        fun x => infiniteTorusFourier (Finsupp.single p 1) x := by
      simpa only [criticalPrimeSingletonCharacterL2] using
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier (Finsupp.single p 1))
    calc
      (∫ x, ‖((criticalPrimeSingletonCharacterL2 t p :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x‖ ^ 2
          ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) =
          ∫ _x : PrimeTorus, (1 : ℝ)
            ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num) := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        simp [infiniteTorusFourier]
      _ = 1 := by simp
  nlinarith [norm_nonneg (criticalPrimeSingletonCharacterL2 t p)]

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Put the singleton character at `p` into the grade selected by `g p`. -/
def jointAncestryCriticalPrimeGradedSingletonPacket
    (t : ℝ) (g : Nat.Primes → ℕ) (p : Nat.Primes) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single (g p) (criticalPrimeSingletonCharacterL2 t p)

/-- Existence of a bounded synthesis of a prescribed graded singleton packet family. -/
def JASCriticalPrimeGradedSingletonSynthesis
    (t : ℝ) (g : Nat.Primes → ℕ) : Prop :=
  ∃ T : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
      L2Amplification ℕ (JASCriticalPrimePoissonL2 t),
    ∀ p, T (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      jointAncestryCriticalPrimeGradedSingletonPacket t g p

/-- Every grade fiber carries square-summable critical prime-Poisson mass. -/
def JASCriticalPrimeGradeFibersSummable
    (t : ℝ) (g : Nat.Primes → ℕ) : Prop :=
  ∀ r, Summable fun p : Nat.Primes =>
    if g p = r then
      ‖((primePoissonParameter (1 / 2 : ℝ) t (by norm_num) p :
        CirclePoissonParameter) : ℂ) - 0‖ ^ 2
    else 0

/-- At least one grade fiber has divergent critical prime-Poisson mass. -/
def JASCriticalPrimeGradeHasDivergentFiber
    (t : ℝ) (g : Nat.Primes → ℕ) : Prop :=
  ∃ r, ¬ Summable fun p : Nat.Primes =>
    if g p = r then
      ‖((primePoissonParameter (1 / 2 : ℝ) t (by norm_num) p :
        CirclePoissonParameter) : ℂ) - 0‖ ^ 2
    else 0

/-- Bounded graded singleton synthesis forces square-summability in every grade fiber. -/
theorem JASCriticalPrimeGradedSingletonSynthesis.fibersSummable
    {t : ℝ} {g : Nat.Primes → ℕ}
    (hSynthesis : JASCriticalPrimeGradedSingletonSynthesis t g) :
    JASCriticalPrimeGradeFibersSummable t g := by
  rcases hSynthesis with ⟨T, hT⟩
  intro r
  let Tr : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ] JASCriticalPrimePoissonL2 t :=
    (l2Coordinate (H₁ := JASCriticalPrimePoissonL2 t) r).comp T
  have hsum := (HTGeometry.ellTwoCoordinateBasis Nat.Primes).summable_norm_inner_sq
    (Tr.adjoint (criticalPrimePoissonOneL2 t))
  have hnorm : ∀ p : Nat.Primes,
      ‖inner ℂ (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)
        (Tr.adjoint (criticalPrimePoissonOneL2 t))‖ =
        if g p = r then ‖primePoissonParameterValue (1 / 2 : ℝ) t p‖ else 0 := by
    intro p
    rw [Tr.adjoint_inner_right]
    change ‖inner ℂ ((l2Coordinate (H₁ := JASCriticalPrimePoissonL2 t) r)
      (T (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)))
      (criticalPrimePoissonOneL2 t)‖ = _
    rw [hT]
    by_cases hgrade : g p = r
    · rw [if_pos hgrade]
      subst r
      rw [jointAncestryCriticalPrimeGradedSingletonPacket,
        l2Coordinate_single_same]
      rw [← inner_conj_symm, RCLike.norm_conj]
      rw [inner_criticalPrimePoissonOne_singletonCharacter]
    · rw [if_neg hgrade]
      have hr : r ≠ g p := Ne.symm hgrade
      simp [jointAncestryCriticalPrimeGradedSingletonPacket,
        l2Coordinate_apply, l2Single_apply, lp.single_apply, hr]
  convert hsum using 1
  funext p
  rw [hnorm]
  by_cases hgrade : g p = r <;>
    simp [hgrade, coe_primePoissonParameter]

/-- No bounded graded synthesis can coexist with a divergent grade fiber. -/
theorem not_exists_JASCriticalPrimeGradedSingletonSynthesis_with_divergentFiber
    (t : ℝ) :
    ¬ ∃ g : Nat.Primes → ℕ,
      JASCriticalPrimeGradedSingletonSynthesis t g ∧
        JASCriticalPrimeGradeHasDivergentFiber t g := by
  rintro ⟨g, hSynthesis, r, hdiv⟩
  exact hdiv (hSynthesis.fibersSummable r)

/-- Collision-free packet: prime `p` occupies its canonical enumeration grade. -/
def jointAncestryCriticalPrimeInjectiveGradePacket (t : ℝ) (p : Nat.Primes) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single (natEquivPrimes.symm p) (criticalPrimeSingletonCharacterL2 t p)

/-- Canonically grade-separated critical singleton prime packets are orthonormal. -/
theorem orthonormal_jointAncestryCriticalPrimeInjectiveGradePacket (t : ℝ) :
    Orthonormal ℂ (jointAncestryCriticalPrimeInjectiveGradePacket t) := by
  rw [orthonormal_iff_ite]
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
    rw [jointAncestryCriticalPrimeInjectiveGradePacket, l2Single_apply,
      lp.norm_single (by norm_num), norm_criticalPrimeSingletonCharacterL2]
    norm_num
  · rw [if_neg hpq]
    have hgrade : natEquivPrimes.symm p ≠ natEquivPrimes.symm q := by
      exact fun h => hpq (natEquivPrimes.symm.injective h)
    rw [jointAncestryCriticalPrimeInjectiveGradePacket,
      jointAncestryCriticalPrimeInjectiveGradePacket, l2Single_apply,
      lp.inner_single_left]
    simp [lp.single_apply, hgrade]

/-- Explicit isometric synthesis of the canonical collision-free packet family. -/
def jointAncestryCriticalPrimeInjectiveGradeSynthesis (t : ℝ) :
    HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
      L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  (orthonormal_jointAncestryCriticalPrimeInjectiveGradePacket t).orthogonalFamily.linearIsometry
    |>.toContinuousLinearMap

/-- The explicit synthesis sends each prime coordinate to its collision-free packet. -/
theorem jointAncestryCriticalPrimeInjectiveGradeSynthesis_coordinateBasis
    (t : ℝ) (p : Nat.Primes) :
    jointAncestryCriticalPrimeInjectiveGradeSynthesis t
      (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      jointAncestryCriticalPrimeInjectiveGradePacket t p := by
  rw [jointAncestryCriticalPrimeInjectiveGradeSynthesis,
    HTGeometry.ellTwoCoordinateBasis_apply]
  change (orthonormal_jointAncestryCriticalPrimeInjectiveGradePacket t).orthogonalFamily.linearIsometry
      (lp.single 2 p 1) = _
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

/-- Positive survivor: the canonical injective grade assignment admits bounded singleton
synthesis. -/
theorem jointAncestryCriticalPrimeInjectiveGradeSynthesis_exists (t : ℝ) :
    JASCriticalPrimeGradedSingletonSynthesis t
      (fun p => natEquivPrimes.symm p) := by
  refine ⟨jointAncestryCriticalPrimeInjectiveGradeSynthesis t, ?_⟩
  intro p
  simpa [jointAncestryCriticalPrimeGradedSingletonPacket,
    jointAncestryCriticalPrimeInjectiveGradePacket] using
    jointAncestryCriticalPrimeInjectiveGradeSynthesis_coordinateBasis t p

end

end RHTower
