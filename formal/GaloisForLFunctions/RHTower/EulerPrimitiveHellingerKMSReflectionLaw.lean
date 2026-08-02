import GaloisForLFunctions.HTGeometry.GibbsExposedFaceRadicalFlag
import GaloisForLFunctions.RHTower.EulerPrimitivePolarizedHodgeBetaTransgression
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedReflectionRigidity
import GaloisForLFunctions.RHTower.RiemannGammaCoPoissonHodgeGreenDescentLaw

/-!
# Hellinger--KMS reflection equipartition

This file identifies one source law behind the Euler occupation split,
quantum-recurrence Gibbs limits, and Gamma/co-Poisson Green descent.

First, the complementary Euler head/tail occupations are exactly a
two-state Gibbs state.  Their Hellinger geometric mean is literally the
KMS/Wightman half-density between the two source states.  The forced odd
Hodge scale transports either occupation to this canonical half-density;
its common Laplace transform is the Beta/Gamma column.

Second, modular reflection with real displacement `a` is the two-state
Gibbs energy pair `(-a,a)`.  At infinite source depth its exposed face has
cardinality two exactly when `a = 0`; otherwise one reflected orientation
is selected and the other becomes radical.  The limiting Gibbs purity is
therefore `1/2` at zero displacement and `1` off it, while off-diagonal KMS
coherence has the complementary limits `1/2` and `0`.

Finally, this same equipartition condition is equivalent both to
finite-energy landing of the reflection-odd source profile and to descent
of the actual Gamma/co-Poisson Hodge-boundary comparison through exact
Calderón--Witt Green boundaries.  At Xi-divisor points the displacement is
the centered real-part fracture, so global descent is the already isolated
RH condition.
-/

open Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## Euler occupation as a two-state Gibbs source -/

/--
Two-state Hamiltonian whose unit-temperature Gibbs weights are the Euler
head and tail occupations.  `false` is the compact head and `true` the
Hardy tail.
-/
def eulerPrimitiveBoundaryOccupationEnergy (t : ℝ) : Bool → ℝ
  | false => t
  | true => -Real.log (eulerPrimitiveBoundaryTailWeight t)

theorem eulerPrimitiveBoundaryOccupationGibbsPartition
    {t : ℝ} (ht : 0 < t) :
    HTGeometry.finiteGibbsPartition 1
        (eulerPrimitiveBoundaryOccupationEnergy t) =
      1 := by
  rw [HTGeometry.finiteGibbsPartition, Fintype.sum_bool]
  have htail :
      0 < eulerPrimitiveBoundaryTailWeight t :=
    eulerPrimitiveBoundaryTailWeight_pos ht
  simp only [eulerPrimitiveBoundaryOccupationEnergy]
  rw [show
      -(1 : ℝ) * -Real.log (eulerPrimitiveBoundaryTailWeight t) =
        Real.log (eulerPrimitiveBoundaryTailWeight t) by ring,
    Real.exp_log htail,
    show -(1 : ℝ) * t = -t by ring]
  simpa [eulerPrimitiveBoundaryHeadWeight, add_comm] using
    eulerPrimitiveBoundaryHeadWeight_add_tailWeight t

theorem eulerPrimitiveBoundaryOccupationGibbsStateWeight_head
    {t : ℝ} (ht : 0 < t) :
    HTGeometry.finiteGibbsStateWeight 1
        (eulerPrimitiveBoundaryOccupationEnergy t) false =
      eulerPrimitiveBoundaryHeadWeight t := by
  rw [HTGeometry.finiteGibbsStateWeight,
    eulerPrimitiveBoundaryOccupationGibbsPartition ht,
    div_one]
  simp [eulerPrimitiveBoundaryOccupationEnergy,
    eulerPrimitiveBoundaryHeadWeight]

theorem eulerPrimitiveBoundaryOccupationGibbsStateWeight_tail
    {t : ℝ} (ht : 0 < t) :
    HTGeometry.finiteGibbsStateWeight 1
        (eulerPrimitiveBoundaryOccupationEnergy t) true =
      eulerPrimitiveBoundaryTailWeight t := by
  rw [HTGeometry.finiteGibbsStateWeight,
    eulerPrimitiveBoundaryOccupationGibbsPartition ht,
    div_one]
  have htail :
      0 < eulerPrimitiveBoundaryTailWeight t :=
    eulerPrimitiveBoundaryTailWeight_pos ht
  simp only [eulerPrimitiveBoundaryOccupationEnergy]
  rw [show
      -(1 : ℝ) * -Real.log (eulerPrimitiveBoundaryTailWeight t) =
        Real.log (eulerPrimitiveBoundaryTailWeight t) by ring,
    Real.exp_log htail]

/--
The Euler Hellinger cross-density is exactly the canonical KMS/Wightman
half-density of its two-state occupation Hamiltonian.
-/
theorem eulerPrimitiveBoundaryHellingerDensity_eq_KMSWightman
    {t : ℝ} (ht : 0 < t) :
    eulerPrimitiveBoundaryOccupationHellingerDensity t =
      HTGeometry.finiteKMSWightmanWeight 1
        (eulerPrimitiveBoundaryOccupationEnergy t) false true := by
  have hwPos :
      0 < HTGeometry.finiteKMSWightmanWeight 1
        (eulerPrimitiveBoundaryOccupationEnergy t) false true :=
    HTGeometry.finiteKMSWightmanWeight_pos _ _ _ _
  have hhellNonneg :
      0 ≤ eulerPrimitiveBoundaryOccupationHellingerDensity t :=
    Real.sqrt_nonneg _
  have hsq :
      eulerPrimitiveBoundaryOccupationHellingerDensity t ^ 2 =
        HTGeometry.finiteKMSWightmanWeight 1
          (eulerPrimitiveBoundaryOccupationEnergy t) false true ^ 2 := by
    rw [HTGeometry.finiteKMSWightmanWeight_sq,
      eulerPrimitiveBoundaryOccupationGibbsStateWeight_head ht,
      eulerPrimitiveBoundaryOccupationGibbsStateWeight_tail ht,
      eulerPrimitiveBoundaryOccupationHellingerDensity,
      Real.sq_sqrt]
    exact mul_nonneg
      (eulerPrimitiveBoundaryHeadWeight_pos t).le
      (eulerPrimitiveBoundaryTailWeight_pos ht).le
  nlinarith

/-! ## Modular reflection as a two-state Gibbs face -/

/-- Reflected source orientations carry opposite modular energies. -/
def reflectionOrientationEnergy (a : ℝ) : Bool → ℝ
  | false => -a
  | true => a

theorem reflectionOrientationEnergy_le_abs (a : ℝ) (b : Bool) :
    reflectionOrientationEnergy a b ≤ |a| := by
  cases b
  · exact neg_le_abs a
  · exact le_abs_self a

theorem reflectionOrientationEnergy_exists_abs (a : ℝ) :
    ∃ b : Bool, reflectionOrientationEnergy a b = |a| := by
  by_cases ha : 0 ≤ a
  · exact ⟨true, by simp [reflectionOrientationEnergy, abs_of_nonneg ha]⟩
  · have ha' : a ≤ 0 := le_of_not_ge ha
    exact ⟨false, by simp [reflectionOrientationEnergy, abs_of_nonpos ha']⟩

/--
The tropical exposed face retains both reflected orientations exactly at
zero modular displacement; every nonzero displacement selects one.
-/
theorem reflectionOrientationExposedFaceCard (a : ℝ) :
    HTGeometry.finiteSourceExposedFaceCard
        (reflectionOrientationEnergy a) |a| =
      if a = 0 then 2 else 1 := by
  by_cases ha : a = 0
  · subst a
    unfold HTGeometry.finiteSourceExposedFaceCard
    have hset :
        Finset.univ.filter
            (fun b : Bool => reflectionOrientationEnergy 0 b = |(0 : ℝ)|) =
          Finset.univ := by
      ext b
      cases b <;> simp [reflectionOrientationEnergy]
    rw [hset]
    simpa using Fintype.card_bool
  · rcases lt_or_gt_of_ne ha with haNeg | haPos
    · unfold HTGeometry.finiteSourceExposedFaceCard
      simp only [abs_of_neg haNeg, if_neg ha]
      have hset :
          Finset.univ.filter
              (fun b : Bool => reflectionOrientationEnergy a b = -a) =
            {false} := by
        ext b
        cases b <;> simp [reflectionOrientationEnergy] <;> linarith
      rw [hset]
      simp
    · unfold HTGeometry.finiteSourceExposedFaceCard
      simp only [abs_of_pos haPos, if_neg ha]
      have hset :
          Finset.univ.filter
              (fun b : Bool => reflectionOrientationEnergy a b = a) =
            {true} := by
        ext b
        cases b <;> simp [reflectionOrientationEnergy] <;> linarith
      rw [hset]
      simp

theorem reflectionOrientationExposedFaceCard_eq_two_iff (a : ℝ) :
    HTGeometry.finiteSourceExposedFaceCard
        (reflectionOrientationEnergy a) |a| = 2 ↔
      a = 0 := by
  rw [reflectionOrientationExposedFaceCard]
  by_cases ha : a = 0 <;> simp [ha]

/--
Zero-temperature purity detects reflection superselection: it tends to
the maximally mixed two-state value at equipartition and to a pure state
for every nonzero modular gap.
-/
theorem tendsto_reflectionOrientationGibbsPurity (a : ℝ) :
    Tendsto
      (fun k : ℕ =>
        HTGeometry.finiteGibbsPurity (k : ℝ)
          (fun b : Bool => -reflectionOrientationEnergy a b))
      atTop
      (nhds (if a = 0 then (1 / 2 : ℝ) else 1)) := by
  have h :=
    HTGeometry.tendsto_finiteGibbsPurity_neg_energy_exposedFaceCard
      (reflectionOrientationEnergy a) |a|
      (reflectionOrientationEnergy_le_abs a)
      (reflectionOrientationEnergy_exists_abs a)
  rw [reflectionOrientationExposedFaceCard] at h
  by_cases ha : a = 0
  · subst a
    convert h using 1 <;> norm_num
  · convert h using 1 <;> simp [ha]

/--
The off-diagonal KMS coherence has the complementary limit: one half at
reflection equipartition and zero after any nonzero modular gap selects a
single exposed orientation.
-/
theorem tendsto_reflectionOrientationKMSOffDiagonalMass (a : ℝ) :
    Tendsto
      (fun k : ℕ =>
        ∑ b : Bool, ∑ c ∈ Finset.univ.erase b,
          HTGeometry.finiteKMSWightmanWeight (k : ℝ)
            (fun d : Bool => -reflectionOrientationEnergy a d) b c ^ 2)
      atTop
      (nhds (if a = 0 then (1 / 2 : ℝ) else 0)) := by
  have h :=
    HTGeometry.tendsto_offDiagonal_sq_finiteKMSWightmanWeight_neg_energy_exposedFaceCard
      (reflectionOrientationEnergy a) |a|
      (reflectionOrientationEnergy_le_abs a)
      (reflectionOrientationEnergy_exists_abs a)
  rw [reflectionOrientationExposedFaceCard] at h
  by_cases ha : a = 0
  · subst a
    convert h using 1 <;> norm_num
  · convert h using 1 <;> simp [ha]

/-! ## Equipartition, positive energy, and Green descent -/

/--
Reflection equipartition is exactly finite-energy landing of the
reflection-odd common-test profile.
-/
theorem reflectionOrientationEquipartition_iff_finiteEnergy (a : ℝ) :
    HTGeometry.finiteSourceExposedFaceCard
          (reflectionOrientationEnergy a) |a| = 2 ↔
      IntegrableOn
        (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
        (Ioi 0) := by
  rw [reflectionOrientationExposedFaceCard_eq_two_iff,
    integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff]

/--
**Hellinger--KMS reflection descent law.**  Descent of the actual
Gamma/co-Poisson Hodge boundary through every exact Calderón--Witt
incidence is equivalent to retention of both reflected Gibbs faces.
-/
theorem
    gammaBoundaryGreenDescent_iff_reflectionOrientationEquipartition
    (a : ℝ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a = 0 ↔
      HTGeometry.finiteSourceExposedFaceCard
        (reflectionOrientationEnergy a) |a| = 2 := by
  rw [
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq_zero_iff,
    reflectionOrientationExposedFaceCard_eq_two_iff]

/--
Equivalent positive-energy form of the same descent law.
-/
theorem gammaBoundaryGreenDescent_iff_reflectionFiniteEnergy
    (a : ℝ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a = 0 ↔
      IntegrableOn
        (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
        (Ioi 0) := by
  rw [
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq_zero_iff,
    integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff]

end

end RHTower
