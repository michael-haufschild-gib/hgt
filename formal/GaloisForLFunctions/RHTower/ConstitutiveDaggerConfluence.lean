import GaloisForLFunctions.HTGeometry.ConstitutiveCriticalCompletionMechanics
import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection
import GaloisForLFunctions.RHTower.DeningerFailureNerveSingularCartierMetric
import GaloisForLFunctions.RHTower.SourceNormalClockCurvatureLaw
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Constitutive dagger confluence

Finite critical completion already supplies the nonclassical 1 → 2 mechanism: one semantic
repair class has two distinct normal executable presentations.  Ordinary confluence is therefore
the wrong demand.  This module records the stronger metric demand that a source-native potential
must descend through the stationary semantic theory.

The arithmetic calibration is imposed on the whole parameter plane, before restricting to divisor
fibres.  At a divisor fibre, semantic descent makes the two repair presentations metrically
indistinguishable, while the Deninger radial character says their logarithmic difference is
(2 Re(s) - 1) log n.  Thus the defect can remain one semantic error only on the critical line;
off line it splits into two metric provenances.

The existence of an arbitrary calibrated descending potential is proved equivalent to the
critical-line equation.  This is an anti-circularity result, not an RH proof: the remaining
upstream obligation is to construct one fixed pre-divisor potential from the arithmetic source
and prove its descent on closed Xi-error fibres.

Here D is the signed relative source-inverse/analytic-dagger orientation potential.  It is not
positive execution cost: conservative repair can carry unbounded positive history at a stationary
semantic endpoint, so such cost cannot descend and is deliberately retained.
-/

namespace RHTower

open ConstitutiveCriticalCompletionMechanics

/-- A signed relative-orientation potential is dagger-confluent at stage N when it cannot
distinguish presentations identified by the generated semantic equivalence.  This is stronger
than executable confluence: finite stages are nonconfluent, but their semantic theory is
stationary. -/
def DaggerConfluentPotential (N : ℕ) (D : Word → ℝ) : Prop :=
  ∀ u v, Semantic N u v → D u = D v

/-- Pre-divisor radial calibration of the newest semantically conservative repair. -/
def RadiallyCalibratedRepairPotential
    (N n : ℕ) (s : ℂ) (D : Word → ℝ) : Prop :=
  D (left (N + 1)) - D (right (N + 1)) =
    Real.log (deningerHalfDensityMateGain n s)

/-- Dagger confluence identifies the two executable histories of the next conservative repair. -/
theorem daggerConfluentPotential_repair_eq
    {N : ℕ} (hN : 1 ≤ N) {D : Word → ℝ}
    (hD : DaggerConfluentPotential N D) :
    D (left (N + 1)) = D (right (N + 1)) :=
  hD _ _ (semantic_new_rule N hN)

/-- Equal metric values on the two radially calibrated repair histories force neutral radial
grade.  No Xi-divisor hypothesis is used. -/
theorem re_eq_half_of_radiallyCalibrated_repair_eq
    {N n : ℕ} (hn : 2 ≤ n) (s : ℂ) (D : Word → ℝ)
    (hcal : RadiallyCalibratedRepairPotential N n s D)
    (heq : D (left (N + 1)) = D (right (N + 1))) :
    s.re = 1 / 2 := by
  have hlog : Real.log (deningerHalfDensityMateGain n s) = 0 := by
    rw [← hcal, heq]
    ring
  rw [logarithm_deningerHalfDensityMateGain] at hlog
  have hnlog : Real.log (n : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  have hrate : 2 * s.re - 1 = 0 :=
    (mul_eq_zero.mp hlog).resolve_right hnlog
  linarith

/-- A radially calibrated dagger-confluent repair forces the critical half-density line. -/
theorem re_eq_half_of_radiallyCalibrated_daggerConfluentPotential
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) (s : ℂ) (D : Word → ℝ)
    (hdesc : DaggerConfluentPotential N D)
    (hcal : RadiallyCalibratedRepairPotential N n s D) :
    s.re = 1 / 2 :=
  re_eq_half_of_radiallyCalibrated_repair_eq hn s D hcal
    (daggerConfluentPotential_repair_eq hN hdesc)

/-- Off line, the two normal executions are one semantic repair but two distinct metric
provenances.  This is the precise completion-error interpretation of an off-line point. -/
theorem semanticRepair_metricSplit_of_re_ne_half
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) (s : ℂ) (D : Word → ℝ)
    (hcal : RadiallyCalibratedRepairPotential N n s D)
    (hoff : s.re ≠ 1 / 2) :
    Semantic N (left (N + 1)) (right (N + 1)) ∧
      D (left (N + 1)) ≠ D (right (N + 1)) := by
  refine ⟨semantic_new_rule N hN, ?_⟩
  intro heq
  exact hoff (re_eq_half_of_radiallyCalibrated_repair_eq hn s D hcal heq)

/-- Proof-erasure consistency for the two histories of the marked conservative repair: averaging
the two presentations and then deleting one formation slot agrees with deleting first and then
averaging.  It is a three-slot law; two-slot symmetrization is automatically blind to the split. -/
def RepairProofErasureConsistent (N : ℕ) (D : Word → ℝ) : Prop :=
  GaloisForLFunctions.HTGeometry.phaseAveragedSkippedCoincidence
      (D (left (N + 1))) (D (right (N + 1))) =
    GaloisForLFunctions.HTGeometry.phaseAveragedAdjacentCoincidence
      (D (left (N + 1))) (D (right (N + 1)))

/-- Proof-erasure consistency is exactly equality of the two metric presentations. -/
theorem repairProofErasureConsistent_iff_repair_eq
    (N : ℕ) (D : Word → ℝ) :
    RepairProofErasureConsistent N D ↔
      D (left (N + 1)) = D (right (N + 1)) :=
  GaloisForLFunctions.HTGeometry.phaseAveragedThinningConsistent_iff _ _

/-- Full dagger confluence implies the local proof-erasure law at every marked repair. -/
theorem repairProofErasureConsistent_of_daggerConfluentPotential
    {N : ℕ} (hN : 1 ≤ N) {D : Word → ℝ}
    (hD : DaggerConfluentPotential N D) :
    RepairProofErasureConsistent N D :=
  (repairProofErasureConsistent_iff_repair_eq N D).2
    (daggerConfluentPotential_repair_eq hN hD)

/-- A radially calibrated proof-erasure law forces neutral radial grade. -/
theorem re_eq_half_of_radiallyCalibrated_repairProofErasure
    {N n : ℕ} (hn : 2 ≤ n) (s : ℂ) (D : Word → ℝ)
    (hcal : RadiallyCalibratedRepairPotential N n s D)
    (herase : RepairProofErasureConsistent N D) :
    s.re = 1 / 2 :=
  re_eq_half_of_radiallyCalibrated_repair_eq hn s D hcal
    ((repairProofErasureConsistent_iff_repair_eq N D).1 herase)

/-- Off line, radial calibration forces failure of proof-erasure consistency. -/
theorem not_repairProofErasureConsistent_of_re_ne_half
    {N n : ℕ} (hn : 2 ≤ n) (s : ℂ) (D : Word → ℝ)
    (hcal : RadiallyCalibratedRepairPotential N n s D)
    (hoff : s.re ≠ 1 / 2) :
    ¬ RepairProofErasureConsistent N D := by
  intro herase
  exact hoff (re_eq_half_of_radiallyCalibrated_repairProofErasure
    hn s D hcal herase)

/-- Canonical signed orientation potential on the two marked histories.  It is defined on the
whole parameter plane from the source half-density mate gain, before any divisor selection. -/
noncomputable def actualRepairOrientationPotential
    (N n : ℕ) (s : ℂ) (w : Word) : ℝ :=
  if w = left (N + 1) then
    Real.log (deningerHalfDensityMateGain n s) / 2
  else if w = right (N + 1) then
    -Real.log (deningerHalfDensityMateGain n s) / 2
  else 0

theorem actualRepairOrientationPotential_left (N n : ℕ) (s : ℂ) :
    actualRepairOrientationPotential N n s (left (N + 1)) =
      Real.log (deningerHalfDensityMateGain n s) / 2 := by
  simp [actualRepairOrientationPotential]

theorem actualRepairOrientationPotential_right (N n : ℕ) (s : ℂ) :
    actualRepairOrientationPotential N n s (right (N + 1)) =
      -Real.log (deningerHalfDensityMateGain n s) / 2 := by
  rw [actualRepairOrientationPotential,
    if_neg (Ne.symm (left_ne_right (N + 1))), if_pos rfl]

/-- The canonical source potential has the required radial calibration unconditionally. -/
theorem actualRepairOrientationPotential_radiallyCalibrated
    (N n : ℕ) (s : ℂ) :
    RadiallyCalibratedRepairPotential N n s
      (actualRepairOrientationPotential N n s) := by
  rw [RadiallyCalibratedRepairPotential,
    actualRepairOrientationPotential_left,
    actualRepairOrientationPotential_right]
  ring

/-- The source-history value is the negative half-logarithm of the uniquely purified actual
failure-nerve gain.  Thus the canonical potential is not an invented endpoint coordinate. -/
theorem actualRepairOrientationPotential_left_eq_metricSourceReversal
    (N : ℕ) (p : Nat.Primes) (m : ℕ) (s : ℂ)
    (F : Finset Nat.Primes) (hp : p ∉ F) (hs : 0 < s.re) :
    actualRepairOrientationPotential N ((p : ℕ) ^ m) s (left (N + 1)) =
      -Real.log
          (deningerFailureNerveActualPurifiedSquaredGain m s F p) / 2 := by
  have hpm : 0 < (p : ℕ) ^ m := pow_pos p.2.pos m
  rw [actualRepairOrientationPotential_left,
    deningerFailureNerveActualPurifiedSquaredGain_eq m s F p hp hs,
    deningerHalfDensityMateGain_eq_norm_inv_sq hpm]
  rw [inv_pow, Real.log_inv]

/-- The dagger-history value is the positive half-logarithm of the same uniquely purified gain. -/
theorem actualRepairOrientationPotential_right_eq_metricAnalyticDagger
    (N : ℕ) (p : Nat.Primes) (m : ℕ) (s : ℂ)
    (F : Finset Nat.Primes) (hp : p ∉ F) (hs : 0 < s.re) :
    actualRepairOrientationPotential N ((p : ℕ) ^ m) s (right (N + 1)) =
      Real.log
          (deningerFailureNerveActualPurifiedSquaredGain m s F p) / 2 := by
  have hpm : 0 < (p : ℕ) ^ m := pow_pos p.2.pos m
  rw [actualRepairOrientationPotential_right,
    deningerFailureNerveActualPurifiedSquaredGain_eq m s F p hp hs,
    deningerHalfDensityMateGain_eq_norm_inv_sq hpm]
  rw [inv_pow, Real.log_inv, neg_neg]

/-- Exact canonical classifier: the source-metric potential obeys three-slot proof erasure exactly
on the critical line.  No existential metric or divisor-dependent choice remains. -/
theorem actualRepairProofErasureConsistent_iff_re_eq_half
    {N n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    RepairProofErasureConsistent N
        (actualRepairOrientationPotential N n s) ↔
      s.re = 1 / 2 := by
  rw [repairProofErasureConsistent_iff_repair_eq,
    actualRepairOrientationPotential_left,
    actualRepairOrientationPotential_right]
  constructor
  · intro h
    apply re_eq_half_of_radiallyCalibrated_repair_eq hn s
      (actualRepairOrientationPotential N n s)
      (actualRepairOrientationPotential_radiallyCalibrated N n s)
    simpa [actualRepairOrientationPotential_left,
      actualRepairOrientationPotential_right] using h
  · intro hs
    rw [logarithm_deningerHalfDensityMateGain, hs]
    norm_num

/-- Pointwise existence of some calibrated dagger-confluent potential. -/
def AdmitsRadiallyCalibratedDaggerConfluence
    (N n : ℕ) (s : ℂ) : Prop :=
  ∃ D : Word → ℝ,
    DaggerConfluentPotential N D ∧
      RadiallyCalibratedRepairPotential N n s D

/-- Anti-circularity classifier: arbitrary pointwise existence is exactly the critical-line
equation.  A proof route must construct a fixed source potential before seeing divisor points. -/
theorem admitsRadiallyCalibratedDaggerConfluence_iff_re_eq_half
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n) (s : ℂ) :
    AdmitsRadiallyCalibratedDaggerConfluence N n s ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨D, hdesc, hcal⟩
    exact re_eq_half_of_radiallyCalibrated_daggerConfluentPotential
      hN hn s D hdesc hcal
  · intro hs
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro u v huv
      rfl
    · rw [RadiallyCalibratedRepairPotential,
        logarithm_deningerHalfDensityMateGain, hs]
      norm_num

/-- RH consumer for the noncircular formulation.  The potential is one pre-divisor family on all
complex parameters; only its semantic descent is requested on closed Xi-error fibres. -/
theorem riemannHypothesis_of_predivisorDaggerConfluentPotential
    {N n : ℕ} (hN : 1 ≤ N) (hn : 2 ≤ n)
    (D : ℂ → Word → ℝ)
    (hdesc : ∀ rho : XiDivisorSupport,
      DaggerConfluentPotential N (D (rho : ℂ)))
    (hcal : ∀ s : ℂ,
      RadiallyCalibratedRepairPotential N n s (D s)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro rho
  exact re_eq_half_of_radiallyCalibrated_daggerConfluentPotential
    hN hn (rho : ℂ) (D (rho : ℂ)) (hdesc rho) (hcal (rho : ℂ))

/-- RH consumer in the weakest local form.  A fixed pre-divisor potential is radially calibrated
everywhere; proof erasure is imposed only where the completed Xi constraint closes. -/
theorem riemannHypothesis_of_predivisorRepairProofErasure
    {N n : ℕ} (hn : 2 ≤ n)
    (D : ℂ → Word → ℝ)
    (herase : ∀ rho : XiDivisorSupport,
      RepairProofErasureConsistent N (D (rho : ℂ)))
    (hcal : ∀ s : ℂ,
      RadiallyCalibratedRepairPotential N n s (D s)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro rho
  exact re_eq_half_of_radiallyCalibrated_repairProofErasure
    hn (rho : ℂ) (D (rho : ℂ)) (hcal (rho : ℂ)) (herase rho)

end RHTower
