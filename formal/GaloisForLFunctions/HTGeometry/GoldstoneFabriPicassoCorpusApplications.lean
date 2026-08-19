import GaloisForLFunctions.HTGeometry.AbstractSpectralCharge
import GaloisForLFunctions.HTGeometry.ClockMasslessReference
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SymmetryInheritance
import GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedEulerShellWall
import GaloisForLFunctions.HTGeometry.EulerPrimeOrbitFourOrganLaw
import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank
import GaloisForLFunctions.HTGeometry.GammaGaugeClockVarianceSeparation
import GaloisForLFunctions.HTGeometry.OrbitQuotientLiftNoGo
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Goldstone and Fabri--Picasso applications in reusable geometry

Closed applications of three corpus-native mechanisms:

* broken symmetry or rank imbalance produces an exact nonzero zero mode;
* a symmetry lift or critical source escapes every finite-energy realization;
* inequivalent finite vacua become orthogonal under tensor replication.

These are formal structural analogues.  They do not assert the locality, relativistic spectrum,
or infinite-volume operator hypotheses of a physical quantum-field-theory theorem.
-/

open Filter Topology
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A coordinate conformal profile carries a nowhere-zero massless wave mode. -/
theorem goldstone_coordinateMasslessMode
    {d : ℕ} (M : SmoothMetricChart d) (a : ℝ) (i : Fin d) :
    SolvesPotentialWave M.dalembert
        (M.conformalPotential a 0 (fun y : Fin d → ℝ => y i))
        (chartExpProbe fun y : Fin d → ℝ => a * y i) ∧
      ∀ x : Fin d → ℝ, (chartExpProbe fun y : Fin d → ℝ => a * y i) x ≠ 0 := by
  constructor
  · apply solvesPotentialWave_masslessProbe M a
    fun_prop
  · intro x
    exact masslessProbe_ne_zero a (fun y : Fin d → ℝ => y i) x

/-- Concrete Ward witness: the grading symmetry has a nonzero differential commutator. -/
theorem goldstone_gradingCommutatorWitness :
    (_root_.HTGeometry.ConstraintRelativity.anomalyDifferential (K := ℂ)).comp
        (_root_.HTGeometry.ConstraintRelativity.anomalyFlow (K := ℂ)).grading ≠
      (_root_.HTGeometry.ConstraintRelativity.anomalyFlow (K := ℂ)).grading.comp
        (_root_.HTGeometry.ConstraintRelativity.anomalyDifferential (K := ℂ)) :=
  _root_.HTGeometry.ConstraintRelativity.anomalyDifferential_grading_commutator_ne_zero

/-- Exact symmetry charge neutrality at unit inverse temperature. -/
theorem goldstone_unbrokenSpectralChargeNeutrality
    {ι : Type*} (F : _root_.HTGeometry.AbstractSpectralFamily ι) :
    ∑' i : ι, F.weight 1 i * F.charge i = 0 :=
  F.tsum_weight_mul_charge_eq_zero (by norm_num)

/-- Every finite modal packet has a nonzero zero mode in its first oversized Hankel block. -/
theorem goldstone_finiteModalHankelZeroMode
    {K : Type*} [Field K] {d : ℕ} (weight node : Fin d → K) :
    ∃ v : Fin (d + 1) → K, v ≠ 0 ∧
      _root_.HTGeometry.algebraicHankelMatrix
          (_root_.HTGeometry.finiteModalSequence weight node) (d + 1) *ᵥ v = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  exact _root_.HTGeometry.det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero
    weight node

/-- A recurrent projective symmetry can have an unbounded implementing angle. -/
theorem fabriPicasso_recurrentShadowOpenLift :
    (∀ (t : ℝ) (n : ℤ), supportLine (t + n * Real.pi) = supportLine t) ∧
      (∀ t : ℝ, MeasureTheory.Measure.map (passiveRotation t) sourceLaw = sourceLaw) ∧
      ∀ M : ℝ, ∃ n : ℕ, M < (n : ℝ) * Real.pi :=
  recurrent_shadow_open_lift

/-- One nonzero phase mode already has unbounded logarithmic lift energy. -/
theorem fabriPicasso_unitPhaseLiftEnergyUnbounded :
    ∀ R : ℝ, ∃ t : ℝ,
      R < finitePhaseLiftEnergy (fun _ : Unit => (1 : ℝ)) t := by
  intro R
  exact finitePhaseLiftEnergy_unbounded (fun _ : Unit => (1 : ℝ)) () one_ne_zero R

/-- A nonconstant periodic gauge mode has no vector in the factorial reporter Hilbert space. -/
theorem fabriPicasso_firstPeriodicGaugeModeOutsideHilbert :
    ¬ ∃ x : lp (fun _ : ℕ => ℂ) 2,
      ∀ n, x n = gammaPeriodicModeTail 1 n :=
  not_exists_lp_eq_gammaPeriodicModeTail one_ne_zero

/-- No fixed positive radial pivot contains every pure periodic gauge mode. -/
theorem fabriPicasso_unitRadialPivotMissesPeriodicGaugeMode :
    ∃ m : ℕ,
      ¬ Summable (fun n : ℕ => ‖gammaPeriodicModeRadialTail 1 m n‖ ^ 2) :=
  exists_gammaPeriodicMode_not_summable_at_radialPivot (by norm_num)

/-- The critical Euler-prime half-density source has no standard prime `ell^2` realization. -/
theorem fabriPicasso_eulerPrimeHalfDensityOutsideHilbert :
    ¬ Summable (fun p : Nat.Primes => ‖eulerPrimeHalfDensityAmplitude p‖ ^ 2) :=
  not_summable_normSq_eulerPrimeHalfDensityAmplitude

/-- The marked Euler-shell Mass half-density has divergent squared norm. -/
theorem fabriPicasso_markedEulerMassOutsideHilbert :
    ¬ Summable (fun p : Nat.Primes =>
      (_root_.HTGeometry.ConstraintMotiveRelativity.massCoeff (p : ℕ)) ^ 2) :=
  _root_.HTGeometry.ConstraintMotiveRelativity.not_summable_massCoeff_sq

/-- No nonzero square-summable vector is invariant under every integral translation. -/
theorem fabriPicasso_noInvariantIntegralOrbitVector :
    ¬ ∃ f : Multiplicative ℤ → ℂ,
      f ≠ 0 ∧ Summable (fun g => ‖f g‖ ^ 2) ∧
        ∀ h x, f (h * x) = f x := by
  rintro ⟨f, hf, hsum, hinv⟩
  apply hf
  exact GaloisForLFunctions.eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq
    (⊤ : Subgroup (Multiplicative ℤ)) f hsum (fun h x => hinv h.1 x)

/-- Reference one-site vacuum. -/
def fabriPicassoReferenceVacuum : Fin 2 → ℂ := ![1, 0]

/-- A distinct normalized one-site vacuum with nontrivial overlap. -/
def fabriPicassoRotatedVacuum : Fin 2 → ℂ :=
  ![((1 : ℝ) / 2 : ℂ), (Real.sqrt 3 / 2 : ℂ)]

theorem finiteComplexInner_fabriPicassoReferenceVacuum_self :
    finiteComplexInner fabriPicassoReferenceVacuum fabriPicassoReferenceVacuum = 1 := by
  simp [finiteComplexInner, fabriPicassoReferenceVacuum, Fin.sum_univ_two]

theorem finiteComplexInner_fabriPicassoRotatedVacuum_self :
    finiteComplexInner fabriPicassoRotatedVacuum fabriPicassoRotatedVacuum = 1 := by
  rw [finiteComplexInner, Fin.sum_univ_two]
  simp only [fabriPicassoRotatedVacuum, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_div₀, map_ofNat, map_one, Complex.ofReal_one, Complex.conj_ofReal]
  have hsqrt : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  calc
    (1 : ℂ) / 2 * (1 / 2) + (Real.sqrt 3 : ℂ) / 2 * ((Real.sqrt 3 : ℂ) / 2) =
        (1 : ℂ) / 4 + (Real.sqrt 3 : ℂ) ^ 2 / 4 := by ring
    _ = 1 := by rw [hsqrt]; norm_num

theorem finitePureStateFidelity_fabriPicassoVacua :
    finitePureStateFidelity fabriPicassoReferenceVacuum fabriPicassoRotatedVacuum = 1 / 4 := by
  norm_num [finitePureStateFidelity, finiteComplexInner,
    fabriPicassoReferenceVacuum, fabriPicassoRotatedVacuum, Fin.sum_univ_two]

/-- Tensor powers of two distinct normalized vacua become asymptotically orthogonal. -/
theorem fabriPicasso_tensorVacuumOverlap_tendsto_zero :
    Tendsto (fun r : ℕ =>
        finitePureStateFidelity
          (finitePureTensorPower r fabriPicassoReferenceVacuum)
          (finitePureTensorPower r fabriPicassoRotatedVacuum))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℕ => ((1 / 4 : ℝ) ^ r)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [finitePureStateFidelity_tensorPower,
    finitePureStateFidelity_fabriPicassoVacua] using hpow

end GaloisForLFunctions.HTGeometry
