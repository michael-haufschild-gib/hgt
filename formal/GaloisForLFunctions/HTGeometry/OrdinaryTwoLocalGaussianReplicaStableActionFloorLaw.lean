import GaloisForLFunctions.RHTower.ContinuousCircuitReturnExcisedFirstEntryLaw
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-!
# Replica-stable exceptional-source floor for projected coarea action

For the termwise ordinary two-local Gaussian ensemble, a single explicit
coefficient box fails the fixed-error incidence-action receiver at every
positive replica order. The Hamiltonian is drawn once and time independent.
The complete unitary target family may have arbitrary cardinality; identity
is included explicitly, and the physical target projector, occupied rank,
and both return-excised time sheets are retained.

For `T = 1 + 4*|a| + u^2` and generator-norm mass `M`, the box radius is
`rho = 1/(2*T*(M+1))`. Its Gaussian mass is at least
`(2*gaussianFloorTwo*rho)^m`, independently of replica order. Every draw in
that box stays within Choi trace distance `1/2` of identity throughout the
surviving block `[3*T/4,T]`. The exact coarea receiver consequently gives

`N_inc*A_exc >= [gaussianFloorTwo/4 * (3/4)^r]^2`,

strictly larger than `[gaussianFloorTwo/(8*v*T)*(7/16)^r]^2`
for `v = 1 + norm(H)`.

The cutoff `a` may depend on circuit budget, but is fixed in the source draw.
A source-dependent inverse-speed cutoff is not covered. The conclusion is
an outer-measure lower bound: no measurability of the rank-changing failure
event is assumed. The coefficient box itself is measurable.

This is a known continuity/coarea bridge and necessary exceptional-mass
constraint, not an external novelty claim or a typical-draw growth theorem.
It does not disprove a high-probability quenched law; the decisive suppression
estimate outside exceptional sources remains open. Public inputs are data
only. No proof resource budget is modified.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
open GaloisForLFunctions.RHTower
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianReplicaStableActionFloorLaw

abbrev OrdinaryChoiSpace (L : ℕ) :=
  EuclideanSpace ℂ (Config (PairQubit L) × Config (PairQubit L))

def ordinaryChoiState (L : ℕ) (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ)
    (t : ℝ) : OrdinaryChoiSpace L :=
  choiVector (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t)

def identityAnchoredUnitaryChoiTarget {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :
    Option C → OrdinaryChoiSpace L
  | none => choiVector 1
  | some c => choiVector (U c : Matrix _ _ ℂ)

/-- Actual occupied-rank action, with the physical circuit projector and both
return-excised time sheets retained. No full-purity replacement is used. -/
def ordinaryChoiIncidenceActionCapacity {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) (r : ℕ) (a T : ℝ) : ℝ :=
  let target := fun c => (identityAnchoredUnitaryChoiTarget L U c).ofLp
  let state := fun x => (ordinaryChoiState L J (T * x)).ofLp
  let R := Icc (-|a| / T) (|a| / T)
  (returnExcisedReplicaIncidenceNumber r target state R : ℝ) *
    returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r target state R

private theorem choi_continuous {d : Type*} [Fintype d] [DecidableEq d] :
    Continuous (fun U : Matrix d d ℂ => choiVector U) := by
  unfold choiVector
  fun_prop

/-- Keep the matrix abstract so continuity inference does not unfold the
ordinary ensemble's finite coefficient sum. -/
private theorem fixed_hamiltonian_choi_continuous
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (H : Matrix d d ℂ) (T : ℝ) :
    Continuous (fun x : ℝ => choiVector (unitaryEvolution H (T * x))) := by
  have hp : Continuous (fun x : ℝ => (H, T * x)) :=
    (continuous_const (y := H)).prodMk
      ((continuous_const (y := T)).mul continuous_id)
  exact choi_continuous.comp ((continuous_unitaryEvolution (d := d)).comp hp)

private theorem state_continuous (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) (T : ℝ) :
    Continuous (fun x : ℝ => ordinaryChoiState L J (T * x)) :=
  fixed_hamiltonian_choi_continuous (ordinaryTwoLocalGaussianHamiltonian L J) T

private theorem state_norm (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) (t : ℝ) :
    ‖ordinaryChoiState L J t‖ = 1 :=
  norm_choiVector_eq_one Fintype.card_pos
    (Matrix.mem_unitaryGroup_iff'.mp (unitaryEvolution_mem_unitary
      (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J) t))

private theorem target_norm {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) (c : Option C) :
    ‖identityAnchoredUnitaryChoiTarget L U c‖ = 1 := by
  cases c with
  | none => exact norm_choiVector_eq_one Fintype.card_pos (by simp)
  | some c => exact norm_choiVector_eq_one Fintype.card_pos (U c).2.1

private theorem finite_inner_self_of_norm_one
    {α : Type*} [Fintype α] (psi : EuclideanSpace ℂ α) (h : ‖psi‖ = 1) :
    finiteComplexInner psi.ofLp psi.ofLp = 1 := by
  rw [← inner_toLp_eq_finiteComplexInner]
  simp only [WithLp.toLp_ofLp]
  rw [inner_self_eq_norm_sq_to_K, h]
  norm_num

private theorem norm_hamiltonian_on_box (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) {ρ : ℝ}
    (hJ : J ∈ closedBall 0 ρ) :
    ‖ordinaryTwoLocalGaussianHamiltonian L J‖ ≤ ρ * ordinaryTwoLocalGeneratorMass L := by
  classical
  have hnorm : ‖J‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hJ
  unfold ordinaryTwoLocalGaussianHamiltonian
  calc
    ‖∑ k, (J k : ℂ) • ordinaryTwoLocalGenerator L k‖ ≤
        ∑ k, ‖(J k : ℂ) • ordinaryTwoLocalGenerator L k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ * ‖ordinaryTwoLocalGenerator L k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have hcoord : |J k| ≤ ρ := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm J k).trans hnorm
      exact mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
    _ = ρ * ordinaryTwoLocalGeneratorMass L := by
      rw [ordinaryTwoLocalGeneratorMass, Finset.mul_sum]

private theorem state_near_identity (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) (t : ℝ) :
    pureStateTraceDistance (ordinaryChoiState L J t)
      (choiVector (1 : Matrix (Config (PairQubit L)) _ ℂ)) ≤
        |t| * ‖ordinaryTwoLocalGaussianHamiltonian L J‖ := by
  have hH := ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J
  have hdist := choiDist_le_l2_opNorm_sub
    (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t) 1
    (Matrix.mem_unitaryGroup_iff'.mp (unitaryEvolution_mem_unitary hH t)) (by simp)
  have hevol := norm_unitaryEvolution_sub_le
    (ordinaryTwoLocalGaussianHamiltonian L J) 0 hH (IsSelfAdjoint.zero _) t
  have hzero : unitaryEvolution (0 : Matrix (Config (PairQubit L)) _ ℂ) t = 1 := by
    simp only [unitaryEvolution, smul_zero, NormedSpace.exp_zero]
  rw [hzero, sub_zero] at hevol
  exact hdist.trans hevol

private theorem coordinate_integrable
    {α : Type*} [Fintype α] {r : ℕ}
    (psi : ℝ → EuclideanSpace ℂ α) (hc : Continuous psi)
    (hn : ∀ x, ‖psi x‖ = 1)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (i : Fin (Module.finrank ℂ S)) (R : Set ℝ) :
    Integrable (fun x => ‖replicaSubspaceCoordinate r S (psi x) i‖ ^ 2)
      ((gaussianReal 0 1).restrict R) := by
  have hcont := continuous_replicaSubspaceCoordinate_comp psi hc S i
  apply Integrable.of_bound (hcont.norm.pow 2).aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖replicaSubspaceCoordinate r S (psi x) i‖ ^ 2 ≤ 1
  have hb := norm_replicaSubspaceCoordinate_le_one r S (psi x)
    (finite_inner_self_of_norm_one (psi x) (hn x)) i
  simpa only [one_pow] using
    (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hb

private theorem surviving_gaussian_block_mass {a T : ℝ}
    (hcut : |a| / T < 1 / 4) :
    gaussianFloorTwo / 4 ≤
      ((gaussianReal 0 1).restrict (Icc (-|a| / T) (|a| / T))ᶜ).real
        (Icc (3 / 4 : ℝ) 1) := by
  have hdisj : Icc (3 / 4 : ℝ) 1 ⊆ (Icc (-|a| / T) (|a| / T))ᶜ := by
    intro x hx hbad
    linarith only [hx.1, hbad.2, hcut]
  rw [measureReal_restrict_apply' measurableSet_Icc.compl,
    inter_eq_left.mpr hdisj]
  have hl := ENNReal.toReal_mono (measure_ne_top _ _)
    (gaussianReal_Icc_shifted_lower (a := (7 / 8 : ℝ)) (rho := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num))
  rw [ENNReal.toReal_ofReal (by positivity [gaussianFloorTwo_pos])] at hl
  norm_num at hl
  change 2 * gaussianFloorTwo * (1 / 8) ≤
    (gaussianReal 0 1).real (Icc (3 / 4 : ℝ) 1) at hl
  linarith only [hl]

private theorem action_capacity_floor_on_slow_draw {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) {r : ℕ} (hr : 0 < r)
    {a T : ℝ} (hT : 1 ≤ T) (hcut : |a| / T < 1 / 4)
    (hslow : T * ‖ordinaryTwoLocalGaussianHamiltonian L J‖ ≤ 1 / 2) :
    (gaussianFloorTwo / 4 * (3 / 4 : ℝ) ^ r) ^ 2 ≤
      ordinaryChoiIncidenceActionCapacity L U J r a T := by
  let target := fun c => (identityAnchoredUnitaryChoiTarget L U c).ofLp
  let state := fun x => (ordinaryChoiState L J (T * x)).ofLp
  let R := Icc (-|a| / T) (|a| / T)
  let S := returnExcisedReplicaIncidenceSpan r target state R
  let E : Set ℝ := {x | ∃ c, (3 / 4 : ℝ) ≤ finitePureStateFidelity (state x) (target c)}
  let ν := (gaussianReal 0 1).restrict Rᶜ
  have hc := state_continuous L J T
  have htnorm : ∀ c, finiteComplexInner (target c) (target c) = 1 := fun c =>
    finite_inner_self_of_norm_one _ (target_norm L U c)
  have hcoords := fun i => coordinate_integrable
    (fun x => ordinaryChoiState L J (T * x)) hc (fun x => state_norm L J _) S i Rᶜ
  have hreceiver := quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound_arbitraryTarget
    (gaussianReal 0 1) hr target state htnorm (3 / 4) (by norm_num)
    R measurableSet_Icc
    (fun i => (continuous_replicaSubspaceCoordinate_comp
      (fun x => ordinaryChoiState L J (T * x)) hc S i).aestronglyMeasurable) hcoords
  have hcapture : Icc (3 / 4 : ℝ) 1 ⊆ E := by
    intro x hx
    refine ⟨none, ?_⟩
    have ht : |T * x| ≤ T := by
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hT)]
      apply mul_le_of_le_one_right (lt_of_lt_of_le zero_lt_one hT).le
      exact abs_le.mpr ⟨by linarith only [hx.1], hx.2⟩
    have hdist : pureStateTraceDistance (ordinaryChoiState L J (T * x))
        (choiVector (1 : Matrix (Config (PairQubit L)) _ ℂ)) ≤ 1 / 2 :=
      (state_near_identity L J _).trans
        ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans hslow)
    have hsq := sq_pureStateTraceDistance (ordinaryChoiState L J (T * x))
      (choiVector (1 : Matrix (Config (PairQubit L)) _ ℂ))
      (state_norm L J _).le (norm_choiVector_eq_one Fintype.card_pos (by simp)).le
    have hdistSq := (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hdist
    change (3 / 4 : ℝ) ≤ finitePureStateFidelity
      (ordinaryChoiState L J (T * x)).ofLp (choiVector (1 : Matrix _ _ ℂ)).ofLp
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    rw [norm_inner_symm]
    linarith only [hsq, hdistSq]
  have hmass : gaussianFloorTwo / 4 ≤ ν.real E :=
    (surviving_gaussian_block_mass hcut).trans
      (measureReal_mono hcapture (measure_ne_top _ _))
  apply le_trans ?_ hreceiver
  apply (sq_le_sq₀ (by positivity [gaussianFloorTwo_pos]) (by positivity)).2
  exact mul_le_mul_of_nonneg_right hmass (by positivity)

private theorem receiver_lt_floor {v T : ℝ} (hv : 1 ≤ v) (hT : 1 ≤ T) (r : ℕ) :
    (gaussianFloorTwo / (8 * v * T) * (7 / 16 : ℝ) ^ r) ^ 2 <
      (gaussianFloorTwo / 4 * (3 / 4 : ℝ) ^ r) ^ 2 := by
  have hden : (8 : ℝ) ≤ 8 * v * T :=
    (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 8) hv).trans
      (le_mul_of_one_le_right (by positivity) hT)
  have hcoef : gaussianFloorTwo / (8 * v * T) ≤ gaussianFloorTwo / 8 :=
    div_le_div_of_nonneg_left gaussianFloorTwo_pos.le (by norm_num) hden
  have hp : (7 / 16 : ℝ) ^ r ≤ (3 / 4 : ℝ) ^ r :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) r
  apply (sq_lt_sq₀ (by positivity [gaussianFloorTwo_pos])
    (by positivity [gaussianFloorTwo_pos])).2
  calc
    gaussianFloorTwo / (8 * v * T) * (7 / 16 : ℝ) ^ r ≤
        gaussianFloorTwo / 8 * (3 / 4 : ℝ) ^ r :=
      mul_le_mul hcoef hp (by positivity) (by positivity [gaussianFloorTwo_pos])
    _ < gaussianFloorTwo / 4 * (3 / 4 : ℝ) ^ r :=
      mul_lt_mul_of_pos_right (by linarith only [gaussianFloorTwo_pos]) (by positivity)

/-- Failure of the fixed-error incidence receiver at every positive replica
order. The clock speed `1 + ‖H‖` is a valid conservative physical speed.
This definition uses outer measure below; no measurability of the rank-changing
event is assumed. -/
def ordinaryReplicaStableReceiverFailureSet {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) (a T : ℝ) :
    Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ r : ℕ,
    (gaussianFloorTwo /
      (8 * (‖ordinaryTwoLocalGaussianHamiltonian L J‖ + 1) * T) *
        (7 / 16 : ℝ) ^ (r + 1)) ^ 2 <
      ordinaryChoiIncidenceActionCapacity L U J (r + 1) a T}

private theorem generator_mass_nonneg (L : ℕ) :
    0 ≤ ordinaryTwoLocalGeneratorMass L := by
  unfold ordinaryTwoLocalGeneratorMass
  exact Finset.sum_nonneg fun k _ => norm_nonneg (ordinaryTwoLocalGenerator L k)

private theorem scale_bounds (a u M : ℝ) (hM : 0 ≤ M) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    let ρ := 1 / (2 * T * (M + 1))
    1 ≤ T ∧ 0 < ρ ∧ ρ ≤ 1 ∧ |a| / T < 1 / 4 ∧ T * (ρ * M) ≤ 1 / 2 := by
  let T := 1 + 4 * |a| + u ^ (2 : ℕ)
  let ρ := 1 / (2 * T * (M + 1))
  have hT : 1 ≤ T := by
    dsimp [T]
    linarith only [abs_nonneg a, sq_nonneg u]
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hMpos : 0 < M + 1 := by linarith only [hM]
  have htwoT : 0 < 2 * T := mul_pos (by norm_num) hTpos
  have hρpos : 0 < ρ := one_div_pos.mpr (mul_pos htwoT hMpos)
  have hden : 1 ≤ 2 * T * (M + 1) := by
    calc
      (1 : ℝ) ≤ 2 := by norm_num
      _ ≤ 2 * T := le_mul_of_one_le_right (by norm_num) hT
      _ ≤ 2 * T * (M + 1) :=
        le_mul_of_one_le_right htwoT.le (by linarith only [hM])
  have hρ1 : ρ ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hden
  have hcut : |a| / T < 1 / 4 := by
    apply (div_lt_iff₀ hTpos).2
    dsimp [T]
    linarith only [sq_nonneg u]
  have hscale : T * (ρ * M) ≤ 1 / 2 := by
    calc
      T * (ρ * M) ≤ T * (ρ * (M + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith only) hρpos.le) hTpos.le
      _ = 1 / 2 := by
        dsimp [ρ]
        field_simp [hTpos.ne', hMpos.ne']
  exact ⟨hT, hρpos, hρ1, hcut, hscale⟩

private theorem box_subset_failure {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {a T ρ : ℝ} (hT : 1 ≤ T) (hcut : |a| / T < 1 / 4)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ 1 / 2) :
    closedBall (0 : OrdinaryTwoLocalGaussianCoordinate L → ℝ) ρ ⊆
      ordinaryReplicaStableReceiverFailureSet L U a T := by
  intro J hJ r
  have hslow : T * ‖ordinaryTwoLocalGaussianHamiltonian L J‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (norm_hamiltonian_on_box L J hJ)
      (lt_of_lt_of_le zero_lt_one hT).le).trans hscale
  exact (receiver_lt_floor (le_add_of_nonneg_left (norm_nonneg _)) hT (r + 1)).trans_le
    (action_capacity_floor_on_slow_draw L U J (Nat.succ_pos r) hT hcut hslow)

/-- **Replica-stable exceptional-source floor for the actual projected action.**
For any finite cutoff (including a circuit-budget-dependent cutoff), the same
positive Gaussian coefficient box violates the receiver at every replica order.
The unitary family can be continuous; identity is included explicitly.

This is a necessary exceptional-mass bound, not a typical-draw growth theorem.
Its mass can be small and does not disprove a high-probability quenched law.
The cutoff is fixed in the source draw; a source-dependent inverse-speed cutoff
is not covered. Public inputs are data only. -/
theorem ordinaryTwoLocalGaussian_replicaStable_actionFailure_outerMeasure_floor
    {C : Type*} (L : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) (a u : ℝ) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    let ρ := 1 / (2 * T * (ordinaryTwoLocalGeneratorMass L + 1))
    0 < ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ∧
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryReplicaStableReceiverFailureSet L U a T) := by
  classical
  let T := 1 + 4 * |a| + u ^ (2 : ℕ)
  let M := ordinaryTwoLocalGeneratorMass L
  let ρ := 1 / (2 * T * (M + 1))
  obtain ⟨hT, hρpos, hρ1, hcut, hscale⟩ :=
    scale_bounds a u M (generator_mass_nonneg L)
  have hbox := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (y := (0 : OrdinaryTwoLocalGaussianCoordinate L → ℝ))
    (by simp) hρpos.le hρ1
  have hp : 0 < (2 * gaussianFloorTwo * ρ) ^
      Fintype.card (OrdinaryTwoLocalRawCoordinate L) :=
    pow_pos (mul_pos (mul_pos (by norm_num) gaussianFloorTwo_pos) hρpos) _
  exact ⟨ENNReal.ofReal_pos.mpr hp,
    hbox.trans (measure_mono (box_subset_failure L U hT hcut hscale))⟩

end GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianReplicaStableActionFloorLaw
