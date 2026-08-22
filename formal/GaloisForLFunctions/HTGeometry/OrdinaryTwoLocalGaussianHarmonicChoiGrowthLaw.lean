import GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianOneDrawGrowthLaw
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

namespace GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

theorem norm_trace_le_card_mul_l2_opNorm
    {d : Type*} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) :
    ‖Matrix.trace X‖ ≤ Fintype.card d * ‖X‖ := by
  rw [Matrix.trace]
  calc
    ‖∑ i, X i i‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : d, ‖X‖ := Finset.sum_le_sum fun i _ => norm_entry_le_l2_opNorm X i i
    _ = Fintype.card d * ‖X‖ := by simp

theorem norm_choiVector_le_l2_opNorm
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (A : Matrix d d ℂ) : ‖choiVector A‖ ≤ ‖A‖ := by
  have hd : 0 < Fintype.card d := Fintype.card_pos
  have hinner := inner_choiVector hd A A
  have hnormeq := congrArg norm hinner
  rw [inner_self_eq_norm_sq_to_K] at hnormeq
  have hcardR : (0 : ℝ) < Fintype.card d := by exact_mod_cast hd
  have htrace := norm_trace_le_card_mul_l2_opNorm (Aᴴ * A)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at htrace
  rw [norm_div, Complex.norm_natCast] at hnormeq
  change ‖((‖choiVector A‖ : ℂ) ^ 2)‖ =
      ‖(Aᴴ * A).trace‖ / (Fintype.card d : ℝ) at hnormeq
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg (choiVector A))] at hnormeq
  have hsq : ‖choiVector A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [hnormeq]
    rw [div_le_iff₀ hcardR]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using htrace
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem choiDist_le_l2_opNorm_sub
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (U V : Matrix d d ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    choiDist U V ≤ ‖U - V‖ := by
  rw [choiDist]
  refine (pureStateTraceDistance_le_norm_sub (choiVector U) (choiVector V)
    (norm_choiVector_eq_one Fintype.card_pos hU)
    (norm_choiVector_eq_one Fintype.card_pos hV)).trans ?_
  have hsub : choiVector U - choiVector V = choiVector (U - V) := by
    ext p
    simp [choiVector]
    ring
  rw [hsub]
  exact norm_choiVector_le_l2_opNorm (U - V)

/-! Harmonic center inside ordinary termwise two-local coordinates. -/

noncomputable def harmonicMatchingHamiltonian (L : ℕ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal fun x => (harmonicMatchingEnergy x : ℂ)

def harmonicOrdinaryTwoLocalRawCenter (L : ℕ) :
    OrdinaryTwoLocalRawCoordinate L → ℝ
  | Sum.inl j => harmonicPairWeight j
  | Sum.inr _ => 0

def harmonicOrdinaryTwoLocalCenter (L : ℕ)
    (k : OrdinaryTwoLocalGaussianCoordinate L) : ℝ :=
  harmonicOrdinaryTwoLocalRawCenter L ((ordinaryTwoLocalRawEquivFin L).symm k)

theorem ordinaryTwoLocalGaussianHamiltonian_harmonicCenter (L : ℕ) :
    ordinaryTwoLocalGaussianHamiltonian L (harmonicOrdinaryTwoLocalCenter L) =
      harmonicMatchingHamiltonian L := by
  classical
  rw [ordinaryTwoLocalGaussianHamiltonian]
  change (∑ k, ((harmonicOrdinaryTwoLocalRawCenter L
    ((ordinaryTwoLocalRawEquivFin L).symm k) : ℝ) : ℂ) •
      ordinaryTwoLocalRawGenerator L ((ordinaryTwoLocalRawEquivFin L).symm k)) = _
  rw [← (ordinaryTwoLocalRawEquivFin L).sum_comp]
  simp only [Fintype.sum_sum_type]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [harmonicOrdinaryTwoLocalRawCenter, ordinaryTwoLocalRawGenerator,
      matchingOccupationMatrix, bridgeOccupationMatrix,
      harmonicMatchingHamiltonian, harmonicMatchingEnergy, harmonicPairTerm,
      Matrix.sum_apply, Matrix.smul_apply,
      Matrix.diagonal_apply_eq]
    congr 1
    funext j
    split_ifs <;> simp_all
  · simp [harmonicOrdinaryTwoLocalRawCenter, ordinaryTwoLocalRawGenerator,
      matchingOccupationMatrix, bridgeOccupationMatrix,
      harmonicMatchingHamiltonian, Matrix.sum_apply,
      Matrix.smul_apply, hxy]

theorem harmonicMatchingHamiltonian_isSelfAdjoint (L : ℕ) :
    IsSelfAdjoint (harmonicMatchingHamiltonian L) := by
  rw [← ordinaryTwoLocalGaussianHamiltonian_harmonicCenter]
  exact ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L _

theorem unitaryEvolution_harmonicMatchingHamiltonian (L : ℕ) (t : ℝ) :
    unitaryEvolution (harmonicMatchingHamiltonian L) t =
      harmonicMatchingEvolution L t := by
  exact unitaryEvolution_diagonal _ _

theorem harmonicOrdinaryTwoLocalCenter_norm_le_one (L : ℕ) :
    ‖harmonicOrdinaryTwoLocalCenter L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
  change ‖harmonicOrdinaryTwoLocalRawCenter L
    ((ordinaryTwoLocalRawEquivFin L).symm k)‖ ≤ 1
  rcases (ordinaryTwoLocalRawEquivFin L).symm k with j | rest
  · have hden : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
    have hw : 0 ≤ harmonicPairWeight j := by
      unfold harmonicPairWeight
      positivity
    rw [harmonicOrdinaryTwoLocalRawCenter, Real.norm_eq_abs, abs_of_nonneg hw]
    unfold harmonicPairWeight
    apply (div_le_one hden).2
    exact_mod_cast j.val.add_one_pos
  · simp [harmonicOrdinaryTwoLocalRawCenter]

theorem norm_ordinaryTwoLocalGaussianHamiltonian_sub_harmonicCenter_le
    (L : ℕ) (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) {ρ : ℝ}
    (hJ : J ∈ closedBall (harmonicOrdinaryTwoLocalCenter L) ρ) :
    ‖ordinaryTwoLocalGaussianHamiltonian L J - harmonicMatchingHamiltonian L‖ ≤
      ρ * ordinaryTwoLocalGeneratorMass L := by
  classical
  have hnorm : ‖J - harmonicOrdinaryTwoLocalCenter L‖ ≤ ρ := by
    simpa [mem_closedBall, dist_eq_norm] using hJ
  have hcoord : ∀ k, |J k - harmonicOrdinaryTwoLocalCenter L k| ≤ ρ := by
    intro k
    have hk := norm_le_pi_norm (J - harmonicOrdinaryTwoLocalCenter L) k
    rw [Pi.sub_apply, Real.norm_eq_abs] at hk
    exact hk.trans hnorm
  rw [← ordinaryTwoLocalGaussianHamiltonian_harmonicCenter L,
    ordinaryTwoLocalGaussianHamiltonian, ordinaryTwoLocalGaussianHamiltonian]
  calc
    ‖(∑ k, ((J k : ℝ) : ℂ) • ordinaryTwoLocalGenerator L k) -
        ∑ k, ((harmonicOrdinaryTwoLocalCenter L k : ℝ) : ℂ) •
          ordinaryTwoLocalGenerator L k‖
      = ‖∑ k, (((J k - harmonicOrdinaryTwoLocalCenter L k : ℝ)) : ℂ) •
          ordinaryTwoLocalGenerator L k‖ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [← sub_smul, Complex.ofReal_sub]
    _ ≤ ∑ k, ‖((((J k - harmonicOrdinaryTwoLocalCenter L k : ℝ)) : ℂ) •
          ordinaryTwoLocalGenerator L k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ * ‖ordinaryTwoLocalGenerator L k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hcoord k) (norm_nonneg _)
    _ = ρ * ordinaryTwoLocalGeneratorMass L := by
      rw [ordinaryTwoLocalGeneratorMass, Finset.mul_sum]

/-- A fixed operator-norm tube around the harmonic center inherits every complete Choi shell. -/
theorem perturbed_harmonicMatching_twoGateCount_shell_lower
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {T t ε η : ℝ}
    (hH : IsSelfAdjoint H)
    (hKL : 2 * K ≤ L)
    (htlo : Real.pi * K ≤ t) (hthi : t < Real.pi * (K + 1))
    (htT : t ≤ T)
    (htube : T * ‖H - harmonicMatchingHamiltonian L‖ ≤ η)
    (hbudget : ε + η < Real.sqrt ((1 : ℝ) / 8))
    (hclose : choiDist (circuitMatrix c) (unitaryEvolution H t) < ε) :
    K ≤ 2 * twoGateCount c := by
  let U := unitaryEvolution H t
  let V := unitaryEvolution (harmonicMatchingHamiltonian L) t
  have ht0 : 0 ≤ t := by
    have hbase : 0 ≤ Real.pi * (K : ℝ) := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg K)
    exact hbase.trans htlo
  have hC : (circuitMatrix c)ᴴ * circuitMatrix c = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (circuitMatrix_unitary c))
  have hU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (unitaryEvolution_mem_unitary hH t))
  have hVself := harmonicMatchingHamiltonian_isSelfAdjoint L
  have hV : Vᴴ * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unitaryEvolution_mem_unitary hVself t))
  have hUV : choiDist U V ≤ η := by
    calc
      choiDist U V ≤ ‖U - V‖ := choiDist_le_l2_opNorm_sub U V hU hV
      _ ≤ |t| * ‖H - harmonicMatchingHamiltonian L‖ := by
        exact norm_unitaryEvolution_sub_le H (harmonicMatchingHamiltonian L) hH hVself t
      _ = t * ‖H - harmonicMatchingHamiltonian L‖ := by rw [abs_of_nonneg ht0]
      _ ≤ T * ‖H - harmonicMatchingHamiltonian L‖ :=
        mul_le_mul_of_nonneg_right htT (norm_nonneg _)
      _ ≤ η := htube
  have htri : choiDist (circuitMatrix c) V ≤
      choiDist (circuitMatrix c) U + choiDist U V :=
    choiDist_triangle Fintype.card_pos hC hU hV
  have hcenter : choiDist (circuitMatrix c) V < Real.sqrt ((1 : ℝ) / 8) :=
    lt_of_le_of_lt htri <| (add_lt_add_of_lt_of_le hclose hUV).trans hbudget
  apply harmonicMatching_twoGateCount_shell_lower c hKL htlo hthi
  simpa [V, unitaryEvolution_harmonicMatchingHamiltonian] using hcenter

/-- One draw obeys the Choi two-gate floor on every shell below one fixed horizon. -/
def ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent
    (L : ℕ) (T ε : ℝ) : Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ (K : ℕ) (c : List (LocalGate (PairQubit L))) (t : ℝ),
    2 * K ≤ L →
    Real.pi * K ≤ t →
    t < Real.pi * (K + 1) →
    t ≤ T →
    choiDist (circuitMatrix c)
      (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t) < ε →
    K ≤ 2 * twoGateCount c}

/-- Explicit Gaussian mass of one-draw Hamiltonians satisfying every harmonic Choi shell. -/
theorem measure_ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent_lower
    (L : ℕ) {T ε η ρ : ℝ}
    (hT : 0 ≤ T)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ η)
    (hbudget : ε + η < Real.sqrt ((1 : ℝ) / 8)) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent L T ε) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (harmonicOrdinaryTwoLocalCenter_norm_le_one L) hρ0 hρ1
  refine hball.trans (measure_mono ?_)
  intro J hJ K c t hKL htlo hthi htT hclose
  have hnorm :=
    norm_ordinaryTwoLocalGaussianHamiltonian_sub_harmonicCenter_le L J hJ
  have htube : T * ‖ordinaryTwoLocalGaussianHamiltonian L J -
      harmonicMatchingHamiltonian L‖ ≤ η := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
  exact perturbed_harmonicMatching_twoGateCount_shell_lower c
    (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
    hKL htlo hthi htT htube hbudget hclose

/-- The same-draw all-shell Choi growth event has strictly positive Gaussian probability. -/
theorem measure_ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent_pos
    (L : ℕ) {T ε η ρ : ℝ}
    (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ η)
    (hbudget : ε + η < Real.sqrt ((1 : ℝ) / 8)) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent L T ε) := by
  have hlower := measure_ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent_lower
    L hT hρ.le hρ1 hscale hbudget
  exact (ENNReal.ofReal_pos.mpr (by positivity [gaussianFloorTwo_pos])).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
