import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

namespace GaloisForLFunctions.HTGeometry.HarmonicMatchingScalarFirstReturnLaw

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

def harmonicAdaptivePair {L K : ℕ} (hKL : K < L) : Fin L :=
  ⟨K, hKL⟩

theorem harmonicAdaptivePair_phase_bounds
    {L K : ℕ} (hK : 1 ≤ K) (hKL : K < L)
    {t : ℝ} (htlo : Real.pi * K ≤ t)
    (hthi : t ≤ Real.pi * (K + 1)) :
    Real.pi / 2 ≤ t * harmonicPairWeight (harmonicAdaptivePair hKL) ∧
      t * harmonicPairWeight (harmonicAdaptivePair hKL) ≤ Real.pi := by
  have hdenN : 0 < K + 1 := by omega
  have hden : (0 : ℝ) < K + 1 := by exact_mod_cast hdenN
  have htloR : Real.pi * (K : ℝ) ≤ t := by exact_mod_cast htlo
  have hthiR : t ≤ Real.pi * ((K : ℝ) + 1) := by exact_mod_cast hthi
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKhalf : ((K : ℝ) + 1) / 2 ≤ K := by linarith
  have hhalf : (Real.pi / 2) * ((K : ℝ) + 1) ≤ Real.pi * K := by
    calc
      (Real.pi / 2) * ((K : ℝ) + 1) =
          Real.pi * (((K : ℝ) + 1) / 2) := by ring
      _ ≤ Real.pi * K :=
        mul_le_mul_of_nonneg_left hKhalf Real.pi_pos.le
  unfold harmonicPairWeight harmonicAdaptivePair
  rw [mul_one_div]
  change Real.pi / 2 ≤ t / ((K + 1 : ℕ) : ℝ) ∧
    t / ((K + 1 : ℕ) : ℝ) ≤ Real.pi
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).2
    simpa only [Nat.cast_add, Nat.cast_one] using hhalf.trans htloR
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).2
    simpa only [Nat.cast_add, Nat.cast_one] using hthiR

theorem harmonicMatching_identityChoiDist_ge_on_adaptive_shell
    {L K : ℕ} (hK : 1 ≤ K) (hKL : K < L)
    {t : ℝ} (htlo : Real.pi * K ≤ t)
    (hthi : t ≤ Real.pi * (K + 1)) :
    Real.sqrt ((1 : ℝ) / 8) ≤
      choiDist (1 : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
        (harmonicMatchingEvolution L t) := by
  have hphase := harmonicAdaptivePair_phase_bounds hK hKL htlo hthi
  simpa [circuitMatrix] using
    (choiDist_circuit_harmonicMatchingEvolution_ge_of_separates
      ([] : List (LocalGate (PairQubit L))) (harmonicAdaptivePair hKL) t
      (SeparatesAcross.one ({(harmonicAdaptivePair hKL, false)} :
        Finset (PairQubit L))) hphase.1 hphase.2)

theorem harmonicMatching_normalizedTrace_sq_le_seven_eighth_on_adaptive_shell
    {L K : ℕ} (hK : 1 ≤ K) (hKL : K < L)
    {t : ℝ} (htlo : Real.pi * K ≤ t)
    (hthi : t ≤ Real.pi * (K + 1)) :
    (‖Matrix.trace (harmonicMatchingEvolution L t)‖ /
      Fintype.card (Config (PairQubit L))) ^ 2 ≤ (7 : ℝ) / 8 := by
  have hdist := harmonicMatching_identityChoiDist_ge_on_adaptive_shell
    hK hKL htlo hthi
  rw [choiDist_eq Fintype.card_pos] at hdist
  simp only [conjTranspose_one, one_mul] at hdist
  have hdef : 0 ≤ 1 - (‖Matrix.trace (harmonicMatchingEvolution L t)‖ /
      Fintype.card (Config (PairQubit L))) ^ 2 := by
    by_contra hnot
    have hsqrt : Real.sqrt (1 -
        (‖Matrix.trace (harmonicMatchingEvolution L t)‖ /
          Fintype.card (Config (PairQubit L))) ^ 2) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hnot)
    rw [hsqrt] at hdist
    have hpos : 0 < Real.sqrt ((1 : ℝ) / 8) := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hsq : (1 : ℝ) / 8 ≤
      1 - (‖Matrix.trace (harmonicMatchingEvolution L t)‖ /
        Fintype.card (Config (PairQubit L))) ^ 2 := by
    exact (Real.sqrt_le_sqrt_iff hdef).mp hdist
  linarith

/-- Fixed robust scalar gap: half the exact harmonic-center gap. -/
noncomputable def harmonicScalarGap : ℝ :=
  Real.sqrt ((1 : ℝ) / 8) / 2

theorem harmonicScalarGap_pos : 0 < harmonicScalarGap := by
  unfold harmonicScalarGap
  positivity

/-- A perturbation tube transfers the dimension-free scalar nonreturn gap
uniformly over every adaptive harmonic shell. -/
theorem perturbed_harmonicMatching_identityChoiDist_ge_on_adaptive_shell
    {L K : ℕ} (hK : 1 ≤ K) (hKL : K < L)
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {T t η : ℝ}
    (hH : IsSelfAdjoint H)
    (htlo : Real.pi * K ≤ t)
    (hthi : t ≤ Real.pi * (K + 1))
    (htT : t ≤ T)
    (htube : T * ‖H - harmonicMatchingHamiltonian L‖ ≤ η) :
    Real.sqrt ((1 : ℝ) / 8) - η ≤
      choiDist (1 : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
        (unitaryEvolution H t) := by
  let U := unitaryEvolution H t
  let V := unitaryEvolution (harmonicMatchingHamiltonian L) t
  have ht0 : 0 ≤ t := by
    exact (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg K)).trans htlo
  have hI :
      (1 : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)ᴴ * 1 = 1 := by
    simp
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
  have htri : choiDist (1 : Matrix (Config (PairQubit L))
      (Config (PairQubit L)) ℂ) V ≤ choiDist 1 U + choiDist U V :=
    choiDist_triangle Fintype.card_pos hI hU hV
  have hcenter : Real.sqrt ((1 : ℝ) / 8) ≤
      choiDist (1 : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) V := by
    simpa [V, unitaryEvolution_harmonicMatchingHamiltonian] using
      harmonicMatching_identityChoiDist_ge_on_adaptive_shell hK hKL htlo hthi
  linarith

/-- Radius selected so the complete interval `0 ≤ t ≤ πL` spends at most
half the exact harmonic-center scalar gap. -/
noncomputable def harmonicScalarTubeRadius (L : ℕ) : ℝ :=
  harmonicScalarGap /
    (1 + (Real.pi * L) * ordinaryTwoLocalGeneratorMass L)

theorem ordinaryTwoLocalGeneratorMass_nonneg (L : ℕ) :
    0 ≤ ordinaryTwoLocalGeneratorMass L := by
  unfold ordinaryTwoLocalGeneratorMass
  exact Finset.sum_nonneg fun k _ => norm_nonneg (ordinaryTwoLocalGenerator L k)

theorem harmonicScalarTubeRadius_pos (L : ℕ) :
    0 < harmonicScalarTubeRadius L := by
  have hmass := ordinaryTwoLocalGeneratorMass_nonneg L
  have hA : 0 ≤ (Real.pi * L) * ordinaryTwoLocalGeneratorMass L :=
    mul_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg L)) hmass
  have hden : 0 < 1 + (Real.pi * L) * ordinaryTwoLocalGeneratorMass L := by
    linarith
  unfold harmonicScalarTubeRadius
  exact div_pos harmonicScalarGap_pos hden

theorem harmonicScalarTubeRadius_le_one (L : ℕ) :
    harmonicScalarTubeRadius L ≤ 1 := by
  have hgap : harmonicScalarGap ≤ 1 := by
    unfold harmonicScalarGap
    have hsqrt : Real.sqrt ((1 : ℝ) / 8) ≤ 1 := by
      rw [Real.sqrt_le_one]
      norm_num
    linarith
  have hmass := ordinaryTwoLocalGeneratorMass_nonneg L
  have hA : 0 ≤ (Real.pi * L) * ordinaryTwoLocalGeneratorMass L :=
    mul_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg L)) hmass
  have hden : 0 < 1 + (Real.pi * L) * ordinaryTwoLocalGeneratorMass L := by
    linarith
  unfold harmonicScalarTubeRadius
  apply (div_le_one hden).2
  exact hgap.trans (by linarith)

theorem harmonicScalarTubeRadius_scale (L : ℕ) :
    (Real.pi * L) *
        (harmonicScalarTubeRadius L * ordinaryTwoLocalGeneratorMass L) ≤
      harmonicScalarGap := by
  let A : ℝ := (Real.pi * L) * ordinaryTwoLocalGeneratorMass L
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) (ordinaryTwoLocalGeneratorMass_nonneg L)
  have hden : 0 < 1 + A := by positivity
  have hgap : 0 ≤ harmonicScalarGap := harmonicScalarGap_pos.le
  calc
    (Real.pi * L) *
        (harmonicScalarTubeRadius L * ordinaryTwoLocalGeneratorMass L) =
      A * (harmonicScalarGap / (1 + A)) := by
        dsimp [A, harmonicScalarTubeRadius]
        ring
    _ ≤ harmonicScalarGap := by
      rw [show A * (harmonicScalarGap / (1 + A)) =
          (A * harmonicScalarGap) / (1 + A) by ring]
      apply (div_le_iff₀ hden).2
      nlinarith

/-- Same-draw scalar exclusion on every complete shell from `π` through
`πL`, for one ordinary time-independent two-local Gaussian Hamiltonian. -/
def ordinaryTwoLocalGaussianInitialScalarExclusionEvent (L : ℕ) :
    Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ (K : ℕ) (t : ℝ),
    1 ≤ K → K < L →
    Real.pi * K ≤ t → t ≤ Real.pi * (K + 1) →
    harmonicScalarGap ≤
      choiDist (1 : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
        (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t)}

theorem measure_ordinaryTwoLocalGaussianInitialScalarExclusionEvent_lower
    (L : ℕ) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * harmonicScalarTubeRadius L) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianInitialScalarExclusionEvent L) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (harmonicOrdinaryTwoLocalCenter_norm_le_one L)
    (harmonicScalarTubeRadius_pos L).le (harmonicScalarTubeRadius_le_one L)
  refine hball.trans (measure_mono ?_)
  intro J hJ K t hK hKL htlo hthi
  have hnorm :=
    norm_ordinaryTwoLocalGaussianHamiltonian_sub_harmonicCenter_le L J hJ
  have htT : t ≤ Real.pi * L := by
    have hcast : (K : ℝ) + 1 ≤ L := by exact_mod_cast Nat.succ_le_iff.mpr hKL
    exact hthi.trans (mul_le_mul_of_nonneg_left hcast Real.pi_pos.le)
  have hT : 0 ≤ Real.pi * L := by positivity
  have htube : (Real.pi * L) *
      ‖ordinaryTwoLocalGaussianHamiltonian L J - harmonicMatchingHamiltonian L‖ ≤
        harmonicScalarGap := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans
      (harmonicScalarTubeRadius_scale L)
  have hgap := perturbed_harmonicMatching_identityChoiDist_ge_on_adaptive_shell
    hK hKL (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
    htlo hthi htT htube
  dsimp [harmonicScalarGap] at hgap ⊢
  linarith

theorem measure_ordinaryTwoLocalGaussianInitialScalarExclusionEvent_pos
    (L : ℕ) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianInitialScalarExclusionEvent L) := by
  have hlower := measure_ordinaryTwoLocalGaussianInitialScalarExclusionEvent_lower L
  have hbase : 0 < 2 * gaussianFloorTwo * harmonicScalarTubeRadius L := by
    exact mul_pos (mul_pos (by norm_num) gaussianFloorTwo_pos)
      (harmonicScalarTubeRadius_pos L)
  exact (ENNReal.ofReal_pos.mpr
    (pow_pos hbase _)).trans_le hlower

/-- Common tube for simultaneous harmonic complexity growth and scalar
first-return exclusion. -/
noncomputable def harmonicGrowthScalarTubeRadius (L : ℕ) : ℝ :=
  harmonicScalarTubeRadius L / 2

theorem harmonicGrowthScalarTubeRadius_pos (L : ℕ) :
    0 < harmonicGrowthScalarTubeRadius L := by
  unfold harmonicGrowthScalarTubeRadius
  exact div_pos (harmonicScalarTubeRadius_pos L) (by norm_num)

theorem harmonicGrowthScalarTubeRadius_le_one (L : ℕ) :
    harmonicGrowthScalarTubeRadius L ≤ 1 := by
  unfold harmonicGrowthScalarTubeRadius
  have hρ := harmonicScalarTubeRadius_le_one L
  have hρ0 := (harmonicScalarTubeRadius_pos L).le
  linarith

theorem harmonicGrowthScalarTubeRadius_scale (L : ℕ) :
    (Real.pi * L) *
        (harmonicGrowthScalarTubeRadius L * ordinaryTwoLocalGeneratorMass L) ≤
      harmonicScalarGap / 2 := by
  have hscale := harmonicScalarTubeRadius_scale L
  unfold harmonicGrowthScalarTubeRadius
  calc
    (Real.pi * L) *
        (harmonicScalarTubeRadius L / 2 * ordinaryTwoLocalGeneratorMass L) =
      ((Real.pi * L) *
        (harmonicScalarTubeRadius L * ordinaryTwoLocalGeneratorMass L)) / 2 := by ring
    _ ≤ harmonicScalarGap / 2 := by linarith

/-- Same ordinary static draw carries both the complete harmonic Choi ramp
and dimension-free scalar nonreturn on every subsequent adaptive shell. -/
def ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent (L : ℕ) :
    Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  ordinaryTwoLocalGaussianHarmonicChoiGrowthEvent L (Real.pi * L) harmonicScalarGap ∩
    ordinaryTwoLocalGaussianInitialScalarExclusionEvent L

theorem measure_ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent_lower
    (L : ℕ) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * harmonicGrowthScalarTubeRadius L) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent L) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (harmonicOrdinaryTwoLocalCenter_norm_le_one L)
    (harmonicGrowthScalarTubeRadius_pos L).le
    (harmonicGrowthScalarTubeRadius_le_one L)
  refine hball.trans (measure_mono ?_)
  intro J hJ
  have hnorm :=
    norm_ordinaryTwoLocalGaussianHamiltonian_sub_harmonicCenter_le L J hJ
  have hT : 0 ≤ Real.pi * L := by positivity
  have htube : (Real.pi * L) *
      ‖ordinaryTwoLocalGaussianHamiltonian L J - harmonicMatchingHamiltonian L‖ ≤
        harmonicScalarGap / 2 := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans
      (harmonicGrowthScalarTubeRadius_scale L)
  constructor
  · intro K c t hKL htlo hthi htT hclose
    apply perturbed_harmonicMatching_twoGateCount_shell_lower
      (ε := harmonicScalarGap) (η := harmonicScalarGap / 2) c
      (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
      hKL htlo hthi htT htube
    · unfold harmonicScalarGap
      have hroot : 0 < Real.sqrt ((1 : ℝ) / 8) := by positivity
      linarith
    · exact hclose
  · intro K t hK hKL htlo hthi
    have htT : t ≤ Real.pi * L := by
      have hcast : (K : ℝ) + 1 ≤ L := by exact_mod_cast Nat.succ_le_iff.mpr hKL
      exact hthi.trans (mul_le_mul_of_nonneg_left hcast Real.pi_pos.le)
    have hgap := perturbed_harmonicMatching_identityChoiDist_ge_on_adaptive_shell
      hK hKL (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
      htlo hthi htT htube
    unfold harmonicScalarGap at hgap ⊢
    have hroot : 0 < Real.sqrt ((1 : ℝ) / 8) := by positivity
    linarith

theorem measure_ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent_pos
    (L : ℕ) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent L) := by
  have hlower :=
    measure_ordinaryTwoLocalGaussianGrowthAndInitialScalarExclusionEvent_lower L
  have hbase : 0 < 2 * gaussianFloorTwo * harmonicGrowthScalarTubeRadius L := by
    exact mul_pos (mul_pos (by norm_num) gaussianFloorTwo_pos)
      (harmonicGrowthScalarTubeRadius_pos L)
  exact (ENNReal.ofReal_pos.mpr (pow_pos hbase _)).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.HarmonicMatchingScalarFirstReturnLaw
