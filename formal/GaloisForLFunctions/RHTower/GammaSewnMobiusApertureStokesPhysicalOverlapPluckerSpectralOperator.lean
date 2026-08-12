import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator

/-!
# Physical-overlap cofinal Plücker spectral operator

P-G94 replaces P-G93's artificial direct sum of four-label packet copies by the literal shared
depth/adjacent-prime lattice.  Neighboring packets overlap on their common prime and consecutive
depth cells.  The source-normalized centered-vector series remains positive, Schatten-one, and
compact.  Each local weighted spectral block is still exact, but its local common-mode null vector
acquires strictly positive energy from the neighboring packet and is therefore not a global null
vector.  Blockwise degeneracy is a representation artifact, not a conserved source mode.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext
    (z : ℕ × ℕ) : Fin 4 → ℝ :=
  ![gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z 2,
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z 3,
    0, 0]

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel
    (z : ℕ × ℕ) (x : Fin 4 → ℝ) :
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z).mulVec x = 0 ↔
      ∃ c : ℝ,
        x = c • gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z := by
  exact gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff_smul_kernel
    (gammaSewnCriticalAdjacentPrime_order z.2) x

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i ≠ 0 := by
  have hsqrt : 0 < Real.sqrt
      (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  simp [gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector, hsqrt.ne']

theorem gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext_mulVec_ne_zero
    (z : ℕ × ℕ) :
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock (z.1, z.2 + 1)).mulVec
        (gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext z) ≠ 0 := by
  rw [Ne, gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel]
  rintro ⟨c, hc⟩
  have h2 := congrFun hc (2 : Fin 4)
  have h0 := congrFun hc (0 : Fin 4)
  simp only [gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext,
    Matrix.cons_val_two, Pi.smul_apply, smul_eq_mul] at h2
  simp only [gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext,
    Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul] at h0
  have hk2 := gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero
    (z.1, z.2 + 1) 2
  have hc0 : c = 0 := (mul_eq_zero.mp h2.symm).resolve_right hk2
  subst c
  simp only [zero_mul] at h0
  exact gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero z 2 h0

abbrev GammaSewnCriticalPhysicalPluckerIndex := ℕ × ℕ

abbrev GammaSewnCriticalPhysicalPluckerHilbert :=
  lp (fun _ : GammaSewnCriticalPhysicalPluckerIndex => ℂ) 2

def gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel
    (z : ℕ × ℕ) (i : Fin 4) : GammaSewnCriticalPhysicalPluckerIndex :=
  ![(z.1, z.2), (z.1 + 1, z.2), (z.1, z.2 + 1), (z.1 + 1, z.2 + 1)] i

theorem gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective
    (z : ℕ × ℕ) :
    Function.Injective (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z) := by
  rcases z with ⟨e, n⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel] at hij ⊢

theorem gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_right_overlap_zero
    (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 2 =
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1, z.2 + 1) 0 := by
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel]

theorem gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_right_overlap_one
    (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 3 =
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1, z.2 + 1) 1 := by
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel]

theorem gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_depth_overlap_zero
    (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 1 =
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1 + 1, z.2) 0 := by
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel]

theorem gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_depth_overlap_one
    (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 3 =
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1 + 1, z.2) 2 := by
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel]

def gammaSewnCriticalPhysicalPluckerBasis
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    GammaSewnCriticalPhysicalPluckerHilbert :=
  lp.single 2 u 1

theorem norm_gammaSewnCriticalPhysicalPluckerBasis
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    ‖gammaSewnCriticalPhysicalPluckerBasis u‖ = 1 := by
  unfold gammaSewnCriticalPhysicalPluckerBasis
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

theorem inner_gammaSewnCriticalPhysicalPluckerBasis
    (u v : GammaSewnCriticalPhysicalPluckerIndex) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerBasis u)
        (gammaSewnCriticalPhysicalPluckerBasis v) =
      if u = v then 1 else 0 := by
  by_cases h : u = v
  · subst v
    simp [gammaSewnCriticalPhysicalPluckerBasis]
  · simp [gammaSewnCriticalPhysicalPluckerBasis, lp.inner_single_left, h]

def gammaSewnCriticalPhysicalPluckerCenteredVector
    (z : ℕ × ℕ) (s : Fin 6) :
    GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑ i : Fin 4,
    (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) •
      gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)

theorem inner_basis_gammaSewnCriticalPhysicalPluckerCenteredVector
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
        (gammaSewnCriticalPhysicalPluckerCenteredVector z s) =
      gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i := by
  rw [gammaSewnCriticalPhysicalPluckerCenteredVector, inner_sum]
  simp only [inner_smul_right, inner_gammaSewnCriticalPhysicalPluckerBasis]
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z |>.eq_iff]

theorem inner_gammaSewnCriticalPhysicalPluckerCenteredVector_basis
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerCenteredVector z s)
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)) =
      gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i := by
  rw [← inner_conj_symm]
  simp [inner_basis_gammaSewnCriticalPhysicalPluckerCenteredVector]

theorem norm_gammaSewnCriticalPhysicalPluckerCenteredVector_le
    (z : ℕ × ℕ) (s : Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ≤
      4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
  calc
    ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ≤
        ∑ i : Fin 4,
          ‖(gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) •
            gammaSewnCriticalPhysicalPluckerBasis
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)‖ := by
      exact norm_sum_le _ _
    _ = ∑ i : Fin 4,
        |gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        norm_gammaSewnCriticalPhysicalPluckerBasis, mul_one]
    _ ≤ ∑ _i : Fin 4, Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
      exact Finset.sum_le_sum fun i _ =>
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_sqrtBound z s i
    _ = 4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by simp

def gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
    (idx : (ℕ × ℕ) × Fin 6) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
      gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ
      (gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2)
      (gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2)

theorem gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_hasRankLE
    (idx : (ℕ × ℕ) × Fin 6) :
    HasRankLE (gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx) 1 := by
  apply hasRankLE_smul
  simpa [gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm] using
    hasRankLE_sum_range_rankOne
      (fun _ : ℕ => gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2)
      (fun _ : ℕ => gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2) 1

theorem gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_isPositive
    (idx : (ℕ × ℕ) × Fin 6) :
    (gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx).IsPositive := by
  apply (InnerProductSpace.isPositive_rankOne_self
    (𝕜 := ℂ) (gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2)).smul_of_nonneg
  exact (RCLike.ofReal_nonneg (K := ℂ)).2 <| mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
      (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2).le

theorem norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
    (idx : (ℕ × ℕ) × Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖ =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2 := by
  rw [gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_mul,
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1),
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2)]
  ring

theorem norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_le
    (idx : (ℕ × ℕ) × Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖ ≤
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          (16 * gammaSewnCriticalPlucker_nodeBound) := by
  have hnorm :=
    norm_gammaSewnCriticalPhysicalPluckerCenteredVector_le idx.1 idx.2
  have hsqrt0 : 0 ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound :=
    Real.sqrt_nonneg _
  have hsq :
      ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2 ≤
        16 * gammaSewnCriticalPlucker_nodeBound := by
    have hnorm0 :=
      norm_nonneg (gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2)
    have hmul := mul_le_mul hnorm hnorm hnorm0
      (mul_nonneg (by norm_num) hsqrt0)
    rw [← pow_two, ← pow_two] at hmul
    nlinarith [Real.sq_sqrt gammaSewnCriticalPlucker_nodeBound_pos.le]
  rw [norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm]
  exact mul_le_mul_of_nonneg_left hsq
    (mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
      (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2).le)

theorem summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm :
    Summable (fun idx : (ℕ × ℕ) × Fin 6 =>
      ‖gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖) := by
  have hmajor :
      Summable (fun idx : (ℕ × ℕ) × Fin 6 =>
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
          gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
            (16 * gammaSewnCriticalPlucker_nodeBound)) := by
    rw [summable_prod_of_nonneg (fun idx =>
      mul_nonneg
        (mul_nonneg
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
          (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2).le)
        (mul_nonneg (by norm_num) gammaSewnCriticalPlucker_nodeBound_pos.le))]
    constructor
    · intro z
      exact Summable.of_finite
    · have hweight :=
        summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right
          (16 * gammaSewnCriticalPlucker_nodeBound)
      exact hweight.congr fun z => by
        rw [tsum_fintype]
        symm
        calc
          (∑ i : Fin 6,
              gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                gammaSewnCriticalAdjacentPrime_PluckerProbability z i *
                  (16 * gammaSewnCriticalPlucker_nodeBound)) =
              gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                (16 * gammaSewnCriticalPlucker_nodeBound) *
                  ∑ i : Fin 6,
                    gammaSewnCriticalAdjacentPrime_PluckerProbability z i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            rw [sum_gammaSewnCriticalAdjacentPrime_PluckerProbability, mul_one]
  exact Summable.of_nonneg_of_le
    (fun idx => norm_nonneg _)
    norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_le hmajor

def gammaSewnCriticalPhysicalPluckerSpectralOperator :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑' idx : (ℕ × ℕ) × Fin 6,
    gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one :
    MemSchattenClass 1 gammaSewnCriticalPhysicalPluckerSpectralOperator :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
    gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_hasRankLE
    summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive :
    gammaSewnCriticalPhysicalPluckerSpectralOperator.IsPositive := by
  apply isPositive_tsum_of_summable
  · exact Summable.of_norm
      summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
  · exact gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_isPositive

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_isCompact :
    IsCompactOperator gammaSewnCriticalPhysicalPluckerSpectralOperator :=
  gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one.isCompactOperator
    (by norm_num)

def gammaSewnCriticalPhysicalPluckerSpectralBlockOperator
    (z : ℕ × ℕ) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑ s : Fin 6, gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm (z, s)

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive
    (z : ℕ × ℕ) :
    (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z).IsPositive := by
  have hposTsum := isPositive_tsum_of_summable
      (fun s : Fin 6 => gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm (z, s))
      Summable.of_finite
      (fun s => gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_isPositive (z, s))
  simpa [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator, tsum_fintype] using hposTsum

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_matrix
    (z : ℕ × ℕ) (i j : Fin 4) :
    inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z
          (gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j))) =
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℝ) := by
  let L : (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ
      (gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalPhysicalPluckerHilbert
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j)))
  change L (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z) = _
  rw [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator, map_sum]
  simp only [gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm, map_smul]
  change
    ∑ s : Fin 6,
      ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℝ) : ℂ) *
        inner ℂ
          (gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
          ((InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalPhysicalPluckerCenteredVector z s)
            (gammaSewnCriticalPhysicalPluckerCenteredVector z s))
              (gammaSewnCriticalPhysicalPluckerBasis
                (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j))) = _
  simp_rw [InnerProductSpace.inner_right_rankOne_apply,
    inner_basis_gammaSewnCriticalPhysicalPluckerCenteredVector,
    inner_gammaSewnCriticalPhysicalPluckerCenteredVector_basis]
  norm_cast
  rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem summable_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm :
    Summable gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm :=
  Summable.of_norm
    summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm

theorem summable_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator :
    Summable gammaSewnCriticalPhysicalPluckerSpectralBlockOperator := by
  have hprod := summable_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm.prod
  exact hprod.congr fun z => by
    rw [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator, tsum_fintype]

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_eq_tsum_blocks :
    gammaSewnCriticalPhysicalPluckerSpectralOperator =
      ∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z := by
  rw [gammaSewnCriticalPhysicalPluckerSpectralOperator,
    summable_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm.tsum_prod]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  rfl

def gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector
    (z : ℕ × ℕ) : GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑ i : Fin 4,
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i : ℂ) •
      gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)

theorem inner_basis_gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector
    (z : ℕ × ℕ) (i : Fin 4) :
    inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
        (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z) =
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i := by
  rw [gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector, inner_sum]
  simp only [inner_smul_right, inner_gammaSewnCriticalPhysicalPluckerBasis]
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z |>.eq_iff]

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_kernelVector
    (z : ℕ × ℕ) :
    gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z
        (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z) = 0 := by
  apply (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive z).apply_eq_zero_of_inner_eq_zero
  rw [gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right]
  simp_rw [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_matrix]
  have hmul :=
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_mulVec_eq_zero z
  apply Finset.sum_eq_zero
  intro i _
  have hrow := congrFun hmul i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
  simp only [Complex.conj_ofReal]
  norm_cast
  have hcol :
      ∑ x : Fin 4,
        gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z x *
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
            gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z x i) = 0 := by
    calc
      _ = gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          ∑ x : Fin 4,
            gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i x *
              gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_symmetric]
        ring
      _ = 0 := by rw [hrow, mul_zero]
  rw [hcol, mul_zero]

theorem inner_basis_gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector_rightBlock
    (z : ℕ × ℕ) (i : Fin 4) :
    inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1, z.2 + 1) i))
        (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z) =
      gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext z i := by
  rcases z with ⟨e, n⟩
  rw [gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector, inner_sum]
  simp_rw [inner_smul_right, inner_gammaSewnCriticalPhysicalPluckerBasis]
  rw [Fin.sum_univ_four]
  fin_cases i <;>
    simp [gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext,
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel] <;> omega

theorem inner_gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector_basis_rightBlock
    (z : ℕ × ℕ) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z)
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel (z.1, z.2 + 1) i)) =
      gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext z i := by
  rw [← inner_conj_symm]
  simp [inner_basis_gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector_rightBlock]

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_apply_coordinate
    (z : ℕ × ℕ) (i : Fin 4)
    (x : GammaSewnCriticalPhysicalPluckerHilbert) :
    inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x) =
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        ∑ j : Fin 4,
          (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℂ) *
            inner ℂ
              (gammaSewnCriticalPhysicalPluckerBasis
                (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j)) x := by
  let L : GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] ℂ :=
    innerSL ℂ
      (gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
  change L (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x) = _
  rw [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator,
    _root_.sum_apply, map_sum]
  simp only [gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm,
    _root_.smul_apply, map_smul]
  change
    ∑ s : Fin 6,
      ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℝ) : ℂ) *
        inner ℂ
          (gammaSewnCriticalPhysicalPluckerBasis
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
          ((InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalPhysicalPluckerCenteredVector z s)
            (gammaSewnCriticalPhysicalPluckerCenteredVector z s)) x) = _
  simp_rw [InnerProductSpace.inner_right_rankOne_apply,
    inner_basis_gammaSewnCriticalPhysicalPluckerCenteredVector]
  simp only [gammaSewnCriticalPhysicalPluckerCenteredVector, sum_inner,
    inner_smul_left, Complex.conj_ofReal]
  push_cast
  calc
    _ = (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        ∑ s : Fin 6,
          (gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℂ) *
            (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) *
              ∑ j : Fin 4,
                (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j : ℂ) *
                  inner ℂ
                    (gammaSewnCriticalPhysicalPluckerBasis
                      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j)) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        ∑ s : Fin 6, ∑ j : Fin 4,
          (gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℂ) *
            (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) *
              (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j : ℂ) *
                inner ℂ
                  (gammaSewnCriticalPhysicalPluckerBasis
                    (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j)) x := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) *
        ∑ j : Fin 4,
          (∑ s : Fin 6,
            (gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℂ) *
              (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) *
                (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j : ℂ)) *
            inner ℂ
              (gammaSewnCriticalPhysicalPluckerBasis
                (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j)) x := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hA :
          (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℂ) =
            ∑ s : Fin 6,
              (gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℂ) *
                (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) *
                  (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j : ℂ) := by
        exact_mod_cast
          gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered z i j
      rw [hA]

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_rightBlock_quadratic_ne_zero
    (z : ℕ × ℕ) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z)
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator (z.1, z.2 + 1)
          (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z)) ≠ 0 := by
  let w : ℕ × ℕ := (z.1, z.2 + 1)
  let x := gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z
  have happly : gammaSewnCriticalPhysicalPluckerSpectralBlockOperator w x ≠ 0 := by
    intro hzero
    have hmul := gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext_mulVec_ne_zero z
    apply hmul
    funext i
    have hcoord := congrArg
      (fun y => inner ℂ
        (gammaSewnCriticalPhysicalPluckerBasis
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel w i)) y) hzero
    rw [gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_apply_coordinate]
      at hcoord
    simp only [inner_zero_right] at hcoord
    dsimp [w, x] at hcoord
    simp_rw [inner_basis_gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector_rightBlock]
      at hcoord
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    have hweight :
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight w : ℂ) ≠ 0 := by
      exact_mod_cast (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos w).ne'
    exact_mod_cast (mul_eq_zero.mp hcoord).resolve_left hweight
  intro hquad
  exact happly
    ((gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive w).apply_eq_zero_of_inner_eq_zero
      hquad)

theorem re_inner_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_rightBlock_pos
    (z : ℕ × ℕ) :
    0 < (inner ℂ (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z)
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator (z.1, z.2 + 1)
          (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z))).re := by
  let w : ℕ × ℕ := (z.1, z.2 + 1)
  let x := gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z
  let q := inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator w x)
  have hpos := gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive w
  have hq0 : q ≠ 0 := by
    exact gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_rightBlock_quadratic_ne_zero z
  have hqnonneg : 0 ≤ q.re := hpos.re_inner_nonneg_right x
  have hqreal : (q.re : ℂ) = q := by
    have hs := hpos.inner_left_eq_inner_right x x
    have hc : star q = q := by
      calc
        star q = inner ℂ (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator w x) x :=
          inner_conj_symm _ _
        _ = q := hs
    exact (Complex.conj_eq_iff_re).mp hc
  have hqre : q.re ≠ 0 := by
    intro hre
    apply hq0
    rw [← hqreal, hre]
    simp
  exact lt_of_le_of_ne hqnonneg (Ne.symm hqre)

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_embeddedKernelVector_ne_zero
    (z : ℕ × ℕ) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator
        (gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z) ≠ 0 := by
  let x := gammaSewnCriticalPhysicalPluckerEmbeddedKernelVector z
  let Lc : (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ x).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalPhysicalPluckerHilbert x)
  let Lr : (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert) →L[ℝ] ℝ :=
    Complex.reCLM.comp (Lc.restrictScalars ℝ)
  let f : (ℕ × ℕ) → ℝ :=
    fun w => Lr (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator w)
  have hsumf : Summable f :=
    summable_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator.mapL Lr
  have hfnonneg (w : ℕ × ℕ) : 0 ≤ f w := by
    simpa [f, Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm] using
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive w).re_inner_nonneg_right x
  have hfpos : 0 < f (z.1, z.2 + 1) := by
    simpa [f, Lr, Lc, x, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm] using
        re_inner_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_rightBlock_pos z
  have htsumpos : 0 < ∑' w, f w :=
    hsumf.tsum_pos hfnonneg (z.1, z.2 + 1) hfpos
  intro hzero
  have hmap := Lr.map_tsum
    summable_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator
  have hglobal :
      (inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x)).re =
        ∑' w, f w := by
    rw [gammaSewnCriticalPhysicalPluckerSpectralOperator_eq_tsum_blocks]
    simpa [f, Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm] using hmap
  rw [hzero, inner_zero_right, Complex.zero_re] at hglobal
  exact (ne_of_gt htsumpos) hglobal.symm

end RHTower.HedenmalmThetaSource
