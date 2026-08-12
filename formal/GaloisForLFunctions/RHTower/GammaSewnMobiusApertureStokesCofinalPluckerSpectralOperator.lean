import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.PositiveOperatorKernel
import GaloisForLFunctions.HTGeometry.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Cofinal physical Plücker spectral operator

Builds the source-forced adjacent-prime completion of the physical Plücker covariance blocks.
The completed operator is an absolutely nuclear sum of positive rank-one centered source vectors,
hence positive, Schatten-one, and compact.  Its exact matrix entries are the normalized physical
rank-three Plücker spectral blocks, not a scalar diagonal transfer.  Every adjacent-prime block
retains its forced nonzero common-mode null vector in the global kernel.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalAdjacentPrime_PluckerBlockWeight (z : ℕ × ℕ) : ℝ :=
  gammaSewnCriticalAdjacentPrime_DenominatorTerm z /
    gammaSewnCriticalAdjacentPrime_CofinalDenominator

theorem gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z := by
  exact div_pos (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z)
    gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos

theorem summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight :
    Summable gammaSewnCriticalAdjacentPrime_PluckerBlockWeight := by
  unfold gammaSewnCriticalAdjacentPrime_PluckerBlockWeight
  exact summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.div_const _

theorem tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight :
    ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z = 1 := by
  unfold gammaSewnCriticalAdjacentPrime_PluckerBlockWeight
  rw [tsum_div_const]
  change gammaSewnCriticalAdjacentPrime_CofinalDenominator /
      gammaSewnCriticalAdjacentPrime_CofinalDenominator = 1
  exact div_self gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos.ne'

private theorem fourRateSelectedSum_coordinateDelta_mem
    (i : Fin 4) (s : Fin 6) :
    RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s ∈
      Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> fin_cases s <;>
    simp [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
      RHTower.fourRatePairRight, fourRateCoordinateDelta]

private theorem fourRatePluckerCovariance_coordinateDelta_abs_le_one
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (hsum : ∑ s, weight s = 1) (i j : Fin 4) :
    |fourRatePluckerCovariance weight
        (fourRateCoordinateDelta i) (fourRateCoordinateDelta j)| ≤ 1 := by
  let xi : Fin 6 → ℝ :=
    fun s => RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s
  let xj : Fin 6 → ℝ :=
    fun s => RHTower.fourRateSelectedSum (fourRateCoordinateDelta j) s
  have hxi (s : Fin 6) : xi s ∈ Set.Icc (0 : ℝ) 1 :=
    fourRateSelectedSum_coordinateDelta_mem i s
  have hxj (s : Fin 6) : xj s ∈ Set.Icc (0 : ℝ) 1 :=
    fourRateSelectedSum_coordinateDelta_mem j s
  have hmi : (∑ s, weight s * xi s) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (hweight s) (hxi s).1
    · calc
        ∑ s, weight s * xi s ≤ ∑ s, weight s * 1 := by
          exact Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (hxi s).2 (hweight s)
        _ = 1 := by simpa using hsum
  have hmj : (∑ s, weight s * xj s) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (hweight s) (hxj s).1
    · calc
        ∑ s, weight s * xj s ≤ ∑ s, weight s * 1 := by
          exact Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (hxj s).2 (hweight s)
        _ = 1 := by simpa using hsum
  have hmij : (∑ s, weight s * xi s * xj s) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg fun s _ =>
        mul_nonneg (mul_nonneg (hweight s) (hxi s).1) (hxj s).1
    · calc
        ∑ s, weight s * xi s * xj s ≤ ∑ s, weight s * 1 := by
          apply Finset.sum_le_sum
          intro s _
          have hxixj : xi s * xj s ≤ 1 :=
            (mul_le_mul (hxi s).2 (hxj s).2 (hxj s).1 (by norm_num)).trans_eq
              (mul_one 1)
          nlinarith [hweight s]
        _ = 1 := by simpa using hsum
  have hprod0 : 0 ≤ (∑ s, weight s * xi s) * (∑ s, weight s * xj s) :=
    mul_nonneg hmi.1 hmj.1
  have hprod1 : (∑ s, weight s * xi s) * (∑ s, weight s * xj s) ≤ 1 := by
    exact (mul_le_of_le_one_right hmi.1 hmj.2).trans hmi.2
  unfold fourRatePluckerCovariance
  change |(∑ s, weight s * xi s * xj s) -
      (∑ s, weight s * xi s) * (∑ s, weight s * xj s)| ≤ 1
  rw [abs_le]
  constructor <;> linarith [hmij.1, hmij.2]

private theorem fourRatePluckerCovariance_eq_centered
    (weight : Fin 6 → ℝ) (hsum : ∑ s, weight s = 1)
    (x y : Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x y =
      ∑ s, weight s *
        (RHTower.fourRateSelectedSum x s -
          ∑ t, weight t * RHTower.fourRateSelectedSum x t) *
        (RHTower.fourRateSelectedSum y s -
          ∑ t, weight t * RHTower.fourRateSelectedSum y t) := by
  let mx := ∑ t, weight t * RHTower.fourRateSelectedSum x t
  let my := ∑ t, weight t * RHTower.fourRateSelectedSum y t
  calc
    fourRatePluckerCovariance weight x y =
        (∑ s, weight s * RHTower.fourRateSelectedSum x s *
          RHTower.fourRateSelectedSum y s) - mx * my := by
      rfl
    _ = (∑ s, weight s * RHTower.fourRateSelectedSum x s *
          RHTower.fourRateSelectedSum y s) -
        mx * (∑ s, weight s * RHTower.fourRateSelectedSum y s) -
        my * (∑ s, weight s * RHTower.fourRateSelectedSum x s) +
        mx * my * (∑ s, weight s) := by
      rw [hsum]
      dsimp [mx, my]
      ring
    _ = ∑ s,
        (weight s * RHTower.fourRateSelectedSum x s *
            RHTower.fourRateSelectedSum y s -
          mx * (weight s * RHTower.fourRateSelectedSum y s) -
          my * (weight s * RHTower.fourRateSelectedSum x s) +
          mx * my * weight s) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
    _ = ∑ s, weight s *
        (RHTower.fourRateSelectedSum x s - mx) *
        (RHTower.fourRateSelectedSum y s - my) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := rfl

theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_abs_le_one
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (i j : Fin 4) :
    |gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q i j| ≤ 1 := by
  apply fourRatePluckerCovariance_coordinateDelta_abs_le_one
  · intro s
    exact (gammaSewnCriticalPrimeDepthPacket_probability_pos hpq s).le
  · exact sum_gammaSewnCriticalPrimeDepthPacket_probability hpq

def gammaSewnCriticalPlucker_nodeBound : ℝ :=
  ((Real.log 2)⁻¹) ^ 2

theorem gammaSewnCriticalPlucker_nodeBound_pos :
    0 < gammaSewnCriticalPlucker_nodeBound := by
  unfold gammaSewnCriticalPlucker_nodeBound
  exact sq_pos_of_pos (inv_pos.mpr (Real.log_pos (by norm_num)))

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_abs_le_nodeBound
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (i j : Fin 4) :
    |gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q i j| ≤
      gammaSewnCriticalPlucker_nodeBound := by
  let ni := gammaSewnCriticalPrimeDepthPacket_node e p q i
  let nj := gammaSewnCriticalPrimeDepthPacket_node e p q j
  let B := gammaSewnCriticalPlucker_nodeBound
  have hni0 : 0 ≤ ni := (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i).le
  have hnj0 : 0 ≤ nj := (gammaSewnCriticalPrimeDepthPacket_node_pos e p q j).le
  have hniB : ni ≤ B := by
    exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (by norm_num) (by norm_num) _
  have hnjB : nj ≤ B := by
    exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (by norm_num) (by norm_num) _
  have hsqrti : Real.sqrt ni ≤ Real.sqrt B := Real.sqrt_le_sqrt hniB
  have hsqrtj : Real.sqrt nj ≤ Real.sqrt B := Real.sqrt_le_sqrt hnjB
  have hprod : Real.sqrt ni * Real.sqrt nj ≤ B := by
    calc
      Real.sqrt ni * Real.sqrt nj ≤ Real.sqrt B * Real.sqrt B :=
        mul_le_mul hsqrti hsqrtj (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt gammaSewnCriticalPlucker_nodeBound_pos.le
  rw [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_apply,
    abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt ni *
          |gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q i j| *
        Real.sqrt nj ≤
      Real.sqrt ni * 1 * Real.sqrt nj := by
        gcongr
        exact gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_abs_le_one hpq i j
    _ = Real.sqrt ni * Real.sqrt nj := by ring
    _ ≤ B := hprod

def gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock
    (z : ℕ × ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2)

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_abs_le_nodeBound
    (z : ℕ × ℕ) (i j : Fin 4) :
    |gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j| ≤
      gammaSewnCriticalPlucker_nodeBound := by
  exact gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_abs_le_nodeBound
    (gammaSewnCriticalAdjacentPrime_order z.2) i j

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_symmetric
    (z : ℕ × ℕ) (i j : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j =
      gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z j i := by
  have hherm :=
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef
      (e := z.1)
      (p := gammaSewnCriticalAdjacentPrime_lower z.2)
      (q := gammaSewnCriticalAdjacentPrime_upper z.2)
      (gammaSewnCriticalAdjacentPrime_order z.2)).1.apply i j
  simpa [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock] using hherm.symm

def gammaSewnCriticalAdjacentPrime_PluckerProbability
    (z : ℕ × ℕ) (s : Fin 6) : ℝ :=
  gammaSewnOrderedPrimeDepthPlucker_probability
    gammaSewnCriticalFinitePacket_aperture z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2) s

theorem gammaSewnCriticalAdjacentPrime_PluckerProbability_pos
    (z : ℕ × ℕ) (s : Fin 6) :
    0 < gammaSewnCriticalAdjacentPrime_PluckerProbability z s := by
  exact gammaSewnCriticalPrimeDepthPacket_probability_pos
    (gammaSewnCriticalAdjacentPrime_order z.2) s

theorem sum_gammaSewnCriticalAdjacentPrime_PluckerProbability
    (z : ℕ × ℕ) :
    ∑ s, gammaSewnCriticalAdjacentPrime_PluckerProbability z s = 1 := by
  exact sum_gammaSewnCriticalPrimeDepthPacket_probability
    (gammaSewnCriticalAdjacentPrime_order z.2)

def gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean
    (z : ℕ × ℕ) (i : Fin 4) : ℝ :=
  ∑ s, gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
    RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s

theorem gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun s _ =>
      mul_nonneg
        (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z s).le
        (fourRateSelectedSum_coordinateDelta_mem i s).1
  · calc
      ∑ s, gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s ≤
        ∑ s, gammaSewnCriticalAdjacentPrime_PluckerProbability z s * 1 := by
          exact Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left
              (fourRateSelectedSum_coordinateDelta_mem i s).2
              (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z s).le
      _ = 1 := by
        simpa using sum_gammaSewnCriticalAdjacentPrime_PluckerProbability z

def gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) : ℝ :=
  Real.sqrt
      (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
    (RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s -
      gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered
    (z : ℕ × ℕ) (i j : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j =
      ∑ s, gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i *
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j := by
  let p := gammaSewnCriticalAdjacentPrime_lower z.2
  let q := gammaSewnCriticalAdjacentPrime_upper z.2
  let probability := gammaSewnCriticalAdjacentPrime_PluckerProbability z
  have hsum : ∑ s, probability s = 1 :=
    sum_gammaSewnCriticalAdjacentPrime_PluckerProbability z
  rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_apply]
  change
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1 p q i) *
        fourRatePluckerCovariance probability
          (fourRateCoordinateDelta i) (fourRateCoordinateDelta j) *
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1 p q j) = _
  rw [fourRatePluckerCovariance_eq_centered probability hsum]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp only [gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature,
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean, probability, p, q]
  ring

theorem gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_sqrtBound
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    |gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i| ≤
      Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
  let node := gammaSewnCriticalPrimeDepthPacket_node z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2) i
  have hnode : node ≤ gammaSewnCriticalPlucker_nodeBound := by
    exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (by norm_num) (by norm_num) _
  have hsqrt :
      Real.sqrt node ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound :=
    Real.sqrt_le_sqrt hnode
  have hselected := fourRateSelectedSum_coordinateDelta_mem i s
  have hmean :=
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i
  have hdiff :
      |RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s -
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hselected.1, hselected.2, hmean.1, hmean.2]
  unfold gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt node *
        |RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s -
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i| ≤
      Real.sqrt node * 1 :=
        mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)
    _ = Real.sqrt node := mul_one _
    _ ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound := hsqrt

abbrev GammaSewnCriticalCofinalPluckerIndex := (ℕ × ℕ) × Fin 4

abbrev GammaSewnCriticalCofinalPluckerHilbert :=
  lp (fun _ : GammaSewnCriticalCofinalPluckerIndex => ℂ) 2

def gammaSewnCriticalCofinalPluckerBasis
    (z : ℕ × ℕ) (i : Fin 4) : GammaSewnCriticalCofinalPluckerHilbert :=
  lp.single 2 (z, i) 1

def gammaSewnCriticalCofinalPluckerCenteredVector
    (z : ℕ × ℕ) (s : Fin 6) :
    GammaSewnCriticalCofinalPluckerHilbert :=
  ∑ i : Fin 4,
    (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) •
      gammaSewnCriticalCofinalPluckerBasis z i

theorem norm_gammaSewnCriticalCofinalPluckerBasis
    (z : ℕ × ℕ) (i : Fin 4) :
    ‖gammaSewnCriticalCofinalPluckerBasis z i‖ = 1 := by
  unfold gammaSewnCriticalCofinalPluckerBasis
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

theorem inner_gammaSewnCriticalCofinalPluckerBasis
    (z w : ℕ × ℕ) (i j : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerBasis w j) =
      if (z, i) = (w, j) then 1 else 0 := by
  by_cases h : (z, i) = (w, j)
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    simp [gammaSewnCriticalCofinalPluckerBasis]
  · simp [gammaSewnCriticalCofinalPluckerBasis, lp.inner_single_left, h]

theorem inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerCenteredVector z s) =
      gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i := by
  rw [gammaSewnCriticalCofinalPluckerCenteredVector, inner_sum]
  simp only [inner_smul_right,
    inner_gammaSewnCriticalCofinalPluckerBasis]
  simp

theorem inner_gammaSewnCriticalCofinalPluckerCenteredVector_basis
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerCenteredVector z s)
        (gammaSewnCriticalCofinalPluckerBasis z i) =
      gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i := by
  rw [← inner_conj_symm]
  simp [inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector]

theorem inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector_general
    (z w : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerCenteredVector w s) =
      if z = w then
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature w s i
      else 0 := by
  by_cases h : z = w
  · subst w
    simp [inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector]
  · rw [gammaSewnCriticalCofinalPluckerCenteredVector, inner_sum]
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    rw [inner_smul_right,
      inner_gammaSewnCriticalCofinalPluckerBasis]
    simp [Prod.ext_iff, h]

theorem inner_gammaSewnCriticalCofinalPluckerCenteredVector_basis_general
    (z w : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerCenteredVector w s)
        (gammaSewnCriticalCofinalPluckerBasis z i) =
      if z = w then
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature w s i
      else 0 := by
  rw [← inner_conj_symm]
  by_cases h : z = w
  · simp [h,
      inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector_general]
  · simp [h,
      inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector_general]

theorem norm_gammaSewnCriticalCofinalPluckerCenteredVector_le
    (z : ℕ × ℕ) (s : Fin 6) :
    ‖gammaSewnCriticalCofinalPluckerCenteredVector z s‖ ≤
      4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
  calc
    ‖gammaSewnCriticalCofinalPluckerCenteredVector z s‖ ≤
        ∑ i : Fin 4,
          ‖(gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ) •
            gammaSewnCriticalCofinalPluckerBasis z i‖ := by
      exact norm_sum_le _ _
    _ = ∑ i : Fin 4,
        |gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        norm_gammaSewnCriticalCofinalPluckerBasis, mul_one]
    _ ≤ ∑ _i : Fin 4,
        Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
      exact Finset.sum_le_sum fun i _ =>
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_sqrtBound
          z s i
    _ = 4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by simp

def gammaSewnCriticalCofinalPluckerPositiveRankOneTerm
    (idx : (ℕ × ℕ) × Fin 6) :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
      gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ
      (gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2)
      (gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2)

theorem gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_hasRankLE
    (idx : (ℕ × ℕ) × Fin 6) :
    HasRankLE (gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx) 1 := by
  apply hasRankLE_smul
  simpa [gammaSewnCriticalCofinalPluckerPositiveRankOneTerm] using
    hasRankLE_sum_range_rankOne
      (fun _ : ℕ => gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2)
      (fun _ : ℕ => gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2) 1

theorem gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_isPositive
    (idx : (ℕ × ℕ) × Fin 6) :
    (gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx).IsPositive := by
  apply (InnerProductSpace.isPositive_rankOne_self
    (𝕜 := ℂ) (gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2)).smul_of_nonneg
  exact (RCLike.ofReal_nonneg (K := ℂ)).2 <| mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
      (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2).le

theorem norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm
    (idx : (ℕ × ℕ) × Fin 6) :
    ‖gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx‖ =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          ‖gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2‖ ^ 2 := by
  rw [gammaSewnCriticalCofinalPluckerPositiveRankOneTerm, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_mul,
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1),
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2)]
  ring

theorem norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_le
    (idx : (ℕ × ℕ) × Fin 6) :
    ‖gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx‖ ≤
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          (16 * gammaSewnCriticalPlucker_nodeBound) := by
  have hnorm :=
    norm_gammaSewnCriticalCofinalPluckerCenteredVector_le idx.1 idx.2
  have hsqrt0 : 0 ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound :=
    Real.sqrt_nonneg _
  have hsq :
      ‖gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2‖ ^ 2 ≤
        16 * gammaSewnCriticalPlucker_nodeBound := by
    have hnorm0 :=
      norm_nonneg (gammaSewnCriticalCofinalPluckerCenteredVector idx.1 idx.2)
    have hmul := mul_le_mul hnorm hnorm hnorm0
      (mul_nonneg (by norm_num) hsqrt0)
    rw [← pow_two, ← pow_two] at hmul
    nlinarith [Real.sq_sqrt gammaSewnCriticalPlucker_nodeBound_pos.le]
  rw [norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm]
  exact mul_le_mul_of_nonneg_left hsq
    (mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
      (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos idx.1 idx.2).le)

theorem summable_norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm :
    Summable (fun idx : (ℕ × ℕ) × Fin 6 =>
      ‖gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx‖) := by
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
    norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_le hmajor

def gammaSewnCriticalCofinalPluckerPositiveSpectralOperator :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ∑' idx : (ℕ × ℕ) × Fin 6,
    gammaSewnCriticalCofinalPluckerPositiveRankOneTerm idx

def gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator
    (z : ℕ × ℕ) :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ∑ s : Fin 6, gammaSewnCriticalCofinalPluckerPositiveRankOneTerm (z, s)

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator_matrix
    (z : ℕ × ℕ) (i j : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator z
          (gammaSewnCriticalCofinalPluckerBasis z j)) =
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℝ) := by
  let L : (GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (gammaSewnCriticalCofinalPluckerBasis z i)).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalCofinalPluckerHilbert
        (gammaSewnCriticalCofinalPluckerBasis z j))
  change L (gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator z) = _
  rw [gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator, map_sum]
  simp only [gammaSewnCriticalCofinalPluckerPositiveRankOneTerm, map_smul]
  change
    ∑ s : Fin 6,
      ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerProbability z s : ℝ) : ℂ) *
        inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
          ((InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalCofinalPluckerCenteredVector z s)
            (gammaSewnCriticalCofinalPluckerCenteredVector z s))
              (gammaSewnCriticalCofinalPluckerBasis z j)) = _
  simp_rw [InnerProductSpace.inner_right_rankOne_apply,
    inner_basis_gammaSewnCriticalCofinalPluckerCenteredVector,
    inner_gammaSewnCriticalCofinalPluckerCenteredVector_basis]
  norm_cast
  rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator_other_matrix
    {z w : ℕ × ℕ} (hzw : z ≠ w) (i j : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator w
          (gammaSewnCriticalCofinalPluckerBasis z j)) = 0 := by
  let L : (GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (gammaSewnCriticalCofinalPluckerBasis z i)).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalCofinalPluckerHilbert
        (gammaSewnCriticalCofinalPluckerBasis z j))
  change L (gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator w) = 0
  rw [gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator, map_sum]
  simp only [gammaSewnCriticalCofinalPluckerPositiveRankOneTerm, map_smul]
  change
    ∑ s : Fin 6,
      ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight w *
        gammaSewnCriticalAdjacentPrime_PluckerProbability w s : ℝ) : ℂ) *
        inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
          ((InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalCofinalPluckerCenteredVector w s)
            (gammaSewnCriticalCofinalPluckerCenteredVector w s))
              (gammaSewnCriticalCofinalPluckerBasis z j)) = 0
  simp [inner_gammaSewnCriticalCofinalPluckerCenteredVector_basis_general, hzw]

theorem summable_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm :
    Summable gammaSewnCriticalCofinalPluckerPositiveRankOneTerm :=
  Summable.of_norm
    summable_norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm

theorem summable_gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator :
    Summable gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator := by
  have hprod :=
    summable_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm.prod
  exact hprod.congr fun z => by
    rw [gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator,
      tsum_fintype]

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_eq_tsum_blocks :
    gammaSewnCriticalCofinalPluckerPositiveSpectralOperator =
      ∑' z : ℕ × ℕ,
        gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator z := by
  rw [gammaSewnCriticalCofinalPluckerPositiveSpectralOperator,
    summable_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm.tsum_prod]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  rfl

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_matrix
    (z : ℕ × ℕ) (i j : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerPositiveSpectralOperator
          (gammaSewnCriticalCofinalPluckerBasis z j)) =
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℝ) := by
  let L : (GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (gammaSewnCriticalCofinalPluckerBasis z i)).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalCofinalPluckerHilbert
        (gammaSewnCriticalCofinalPluckerBasis z j))
  rw [gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_eq_tsum_blocks]
  have hmap := L.map_tsum
    summable_gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator
  rw [show inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
      ((∑' w, gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator w)
        (gammaSewnCriticalCofinalPluckerBasis z j)) =
      ∑' w, inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator w
          (gammaSewnCriticalCofinalPluckerBasis z j)) by
    simpa [L] using hmap]
  rw [tsum_eq_single z]
  · exact gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator_matrix
      z i j
  · intro w hwz
    exact gammaSewnCriticalCofinalPluckerPositiveSpectralBlockOperator_other_matrix
      hwz.symm i j

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_memSchattenClass_one :
    MemSchattenClass 1 gammaSewnCriticalCofinalPluckerPositiveSpectralOperator :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    gammaSewnCriticalCofinalPluckerPositiveRankOneTerm
    gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_hasRankLE
    summable_norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm

theorem isPositive_tsum_of_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : ι → H →L[ℂ] H)
    (hsum : Summable T) (hpos : ∀ i, (T i).IsPositive) :
    (∑' i, T i).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    change star (∑' i, T i) = ∑' i, T i
    rw [tsum_star]
    apply tsum_congr
    intro i
    exact (hpos i).isSelfAdjoint
  · intro x
    let Lc : (H →L[ℂ] H) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)
    let Lr : (H →L[ℂ] H) →L[ℝ] ℝ :=
      Complex.reCLM.comp (Lc.restrictScalars ℝ)
    have hmap := Lr.map_tsum hsum
    have hnonneg : 0 ≤ ∑' i, Lr (T i) :=
      tsum_nonneg fun i => by
        simpa [Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
          inner_re_symm] using (hpos i).re_inner_nonneg_right x
    rw [← show Lr (∑' i, T i) =
        (∑' i, T i).reApplyInnerSelf x by
      simp [Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
        inner_re_symm]]
    rw [hmap]
    exact hnonneg

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_isPositive :
    gammaSewnCriticalCofinalPluckerPositiveSpectralOperator.IsPositive := by
  apply isPositive_tsum_of_summable
  · exact Summable.of_norm
      summable_norm_gammaSewnCriticalCofinalPluckerPositiveRankOneTerm
  · exact gammaSewnCriticalCofinalPluckerPositiveRankOneTerm_isPositive

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_isCompact :
    IsCompactOperator gammaSewnCriticalCofinalPluckerPositiveSpectralOperator :=
  gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_memSchattenClass_one.isCompactOperator
    (by norm_num)

def gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector
    (z : ℕ × ℕ) : Fin 4 → ℝ :=
  gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2)

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_mulVec_eq_zero
    (z : ℕ × ℕ) :
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z).mulVec
        (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z) = 0 := by
  exact gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_mulVec_eq_zero
    (gammaSewnCriticalAdjacentPrime_order z.2)

def gammaSewnCriticalCofinalPluckerKernelVector
    (z : ℕ × ℕ) : GammaSewnCriticalCofinalPluckerHilbert :=
  ∑ i : Fin 4,
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i : ℂ) •
      gammaSewnCriticalCofinalPluckerBasis z i

theorem inner_basis_gammaSewnCriticalCofinalPluckerKernelVector
    (z : ℕ × ℕ) (i : Fin 4) :
    inner ℂ (gammaSewnCriticalCofinalPluckerBasis z i)
        (gammaSewnCriticalCofinalPluckerKernelVector z) =
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i := by
  rw [gammaSewnCriticalCofinalPluckerKernelVector, inner_sum]
  simp only [inner_smul_right,
    inner_gammaSewnCriticalCofinalPluckerBasis]
  simp

theorem gammaSewnCriticalCofinalPluckerKernelVector_ne_zero
    (z : ℕ × ℕ) :
    gammaSewnCriticalCofinalPluckerKernelVector z ≠ 0 := by
  intro hzero
  have hinner := congrArg
    (fun x => inner ℂ (gammaSewnCriticalCofinalPluckerBasis z 0) x) hzero
  rw [inner_basis_gammaSewnCriticalCofinalPluckerKernelVector] at hinner
  have hsqrt : 0 < Real.sqrt
      (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) 0) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  simp [gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
    hsqrt.ne'] at hinner

theorem gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_kernelVector
    (z : ℕ × ℕ) :
    gammaSewnCriticalCofinalPluckerPositiveSpectralOperator
        (gammaSewnCriticalCofinalPluckerKernelVector z) = 0 := by
  apply
    gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_isPositive.apply_eq_zero_of_inner_eq_zero
  rw [gammaSewnCriticalCofinalPluckerKernelVector]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right]
  simp_rw [gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_matrix]
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

def gammaSewnCriticalCofinalPluckerRankOneTerm
    (idx : (ℕ × ℕ) × Fin 4 × Fin 4) :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock
        idx.1 idx.2.1 idx.2.2 : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ
      (gammaSewnCriticalCofinalPluckerBasis idx.1 idx.2.1)
      (gammaSewnCriticalCofinalPluckerBasis idx.1 idx.2.2)

theorem gammaSewnCriticalCofinalPluckerRankOneTerm_hasRankLE
    (idx : (ℕ × ℕ) × Fin 4 × Fin 4) :
    HasRankLE (gammaSewnCriticalCofinalPluckerRankOneTerm idx) 1 := by
  apply hasRankLE_smul
  simpa [gammaSewnCriticalCofinalPluckerRankOneTerm] using
    hasRankLE_sum_range_rankOne
      (fun _ : ℕ => gammaSewnCriticalCofinalPluckerBasis idx.1 idx.2.1)
      (fun _ : ℕ => gammaSewnCriticalCofinalPluckerBasis idx.1 idx.2.2) 1

theorem norm_gammaSewnCriticalCofinalPluckerRankOneTerm
    (idx : (ℕ × ℕ) × Fin 4 × Fin 4) :
    ‖gammaSewnCriticalCofinalPluckerRankOneTerm idx‖ =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        |gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock
          idx.1 idx.2.1 idx.2.2| := by
  rw [gammaSewnCriticalCofinalPluckerRankOneTerm, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs]
  unfold gammaSewnCriticalCofinalPluckerBasis
  rw [
    lp.norm_single (by norm_num : (0 : ENNReal) < 2),
    lp.norm_single (by norm_num : (0 : ENNReal) < 2),
    norm_one, mul_one]
  rw [abs_mul, abs_of_pos
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1)]
  ring

theorem summable_norm_gammaSewnCriticalCofinalPluckerRankOneTerm :
    Summable (fun idx : (ℕ × ℕ) × Fin 4 × Fin 4 =>
      ‖gammaSewnCriticalCofinalPluckerRankOneTerm idx‖) := by
  have hmajor :
      Summable (fun idx : (ℕ × ℕ) × Fin 4 × Fin 4 =>
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
          gammaSewnCriticalPlucker_nodeBound) := by
    rw [summable_prod_of_nonneg (fun idx =>
      mul_nonneg
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le
        gammaSewnCriticalPlucker_nodeBound_pos.le)]
    constructor
    · intro z
      exact Summable.of_finite
    · simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_assoc] using
        (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right
          (16 * gammaSewnCriticalPlucker_nodeBound)).congr (fun z => by ring)
  refine Summable.of_nonneg_of_le (fun idx => norm_nonneg _) (fun idx => ?_) hmajor
  rw [norm_gammaSewnCriticalCofinalPluckerRankOneTerm]
  exact mul_le_mul_of_nonneg_left
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_abs_le_nodeBound
      idx.1 idx.2.1 idx.2.2)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos idx.1).le

theorem gammaSewnCriticalCofinalPluckerRankOneTerm_star
    (z : ℕ × ℕ) (i j : Fin 4) :
    star (gammaSewnCriticalCofinalPluckerRankOneTerm (z, i, j)) =
      gammaSewnCriticalCofinalPluckerRankOneTerm (z, j, i) := by
  rw [gammaSewnCriticalCofinalPluckerRankOneTerm, star_smul]
  change
    star (((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℝ) : ℂ)) •
        ContinuousLinearMap.adjoint
          (InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalCofinalPluckerBasis z i)
            (gammaSewnCriticalCofinalPluckerBasis z j)) =
      (((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z j i : ℝ) : ℂ)) •
          InnerProductSpace.rankOne ℂ
            (gammaSewnCriticalCofinalPluckerBasis z j)
            (gammaSewnCriticalCofinalPluckerBasis z i)
  rw [InnerProductSpace.adjoint_rankOne,
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_symmetric]
  simp

def gammaSewnCriticalCofinalPluckerSpectralBlockOperator
    (z : ℕ × ℕ) :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ∑ ij : Fin 4 × Fin 4,
    gammaSewnCriticalCofinalPluckerRankOneTerm (z, ij)

theorem gammaSewnCriticalCofinalPluckerSpectralBlockOperator_isSelfAdjoint
    (z : ℕ × ℕ) :
    IsSelfAdjoint (gammaSewnCriticalCofinalPluckerSpectralBlockOperator z) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    gammaSewnCriticalCofinalPluckerSpectralBlockOperator]
  change star (∑ ij : Fin 4 × Fin 4,
    gammaSewnCriticalCofinalPluckerRankOneTerm (z, ij)) = _
  simp only [Fintype.sum_prod_type]
  rw [star_sum]
  simp_rw [star_sum]
  simp_rw [gammaSewnCriticalCofinalPluckerRankOneTerm_star]
  rw [Finset.sum_comm]

def gammaSewnCriticalCofinalPluckerSpectralOperator :
    GammaSewnCriticalCofinalPluckerHilbert →L[ℂ]
      GammaSewnCriticalCofinalPluckerHilbert :=
  ∑' idx : (ℕ × ℕ) × Fin 4 × Fin 4,
    gammaSewnCriticalCofinalPluckerRankOneTerm idx

theorem summable_gammaSewnCriticalCofinalPluckerRankOneTerm :
    Summable gammaSewnCriticalCofinalPluckerRankOneTerm :=
  Summable.of_norm summable_norm_gammaSewnCriticalCofinalPluckerRankOneTerm

theorem summable_gammaSewnCriticalCofinalPluckerSpectralBlockOperator :
    Summable gammaSewnCriticalCofinalPluckerSpectralBlockOperator := by
  have hprod := summable_gammaSewnCriticalCofinalPluckerRankOneTerm.prod
  exact hprod.congr fun z => by
    rw [gammaSewnCriticalCofinalPluckerSpectralBlockOperator, tsum_fintype]

theorem gammaSewnCriticalCofinalPluckerSpectralOperator_eq_tsum_blocks :
    gammaSewnCriticalCofinalPluckerSpectralOperator =
      ∑' z : ℕ × ℕ, gammaSewnCriticalCofinalPluckerSpectralBlockOperator z := by
  rw [gammaSewnCriticalCofinalPluckerSpectralOperator,
    summable_gammaSewnCriticalCofinalPluckerRankOneTerm.tsum_prod]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  rfl

theorem gammaSewnCriticalCofinalPluckerSpectralOperator_isSelfAdjoint :
    IsSelfAdjoint gammaSewnCriticalCofinalPluckerSpectralOperator := by
  rw [gammaSewnCriticalCofinalPluckerSpectralOperator_eq_tsum_blocks,
    ContinuousLinearMap.isSelfAdjoint_iff']
  change star (∑' z : ℕ × ℕ,
    gammaSewnCriticalCofinalPluckerSpectralBlockOperator z) = _
  rw [tsum_star]
  apply tsum_congr
  intro z
  exact gammaSewnCriticalCofinalPluckerSpectralBlockOperator_isSelfAdjoint z

theorem gammaSewnCriticalCofinalPluckerSpectralOperator_memSchattenClass_one :
    MemSchattenClass 1 gammaSewnCriticalCofinalPluckerSpectralOperator :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    gammaSewnCriticalCofinalPluckerRankOneTerm
    gammaSewnCriticalCofinalPluckerRankOneTerm_hasRankLE
    summable_norm_gammaSewnCriticalCofinalPluckerRankOneTerm

theorem gammaSewnCriticalCofinalPluckerSpectralOperator_isCompact :
    IsCompactOperator gammaSewnCriticalCofinalPluckerSpectralOperator :=
  gammaSewnCriticalCofinalPluckerSpectralOperator_memSchattenClass_one.isCompactOperator
    (by norm_num)

end RHTower.HedenmalmThetaSource
