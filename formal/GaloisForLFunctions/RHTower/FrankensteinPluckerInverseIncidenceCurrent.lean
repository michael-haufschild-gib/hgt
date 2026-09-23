import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix
import GaloisForLFunctions.RHTower.GammaValuationSchurAdjacentPrimePrimitiveRecovery

/-!
# Frankenstein Pluecker inverse-incidence current

P-G91 supplies a positive four-label covariance, P-G84 supplies summable literal physical packet
mass, and P-G86 proves adjacent incidence recovers complete prime covariance only after cumulative
integration. This module combines them in the coefficient-faithful order: factor each physical
covariance, attach signed adjacent-prime incidence, sum packets in one common dispersion fiber,
then square.

The pair-dispersion feature is an explicit rectangular square root of P-G91 covariance. Both
retained depth orientations calibrate exactly to P-G86's all-prime layer sums before physical
weighting. The raw P-G84 denominator and first Deninger Koethe seminorm make the resulting
sum-before-square current absolutely convergent and its total energy finite and nonnegative.

This constructs a nonlocal source operator. It does not identify that operator with completed
prime--archimedean moments, force its energy to vanish, or prove RH.
-/

open Real Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.HedenmalmThetaSource

def fourRateSelectedSumC (x : Fin 4 → ℂ) (s : Fin 6) : ℂ :=
  x (RHTower.fourRatePairLeft s) + x (RHTower.fourRatePairRight s)

def fourRatePluckerDispersionFeature
    (weight : Fin 6 → ℝ) (x : Fin 4 → ℂ) (s t : Fin 6) : ℂ :=
  (Real.sqrt (weight s * weight t / 2) : ℂ) *
    (fourRateSelectedSumC x s - fourRateSelectedSumC x t)

theorem fourRatePluckerDispersionFeature_ofReal_norm_sq
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (x : Fin 4 → ℝ) (s t : Fin 6) :
    ‖fourRatePluckerDispersionFeature weight (fun i => (x i : ℂ)) s t‖ ^ (2 : ℕ) =
      weight s * weight t / 2 *
        (RHTower.fourRateSelectedSum x s -
          RHTower.fourRateSelectedSum x t) ^ (2 : ℕ) := by
  have hprod : 0 ≤ weight s * weight t / 2 :=
    div_nonneg (mul_nonneg (hweight s) (hweight t)) (by norm_num)
  have hs : fourRateSelectedSumC (fun i => (x i : ℂ)) s =
      (RHTower.fourRateSelectedSum x s : ℂ) := by
    simp [fourRateSelectedSumC, RHTower.fourRateSelectedSum]
  have ht : fourRateSelectedSumC (fun i => (x i : ℂ)) t =
      (RHTower.fourRateSelectedSum x t : ℂ) := by
    simp [fourRateSelectedSumC, RHTower.fourRateSelectedSum]
  rw [fourRatePluckerDispersionFeature, hs, ht, ← Complex.ofReal_sub,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hprod, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem sum_fourRatePluckerDispersionFeature_ofReal_norm_sq_eq_covariance
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (hsum : ∑ s, weight s = 1) (x : Fin 4 → ℝ) :
    (∑ s, ∑ t,
      ‖fourRatePluckerDispersionFeature weight (fun i => (x i : ℂ)) s t‖ ^ (2 : ℕ)) =
      fourRatePluckerCovariance weight x x := by
  simp_rw [fourRatePluckerDispersionFeature_ofReal_norm_sq weight hweight x]
  have hpair := HTGeometry.normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    weight (RHTower.fourRateSelectedSum x) hsum
  rw [fourRatePluckerCovariance_self_eq_variance]
  unfold RHTower.normalizedFiniteVariance
  rw [show (∑ s, ∑ t,
      weight s * weight t / 2 *
        (RHTower.fourRateSelectedSum x s - RHTower.fourRateSelectedSum x t) ^ (2 : ℕ)) =
      (1 / 2 : ℝ) * (∑ s, ∑ t,
        weight s * weight t *
          (RHTower.fourRateSelectedSum x s - RHTower.fourRateSelectedSum x t) ^ (2 : ℕ)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring,
    hpair]
  ring

end RHTower.HedenmalmThetaSource

namespace RHTower.HedenmalmThetaSource

theorem fourRatePluckerDispersionFeature_norm_le
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (hsum : ∑ s, weight s = 1) (x : Fin 4 → ℂ) (s t : Fin 6) :
    ‖fourRatePluckerDispersionFeature weight x s t‖ ≤
      2 * ∑ i, ‖x i‖ := by
  have hweight_le_one (u : Fin 6) : weight u ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun v _ => hweight v) (Finset.mem_univ u)
  have hprod : 0 ≤ weight s * weight t / 2 :=
    div_nonneg (mul_nonneg (hweight s) (hweight t)) (by norm_num)
  have hprod_le : weight s * weight t / 2 ≤ 1 := by
    nlinarith [hweight s, hweight t, hweight_le_one s, hweight_le_one t,
      mul_nonneg (sub_nonneg.mpr (hweight_le_one s))
        (sub_nonneg.mpr (hweight_le_one t))]
  have hsqrt : Real.sqrt (weight s * weight t / 2) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using hprod_le⟩
  have hcoord (i : Fin 4) : ‖x i‖ ≤ ∑ j, ‖x j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
  have hselected (u : Fin 6) :
      ‖fourRateSelectedSumC x u‖ ≤ ∑ i, ‖x i‖ := by
    fin_cases u <;>
      simp [fourRateSelectedSumC, RHTower.fourRatePairLeft,
        RHTower.fourRatePairRight, Fin.sum_univ_succ] <;>
      first | exact norm_add_le _ _ |
        linarith [norm_add_le (x 0) (x 1), norm_add_le (x 0) (x 2),
          norm_add_le (x 0) (x 3), norm_add_le (x 1) (x 2),
          norm_add_le (x 1) (x 3), norm_add_le (x 2) (x 3),
          norm_nonneg (x 0), norm_nonneg (x 1), norm_nonneg (x 2), norm_nonneg (x 3)]
  rw [fourRatePluckerDispersionFeature, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (weight s * weight t / 2) *
        ‖fourRateSelectedSumC x s - fourRateSelectedSumC x t‖ ≤
      1 * (‖fourRateSelectedSumC x s‖ + ‖fourRateSelectedSumC x t‖) := by
        apply mul_le_mul hsqrt (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * ∑ i, ‖x i‖ := by
      simpa [two_mul] using add_le_add (hselected s) (hselected t)

end RHTower.HedenmalmThetaSource


namespace RHTower.HedenmalmThetaSource

private theorem frankenstein_indexWeight_le_height (e n k : ℕ) (hnk : n ≤ k) :
    (n + 1 : ℝ) ≤ RHTower.deningerHeight
      (RHTower.gammaSewnMobiusApertureStokesPrimePowerAxis
        (RHTower.nthPrimeSubtype k, e)) := by
  rw [RHTower.deningerHeight_gammaValuationAxis]
  have hindex : (n + 1 : ℝ) ≤ (RHTower.nthPrimeSubtype k : ℝ) := by
    exact_mod_cast (le_trans (by omega : n + 1 ≤ k + 2)
      (RHTower.nthPrimeSubtype_index_add_two_le k))
  have hp1 : (1 : ℝ) ≤ (RHTower.nthPrimeSubtype k : ℝ) := by
    exact_mod_cast (RHTower.nthPrimeSubtype k).2.one_le
  have hpow : (RHTower.nthPrimeSubtype k : ℝ) ^ (1 : ℕ) ≤
      (RHTower.nthPrimeSubtype k : ℝ) ^ (e + 1) :=
    pow_le_pow_right₀ hp1 (by omega)
  exact hindex.trans (by simpa using hpow)

def frankensteinPluckerLowerNextAxis (z : ℕ × ℕ) : RHTower.DeningerPrimeLattice :=
  RHTower.gammaValuationAdjacentLowerAxis (z.1 + 1, z.2)

def frankensteinPluckerUpperNextAxis (z : ℕ × ℕ) : RHTower.DeningerPrimeLattice :=
  RHTower.gammaValuationAdjacentUpperAxis (z.1 + 1, z.2)

theorem frankensteinPluckerLowerNextAxis_injective :
    Function.Injective frankensteinPluckerLowerNextAxis := by
  rintro ⟨e, n⟩ ⟨f, m⟩ h
  have hpair := RHTower.gammaValuationAdjacentLowerAxis_injective h
  have hef : e = f := by
    have := congrArg Prod.fst hpair
    dsimp at this
    omega
  have hnm : n = m := congrArg Prod.snd hpair
  exact Prod.ext hef hnm

theorem frankensteinPluckerUpperNextAxis_injective :
    Function.Injective frankensteinPluckerUpperNextAxis := by
  rintro ⟨e, n⟩ ⟨f, m⟩ h
  have hpair := RHTower.gammaValuationAdjacentUpperAxis_injective h
  have hef : e = f := by
    have := congrArg Prod.fst hpair
    dsimp at this
    omega
  have hnm : n = m := congrArg Prod.snd hpair
  exact Prod.ext hef hnm

private theorem summable_frankenstein_indexWeight_axis
    (a : RHTower.DeningerHeightKothe)
    (axis : ℕ × ℕ → RHTower.DeningerPrimeLattice)
    (haxis : Function.Injective axis)
    (hheight : ∀ z, (z.2 + 1 : ℝ) ≤ RHTower.deningerHeight (axis z)) :
    Summable (fun z : ℕ × ℕ =>
      (z.2 + 1 : ℝ) * ‖((a : RHTower.DeningerPrimeLattice → ℂ) (axis z))‖) := by
  have hbase := (RHTower.deningerHeightSeminorm_summable a 1).comp_injective haxis
  exact Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun z => by
      change (z.2 + 1 : ℝ) * ‖((a : RHTower.DeningerPrimeLattice → ℂ) (axis z))‖ ≤
        RHTower.deningerHeight (axis z) ^ (1 : ℕ) *
          ‖((a : RHTower.DeningerPrimeLattice → ℂ) (axis z))‖
      simpa using mul_le_mul_of_nonneg_right (hheight z) (norm_nonneg _))
    hbase

theorem summable_frankensteinPluckerLowerAxis_indexWeight
    (a : RHTower.DeningerHeightKothe) :
    Summable (fun z : ℕ × ℕ => (z.2 + 1 : ℝ) *
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (RHTower.gammaValuationAdjacentLowerAxis z))‖) := by
  apply summable_frankenstein_indexWeight_axis a
    RHTower.gammaValuationAdjacentLowerAxis
    RHTower.gammaValuationAdjacentLowerAxis_injective
  intro z
  exact frankenstein_indexWeight_le_height z.1 z.2 z.2 le_rfl

theorem summable_frankensteinPluckerUpperAxis_indexWeight
    (a : RHTower.DeningerHeightKothe) :
    Summable (fun z : ℕ × ℕ => (z.2 + 1 : ℝ) *
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (RHTower.gammaValuationAdjacentUpperAxis z))‖) := by
  apply summable_frankenstein_indexWeight_axis a
    RHTower.gammaValuationAdjacentUpperAxis
    RHTower.gammaValuationAdjacentUpperAxis_injective
  intro z
  exact frankenstein_indexWeight_le_height z.1 z.2 (z.2 + 1) (by omega)

theorem summable_frankensteinPluckerLowerNextAxis_indexWeight
    (a : RHTower.DeningerHeightKothe) :
    Summable (fun z : ℕ × ℕ => (z.2 + 1 : ℝ) *
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (frankensteinPluckerLowerNextAxis z))‖) := by
  apply summable_frankenstein_indexWeight_axis a
    frankensteinPluckerLowerNextAxis
    frankensteinPluckerLowerNextAxis_injective
  intro z
  exact frankenstein_indexWeight_le_height (z.1 + 1) z.2 z.2 le_rfl

theorem summable_frankensteinPluckerUpperNextAxis_indexWeight
    (a : RHTower.DeningerHeightKothe) :
    Summable (fun z : ℕ × ℕ => (z.2 + 1 : ℝ) *
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (frankensteinPluckerUpperNextAxis z))‖) := by
  apply summable_frankenstein_indexWeight_axis a
    frankensteinPluckerUpperNextAxis
    frankensteinPluckerUpperNextAxis_injective
  intro z
  exact frankenstein_indexWeight_le_height (z.1 + 1) z.2 (z.2 + 1) (by omega)

end RHTower.HedenmalmThetaSource

namespace RHTower.HedenmalmThetaSource

def frankensteinPluckerSignedPacket
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) : Fin 4 → ℂ :=
  ![
    ((a : RHTower.DeningerPrimeLattice → ℂ)
      (RHTower.gammaValuationAdjacentLowerAxis z)),
    ((a : RHTower.DeningerPrimeLattice → ℂ)
      (frankensteinPluckerLowerNextAxis z)),
    -((a : RHTower.DeningerPrimeLattice → ℂ)
      (RHTower.gammaValuationAdjacentUpperAxis z)),
    -((a : RHTower.DeningerPrimeLattice → ℂ)
      (frankensteinPluckerUpperNextAxis z))]

/-- Reciprocal-gap congruence from P-G92, complexified without changing its literal nodes. -/
def frankensteinPluckerNodeWeight
    (z : ℕ × ℕ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i =>
    (Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i) : ℂ) * x i

/-- Signed inverse-incidence packet after the exact P-G92 reciprocal-gap congruence. -/
def frankensteinPluckerNodeWeightedSignedPacket
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) : Fin 4 → ℂ :=
  frankensteinPluckerNodeWeight z (frankensteinPluckerSignedPacket a z)

def frankensteinPluckerProbability (z : ℕ × ℕ) : Fin 6 → ℝ :=
  gammaSewnOrderedPrimeDepthPlucker_probability
    gammaSewnCriticalFinitePacket_aperture z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2)

def frankensteinPluckerPacketFeature
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) (s t : Fin 6) : ℂ :=
  fourRatePluckerDispersionFeature (frankensteinPluckerProbability z)
    (frankensteinPluckerNodeWeightedSignedPacket a z) s t

def frankensteinPluckerInverseIncidenceTerm
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) (s t : Fin 6) : ℂ :=
  (((z.2 + 1 : ℝ) *
      Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) : ℝ) : ℂ) *
    frankensteinPluckerPacketFeature a z s t

theorem frankensteinPluckerProbability_pos (z : ℕ × ℕ) (s : Fin 6) :
    0 < frankensteinPluckerProbability z s := by
  exact gammaSewnCriticalPrimeDepthPacket_probability_pos
    (gammaSewnCriticalAdjacentPrime_order z.2) s

theorem sum_frankensteinPluckerProbability (z : ℕ × ℕ) :
    ∑ s, frankensteinPluckerProbability z s = 1 := by
  exact sum_gammaSewnCriticalPrimeDepthPacket_probability
    (gammaSewnCriticalAdjacentPrime_order z.2)

/-- Pair-dispersion feature is a rectangular square root of the P-G91 covariance after P-G92's
literal reciprocal-gap congruence. -/
theorem sum_frankensteinPluckerPacketFeature_ofReal_norm_sq_eq_spectralCovariance
    (z : ℕ × ℕ) (x : Fin 4 → ℝ) :
    (∑ s, ∑ t, ‖fourRatePluckerDispersionFeature
      (frankensteinPluckerProbability z)
      (frankensteinPluckerNodeWeight z (fun i => (x i : ℂ))) s t‖ ^ (2 : ℕ)) =
      gammaSewnCriticalPrimeDepthPacket_PluckerCovariance z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2)
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2)).mulVec x)
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2)).mulVec x) := by
  let y := (gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2)).mulVec x
  have hy : frankensteinPluckerNodeWeight z (fun i => (x i : ℂ)) =
      fun i => (y i : ℂ) := by
    funext i
    dsimp [y]
    rw [frankensteinPluckerNodeWeight,
      gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal_mulVec_apply]
    norm_cast
  rw [hy]
  exact sum_fourRatePluckerDispersionFeature_ofReal_norm_sq_eq_covariance
    (frankensteinPluckerProbability z)
    (fun s => (frankensteinPluckerProbability_pos z s).le)
    (sum_frankensteinPluckerProbability z) y

theorem sqrt_gammaSewnCriticalAdjacentPrime_DenominatorTerm_le_cofinal
    (z : ℕ × ℕ) :
    Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) ≤
      Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator := by
  apply Real.sqrt_le_sqrt
  exact summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.le_tsum z
    (fun j _ => (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos j).le)

theorem sqrt_frankensteinPluckerNode_le_logTwoInv
    (z : ℕ × ℕ) (i : Fin 4) :
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i) ≤
      (Real.log 2)⁻¹ := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact (inv_pos.mpr (Real.log_pos (by norm_num))).le
  · unfold gammaSewnCriticalPrimeDepthPacket_node
    exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (by norm_num) (by norm_num) _

theorem sum_norm_frankensteinPluckerNodeWeight_le
    (z : ℕ × ℕ) (x : Fin 4 → ℂ) :
    (∑ i, ‖frankensteinPluckerNodeWeight z x i‖) ≤
      (Real.log 2)⁻¹ * ∑ i, ‖x i‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [frankensteinPluckerNodeWeight, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (sqrt_frankensteinPluckerNode_le_logTwoInv z i) (norm_nonneg _)

private theorem sum_norm_frankensteinPluckerSignedPacket
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) :
    (∑ i, ‖frankensteinPluckerSignedPacket a z i‖) =
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (frankensteinPluckerLowerNextAxis z))‖ +
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
        (frankensteinPluckerUpperNextAxis z))‖ := by
  simp [frankensteinPluckerSignedPacket, Fin.sum_univ_succ]
  ring

theorem norm_frankensteinPluckerInverseIncidenceTerm_le
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) (s t : Fin 6) :
    ‖frankensteinPluckerInverseIncidenceTerm a z s t‖ ≤
      2 * (Real.log 2)⁻¹ *
        Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator *
        ((z.2 + 1 : ℝ) *
          (‖((a : RHTower.DeningerPrimeLattice → ℂ)
              (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
           ‖((a : RHTower.DeningerPrimeLattice → ℂ)
              (frankensteinPluckerLowerNextAxis z))‖ +
           ‖((a : RHTower.DeningerPrimeLattice → ℂ)
              (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
           ‖((a : RHTower.DeningerPrimeLattice → ℂ)
              (frankensteinPluckerUpperNextAxis z))‖)) := by
  have hfeature := fourRatePluckerDispersionFeature_norm_le
    (frankensteinPluckerProbability z)
    (fun u => (frankensteinPluckerProbability_pos z u).le)
    (sum_frankensteinPluckerProbability z)
    (frankensteinPluckerNodeWeightedSignedPacket a z) s t
  have hnode := sum_norm_frankensteinPluckerNodeWeight_le z
    (frankensteinPluckerSignedPacket a z)
  have hfeature' : ‖frankensteinPluckerPacketFeature a z s t‖ ≤
      2 * (Real.log 2)⁻¹ *
        (∑ i, ‖frankensteinPluckerSignedPacket a z i‖) := by
    calc
      ‖frankensteinPluckerPacketFeature a z s t‖ ≤
          2 * ∑ i, ‖frankensteinPluckerNodeWeightedSignedPacket a z i‖ := hfeature
      _ ≤ 2 * ((Real.log 2)⁻¹ *
          ∑ i, ‖frankensteinPluckerSignedPacket a z i‖) := by
        exact mul_le_mul_of_nonneg_left hnode (by norm_num)
      _ = _ := by ring
  rw [sum_norm_frankensteinPluckerSignedPacket] at hfeature'
  rw [frankensteinPluckerInverseIncidenceTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _))]
  have hsqrt := sqrt_gammaSewnCriticalAdjacentPrime_DenominatorTerm_le_cofinal z
  have hn : 0 ≤ (z.2 + 1 : ℝ) := by positivity
  have hsum : 0 ≤
      ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerLowerNextAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerUpperNextAxis z))‖ := by positivity
  calc
    ((z.2 + 1 : ℝ) *
        Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z)) *
        ‖frankensteinPluckerPacketFeature a z s t‖ ≤
      ((z.2 + 1 : ℝ) *
        Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z)) *
        (2 * (Real.log 2)⁻¹ * (‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerLowerNextAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerUpperNextAxis z))‖)) := by
        exact mul_le_mul_of_nonneg_left hfeature'
          (mul_nonneg hn (Real.sqrt_nonneg _))
    _ ≤ ((z.2 + 1 : ℝ) *
        Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator) *
        (2 * (Real.log 2)⁻¹ * (‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerLowerNextAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerUpperNextAxis z))‖)) := by
        gcongr
    _ = _ := by ring

end RHTower.HedenmalmThetaSource

namespace RHTower.HedenmalmThetaSource

def frankensteinPluckerInverseIncidenceMajor
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) : ℝ :=
  2 * (Real.log 2)⁻¹ *
    Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator *
    ((z.2 + 1 : ℝ) *
      (‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerLowerNextAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
       ‖((a : RHTower.DeningerPrimeLattice → ℂ)
          (frankensteinPluckerUpperNextAxis z))‖))

theorem summable_frankensteinPluckerInverseIncidenceMajor
    (a : RHTower.DeningerHeightKothe) :
    Summable (frankensteinPluckerInverseIncidenceMajor a) := by
  have hcore : Summable (fun z : ℕ × ℕ =>
      (z.2 + 1 : ℝ) *
        (‖((a : RHTower.DeningerPrimeLattice → ℂ)
            (RHTower.gammaValuationAdjacentLowerAxis z))‖ +
         ‖((a : RHTower.DeningerPrimeLattice → ℂ)
            (frankensteinPluckerLowerNextAxis z))‖ +
         ‖((a : RHTower.DeningerPrimeLattice → ℂ)
            (RHTower.gammaValuationAdjacentUpperAxis z))‖ +
         ‖((a : RHTower.DeningerPrimeLattice → ℂ)
            (frankensteinPluckerUpperNextAxis z))‖)) := by
    have h := (((summable_frankensteinPluckerLowerAxis_indexWeight a).add
      (summable_frankensteinPluckerLowerNextAxis_indexWeight a)).add
      (summable_frankensteinPluckerUpperAxis_indexWeight a)).add
      (summable_frankensteinPluckerUpperNextAxis_indexWeight a)
    exact h.congr fun z => by ring
  exact hcore.mul_left
    (2 * (Real.log 2)⁻¹ *
      Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator)

theorem summable_frankensteinPluckerInverseIncidenceTerm
    (a : RHTower.DeningerHeightKothe) (s t : Fin 6) :
    Summable (fun z : ℕ × ℕ =>
      frankensteinPluckerInverseIncidenceTerm a z s t) := by
  exact Summable.of_norm_bounded
    (summable_frankensteinPluckerInverseIncidenceMajor a)
    (fun z => by
      exact norm_frankensteinPluckerInverseIncidenceTerm_le a z s t)

/-- Sum-before-square current: inverse incidence is accumulated in the common six-by-six
Pluecker dispersion fiber, so distinct prime packets generate cross terms. -/
def frankensteinPluckerCofinalCurrent
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) : ℂ :=
  ∑' n : ℕ, frankensteinPluckerInverseIncidenceTerm a (e, n) s t

theorem summable_norm_frankensteinPluckerCofinalCurrent
    (a : RHTower.DeningerHeightKothe) (s t : Fin 6) :
    Summable (fun e : ℕ => ‖frankensteinPluckerCofinalCurrent a e s t‖) := by
  have hglobal := (summable_frankensteinPluckerInverseIncidenceTerm a s t).norm
  have hslices : Summable (fun e : ℕ =>
      ∑' n : ℕ, ‖frankensteinPluckerInverseIncidenceTerm a (e, n) s t‖) :=
    hglobal.prod
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun e => by
      apply norm_tsum_le_tsum_norm
      exact hglobal.comp_injective (fun _ _ h => congrArg Prod.snd h))
    hslices

theorem summable_sq_norm_frankensteinPluckerCofinalCurrent
    (a : RHTower.DeningerHeightKothe) (s t : Fin 6) :
    Summable (fun e : ℕ => ‖frankensteinPluckerCofinalCurrent a e s t‖ ^ (2 : ℕ)) := by
  let C : ℝ := ∑' e : ℕ, ‖frankensteinPluckerCofinalCurrent a e s t‖
  have hnorm := summable_norm_frankensteinPluckerCofinalCurrent a s t
  have hC : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  have hle (e : ℕ) : ‖frankensteinPluckerCofinalCurrent a e s t‖ ≤ C := by
    exact hnorm.le_tsum e (fun _ _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun e => ?_)
    (hnorm.mul_left C)
  nlinarith [hle e, hC,
    norm_nonneg (frankensteinPluckerCofinalCurrent a e s t)]

/-- Total finite source energy of the coefficient-faithful nonlocal Pluecker current. -/
def frankensteinPluckerCofinalEnergy
    (a : RHTower.DeningerHeightKothe) : ℝ :=
  ∑' k : (Fin 6 × Fin 6) × ℕ,
    ‖frankensteinPluckerCofinalCurrent a k.2 k.1.1 k.1.2‖ ^ (2 : ℕ)

theorem summable_frankensteinPluckerCofinalEnergy
    (a : RHTower.DeningerHeightKothe) :
    Summable (fun k : (Fin 6 × Fin 6) × ℕ =>
      ‖frankensteinPluckerCofinalCurrent a k.2 k.1.1 k.1.2‖ ^ (2 : ℕ)) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro st
    exact summable_sq_norm_frankensteinPluckerCofinalCurrent a st.1 st.2
  · exact (hasSum_fintype _).summable

theorem frankensteinPluckerCofinalEnergy_nonneg
    (a : RHTower.DeningerHeightKothe) :
    0 ≤ frankensteinPluckerCofinalEnergy a := by
  exact tsum_nonneg fun _ => sq_nonneg _

end RHTower.HedenmalmThetaSource

namespace RHTower.HedenmalmThetaSource

/-- Lower-depth signed orientation is exactly P-G86's adjacent difference. -/
theorem frankensteinPluckerSignedPacket_lowerOrientation
    (a : RHTower.DeningerHeightKothe) (e n : ℕ) :
    frankensteinPluckerSignedPacket a (e, n) 0 +
        frankensteinPluckerSignedPacket a (e, n) 2 =
      RHTower.gammaValuationNthPrimeCoord e a n -
        RHTower.gammaValuationNthPrimeCoord e a (n + 1) := by
  simp [frankensteinPluckerSignedPacket,
    RHTower.gammaValuationNthPrimeCoord,
    RHTower.gammaValuationNthPrimeAxis,
    RHTower.gammaValuationAdjacentLowerAxis,
    RHTower.gammaValuationAdjacentUpperAxis]
  ring

/-- Upper-depth signed orientation is the same inverse-incidence difference at depth `e+1`. -/
theorem frankensteinPluckerSignedPacket_upperOrientation
    (a : RHTower.DeningerHeightKothe) (e n : ℕ) :
    frankensteinPluckerSignedPacket a (e, n) 1 +
        frankensteinPluckerSignedPacket a (e, n) 3 =
      RHTower.gammaValuationNthPrimeCoord (e + 1) a n -
        RHTower.gammaValuationNthPrimeCoord (e + 1) a (n + 1) := by
  simp [frankensteinPluckerSignedPacket,
    frankensteinPluckerLowerNextAxis,
    frankensteinPluckerUpperNextAxis,
    RHTower.gammaValuationNthPrimeCoord,
    RHTower.gammaValuationNthPrimeAxis,
    RHTower.gammaValuationAdjacentLowerAxis,
    RHTower.gammaValuationAdjacentUpperAxis]
  ring

/-- Calibration: before physical covariance weighting, lower signed orientation recovers complete
all-prime layer exactly. -/
theorem tsum_frankensteinPluckerSignedPacket_lowerOrientation_eq_layerSum
    (a : RHTower.DeningerHeightKothe) (e : ℕ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
      (frankensteinPluckerSignedPacket a (e, n) 0 +
        frankensteinPluckerSignedPacket a (e, n) 2)) =
      RHTower.gammaValuationLayerSum e a := by
  rw [← RHTower.gammaValuationAdjacentPrimitive_eq_layerSum e a]
  unfold RHTower.gammaValuationAdjacentPrimitive
  apply tsum_congr
  intro n
  rw [frankensteinPluckerSignedPacket_lowerOrientation]
  rfl

/-- Calibration: second retained depth orientation recovers next complete all-prime layer. -/
theorem tsum_frankensteinPluckerSignedPacket_upperOrientation_eq_layerSum
    (a : RHTower.DeningerHeightKothe) (e : ℕ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
      (frankensteinPluckerSignedPacket a (e, n) 1 +
        frankensteinPluckerSignedPacket a (e, n) 3)) =
      RHTower.gammaValuationLayerSum (e + 1) a := by
  rw [← RHTower.gammaValuationAdjacentPrimitive_eq_layerSum (e + 1) a]
  unfold RHTower.gammaValuationAdjacentPrimitive
  apply tsum_congr
  intro n
  rw [frankensteinPluckerSignedPacket_upperOrientation]
  rfl

end RHTower.HedenmalmThetaSource
