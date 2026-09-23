import GaloisForLFunctions.RHTower.HedenmalmThetaSkewAdjointDefectCriterion
import GaloisForLFunctions.RHTower.HedenmalmThetaTraceKernel
import GaloisForLFunctions.RHTower.MixedSpikeQuantumFisher

/-!
# Positive skew-adjoint floor of the corrected theta stages

The coefficient-only skew-adjoint producer is impossible for the actual corrected theta stages.
Their finite matrix energies converge exactly to the anti-Hermitian Hilbert--Schmidt energy of the
signed fixed theta kernel, and that limit is strictly positive.

Strict positivity is detected without spectral data.  On the pinned coordinate vector `t`, the
fixed theta source inverse has expectation

`-i ∫ q(t) t²(1-t)/2 dt`,

whose imaginary part is strictly negative because the quantile speed `q` is positive.  Thus the
fixed operator is not ordinarily self-adjoint.  Finite support identifies each matrix energy with
the full kernel energy, and Hilbert--Schmidt convergence transports the positive defect to a
strict eventual floor.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt

noncomputable section

/-- The pinned prefix of the coordinate vector is the elementary quadratic primitive. -/
theorem pinnedPrefix_pinnedCoordinate {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedPrefix pinnedCoordinate t = ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  rw [pinnedPrefix_eq_intervalIntegral pinnedCoordinate ht]
  rw [intervalIntegral.integral_of_le ht.1]
  have hsubset : Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨hu.1.le, le_trans hu.2 ht.2⟩
  have hmeasure : volume.restrict (Ioc (0 : ℝ) t) ≤ unitIntervalMeasure := by
    rw [unitIntervalMeasure]
    exact Measure.restrict_mono hsubset le_rfl
  have hcoord :
      (fun u => pinnedCoordinate u) =ᵐ[volume.restrict (Ioc (0 : ℝ) t)]
        fun u : ℝ => (u : ℂ) :=
    ae_mono hmeasure pinnedCoordinate_coeFn
  rw [integral_congr_ae hcoord]
  rw [← intervalIntegral.integral_of_le ht.1,
    intervalIntegral.integral_ofReal, integral_id]
  push_cast
  ring

/-- The pinned Volterra primitive of the coordinate vector is `t(t-1)/2`. -/
theorem pinnedVolterraFun_pinnedCoordinate {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun pinnedCoordinate t =
      (((t ^ (2 : ℕ) - t) / 2 : ℝ) : ℂ) := by
  rw [pinnedVolterraFun, pinnedPrefix_pinnedCoordinate ht, pinnedMean_pinnedCoordinate]
  push_cast
  ring

/-- Positive real density detected by the coordinate-vector expectation. -/
def thetaSkewAdjointCoordinateDensity (t : ℝ) : ℝ :=
  quantileSpeed thetaSource t * (t ^ (2 : ℕ) * (1 - t) / 2)

theorem integrable_thetaSkewAdjointCoordinateDensity :
    Integrable thetaSkewAdjointCoordinateDensity unitIntervalMeasure := by
  have hbase := integrable_quantileSpeed_mul_poly thetaSource
    hasFiniteKernelEnergy_thetaSource
  have hmul := hbase.bdd_mul (c := 1)
    ((continuous_id.const_mul (1 / 4)).aestronglyMeasurable) (by
      filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_le]
      simp only [id_eq]
      constructor <;> linarith [ht.1, ht.2])
  refine hmul.congr ?_
  filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
  dsimp [thetaSkewAdjointCoordinateDensity]
  ring

/-- Quantile-speed positivity leaves a strict coordinate expectation charge. -/
theorem integral_thetaSkewAdjointCoordinateDensity_pos :
    0 < ∫ t, thetaSkewAdjointCoordinateDensity t ∂unitIntervalMeasure := by
  have hnonneg : 0 ≤ᵐ[unitIntervalMeasure] thetaSkewAdjointCoordinateDensity := by
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    dsimp [thetaSkewAdjointCoordinateDensity]
    have hq := quantileSpeed_pos thetaSource t
    exact mul_nonneg hq.le
      (div_nonneg (mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2.le)) (by norm_num))
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg
    integrable_thetaSkewAdjointCoordinateDensity).2
  have hsubset : Ioo (1 / 4 : ℝ) (3 / 4) ⊆
      Function.support thetaSkewAdjointCoordinateDensity := by
    intro t ht
    dsimp [Function.support, thetaSkewAdjointCoordinateDensity]
    have hq := quantileSpeed_pos thetaSource t
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : t < 1 := by linarith [ht.2]
    exact mul_ne_zero hq.ne'
      (div_ne_zero (mul_ne_zero (pow_ne_zero 2 ht0.ne')
        (sub_ne_zero.mpr ht1.ne.symm)) (by norm_num))
  have hvolume : 0 < unitIntervalMeasure (Ioo (1 / 4 : ℝ) (3 / 4)) := by
    rw [unitIntervalMeasure_eq, Measure.restrict_apply measurableSet_Ioo]
    rw [show Ioo (1 / 4 : ℝ) (3 / 4) ∩ Ioo 0 1 = Ioo (1 / 4) (3 / 4) by
      ext t
      simp only [mem_inter_iff, mem_Ioo]
      constructor
      · exact fun h => h.1
      · intro h
        constructor
        · exact h
        · constructor <;> linarith [h.1, h.2]]
    rw [Real.volume_Ioo]
    norm_num
  exact hvolume.trans_le (measure_mono hsubset)

/-- Exact ordinary expectation of the fixed theta source inverse on the coordinate vector. -/
theorem inner_pinnedCoordinate_thetaKernelOperator_pinnedCoordinate :
    inner ℂ pinnedCoordinate (thetaKernelOperator pinnedCoordinate) =
      -Complex.I *
        ((∫ t, thetaSkewAdjointCoordinateDensity t
          ∂unitIntervalMeasure : ℝ) : ℂ) := by
  have hop :
      (thetaKernelOperator pinnedCoordinate : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
        fun t => pinnedKernelField thetaSource t pinnedCoordinate := by
    simpa only [thetaKernelOperator] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource
        pinnedCoordinate)
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) (pinnedCoordinate t) *
        (thetaKernelOperator pinnedCoordinate) t ∂unitIntervalMeasure) =
        ∫ t, -Complex.I * ((thetaSkewAdjointCoordinateDensity t : ℝ) : ℂ)
          ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [pinnedCoordinate_coeFn, hop,
        ae_unitIntervalMeasure_mem_Ioo] with t hcoord hopT ht
      rw [hcoord, hopT, pinnedKernelField_apply_eq_pinnedVolterraFun,
        pinnedVolterraFun_pinnedCoordinate (Ioo_subset_Icc_self ht)]
      dsimp [thetaSkewAdjointCoordinateDensity]
      simp only [Complex.conj_ofReal]
      push_cast
      ring
    _ = -Complex.I *
        ((∫ t, thetaSkewAdjointCoordinateDensity t
          ∂unitIntervalMeasure : ℝ) : ℂ) := by
      rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]

/-- The coordinate expectation has strictly negative imaginary part. -/
theorem inner_pinnedCoordinate_thetaKernelOperator_pinnedCoordinate_im_neg :
    (inner ℂ pinnedCoordinate (thetaKernelOperator pinnedCoordinate)).im < 0 := by
  rw [inner_pinnedCoordinate_thetaKernelOperator_pinnedCoordinate]
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul,
    zero_add]
  exact neg_neg_of_pos integral_thetaSkewAdjointCoordinateDensity_pos

/-- The fixed theta source inverse is not ordinarily self-adjoint. -/
theorem thetaKernelOperator_adjoint_ne_thetaKernelOperator :
    ContinuousLinearMap.adjoint thetaKernelOperator ≠ thetaKernelOperator := by
  intro hself
  have hzero := inner_selfadjoint_apply_im_eq_zero thetaKernelOperator hself pinnedCoordinate
  exact (ne_of_lt inner_pinnedCoordinate_thetaKernelOperator_pinnedCoordinate_im_neg) hzero

private theorem blockFin_sub_conjTranspose
    {ι : Type*} [DecidableEq ι] (K : ι × ι → ℂ) (s : Finset ι) :
    blockFin K s - (blockFin K s)ᴴ =
      blockFin (K - HilbertSchmidt.hsAdjoint K) s := by
  ext i j
  simp [blockFin, HilbertSchmidt.blockMatrix, HilbertSchmidt.hsAdjoint]

private theorem finiteMatrixSkewAdjointEnergy_blockFin_eq_hsNormSq
    {ι : Type*} [DecidableEq ι] (K : ι × ι → ℂ) (s : Finset ι)
    (hsupp : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) :
    finiteMatrixSkewAdjointEnergy (blockFin K s) =
      HilbertSchmidt.hsNormSq (K - HilbertSchmidt.hsAdjoint K) := by
  have hdef : ∀ p : ι × ι, p ∉ s ×ˢ s →
      (K - HilbertSchmidt.hsAdjoint K) p = 0 := by
    intro p hp
    have hswap : (p.2, p.1) ∉ s ×ˢ s := by
      intro hmem
      apply hp
      rw [Finset.mem_product] at hmem ⊢
      exact ⟨hmem.2, hmem.1⟩
    simp only [Pi.sub_apply, HilbertSchmidt.hsAdjoint,
      hsupp p hp, hsupp (p.2, p.1) hswap, map_zero, sub_zero]
  rw [finiteMatrixSkewAdjointEnergy, blockFin_sub_conjTranspose,
    blockFin, matHSNormSq_submatrix,
    HilbertSchmidt.matHSNormSq_blockMatrix,
    ← HilbertSchmidt.hsNormSq_truncKernel_eq_sum,
    truncKernel_eq_self_of_support hdef]

/-- Exact finite-support identification of each stage energy with its full kernel defect. -/
theorem thetaSourceSignedStageSkewAdjointEnergy_eq_hsNormSq (k : ℕ) :
    thetaSourceSignedStageSkewAdjointEnergy k =
      HilbertSchmidt.hsNormSq
        (thetaSourceSignedKernel k -
          HilbertSchmidt.hsAdjoint (thetaSourceSignedKernel k)) := by
  exact finiteMatrixSkewAdjointEnergy_blockFin_eq_hsNormSq
    (thetaSourceSignedKernel k) (thetaSourceSignedCutoff k)
    (thetaSourceSignedKernel_support k)

/-- Positive anti-Hermitian Hilbert--Schmidt energy of the signed fixed theta kernel. -/
theorem neg_thetaKernelMatrix_skewAdjointEnergy_pos :
    0 < HilbertSchmidt.hsNormSq
      ((-thetaKernelMatrix) - HilbertSchmidt.hsAdjoint (-thetaKernelMatrix)) := by
  let L := -thetaKernelMatrix
  have hL : HilbertSchmidt.IsHS L := isHS_neg_thetaKernelMatrix
  have hLadj : HilbertSchmidt.IsHS (HilbertSchmidt.hsAdjoint L) :=
    HilbertSchmidt.isHS_hsAdjoint hL
  have hdef : HilbertSchmidt.IsHS (L - HilbertSchmidt.hsAdjoint L) :=
    HilbertSchmidt.isHS_sub hL hLadj
  have hdefne : L - HilbertSchmidt.hsAdjoint L ≠ 0 := by
    intro hzero
    have hadj : HilbertSchmidt.hsAdjoint L = L := (sub_eq_zero.mp hzero).symm
    have hopadj :
        ContinuousLinearMap.adjoint (HilbertSchmidt.toOperator hL) =
          HilbertSchmidt.toOperator hL := by
      rw [HilbertSchmidt.adjoint_toOperator hL]
      exact HilbertSchmidt.toOperator_congr _ _ hadj
    have himzero := inner_selfadjoint_apply_im_eq_zero
      (HilbertSchmidt.toOperator hL) hopadj (thetaCoord pinnedCoordinate)
    have htransport :
        inner ℂ (thetaCoord pinnedCoordinate)
            (HilbertSchmidt.toOperator hL (thetaCoord pinnedCoordinate)) =
          inner ℂ pinnedCoordinate ((-thetaKernelOperator) pinnedCoordinate) := by
      rw [show HilbertSchmidt.toOperator hL (thetaCoord pinnedCoordinate) =
          thetaCoord ((-thetaKernelOperator) pinnedCoordinate) by
        exact (thetaCoord_intertwines_neg_sourceInverse pinnedCoordinate).symm]
      exact thetaCoord.inner_map_map pinnedCoordinate
        ((-thetaKernelOperator) pinnedCoordinate)
    rw [htransport] at himzero
    simp only [neg_apply, inner_neg_right, Complex.neg_im] at himzero
    exact (ne_of_gt (neg_pos.mpr
      inner_pinnedCoordinate_thetaKernelOperator_pinnedCoordinate_im_neg)) himzero
  have henergyne :
      HilbertSchmidt.hsNormSq (L - HilbertSchmidt.hsAdjoint L) ≠ 0 := by
    intro henergy
    exact hdefne ((HilbertSchmidt.hsNormSq_eq_zero_iff hdef).mp henergy)
  exact lt_of_le_of_ne (HilbertSchmidt.hsNormSq_nonneg _) (Ne.symm henergyne)

/-- Exact positive limit of actual finite-stage skew-adjoint energies. -/
theorem tendsto_thetaSourceSignedStageSkewAdjointEnergy :
    Tendsto thetaSourceSignedStageSkewAdjointEnergy atTop
      (nhds (HilbertSchmidt.hsNormSq
        ((-thetaKernelMatrix) - HilbertSchmidt.hsAdjoint (-thetaKernelMatrix)))) := by
  let K : ℕ → thetaIndex × thetaIndex → ℂ := thetaSourceSignedKernel
  let L : thetaIndex × thetaIndex → ℂ := -thetaKernelMatrix
  let D : ℕ → thetaIndex × thetaIndex → ℂ :=
    fun k => K k - HilbertSchmidt.hsAdjoint (K k)
  let D0 : thetaIndex × thetaIndex → ℂ := L - HilbertSchmidt.hsAdjoint L
  have hK (k : ℕ) : HilbertSchmidt.IsHS (K k) := isHS_thetaSourceSignedKernel k
  have hL : HilbertSchmidt.IsHS L := isHS_neg_thetaKernelMatrix
  have hD (k : ℕ) : HilbertSchmidt.IsHS (D k) :=
    HilbertSchmidt.isHS_sub (hK k) (HilbertSchmidt.isHS_hsAdjoint (hK k))
  have hD0 : HilbertSchmidt.IsHS D0 :=
    HilbertSchmidt.isHS_sub hL (HilbertSchmidt.isHS_hsAdjoint hL)
  have hdiff (k : ℕ) : HilbertSchmidt.IsHS (K k - L) :=
    HilbertSchmidt.isHS_sub (hK k) hL
  have hskewdiff (k : ℕ) : D k - D0 =
      (K k - L) - HilbertSchmidt.hsAdjoint (K k - L) := by
    funext p
    simp only [D, D0, K, L, Pi.sub_apply, HilbertSchmidt.hsAdjoint, map_sub]
    ring
  have hskewNorm : Tendsto (fun k => HilbertSchmidt.hsNorm (D k - D0))
      atTop (nhds 0) := by
    have hupper : ∀ k,
        HilbertSchmidt.hsNorm (D k - D0) ≤
          2 * HilbertSchmidt.hsNorm (K k - L) := by
      intro k
      rw [hskewdiff]
      calc
        HilbertSchmidt.hsNorm
            ((K k - L) - HilbertSchmidt.hsAdjoint (K k - L)) ≤
            HilbertSchmidt.hsNorm (K k - L) +
              HilbertSchmidt.hsNorm (HilbertSchmidt.hsAdjoint (K k - L)) :=
          HilbertSchmidt.hsNorm_sub_le (hdiff k)
            (HilbertSchmidt.isHS_hsAdjoint (hdiff k))
        _ = 2 * HilbertSchmidt.hsNorm (K k - L) := by
          rw [HilbertSchmidt.hsNorm_hsAdjoint]
          ring
    exact squeeze_zero (fun k => HilbertSchmidt.hsNorm_nonneg _) hupper (by
      simpa only [K, L, mul_zero] using
        thetaSourceSignedKernel_tendsto_source.const_mul 2)
  have habsLe (k : ℕ) :
      |HilbertSchmidt.hsNorm (D k) - HilbertSchmidt.hsNorm D0| ≤
        HilbertSchmidt.hsNorm (D k - D0) := by
    rw [HilbertSchmidt.hsNorm_eq_lp_norm (hD k),
      HilbertSchmidt.hsNorm_eq_lp_norm hD0,
      HilbertSchmidt.hsNorm_eq_lp_norm (HilbertSchmidt.isHS_sub (hD k) hD0)]
    exact abs_norm_sub_norm_le
      (⟨D k, (hD k).memℓp⟩ : lp (fun _ : thetaIndex × thetaIndex => ℂ) 2)
      (⟨D0, hD0.memℓp⟩ : lp (fun _ : thetaIndex × thetaIndex => ℂ) 2)
  have habs : Tendsto
      (fun k => |HilbertSchmidt.hsNorm (D k) - HilbertSchmidt.hsNorm D0|)
      atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) habsLe hskewNorm
  have hsub : Tendsto
      (fun k => HilbertSchmidt.hsNorm (D k) - HilbertSchmidt.hsNorm D0)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  have hnorm : Tendsto (fun k => HilbertSchmidt.hsNorm (D k)) atTop
      (nhds (HilbertSchmidt.hsNorm D0)) := by
    simpa only [sub_add_cancel, zero_add] using
      hsub.add_const (HilbertSchmidt.hsNorm D0)
  have hsq := hnorm.pow 2
  simp only [HilbertSchmidt.hsNorm, Real.sq_sqrt
    (HilbertSchmidt.hsNormSq_nonneg _)] at hsq
  rw [show thetaSourceSignedStageSkewAdjointEnergy =
      fun k => HilbertSchmidt.hsNormSq
        (thetaSourceSignedKernel k -
          HilbertSchmidt.hsAdjoint (thetaSourceSignedKernel k)) by
    funext k
    exact thetaSourceSignedStageSkewAdjointEnergy_eq_hsNormSq k]
  simpa only [D, D0, K, L] using hsq

/-- Every sufficiently late stage lies above half the positive limiting defect. -/
theorem eventually_thetaSourceSignedStageSkewAdjointEnergy_gt_half_limit :
    ∀ᶠ k : ℕ in atTop,
      HilbertSchmidt.hsNormSq
          ((-thetaKernelMatrix) - HilbertSchmidt.hsAdjoint (-thetaKernelMatrix)) / 2 <
        thetaSourceSignedStageSkewAdjointEnergy k := by
  exact (tendsto_order.1 tendsto_thetaSourceSignedStageSkewAdjointEnergy).1 _
    (half_lt_self neg_thetaKernelMatrix_skewAdjointEnergy_pos)

/-- **Producer no-go.** Actual corrected theta stages cannot have cofinally small ordinary
skew-adjoint energy. -/
theorem not_thetaSourceSignedStageSkewAdjointEnergyCofinallySmall :
    ¬ ThetaSourceSignedStageSkewAdjointEnergyCofinallySmall := by
  intro hsmall
  let E : ℝ := HilbertSchmidt.hsNormSq
    ((-thetaKernelMatrix) - HilbertSchmidt.hsAdjoint (-thetaKernelMatrix))
  have hE : 0 < E := neg_thetaKernelMatrix_skewAdjointEnergy_pos
  have hevent : ∀ᶠ k : ℕ in atTop,
      E / 2 < thetaSourceSignedStageSkewAdjointEnergy k := by
    simpa only [E] using
      eventually_thetaSourceSignedStageSkewAdjointEnergy_gt_half_limit
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  obtain ⟨k, hkN, hk⟩ := hsmall (E / 2) (half_pos hE) N
  exact (lt_asymm (hN k hkN) hk).elim

end

end RHTower.HedenmalmThetaSource
