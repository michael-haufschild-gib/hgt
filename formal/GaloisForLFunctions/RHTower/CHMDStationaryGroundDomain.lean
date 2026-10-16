import GaloisForLFunctions.RHTower.CHMDThetaRelativeGraph
import GaloisForLFunctions.RHTower.CHMDPrimeDomain

/-!
# Exact stationary ground-state domain for CHMD

Multiplication by theta removes the spatial weights from the singular jump
energy. The difference is integrable for every mass-L2 source, so this identity
holds on the maximal domain, without compact support or source smoothness.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem exists_theta_lipschitz : ∃ C, LipschitzWith C riemannKernelReal := by
  simpa only [show thetaCuspFullSource = riemannKernelReal from
    funext thetaCuspFullSource_eq_riemannKernelReal] using exists_lipschitz_thetaCuspFullSource

def thetaLipConstant : NNReal := Classical.choose exists_theta_lipschitz

theorem theta_lipschitz : LipschitzWith thetaLipConstant riemannKernelReal :=
  Classical.choose_spec exists_theta_lipschitz

def thetaProduct (v : ℝ → ℝ) (x : ℝ) : ℝ := riemannKernelReal x * v x

theorem measurable_thetaProduct {v : ℝ → ℝ} (hv : Measurable v) :
    Measurable (thetaProduct v) := continuous_riemannKernelReal.measurable.mul hv

theorem integrable_theta_mul_sq {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) : Integrable (fun x => riemannKernelReal x * v x ^ 2) := by
  have hm := (integrable_weighted_iff volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le) _).mp h2.integrable_sq
  apply hm.mono' (continuous_riemannKernelReal.measurable.mul (hv.pow_const 2)).aestronglyMeasurable
  filter_upwards with x
  change ‖riemannKernelReal x * v x ^ 2‖ ≤ massDensity x * v x ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (riemannKernelReal_pos x).le (sq_nonneg _))]
  unfold massDensity
  nlinarith [mul_nonneg (riemannKernelReal_pos x).le (sq_nonneg (v x)),
    mul_le_mul_of_nonneg_right (Real.one_le_cosh (x / 2))
      (mul_nonneg (riemannKernelReal_pos x).le (sq_nonneg (v x)))]

theorem memLp_thetaProduct {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) : MemLp (thetaProduct v) 2 volume := by
  obtain ⟨C, hC, hb, _⟩ := theta_global_and_exponential_bound
  apply (memLp_two_iff_integrable_sq (measurable_thetaProduct hv).aestronglyMeasurable).mpr
  apply ((integrable_theta_mul_sq hv h2).const_mul C).mono'
    ((measurable_thetaProduct hv).pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_right (hb x)
    (mul_nonneg (riemannKernelReal_pos x).le (sq_nonneg (v x)))
  dsimp [thetaProduct]
  nlinarith only [h]

/-- One row of the ground-state correction; `s=1,-1` gives the two directions. -/
def thetaGroundRow (v : ℝ → ℝ) (s : ℝ) (e : ℝ × ℝ) : ℝ :=
  archLevyDensity e.1 * (riemannKernelReal (e.2 + s * e.1) - riemannKernelReal e.2) *
    (riemannKernelReal e.2 * v e.2 ^ 2)

theorem measurable_thetaGroundRow {v : ℝ → ℝ} (hv : Measurable v) (s : ℝ) :
    Measurable (thetaGroundRow v s) := by
  unfold thetaGroundRow
  exact ((measurable_archLevyDensity.comp measurable_fst).mul
    ((continuous_riemannKernelReal.measurable.comp (measurable_snd.add
      (measurable_fst.const_mul s))).sub
        (continuous_riemannKernelReal.measurable.comp measurable_snd))).mul
    ((continuous_riemannKernelReal.measurable.comp measurable_snd).mul
      ((hv.comp measurable_snd).pow_const 2))

theorem norm_thetaGroundRow_le (v : ℝ → ℝ) (s : ℝ) {e : ℝ × ℝ} (he : 0 < e.1) :
    ‖thetaGroundRow v s e‖ ≤ (thetaLipConstant : ℝ) * |s| *
      ((e.1 * archLevyDensity e.1) * (riemannKernelReal e.2 * v e.2 ^ 2)) := by
  have h := theta_lipschitz.norm_sub_le (e.2 + s * e.1) e.2
  simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos he] at h
  rw [thetaGroundRow, norm_mul, norm_mul, Real.norm_of_nonneg (archLevyDensity_pos he).le,
    Real.norm_of_nonneg (mul_nonneg (riemannKernelReal_pos _).le (sq_nonneg _))]
  calc
    _ ≤ archLevyDensity e.1 * ((thetaLipConstant : ℝ) * (|s| * e.1)) *
        (riemannKernelReal e.2 * v e.2 ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (archLevyDensity_pos he).le)
        (mul_nonneg (riemannKernelReal_pos _).le (sq_nonneg _))
    _ = _ := by ring

theorem integrable_thetaGroundRow {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) (s : ℝ) : Integrable (thetaGroundRow v s) archBase := by
  have hi := integrableOn_mul_archLevyDensity.mul_prod (integrable_theta_mul_sq hv h2)
  apply (hi.const_mul ((thetaLipConstant : ℝ) * |s|)).mono'
    (measurable_thetaGroundRow hv s).aestronglyMeasurable
  have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  exact ht.mono fun e he => norm_thetaGroundRow_le v s he

def thetaGroundCorrection (v : ℝ → ℝ) (e : ℝ × ℝ) : ℝ :=
  thetaGroundRow v 1 e + thetaGroundRow v (-1) (e.1, e.2 + e.1)

theorem integrable_thetaGroundCorrection {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) : Integrable (thetaGroundCorrection v) archBase := by
  have hs := (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable
    (integrable_thetaGroundRow hv h2 (-1))
  have hs' : Integrable (fun e : ℝ × ℝ => thetaGroundRow v (-1) (e.1, e.2 + e.1)) archBase := by
    change Integrable (fun e : ℝ × ℝ => thetaGroundRow v (-1) (e.1, e.2 + e.1))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)
    simpa only [Function.comp_def, add_comm] using hs
  exact (integrable_thetaGroundRow hv h2 1).add hs'

/-- The cancellation is algebraic before any singular integral is taken. -/
theorem theta_ground_identity (v : ℝ → ℝ) (e : ℝ × ℝ) :
    archWeight e * difference v e ^ 2 =
      stationaryJump (thetaProduct v) e + thetaGroundCorrection v e := by
  simp only [archWeight, difference, left, right, stationaryJump, thetaProduct,
    thetaGroundCorrection, thetaGroundRow, one_mul, neg_mul, one_mul, add_neg_cancel_right]
  ring

/-- Exact maximal-domain identification; theta multiplication absorbs every singular spatial weight. -/
theorem memLp_arch_difference_iff_stationary {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) :
    MemLp (difference v) 2 archMeasure ↔ Integrable (stationaryJump (thetaProduct v)) archBase := by
  rw [memLp_two_iff_integrable_sq (measurable_difference hv).aestronglyMeasurable,
    archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
  have hcorr := integrable_thetaGroundCorrection hv h2
  have heq : (fun e => archWeight e * difference v e ^ 2) =
      fun e => stationaryJump (thetaProduct v) e + thetaGroundCorrection v e :=
    funext (theta_ground_identity v)
  rw [heq]
  exact integrable_add_iff_integrable_left hcorr

theorem memLp_full_difference_iff_stationary {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) :
    MemLp (difference v) 2 edgeMeasure ↔ Integrable (stationaryJump (thetaProduct v)) archBase := by
  rw [memLp_full_difference_iff_arch h2, memLp_arch_difference_iff_stationary hv h2]

theorem arch_energy_eq_stationary_add_correction {v : ℝ → ℝ} (hv : Measurable v)
    (h2 : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 archMeasure) :
    (∫ e, difference v e ^ 2 ∂archMeasure) = stationaryEnergy (thetaProduct v) +
      ∫ e, thetaGroundCorrection v e ∂archBase := by
  rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae]
  simp_rw [theta_ground_identity]
  exact integral_add ((memLp_arch_difference_iff_stationary hv h2).mp hd)
    (integrable_thetaGroundCorrection hv h2)

end RHTower.CHMDDoobGraph
