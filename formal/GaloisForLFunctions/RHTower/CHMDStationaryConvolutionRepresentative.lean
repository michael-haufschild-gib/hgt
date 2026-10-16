import GaloisForLFunctions.RHTower.CHMDStationaryOperatorMollification
import GaloisForLFunctions.HTGeometry.CompactKernelL2Convolution

/-!
# Literal smooth representatives of stationary operator mollification

A product-measure domination proves Fubini for the mollifier against any two
L2 vectors. Consequently the Hilbert-space Bochner average is exactly the
usual convolution, including for unbounded representatives.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace Convolution
noncomputable section
namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

theorem volume_inner_realLp (u v : StationaryVolumeSpace) :
    ⟪u, v⟫_ℝ = ∫ x, u x * v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mul_comm]

theorem integrable_mollifier_pairing (n : ℕ) (u v : StationaryVolumeSpace) :
    Integrable (fun p : ℝ × ℝ => mollifier n p.1 * u (p.2 - p.1) * v p.2)
      ((volume : Measure ℝ).prod volume) := by
  have hu := (Lp.stronglyMeasurable u).measurable
  have hv := (Lp.stronglyMeasurable v).measurable
  have hm := (mollifier_contDiff n).continuous.measurable
  have h1 : Integrable (fun p : ℝ × ℝ => mollifier n p.1 * (u (p.2 - p.1)) ^ 2)
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
      ((mollifier_integrable n).mul_prod (Lp.memLp u).integrable_sq)
  have h2 := (mollifier_integrable n).mul_prod (Lp.memLp v).integrable_sq
  refine (h1.add h2).mono'
    (((hm.comp measurable_fst).mul (hu.comp (measurable_snd.sub measurable_fst))).mul
      (hv.comp measurable_snd)).aestronglyMeasurable ?_
  filter_upwards [] with p
  have hy : |u (p.2 - p.1) * v p.2| ≤ (u (p.2 - p.1)) ^ 2 + (v p.2) ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|u (p.2 - p.1)| - |v p.2|),
      sq_abs (u (p.2 - p.1)), sq_abs (v p.2),
      mul_nonneg (abs_nonneg (u (p.2 - p.1))) (abs_nonneg (v p.2))]
  change ‖mollifier n p.1 * u (p.2 - p.1) * v p.2‖ ≤
    mollifier n p.1 * u (p.2 - p.1) ^ 2 + mollifier n p.1 * v p.2 ^ 2
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (mollifier_nonneg n p.1)]
  exact (mul_le_mul_of_nonneg_left hy (mollifier_nonneg n p.1)).trans_eq (by ring)

theorem volumeSmooth_inner (n : ℕ) (u v : StationaryVolumeSpace) :
    ⟪volumeSmooth n u, v⟫_ℝ = ∫ x, smooth u n x * v x := by
  rw [real_inner_comm, volumeSmooth, ← integral_inner (integrable_volumeSmooth n u)]
  have hi : (∫ a, ⟪v, mollifier n a • volumeTranslate (-a) u⟫_ℝ) =
      ∫ a, ∫ x, mollifier n a * u (x - a) * v x := by
    apply integral_congr_ae
    filter_upwards [] with a
    rw [inner_smul_right, real_inner_comm, volume_inner_realLp, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [volumeTranslate_ae (-a) u] with x hx
    simp only [hx, sub_eq_add_neg]
    ring
  rw [hi, integral_integral_swap (integrable_mollifier_pairing n u v)]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ a, mollifier n a * u (x - a) * v x) = smooth u n x * v x
  rw [integral_mul_const]
  rfl

theorem memLp_smooth_volume (n : ℕ) (u : StationaryVolumeSpace) :
    MemLp (smooth u n) 2 volume := by
  rw [memLp_two_iff_integrable_sq (smooth_contDiff (Lp.memLp u) n).continuous.aestronglyMeasurable]
  exact integrable_sq_lineConvolution (mollifier_contDiff n).continuous (mollifier_compact n)
    (Lp.stronglyMeasurable u).measurable (Lp.memLp u).integrable_sq

theorem volumeSmooth_eq_toLp (n : ℕ) (u : StationaryVolumeSpace) :
    volumeSmooth n u = (memLp_smooth_volume n u).toLp (smooth u n) := by
  apply ext_inner_right ℝ
  intro v
  rw [volumeSmooth_inner, volume_inner_realLp]
  apply integral_congr_ae
  filter_upwards [(memLp_smooth_volume n u).coeFn_toLp] with x hx
  rw [hx]

theorem volumeSmooth_ae (n : ℕ) (u : StationaryVolumeSpace) :
    volumeSmooth n u =ᵐ[volume] smooth u n := by
  rw [volumeSmooth_eq_toLp]
  exact (memLp_smooth_volume n u).coeFn_toLp

theorem smooth_congr_ae {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) (n : ℕ) :
    smooth u n = smooth v n :=
  convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) h

theorem volumeGeneratorSmooth_representative (n : ℕ) (u : volumeGenerator.domain) :
    ContDiff ℝ 2 (smooth (u : StationaryVolumeSpace) n) ∧
    (volumeGeneratorSmooth n u : StationaryVolumeSpace) =ᵐ[volume]
      smooth (u : StationaryVolumeSpace) n :=
  ⟨smooth_contDiff (Lp.memLp _) n, volumeSmooth_ae n _⟩

theorem volumeGeneratorSmooth_compact (n : ℕ) (u : volumeGenerator.domain)
    (hc : ∃ v : ℝ → ℝ, HasCompactSupport v ∧ (u : StationaryVolumeSpace) =ᵐ[volume] v) :
    HasCompactSupport (smooth (u : StationaryVolumeSpace) n) := by
  obtain ⟨v, hv, huv⟩ := hc
  rw [smooth_congr_ae huv]
  exact smooth_compact hv n

end RHTower.CHMDDoobGraph
