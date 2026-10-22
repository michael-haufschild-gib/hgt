import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ImaginaryCarrierCollapse
import GaloisForLFunctions.HTGeometry.VitaliConvergence

open Complex Metric Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Every cofinal actual prescribed-shift sequence has the same zero carrier
limit on the whole upper half-plane. -/
theorem tendstoLocallyUniformlyOn_suzukiTaV2Livsic_zero_of_cofinal
    (a : ℕ → SuzukiPositiveAperture)
    (ha : Tendsto (fun n => (a n).1) atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => suzukiTaV2Livsic (a n))
      (fun _ => 0) atTop {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let g : ℝ → ℂ := fun s => I * (s : ℂ)
  let Y : Set ℂ := g '' Ioo (1 / 2 : ℝ) 1
  let z₀ := g (3 / 4)
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hF : ∀ n, DifferentiableOn ℂ (suzukiTaV2Livsic (a n)) U := fun n =>
    differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      (differentiable_suzukiTaV2CharacteristicA (a n))
      (differentiable_suzukiTaV2CharacteristicE (a n))
      (suzukiTaV2CharacteristicA_I (a n)) (suzukiTaV2_allAngleRealZeros (a n))
  have hloc : ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ,
      ∀ n, ∀ w ∈ ball z R, ‖suzukiTaV2Livsic (a n) w‖ ≤ C := by
    intro z hz
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hUopen z hz
    exact ⟨R, hR, hball, 1, fun n w hw =>
      (norm_suzukiTaV2Livsic_lt_one (a n) (hball hw)).le⟩
  have hYsub : Y ⊆ U := by
    rintro z ⟨s, hs, rfl⟩
    change 0 < (I * (s : ℂ)).im
    simpa using (show 0 < s by linarith [hs.1])
  have hz₀ : z₀ ∈ U := by norm_num [z₀, U, g]
  have hg : Continuous g := by dsimp [g]; fun_prop
  have ht : Tendsto g (𝓝[≠] (3 / 4 : ℝ)) (𝓝[≠] z₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (hg.tendsto (3 / 4)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s ≠ (3 / 4 : ℝ) at hs
      change g s ≠ g (3 / 4)
      intro heq
      apply hs
      apply Complex.ofReal_injective
      exact mul_left_cancel₀ I_ne_zero heq
  have hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y := by
    change ¬ ∀ᶠ z in 𝓝[≠] z₀, z ∉ Y
    intro hn
    have hseg : ∀ᶠ s in 𝓝[≠] (3 / 4 : ℝ), s ∈ Ioo (1 / 2 : ℝ) 1 :=
      nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
    obtain ⟨s, hs, hns⟩ := (hseg.and (ht.eventually hn)).exists
    exact hns ⟨s, hs, rfl⟩
  have ha' : Tendsto a atTop
      (comap (fun b : SuzukiPositiveAperture => b.1) atTop) :=
    tendsto_comap_iff.2 ha
  have hconv : ∀ z ∈ Y, Tendsto (fun n => suzukiTaV2Livsic (a n) z) atTop (𝓝 0) := by
    rintro z ⟨s, hs, rfl⟩
    exact (tendsto_suzukiTaV2Livsic_imaginary_zero ⟨s, hs⟩).comp ha'
  exact tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet hUopen hUc hF hloc
    (differentiableOn_const (0 : ℂ)) hYsub hz₀ hacc hconv

/-- Full-filter classification of the actual prescribed-shift V2 carrier.
All source estimates, compactness, uniqueness and cofinal promotion are
proved; no limiting or target-identification premise remains. -/
theorem tendstoLocallyUniformlyOn_suzukiTaV2Livsic_prescribed_zero :
    TendstoLocallyUniformlyOn suzukiTaV2Livsic (fun _ => 0)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop)
      {z : ℂ | 0 < z.im} := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).2
  intro K hKU hK
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro a ha
  have h := tendstoLocallyUniformlyOn_suzukiTaV2Livsic_zero_of_cofinal a
    (tendsto_comap_iff.1 ha)
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).1 h K hKU hK

end RHTower
end
