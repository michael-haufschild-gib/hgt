import GaloisForLFunctions.HTGeometry.LocalMellinSobolevTransfer
import GaloisForLFunctions.RHTower.ChiCubicSelectedKernelEnergy
import GaloisForLFunctions.RHTower.ChiCubicNormalizedPhysical
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Local Mellin energy of the actual selected BAG cone

The original normalized cone Schwartz profile agrees exactly with its
physical oscillatory kernel and reciprocal Fourier kernel. Scaling both
Fourier coordinates by `2 * pi` changes curvature to `1 / (2 * pi)` and
cancels the squared Fourier amplitude against both Jacobians. The existing
selected reciprocal-kernel energy therefore bounds the literal normalized
physical family, whose cutoff width is exactly `N^(1/4)`.

The proved uniform local Mellin operator then gives full logarithmic Fourier
energy of order `1 + theta`, for `0 < theta < 1/2`, uniformly in the complete
Mellin parameter square. No stationary replacement or analytic budget is
assumed. Exterior log energy and source-weighted line tails remain separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace
private abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The literal normalized original physical cone Schwartz profile. -/
def bagCubicNormalizedConeSchwartz (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) : SchwartzMap E ℂ :=
  (((Real.log N.1)^3/N.1 : ℝ) : ℂ) •
    bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H)

/-- Exact physical identification, including the original normalization. -/
theorem bagCubicNormalizedConeSchwartz_apply (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (x y : ℝ) :
    bagCubicNormalizedConeSchwartz N H (WithLp.toLp 2 ![x,y])=
      bagCubicNormalizedPhysicalKernel (H.1/N.1) (1/Real.log N.1) N.1 x y := by
  exact bagCubicControlledCone_normalized_physical N H x y

/-- Exact spectral identification. The curvature becomes1/(2*pi) after scaling. -/
theorem bagCubicNormalizedConeSchwartz_fourier (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (a b : ℝ) :
    (𝓕 (bagCubicNormalizedConeSchwartz N H)) (WithLp.toLp 2 ![a,b])=
      (2*Real.pi : ℂ)*bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1)
        (2*Real.pi*a) (2*Real.pi*b) (((1/(2*Real.pi))/N.1)*(2*Real.pi*a)*(2*Real.pi*b)) := by
  rw [bagCubicNormalizedConeSchwartz,FourierTransform.fourier_smul]
  change (((Real.log N.1)^3/N.1 : ℝ) : ℂ)*
    (𝓕 (bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H))) (WithLp.toLp 2 ![a,b])= _
  rw [bagCubicControlledCone_normalized_reciprocal_kernel]
  congr 2
  field_simp [Real.pi_ne_zero]

private def coords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem lintegral_two (F : E→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : E, F u)=∫⁻ a : ℝ, ∫⁻ b : ℝ, F (WithLp.toLp 2 ![a,b]) := by
  have hp := coords_preserving.symm coords
  rw [←hp.lintegral_comp_emb coords.symm.measurableEmbedding F]
  exact lintegral_prod _ (hF.comp coords.symm.measurable).aemeasurable

private theorem scaled_lintegral (c : ℝ) (hc : 0<c) (F : ℝ→ℝ≥0∞) :
    (∫⁻ x : ℝ, ENNReal.ofReal c*F (c*x))=∫⁻ x : ℝ, F x := by
  have hd : ∀x∈(univ : Set ℝ), HasDerivWithinAt (fun t : ℝ => c*t) c univ x := by
    intro x _
    simpa only [mul_one] using! ((hasDerivAt_id x).const_mul c).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => c*x) univ := by
    intro x _ y _ hh
    exact mul_left_cancel₀ hc.ne' hh
  have himage : (fun x : ℝ => c*x) '' univ=univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨y/c,mem_univ _,?_⟩
      field_simp
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj F
  rw [himage,Measure.restrict_univ] at hh
  simpa only [abs_of_pos hc] using hh.symm

private theorem scaled_lintegral_two (c : ℝ) (hc : 0<c) (F : ℝ→ℝ→ℝ≥0∞) :
    (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (c^2)*F (c*a) (c*b))=
      ∫⁻ a : ℝ, ∫⁻ b : ℝ, F a b := by
  have he (a : ℝ) : (∫⁻ b : ℝ, ENNReal.ofReal (c^2)*F (c*a) (c*b))=
      ENNReal.ofReal c*∫⁻ b : ℝ, F (c*a) b := by
    rw [pow_two,ENNReal.ofReal_mul hc.le]
    simp only [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,scaled_lintegral c hc]
  simp_rw [he]
  exact scaled_lintegral c hc (fun a => ∫⁻ b : ℝ, F a b)

private theorem normalized_cone_energy (p : ℝ) (hp : 0 ≤ p) (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) :
    (∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^p*
      ‖(𝓕 (bagCubicNormalizedConeSchwartz N H)) ξ‖^2)) ≤
      ∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal ((1+|a|+|b|)^p*
        ‖bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1) a b
          (((1/(2*Real.pi))/N.1)*a*b)‖^2) := by
  let c := 2*Real.pi
  have hc : 0<c := mul_pos (by norm_num) Real.pi_pos
  have hc1 : 1 ≤ c := by dsimp only [c]; linarith [Real.pi_gt_three]
  let J : ℝ→ℝ→ℝ≥0∞ := fun a b => ENNReal.ofReal ((1+|a|+|b|)^p*
    ‖bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1) a b (((1/c)/N.1)*a*b)‖^2)
  have hcn : ‖(2*Real.pi : ℂ)‖=c := by
    dsimp only [c]
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  have hpoint (a b : ℝ) : ENNReal.ofReal ((1+|a|+|b|)^p*
      ‖(𝓕 (bagCubicNormalizedConeSchwartz N H)) (WithLp.toLp 2 ![a,b])‖^2) ≤
        ENNReal.ofReal (c^2)*J (c*a) (c*b) := by
    rw [bagCubicNormalizedConeSchwartz_fourier,norm_mul,mul_pow,hcn]
    change ENNReal.ofReal ((1+|a|+|b|)^p*(c^2*
      ‖bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1) (c*a) (c*b)
        (((1/c)/N.1)*(c*a)*(c*b))‖^2)) ≤ ENNReal.ofReal (c^2)*J (c*a) (c*b)
    have hw : 1+|a|+|b| ≤ 1+|c*a|+|c*b| := by
      rw [abs_mul c a,abs_mul c b,abs_of_pos hc]
      have ha := mul_le_mul_of_nonneg_right hc1 (abs_nonneg a)
      have hb := mul_le_mul_of_nonneg_right hc1 (abs_nonneg b)
      linarith
    dsimp only [J]
    rw [←ENNReal.ofReal_mul (sq_nonneg c)]
    apply ENNReal.ofReal_le_ofReal
    calc (1+|a|+|b|)^p*(c^2*‖bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1)
          (c*a) (c*b) (((1/c)/N.1)*(c*a)*(c*b))‖^2) ≤
        (1+|c*a|+|c*b|)^p*(c^2*‖bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1)
          (c*a) (c*b) (((1/c)/N.1)*(c*a)*(c*b))‖^2) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hw hp) (by positivity)
      _ = _ := by ring
  have hf := (𝓕 (bagCubicNormalizedConeSchwartz N H)).continuous.measurable
  rw [lintegral_two _ (by fun_prop)]
  change (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal ((1+|a|+|b|)^p*
    ‖(𝓕 (bagCubicNormalizedConeSchwartz N H)) (WithLp.toLp 2 ![a,b])‖^2)) ≤ _
  refine (lintegral_mono (fun a => lintegral_mono (hpoint a))).trans_eq ?_
  exact scaled_lintegral_two c hc J

/-- The literal N^(1/4) cutoff family, with zero only outside its admissible range. -/
def bagCubicSelectedNormalizedCone (N : ℝ) : SchwartzMap E ℂ :=
  if h : 1<N ∧ N^(1/4 : ℝ)<N/2 then
    bagCubicNormalizedConeSchwartz ⟨N,h.1⟩
      ⟨N^(1/4 : ℝ),Real.rpow_pos_of_pos (zero_lt_one.trans h.1) _,h.2⟩
  else 0

private theorem selected_width_ratio (N : ℝ) (hN : 0<N) :
    N^(1/4 : ℝ)/N=N^(-(3/4 : ℝ)) := by
  rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hN]
  congr 1
  norm_num

private theorem selected_admissible : ∀ᶠ N : ℝ in atTop, 1<N ∧ N^(1/4 : ℝ)<N/2 := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hdN
  refine ⟨hN,?_⟩
  have hN0 : 0<N := zero_lt_one.trans hN
  have hh : N^(1/4 : ℝ)/N < (1/2 : ℝ) := by rw [selected_width_ratio N hN0]; exact hdN
  have ht := (div_lt_iff₀ hN0).mp hh
  linarith

/-- Exact eventual identification with the original physical kernel at the literal selection. -/
theorem bagCubicSelectedNormalizedCone_eventually_apply :
    ∀ᶠ N : ℝ in atTop, ∀x y : ℝ,
      bagCubicSelectedNormalizedCone N (WithLp.toLp 2 ![x,y])=
        bagCubicNormalizedPhysicalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) N x y := by
  filter_upwards [selected_admissible] with N hN x y
  rw [bagCubicSelectedNormalizedCone,dif_pos hN,bagCubicNormalizedConeSchwartz_apply]
  simp only [selected_width_ratio N (zero_lt_one.trans hN.1)]

/-- Uniform admitted full physical Fourier energy of the literal normalized selected family. -/
theorem bagCubicSelectedNormalizedCone_uniform_energy
    (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      (∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2*s.1)*
        ‖(𝓕 (bagCubicSelectedNormalizedCone N)) ξ‖^2)) ≤ ENNReal.ofReal C := by
  let tau : {r : ℝ // 0<r} := ⟨1/(2*Real.pi),by positivity⟩
  obtain ⟨C,hC,hCb⟩ := bagCubicReciprocalKernel_selected_uniform_energy s tau
  refine ⟨C,hC,?_⟩
  filter_upwards [selected_admissible,hCb] with N hN hB
  let n : {r : ℝ // 1<r} := ⟨N,hN.1⟩
  let H : {r : ℝ // r∈Ioo (0 : ℝ) (n.1/2)} :=
    ⟨N^(1/4 : ℝ),Real.rpow_pos_of_pos (zero_lt_one.trans hN.1) _,hN.2⟩
  have hb := normalized_cone_energy (2*s.1) (by linarith [s.2.1]) n H
  have he : H.1/n.1=N^(-(3/4 : ℝ)) := selected_width_ratio N (zero_lt_one.trans hN.1)
  rw [he] at hb
  let J : ℝ×ℝ→ℝ := fun ab => (1+|ab.1|+|ab.2|)^(2*s.1)*
    ‖bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) ab.1 ab.2
      ((tau.1/N)*ab.1*ab.2)‖^2
  have hJ : Integrable J := hB.1
  have hJpos (ab : ℝ×ℝ) : 0 ≤ J ab := by dsimp only [J]; positivity
  have hlin : (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (J (a,b)))=
      ENNReal.ofReal (∫ab : ℝ×ℝ, J ab) := by
    rw [ofReal_integral_eq_lintegral_ofReal hJ (Eventually.of_forall hJpos)]
    exact (lintegral_prod _ (ENNReal.measurable_ofReal.comp_aemeasurable hJ.aestronglyMeasurable.aemeasurable)).symm
  rw [bagCubicSelectedNormalizedCone,dif_pos hN]
  refine hb.trans ?_
  change (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (J (a,b))) ≤ ENNReal.ofReal C
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hB.2

/-- Uniform complete local Mellin energy for the actual selected BAG physical profile. -/
theorem bagCubicSelectedNormalizedCone_uniform_local_mellin_energy
    (s : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀σ : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        (∫⁻ ξ : E, ENNReal.ofReal ((1+|ξ 0|+|ξ 1|)^(2+2*s.1)*
          ‖(𝓕 (GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz σ
            (bagCubicSelectedNormalizedCone N))) ξ‖^2)) ≤ ENNReal.ofReal C := by
  obtain ⟨A,hA,hAb⟩ := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz_uniform_energy
    ⟨s.1,s.2.1,by linarith [s.2.2]⟩
  obtain ⟨B,hB,hBb⟩ := bagCubicSelectedNormalizedCone_uniform_energy
    ⟨1+s.1,by constructor <;> linarith [s.2.1,s.2.2]⟩
  refine ⟨A*B,mul_pos hA hB,?_⟩
  filter_upwards [hBb] with N hN
  intro σ
  have hb := (hAb σ (bagCubicSelectedNormalizedCone N)).2
  dsimp only at hb hN
  have he : 2*(1+s.1)=2+2*s.1 := by ring
  simp only [he] at hN
  refine hb.trans ?_
  rw [ENNReal.ofReal_mul hA.le]
  exact mul_le_mul_right hN _

end RHTower.BAGTrace
