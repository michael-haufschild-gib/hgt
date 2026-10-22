import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspHeightTest
import Mathlib.MeasureTheory.Integral.Prod

/-!
Exact native modular cusp measure and pairings, including the full cell width and invariant density.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

private def cuspRectangle : Set ℂ :=
  {z | z.re ∈ Icc (-1/2) (1/2) ∧ 2 < z.im}

private theorem cuspRectangle_subset : cuspRectangle ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by norm_num) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

/-- Exact native modular volume for a full height profile supported above the
cusp cutoff. The horizontal factor is exactly the cell width, namely one. -/
theorem integral_cusp_height (F : ℝ → ℂ) (hF : ∀ y ≤ 2, F y = 0) :
    (∫ z : UpperHalfPlane, F z.im ∂measure) = ∫ y in Ioi 2, F y/(y:ℂ)^(2 : ℕ) := by
  change (∫ z : UpperHalfPlane, F (z:ℂ).im ∂measure) = _
  rw [integral_measure_chart (fun z => F z.im)]
  have hcell : MeasurableSet cellChart :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet
  have hd : (∫ z in cellChart, chartDensity z • F z.im) =
      ∫ z in cellChart, F z.im/(z.im:ℂ)^(2 : ℕ) := by
    apply setIntegral_congr_fun hcell
    rintro z ⟨w,hw,rfl⟩
    simp only [chartDensity,UpperHalfPlane.coe_im,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      coe_nnnorm,Real.norm_eq_abs,abs_of_pos w.im_pos,Complex.real_smul,
      Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
    ring
  rw [hd,setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hcell cuspRectangle_subset]
  · have hm := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun xy : ℝ × ℝ => (1:ℂ)*(F xy.2/(xy.2:ℂ)^(2 : ℕ))) (Icc (-1/2) (1/2) ×ˢ Ioi 2)
    change (∫ z in Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2) (1/2) ×ˢ Ioi 2),
      F z.im/(z.im:ℂ)^(2 : ℕ)) = _
    simp only [Complex.measurableEquivRealProd_apply,one_mul] at hm
    rw [hm,Measure.volume_eq_prod]
    have hp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun _ : ℝ => (1:ℂ))
      (fun y : ℝ => F y/(y:ℂ)^(2 : ℕ)) (Icc (-1/2) (1/2)) (Ioi 2)
    simp only [one_mul] at hp
    rw [hp]
    norm_num [setIntegral_const,measureReal_def,Real.volume_Icc]
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hz.1
    have hy : w.im ≤ 2 := by
      by_contra hn
      apply hz.2
      refine ⟨?_,lt_of_not_ge hn⟩
      change w.re ∈ Icc (-1/2) (1/2)
      simpa only [mem_Icc,neg_div] using abs_le.mp hw.2
    change F w.im/(w.im:ℂ)^(2 : ℕ) = 0
    rw [hF _ hy,zero_div]

/-- The actual modular cusp vectors have their exact one-dimensional native
pairing, with no quotient-volume or normalization assumption. -/
theorem CuspHeightTest.operatorVector_inner (h k : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (k.operatorVector : Space) =
      ∫ y in Ioi 2, conj (h.field y)*k.field y/(y:ℂ)^(2 : ℕ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : UpperHalfPlane, conj (h.field z.im)*k.field z.im ∂measure := by
      apply integral_congr_ae
      filter_upwards [h.operatorVector_coe,k.operatorVector_coe] with z hh hk
      rw [hh,hk]
      simp [RCLike.inner_apply,mul_comm]
    _ = _ := integral_cusp_height (fun y => conj (h.field y)*k.field y)
      (fun y hy => by rw [h.zero_low hy]; simp)

end
end RHTower.D4BMModularCore
