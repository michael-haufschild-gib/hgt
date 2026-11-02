import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeatBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinQuadrants

/-! The actual Epstein continuation is the sum of its original and dual
Gaussian tails, with explicit pole terms. Mellin inversion identifies the
dual tail before applying uniform bounds from the positive Gaussian count. -/

open Complex Real Set Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerEpsteinHeatBounds MayerEpsteinQuadrants
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeatRepresentation

private def heatTail (y t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => (rectTheta y t : ℂ)-1) t

private theorem heatTail_mellin_convergent {y : ℝ} (hy : 0 < y) (s : ℂ) :
    MellinConvergent (heatTail y) s := by
  have hm : MellinConvergent (rectFEPair y hy).f_modif s :=
    ((rectFEPair y hy).isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hi : IntegrableOn ((Ioi (1 : ℝ)).indicator
      (fun t : ℝ => (t : ℂ)^(s-1) • (rectFEPair y hy).f_modif t)) (Ioi 0) :=
    hm.indicator measurableSet_Ioi
  refine MeasureTheory.IntegrableOn.congr_fun hi ?_ measurableSet_Ioi
  intro t ht
  by_cases h1 : 1 < t
  · have hnot : ¬ t < 1 := not_lt.mpr h1.le
    simp [heatTail,WeakFEPair.f_modif,rectFEPair,h1,hnot]
  · simp [heatTail,h1]

private theorem modified_minus_tail {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    (rectFEPair y hy).f_modif t-heatTail y t=
      (y : ℂ)⁻¹*((t : ℂ)^(-1 : ℂ)*heatTail (1/y) t⁻¹) := by
  by_cases h1 : 1 < t
  · have hi : t⁻¹ < 1 := by
      simpa only [one_div] using (div_lt_one ht).mpr h1
    have hn : ¬ t < 1 := not_lt.mpr h1.le
    have hni : ¬ 1 < t⁻¹ := not_lt.mpr hi.le
    simp [heatTail,WeakFEPair.f_modif,rectFEPair,h1,hn,hni]
  · by_cases h2 : t < 1
    · have hi : 1 < t⁻¹ := by
        have hd : 1 < 1/t := (lt_div_iff₀ ht).mpr (by simpa only [one_mul] using h2)
        simpa only [one_div] using hd
      have hF : (rectTheta y t : ℂ)=
          (y : ℂ)⁻¹*(t : ℂ)⁻¹*(rectTheta (1/y) t⁻¹ : ℂ) := by
        have h := (rectFEPair y hy).h_feq t⁻¹ (inv_pos.mpr ht)
        simpa only [rectFEPair,one_div,inv_inv,Real.rpow_one,smul_eq_mul,
          Complex.ofReal_inv,Complex.ofReal_mul] using h
      simp only [one_div] at hF
      simp [WeakFEPair.f_modif,rectFEPair,heatTail,h1,h2,ht,hi,
        Real.rpow_neg_one,Complex.cpow_neg_one]
      rw [hF]
      ring
    · have he : t=1 := le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)
      subst t
      simp [heatTail,WeakFEPair.f_modif,rectFEPair]

private theorem mellin_heatTail (y : ℝ) (s : ℂ) :
    mellin (heatTail y) s=
      ∫ t in Ioi (1 : ℝ), (t : ℂ)^(s-1)*((rectTheta y t : ℂ)-1) := by
  unfold mellin heatTail
  simp only [← Set.indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))]
  simp only [smul_eq_mul]

private theorem lambda0_mellin_tails {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (rectFEPair y hy).Λ₀ s=
      mellin (heatTail y) s+(y : ℂ)⁻¹*mellin (heatTail (1/y)) (1-s) := by
  have hm : MellinConvergent (rectFEPair y hy).f_modif s :=
    ((rectFEPair y hy).isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hsub := (hasMellin_sub hm (heatTail_mellin_convergent hy s)).2
  have he : mellin (fun t => (rectFEPair y hy).f_modif t-heatTail y t) s=
      (y : ℂ)⁻¹*mellin (heatTail (1/y)) (1-s) := by
    calc
      _ = mellin (fun t : ℝ => (y : ℂ)⁻¹ •
          ((t : ℂ)^(-1 : ℂ) • heatTail (1/y) t⁻¹)) s := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [modified_minus_tail hy ht]
        simp only [smul_eq_mul]
      _ = (y : ℂ)⁻¹*mellin (heatTail (1/y)) (1-s) := by
        rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
        simp only [smul_eq_mul]
        congr 2
        ring
  rw [he] at hsub
  change (y : ℂ)⁻¹*mellin (heatTail (1/y)) (1-s)=
    (rectFEPair y hy).Λ₀ s-mellin (heatTail y) s at hsub
  linear_combination -hsub

/-- The actual original Gaussian tail at the spectral parameter `w/2`. -/
def originalTail (w : ℂ) (y : ℝ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (t : ℂ)^(w/2-1)*((rectTheta y t : ℂ)-1)

/-- The actual dual Gaussian tail, including the covolume factor. -/
def dualTail (w : ℂ) (y : ℝ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (y : ℂ)⁻¹*(t : ℂ)^(-w/2)*((rectTheta (1/y) t : ℂ)-1)

private theorem lambda0_heat_tails {y : ℝ} (hy : 0 < y) (w : ℂ) :
    (rectFEPair y hy).Λ₀ (w/2)=originalTail w y+dualTail w y := by
  rw [lambda0_mellin_tails hy,mellin_heatTail,mellin_heatTail]
  unfold originalTail dualTail
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [show (1-w/2)-1= -w/2 by ring]
  ring

/-- Exact Gaussian-tail expansion of the independently continued Epstein function. -/
theorem epsteinLambda_heat_expansion {w : ℂ} (hw0 : w ≠ 0) (hw2 : w ≠ 2)
    {y : ℝ} (hy : 0 < y) :
    epsteinLambda y hy (w/2)=originalTail w y+dualTail w y-2/w+2/((y : ℂ)*(w-2)) := by
  have hhalf : 1-w/2 ≠ 0 := by intro h; apply hw2; linear_combination -2*h
  rw [epsteinLambda,WeakFEPair.Λ,lambda0_heat_tails hy]
  change _-(1/(w/2))*1-(((1/y : ℝ) : ℂ)/(1-w/2))*1=_
  simp only [mul_one,Complex.ofReal_div,Complex.ofReal_one]
  field_simp [hw0,sub_ne_zero.mpr hw2,hhalf,Complex.ofReal_ne_zero.mpr hy.ne']
  ring

private theorem heat_integrable {y : ℝ} (hy : 0 < y) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1)*((rectTheta y t : ℂ)-1)) (Ioi 1) := by
  have hm := heatTail_mellin_convergent hy s
  have hi : IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1) • heatTail y t) (Ioi 1) :=
    hm.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  exact MeasureTheory.IntegrableOn.congr_fun hi
    (fun t ht => by simp only [heatTail,Set.indicator_of_mem ht,smul_eq_mul]) measurableSet_Ioi

/-- The original Gaussian tail converges absolutely at every complex parameter. -/
theorem originalTail_integrable {y : ℝ} (hy : 0 < y) (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(w/2-1)*((rectTheta y t : ℂ)-1)) (Ioi 1) :=
  heat_integrable hy (w/2)

/-- The dual Gaussian tail, including its covolume factor, also converges absolutely. -/
theorem dualTail_integrable {y : ℝ} (hy : 0 < y) (w : ℂ) :
    IntegrableOn (fun t : ℝ => (y : ℂ)⁻¹*(t : ℂ)^(-w/2)*
      ((rectTheta (1/y) t : ℂ)-1)) (Ioi 1) := by
  have hi := (heat_integrable (one_div_pos.mpr hy) (1-w/2)).const_mul (y : ℂ)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun hi ?_ measurableSet_Ioi
  intro t ht
  rw [show (1-w/2)-1= -w/2 by ring]
  ring

private theorem norm_original_integrand {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (w : ℂ) :
    ‖(t : ℂ)^(w/2-1)*((rectTheta y t : ℂ)-1)‖=originalHeatWeight w.re y t := by
  have hn : 0 ≤ rectTheta y t-1 := sub_nonneg.mpr (one_le_rectTheta hy.ne' ht)
  have hv : ‖((rectTheta y t : ℂ)-1)‖=rectTheta y t-1 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  have hr : (w/2-1).re=w.re/2-1 := by simp
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,hv,hr]
  rfl

private theorem norm_dual_integrand {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (w : ℂ) :
    ‖(y : ℂ)⁻¹*(t : ℂ)^(-w/2)*((rectTheta (1/y) t : ℂ)-1)‖=dualHeatWeight w.re y t := by
  have hn : 0 ≤ rectTheta (1/y) t-1 :=
    sub_nonneg.mpr (one_le_rectTheta (one_div_pos.mpr hy).ne' ht)
  have hv : ‖((rectTheta (1/y) t : ℂ)-1)‖=rectTheta (1/y) t-1 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  have hr : (-w/2).re= -w.re/2 := by simp
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,hv,hr]
  rfl

/-- A uniform norm bound for the original complex Gaussian tail. -/
theorem norm_originalTail_le {w : ℂ} {β y : ℝ} (hβ : 1 < β) (hwβ : w.re ≤ β) (hy : 1 ≤ y) :
    ‖originalTail w y‖ ≤ (thetaSum 1+1)*thetaMoment (2-β) := by
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), ‖(t : ℂ)^(w/2-1)*((rectTheta y t : ℂ)-1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (1 : ℝ), originalHeatWeight w.re y t :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => norm_original_integrand (zero_lt_one.trans_le hy) (zero_lt_one.trans ht) w)
    _ ≤ _ := originalHeatWeight_integral_le hβ hwβ hy

/-- A uniform norm bound for the dual complex Gaussian tail. -/
theorem norm_dualTail_le {w : ℂ} {η y : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hηw : η ≤ w.re) (hy : 1 ≤ y) :
    ‖dualTail w y‖ ≤ thetaSum 1*thetaMoment 0+y^(1-η)*thetaMoment η := by
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), ‖(y : ℂ)⁻¹*(t : ℂ)^(-w/2)*((rectTheta (1/y) t : ℂ)-1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (1 : ℝ), dualHeatWeight w.re y t :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => norm_dual_integrand (zero_lt_one.trans_le hy) (zero_lt_one.trans ht) w)
    _ ≤ _ := dualHeatWeight_integral_le hη0 hη1 hηw hy

/-- The continued Epstein function has explicit height growth with its two pole terms retained. -/
theorem norm_epsteinLambda_le {w : ℂ} (hw2 : w ≠ 2) {η β y : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηw : η ≤ w.re) (hβ : 1 < β)
    (hwβ : w.re ≤ β) (hy : 1 ≤ y) :
    ‖epsteinLambda y (zero_lt_one.trans_le hy) (w/2)‖ ≤
      (thetaSum 1+1)*thetaMoment (2-β)+thetaSum 1*thetaMoment 0+
        y^(1-η)*thetaMoment η+2/‖w‖+2/(y*‖w-2‖) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hw0 : w ≠ 0 := by intro h; simp only [h,Complex.zero_re] at hηw; linarith only [hη0,hηw]
  rw [epsteinLambda_heat_expansion hw0 hw2 hy0]
  have h1 := norm_add_le (originalTail w y+dualTail w y-2/w) (2/((y : ℂ)*(w-2)))
  have h2 := norm_sub_le (originalTail w y+dualTail w y) (2/w)
  have h3 := norm_add_le (originalTail w y) (dualTail w y)
  have hp0 : ‖(2 : ℂ)/w‖=2/‖w‖ := by rw [norm_div]; norm_num
  have hp2 : ‖(2 : ℂ)/((y : ℂ)*(w-2))‖=2/(y*‖w-2‖) := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
    norm_num
  rw [hp0] at h2
  rw [hp2] at h1
  have hA := norm_originalTail_le hβ hwβ hy
  have hB := norm_dualTail_le hη0 hη1 hηw hy
  linarith only [h1,h2,h3,hA,hB]

/-- Explicit height bound for the actual normalized Epstein field. -/
theorem norm_epsteinField_le {w : ℂ} (hw2 : w ≠ 2) {η β y : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hηw : η ≤ w.re) (hβ : 1 < β)
    (hwβ : w.re ≤ β) (hy : 1 ≤ y) :
    ‖epsteinField w y‖ ≤ ‖(Real.pi : ℂ)^(w/2)/(2*Complex.Gamma (w/2))‖*
      ((thetaSum 1+1)*thetaMoment (2-β)+thetaSum 1*thetaMoment 0+
        y^(1-η)*thetaMoment η+2/‖w‖+2/(y*‖w-2‖)) := by
  rw [epsteinField,dif_pos (zero_lt_one.trans_le hy),norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_epsteinLambda_le hw2 hη0 hη1 hηw hβ hwβ hy) (norm_nonneg _)

#print axioms originalTail_integrable
#print axioms dualTail_integrable
#print axioms norm_originalTail_le
#print axioms norm_dualTail_le
#print axioms norm_epsteinLambda_le
#print axioms norm_epsteinField_le

#print axioms heatTail_mellin_convergent
#print axioms modified_minus_tail
#print axioms lambda0_heat_tails
#print axioms epsteinLambda_heat_expansion
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeatRepresentation
