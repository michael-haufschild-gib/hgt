import GaloisForLFunctions.SquareRootThreshold.SechRectangleMultiplicity
import GaloisForLFunctions.SquareRootThreshold.SechHorizontalExhaustion
import GaloisForLFunctions.ConjugateDiagonalGeometry.ResidueUnitBoundaryConvolution
import GaloisForLFunctions.RHTower.ZetaOffLineWeightedDensity

/-!
# The full sech boundary bounds each horizontal zero fibre

Positive finite-rectangle residue sums survive an exhaustion along actual
zero-free horizontal edges. The vertical integrals converge absolutely, so
no infinite divisor sum is needed.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

private theorem sech_vertical_translate (a T σ y : ℝ) :
    sechStripWeight a T ((σ : ℂ)+(y : ℂ)*I) =
      sechStripWeight a 0 ((σ : ℂ)+((y-T : ℝ) : ℂ)*I) := by
  unfold sechStripWeight
  congr 2
  push_cast
  ring

private theorem integrable_sech_mul_logarithmic {a σ T C : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hσ : |σ-1/2| < a) (hT : 2 ≤ |T|)
    (hf : Continuous f) (hC : 0 ≤ C) (hbound : ∀ y, ‖f y‖ ≤ C*Real.log (2+|y|)) :
    Integrable (fun y : ℝ => sechStripWeight a T ((σ : ℂ)+(y : ℂ)*I)*f y) := by
  have hline : (σ : ℂ) = 1/2+((σ-1/2 : ℝ) : ℂ) := by push_cast; ring
  have hweight := (integrable_norm_sechStripWeight_vertical_weight ha hσ).comp_sub_right T
  have hlog : 0 < Real.log |T| := Real.log_pos (by linarith only [hT])
  have hcont : Continuous (fun y : ℝ => sechStripWeight a T ((σ : ℂ)+(y : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ((analyticOnNhd_sechStripWeight ha T _ (by simpa using hσ)).continuousAt).comp
      (by fun_prop)
  apply (hweight.const_mul (C*Real.log |T|)).mono' (hcont.mul hf).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  have hr := log_height_translate_ratio_le (u := y-T) hT
  rw [show T+(y-T)=y by ring] at hr
  have hh := (div_le_iff₀ hlog).mp hr
  have hb := (hbound y).trans (mul_le_mul_of_nonneg_left hh hC)
  rw [norm_mul,sech_vertical_translate,hline]
  have hn := mul_le_mul_of_nonneg_left hb
    (norm_nonneg (sechStripWeight a 0 (1/2+((σ-1/2 : ℝ) : ℂ)+((y-T : ℝ) : ℂ)*I)))
  convert hn using 1 <;> ring

private theorem integral_sech_translate (a T b : ℝ) (f : ℝ → ℂ) :
    (∫ y : ℝ, sechStripWeight a T (((1/2+b : ℝ) : ℂ)+(y : ℂ)*I)*f y) =
      ∫ u : ℝ, sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I)*f (T+u) := by
  rw [← integral_add_left_eq_self
    (fun y : ℝ => sechStripWeight a T (((1/2+b : ℝ) : ℂ)+(y : ℂ)*I)*f y) T]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  rw [sech_vertical_translate]
  congr 2 <;> push_cast <;> ring

/-- Every finite set of zeros at height `T` is bounded by the full vertical
boundary term, with its exact analytic multiplicities. -/
theorem sum_fibre_multiplicity_mul_sech_le_boundary {a b T : ℝ}
    (hb : (3:ℝ)/8 < b) (hbhalf : b < 1/2) (hba : b < a) (hT : 2 ≤ |T|)
    (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, 0 < ρ.re ∧ riemannZeta ρ = 0 ∧ ρ.im = T) :
    (∑ ρ ∈ F, ((analyticOrderAt zetaResidueUnit ρ).toNat : ℝ) * (sechStripWeight a T ρ).re) ≤
      (sechResidueUnitBoundary a b T).re/(2*Real.pi) := by
  have hb0 : 0 < b := by linarith only [hb]
  have ha : 0 < a := hb0.trans hba
  have hr : (7:ℝ)/8 < 1/2+b := by linarith only [hb]
  have hr1 : 1/2+b < 1 := by linarith only [hbhalf]
  have hl0 : 0 < 1/2-b := by linarith only [hbhalf]
  have hl : 1/2-b < (1:ℝ)/8 := by linarith only [hb]
  have hab : |b| < a := by rwa [abs_of_pos hb0]
  obtain ⟨Cr,hCr,hgrowthr⟩ := exists_residueUnit_right_boundary_log_bound hr hr1
  obtain ⟨Cl,hCl,hgrowthl⟩ := exists_residueUnit_left_boundary_log_bound hl0 hl
  have hir := integrable_sech_mul_logarithmic ha
    (σ := 1/2+b) (by simpa only [add_sub_cancel_left] using hab) hT
    (continuous_residueUnit_right_boundary hr hr1) hCr hgrowthr
  have hil := integrable_sech_mul_logarithmic ha
    (σ := 1/2-b) (by simpa only [show 1/2-b-1/2 = -b by ring,abs_neg] using hab) hT
    (continuous_residueUnit_left_boundary hl0 hl) hCl hgrowthl
  obtain ⟨lo,hi,hlolim,hhilim,hlohi,hzero,hbotlim,htoplim⟩ :=
    exists_sech_horizontal_exhaustion hb0 hbhalf hba T
  let zlo (n : ℕ) : ℂ := ((1/2-b : ℝ) : ℂ)+(lo n : ℂ)*I
  let zhi (n : ℕ) : ℂ := ((1/2+b : ℝ) : ℂ)+(hi n : ℂ)*I
  let g (z : ℂ) := sechStripWeight a T z*logDeriv zetaResidueUnit z
  have hzlo (n : ℕ) : (zlo n).re = 1/2-b ∧ (zlo n).im = lo n := by simp [zlo]
  have hzhi (n : ℕ) : (zhi n).re = 1/2+b ∧ (zhi n).im = hi n := by simp [zhi]
  have hvl := intervalIntegral_tendsto_integral hil hlolim hhilim
  have hvr := intervalIntegral_tendsto_integral hir hlolim hhilim
  have hcontour : Tendsto (fun n => rectIntegral g (zlo n) (zhi n)) atTop
      (𝓝 (I*sechResidueUnitBoundary a b T)) := by
    have hh := ((hbotlim.sub htoplim).add (hvr.const_smul I)).sub (hvl.const_smul I)
    have heqr := integral_sech_translate a T b
      (fun y => logDeriv zetaResidueUnit (((1/2+b : ℝ) : ℂ)+(y : ℂ)*I))
    have heql := integral_sech_translate a T (-b)
      (fun y => logDeriv zetaResidueUnit (((1/2-b : ℝ) : ℂ)+(y : ℂ)*I))
    simp only [add_neg_eq_sub] at heql
    rw [heqr,heql] at hh
    convert hh using 1
    · funext n
      simp only [rectIntegral,g,(hzlo n).1,(hzlo n).2,(hzhi n).1,(hzhi n).2]
    · simp only [sub_self,zero_add,smul_eq_mul,sechResidueUnitBoundary]
      congr 1
      ring
  have himlim := (Complex.continuous_im.continuousAt.tendsto.comp hcontour).div_const (2*Real.pi)
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] at himlim
  apply neg_le_neg_iff.mp
  apply le_of_tendsto himlim.neg
  filter_upwards [hlolim.eventually (eventually_le_atBot T),
    hhilim.eventually (eventually_ge_atTop T)] with n hnlo hnhi
  apply neg_le_neg
  have hre : (zlo n).re < (zhi n).re := by rw [(hzlo n).1,(hzhi n).1]; linarith only [hb0]
  have him : (zlo n).im < (zhi n).im := by rw [(hzlo n).2,(hzhi n).2]; exact hlohi n
  have hleftdepth : |(zlo n).re-1/2| ≤ b := by
    rw [(hzlo n).1]
    have he : 1/2-b-1/2 = -b := by ring
    rw [he,abs_neg,abs_of_pos hb0]
  have hrightdepth : |(zhi n).re-1/2| ≤ b := by
    rw [(hzhi n).1,add_sub_cancel_left,abs_of_pos hb0]
  apply sum_multiplicity_mul_sechStripWeight_le_rectangle hb0.le hba hre him
    hleftdepth hrightdepth
  · intro x hx
    rw [(hzlo n).1,(hzhi n).1,uIcc_of_le (by linarith only [hb0])] at hx
    rw [(hzlo n).2]
    exact (hzero n x hx).1
  · intro x hx
    rw [(hzlo n).1,(hzhi n).1,uIcc_of_le (by linarith only [hb0])] at hx
    rw [(hzhi n).2]
    exact (hzero n x hx).2
  · intro y _
    rw [(hzhi n).1]
    exact residueUnit_right_boundary_ne_zero hr hr1 y
  · intro y _
    rw [(hzlo n).1]
    exact residueUnit_left_boundary_ne_zero hl0 hl y
  · intro ρ hρ
    obtain ⟨hρre,hρzero,hρim⟩ := hF ρ hρ
    have hstrip := riemannZeta_zero_mem_quasiRH_strip hρre hρzero
    apply mem_zetaResidueUnitClosedRectangleZeros.mpr
    constructor
    · apply Complex.mem_reProdIm.mpr
      rw [(hzlo n).1,(hzlo n).2,(hzhi n).1,(hzhi n).2,
        uIcc_of_le (by linarith only [hb0]),uIcc_of_le (hlohi n).le]
      refine ⟨⟨by linarith only [hstrip.1,hb],by linarith only [hstrip.2,hb]⟩,?_⟩
      rw [hρim]
      exact ⟨hnlo,hnhi⟩
    · have hs : ρ ≠ 1 := by
        intro he
        have hh := congrArg Complex.im he
        rw [hρim,Complex.one_im] at hh
        rw [hh,abs_zero] at hT
        norm_num at hT
      rw [(zetaResidueUnit_eventuallyEq hs).eq_of_nhds,hρzero,mul_zero]

/-- The complete weighted horizontal fibre has coefficient `a/π` at every
sufficiently large absolute height. The finite-set formulation includes every
finite collection of zeros on the fibre without a summability premise. -/
theorem exists_fibre_sech_multiplicity_bound {a ε : ℝ}
    (ha : (3:ℝ)/8 < a) (hahalf : a < 1/2) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ |T| → ∀ F : Finset ℂ,
      (∀ ρ ∈ F, 0 < ρ.re ∧ riemannZeta ρ = 0 ∧ ρ.im = T) →
      (∑ ρ ∈ F, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        (Real.cos (Real.pi/(2*a)*(ρ.re-1/2)))⁻¹) ≤
          (a/Real.pi+ε)*Real.log |T| := by
  let b := ((3:ℝ)/8+a)/2
  have hb : (3:ℝ)/8 < b := by dsimp [b]; linarith only [ha]
  have hba : b < a := by dsimp [b]; linarith only [ha]
  have hbhalf : b < 1/2 := hba.trans hahalf
  have hlim := tendsto_sechResidueUnitBoundary_log_normalized hb hbhalf hba
  have he := hlim.eventually (Iio_mem_nhds (show a/Real.pi < a/Real.pi+ε by linarith only [hε]))
  obtain ⟨U,hU⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨max 2 U,le_max_left _ _,fun T hT F hF => ?_⟩
  have ht2 : 2 ≤ |T| := (le_max_left _ _).trans hT
  have htU : U ≤ |T| := (le_max_right _ _).trans hT
  have hbnd := hU |T| htU T rfl
  rw [← div_div] at hbnd
  have hlog : 0 < Real.log |T| := Real.log_pos (by linarith only [ht2])
  have hmain := (div_lt_iff₀ hlog).mp hbnd
  calc
    _ = ∑ ρ ∈ F, ((analyticOrderAt zetaResidueUnit ρ).toNat : ℝ) *
        (sechStripWeight a T ρ).re := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hs : ρ ≠ 1 := by
        intro heq
        have hi := congrArg Complex.im heq
        rw [(hF ρ hρ).2.2,Complex.one_im] at hi
        rw [hi,abs_zero] at ht2
        norm_num at ht2
      rw [analyticOrderAt_zetaResidueUnit_eq_zeta hs,
        sechStripWeight_same_height a T (hF ρ hρ).2.2,Complex.ofReal_re]
    _ ≤ (sechResidueUnitBoundary a b T).re/(2*Real.pi) :=
      sum_fibre_multiplicity_mul_sech_le_boundary hb hbhalf hba ht2 F hF
    _ ≤ _ := hmain.le

/-- Critical-line zeta multiplicities have upper logarithmic coefficient `3/(8π)`. -/
theorem exists_critical_zeta_multiplicity_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ |T| →
      riemannZeta (1/2+(T : ℂ)*I) = 0 →
      ((analyticOrderAt riemannZeta (1/2+(T : ℂ)*I)).toNat : ℝ) ≤
        (3/(8*Real.pi)+ε)*Real.log |T| := by
  let δ := min (1/16 : ℝ) (ε*Real.pi/2)
  let a := (3:ℝ)/8+δ
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδlo : δ ≤ 1/16 := min_le_left _ _
  have hδhi : δ ≤ ε*Real.pi/2 := min_le_right _ _
  have ha : (3:ℝ)/8 < a := by dsimp [a]; linarith only [hδ]
  have hahalf : a < 1/2 := by dsimp [a]; linarith only [hδlo]
  obtain ⟨T₀,hT₀,hbound⟩ := exists_fibre_sech_multiplicity_bound ha hahalf
    (show 0 < ε/2 by positivity)
  refine ⟨T₀,hT₀,fun T hT hz => ?_⟩
  have hf : ∀ ρ ∈ ({1/2+(T : ℂ)*I} : Finset ℂ),
      0 < ρ.re ∧ riemannZeta ρ = 0 ∧ ρ.im = T := by
    intro ρ hρ
    rw [Finset.mem_singleton] at hρ
    subst ρ
    exact ⟨by norm_num,hz,by simp⟩
  have hh := hbound T hT _ hf
  have hs : ((analyticOrderAt riemannZeta (1/2+(T : ℂ)*I)).toNat : ℝ) ≤
      (a/Real.pi+ε/2)*Real.log |T| := by simpa using hh
  have hδpi : δ/Real.pi ≤ ε/2 := (div_le_iff₀ Real.pi_pos).mpr (by linarith only [hδhi])
  have he : a/Real.pi = 3/(8*Real.pi)+δ/Real.pi := by
    dsimp [a]
    field_simp <;> ring
  have hcoef : a/Real.pi+ε/2 ≤ 3/(8*Real.pi)+ε := by rw [he]; linarith only [hδpi]
  exact hs.trans (mul_le_mul_of_nonneg_right hcoef
    (Real.log_nonneg (by linarith only [hT₀.trans hT])))

/-- Completion preserves the same critical-line multiplicity bound. -/
theorem exists_critical_xi_multiplicity_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ |T| →
      xi (1/2+(T : ℂ)*I) = 0 →
      ((analyticOrderAt xi (1/2+(T : ℂ)*I)).toNat : ℝ) ≤
        (3/(8*Real.pi)+ε)*Real.log |T| := by
  obtain ⟨T₀,hT₀,hbound⟩ := exists_critical_zeta_multiplicity_bound hε
  refine ⟨T₀,hT₀,fun T hT hz => ?_⟩
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip (by constructor <;> norm_num)]
  exact hbound T hT (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hz).1

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.sum_fibre_multiplicity_mul_sech_le_boundary
#print axioms GaloisForLFunctions.SquareRootThreshold.exists_fibre_sech_multiplicity_bound
#print axioms GaloisForLFunctions.SquareRootThreshold.exists_critical_zeta_multiplicity_bound
#print axioms GaloisForLFunctions.SquareRootThreshold.exists_critical_xi_multiplicity_bound
