import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchySchur
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-! The central frequency is the attained maximum of the actual Cauchy
Mellin multiplier for every complex source parameter. The key estimate is
an exact symmetric Gamma-split inequality on `Re z≥1/2`: reflection gives
the boundary value, vertical-ratio bounds control growth, and the
half-plane maximum principle propagates the inequality. Consequently the
sharp central envelope holds throughout the central Mellin weight line. -/

open Complex Set Filter Asymptotics
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerCauchySchur
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyFrequencyMaximum

/-- The symmetric imaginary split of Gamma, relative to its midpoint. -/
def splitRatio (d : ℝ) (z : ℂ) : ℂ :=
  Gamma (z+(d : ℂ)*I)*Gamma (z-(d : ℂ)*I)/Gamma z^2

private theorem gamma_avoids_poles {z : ℂ} (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re,natCast_re] at h
  linarith only [hz,h,Nat.cast_nonneg (α := ℝ) n]

/-- The split quotient is holomorphic on the right half-plane. -/
theorem differentiableAt_splitRatio (d : ℝ) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (splitRatio d) z := by
  have hp : 0 < (z+(d : ℂ)*I).re := by simpa using hz
  have hm : 0 < (z-(d : ℂ)*I).re := by simpa using hz
  have hA := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles hp)).comp z
    (differentiableAt_id.add_const ((d : ℂ)*I))
  have hB := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles hm)).comp z
    (differentiableAt_id.sub_const ((d : ℂ)*I))
  have hC := Complex.differentiableAt_Gamma _ (gamma_avoids_poles hz)
  exact (hA.mul hB).div (hC.pow 2) (pow_ne_zero 2 (Complex.Gamma_ne_zero (gamma_avoids_poles hz)))

private theorem cosh_split (y d : ℝ) :
    Real.cosh (y+d)*Real.cosh (y-d)=Real.cosh y^2+Real.sinh d^2 := by
  rw [Real.cosh_add,Real.cosh_sub]
  calc
    _ = Real.cosh y^2*Real.cosh d^2-Real.sinh y^2*Real.sinh d^2 := by ring
    _ = _ := by rw [Real.cosh_sq y,Real.cosh_sq d]; ring

/-- Reflection gives the exact modulus on the half-line boundary. -/
theorem split_boundary_norm_sq (d y : ℝ) :
    ‖splitRatio d (1/2+(y : ℂ)*I)‖^2=
      Real.cosh (Real.pi*y)^2/(Real.cosh (Real.pi*y)^2+Real.sinh (Real.pi*d)^2) := by
  have hp : (1/2+(y : ℂ)*I)+(d : ℂ)*I=1/2+((y+d : ℝ) : ℂ)*I := by push_cast; ring
  have hm : (1/2+(y : ℂ)*I)-(d : ℂ)*I=1/2+((y-d : ℝ) : ℂ)*I := by push_cast; ring
  rw [splitRatio,norm_div,norm_mul,norm_pow,div_pow,mul_pow,
    show (‖Gamma (1/2+(y : ℂ)*I)‖^2)^2=‖Gamma (1/2+(y : ℂ)*I)‖^2*‖Gamma (1/2+(y : ℂ)*I)‖^2 by ring,
    hp,hm,GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq,
    GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq,
    GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq]
  have hC : Real.cosh (Real.pi*(y+d))*Real.cosh (Real.pi*(y-d))=
      Real.cosh (Real.pi*y)^2+Real.sinh (Real.pi*d)^2 := by
    rw [mul_add,mul_sub,cosh_split]
  have halg (A B C P : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hP : P ≠ 0) :
      ((P/A)*(P/B))/((P/C)*(P/C))=C^2/(A*B) := by field_simp
  rw [halg _ _ _ _ (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
    (Real.cosh_pos _).ne' Real.pi_ne_zero,hC]

/-- Every symmetric split has boundary modulus at most one. -/
theorem split_boundary_norm_le_one (d y : ℝ) : ‖splitRatio d (1/2+(y : ℂ)*I)‖ ≤ 1 := by
  have hden : 0 < Real.cosh (Real.pi*y)^2+Real.sinh (Real.pi*d)^2 := by positivity
  have hsq : ‖splitRatio d (1/2+(y : ℂ)*I)‖^2 ≤ 1 := by
    rw [split_boundary_norm_sq]
    exact (div_le_one hden).mpr (le_add_of_nonneg_right (sq_nonneg _))
  nlinarith only [hsq,norm_nonneg (splitRatio d (1/2+(y : ℂ)*I))]

private theorem gamma_real_ratio_sq {x : ℝ} (hx : 1/2 ≤ x) (y : ℝ) :
    Real.Gamma x^2/‖Gamma ((x : ℂ)+(y : ℂ)*I)‖^2 ≤ Real.cosh (Real.pi*y) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hB : 0 < ‖Gamma ((x : ℂ)+(y : ℂ)*I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero (gamma_avoids_poles (by simpa using hx0)))
  have hA : 0 < ‖Gamma (1/2+(y : ℂ)*I)‖ := by
    apply norm_pos_iff.mpr
    exact Complex.Gamma_ne_zero (gamma_avoids_poles (by norm_num))
  have h := _root_.HTGeometry.norm_Gamma_mul_Gamma_le (a := 1/2) (b := x) (by norm_num) hx y
  have hratio : Real.Gamma x/‖Gamma ((x : ℂ)+(y : ℂ)*I)‖ ≤
      Real.Gamma (1/2)/‖Gamma (1/2+(y : ℂ)*I)‖ := by
    apply (div_le_div_iff₀ hB hA).mpr
    simpa only [ofReal_div,ofReal_one,ofReal_ofNat,mul_comm] using h
  have hs := (sq_le_sq₀ (div_nonneg (Real.Gamma_pos_of_pos hx0).le hB.le)
    (div_nonneg (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ)<1/2)).le hA.le)).mpr hratio
  rw [div_pow,div_pow,Real.Gamma_one_half_eq,Real.sq_sqrt Real.pi_pos.le,
    GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq] at hs
  have hcancel : Real.pi/(Real.pi/Real.cosh (Real.pi*y))=Real.cosh (Real.pi*y) := by
    field_simp
  simpa only [hcancel] using hs

/-- A half-line comparison controls growth uniformly in both real part and imaginary split. -/
theorem split_norm_le_cosh (d : ℝ) {z : ℂ} (hz : 1/2 ≤ z.re) :
    ‖splitRatio d z‖ ≤ Real.cosh (Real.pi*z.im) := by
  have hz0 : 0 < z.re := by linarith only [hz]
  have hp := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
    (s := z+(d : ℂ)*I) (by simpa using hz0)
  have hm := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
    (s := z-(d : ℂ)*I) (by simpa using hz0)
  simp only [add_re,sub_re,mul_I_re,ofReal_im,neg_zero,add_zero,sub_zero] at hp hm
  have hnum : ‖Gamma (z+(d : ℂ)*I)‖*‖Gamma (z-(d : ℂ)*I)‖ ≤ Real.Gamma z.re^2 := by
    simpa only [pow_two] using mul_le_mul hp hm (norm_nonneg _) (Real.Gamma_pos_of_pos hz0).le
  rw [splitRatio,norm_div,norm_mul,norm_pow]
  refine (div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans ?_
  simpa only [Complex.re_add_im] using gamma_real_ratio_sq hz z.im

/-- The split ratio is bounded by one on the real half-axis. -/
theorem split_norm_real_le_one (d : ℝ) {x : ℝ} (hx : 1/2 ≤ x) :
    ‖splitRatio d (x : ℂ)‖ ≤ 1 := by
  simpa only [ofReal_im,mul_zero,Real.cosh_zero] using split_norm_le_cosh d (z := (x : ℂ)) hx

private theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  have hp := Real.exp_le_exp.mpr (le_abs_self y)
  have hm := Real.exp_le_exp.mpr (neg_le_abs y)
  linarith only [hp,hm]

/-- The imaginary symmetric Gamma split is contractive at every abscissa at least one half. -/
theorem split_norm_le_one (d : ℝ) {z : ℂ} (hz : 1/2 ≤ z.re) : ‖splitRatio d z‖ ≤ 1 := by
  let f : ℂ → ℂ := fun v => splitRatio d (v+1/2)
  have hf {v : ℂ} (hv : -1/2 < v.re) : DifferentiableAt ℂ f v := by
    have hv0 : 0 < (v+1/2).re := by simp; linarith only [hv]
    exact (differentiableAt_splitRatio d hv0).comp v (differentiableAt_id.add_const (1/2 : ℂ))
  have hd : DiffContOnCl ℂ f {v : ℂ | 0 < v.re} := by
    constructor
    · intro v hv
      have hv0 : 0 < v.re := hv
      exact (hf (by linarith only [hv0])).differentiableWithinAt
    · intro v hv
      have hcl : closure {v : ℂ | 0 < v.re} ⊆ {v : ℂ | 0 ≤ v.re} :=
        closure_minimal (fun v hv => show 0 ≤ v.re from le_of_lt hv)
          (isClosed_le continuous_const Complex.continuous_re)
      have hv0 : 0 ≤ v.re := hcl hv
      exact (hf (by linarith only [hv0])).continuousAt.continuousWithinAt
  have hO : f =O[Bornology.cobounded ℂ ⊓ principal {v : ℂ | 0 < v.re}]
      (fun v : ℂ => Real.exp (Real.pi*‖v‖)) := by
    apply IsBigO.of_bound 1
    filter_upwards [mem_inf_of_right (mem_principal_self {v : ℂ | 0 < v.re})] with v hv
    rw [one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hv0 : 0 < v.re := hv
    have h := split_norm_le_cosh d (z := v+1/2) (by simp; linarith only [hv0])
    simp only [add_im,div_ofNat_im,one_im,zero_div,add_zero] at h
    refine h.trans ((cosh_le_exp_abs _).trans ?_)
    apply Real.exp_le_exp.mpr
    rw [abs_mul,abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm v) Real.pi_pos.le
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[Bornology.cobounded ℂ ⊓ principal {v : ℂ | 0 < v.re}]
        (fun v : ℂ => Real.exp (B*‖v‖^c)) := by
    exact ⟨1,by norm_num,Real.pi,by simpa only [Real.rpow_one] using hO⟩
  have hreal : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => ‖f (x : ℂ)‖) := by
    have hR : (fun x : ℝ => f (x : ℂ)) =O[atTop] (fun _ : ℝ => (1 : ℂ)) := by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h := split_norm_real_le_one d (x := x+1/2) (by linarith only [hx])
      simpa only [f,ofReal_add,ofReal_div,ofReal_one,ofReal_ofNat,norm_one,mul_one] using h
    exact hR.isBoundedUnder_le
  have hb (y : ℝ) : ‖f ((y : ℂ)*I)‖ ≤ 1 := by
    simpa only [f,add_comm] using split_boundary_norm_le_one d y
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hreal hb
    (z := z-1/2) (by simp; linarith only [hz])
  simpa only [f,sub_add_cancel] using h

#print axioms differentiableAt_splitRatio
#print axioms split_boundary_norm_sq
#print axioms split_boundary_norm_le_one
#print axioms split_norm_le_cosh
#print axioms split_norm_real_le_one
#print axioms split_norm_le_one
/-- A Mellin-frequency displacement is exactly a symmetric imaginary split of Gamma. -/
theorem symbol_frequency_split {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    symbol w (w/2+(ξ : ℂ)*I)=symbol w (w/2)*splitRatio (ξ/2) ((w+2)/4) := by
  have ha : (w/2+(ξ : ℂ)*I+1)/2=(w+2)/4+((ξ/2 : ℝ) : ℂ)*I := by push_cast; ring
  have hb : (w+1-(w/2+(ξ : ℂ)*I))/2=(w+2)/4-((ξ/2 : ℝ) : ℂ)*I := by push_cast; ring
  have hc : 0 < ((w+2)/4).re := by simp; linarith only [hw]
  have hC : Gamma ((w+2)/4) ≠ 0 := Complex.Gamma_ne_zero (gamma_avoids_poles hc)
  rw [MayerCauchyBoundaryAmplification.symbol_half,splitRatio,symbol,ha,hb]
  have halg (A B C D : ℂ) (hC : C ≠ 0) : A*B/D=(C^2/D)*(A*B/C^2) := by field_simp
  exact halg _ _ _ _ hC

/-- For every complex source parameter, the central Mellin frequency maximizes the symbol. -/
theorem norm_symbol_frequency_le {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    ‖symbol w (w/2+(ξ : ℂ)*I)‖ ≤ ‖symbol w (w/2)‖ := by
  rw [symbol_frequency_split hw,norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact split_norm_le_one (ξ/2) (by simp; linarith only [hw])

/-- Every frequency on the central weight line is an absolutely convergent Mellin integral. -/
theorem frequency_hasMellin {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    HasMellin (cauchyKernel w) (w/2+(ξ : ℂ)*I) (symbol w (w/2+(ξ : ℂ)*I)) := by
  have hr : (w/2+(ξ : ℂ)*I).re=w.re/2 := by simp
  exact cauchyKernel_hasMellin hw (by rw [hr]; linarith only [hw])
    (by rw [hr]; linarith only [hw])

/-- The actual central value is the attained maximum over all central-weight Mellin frequencies. -/
theorem norm_mellin_frequency_le {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    ‖mellin (cauchyKernel w) (w/2+(ξ : ℂ)*I)‖ ≤ ‖mellin (cauchyKernel w) (w/2)‖ := by
  have h0 := (frequency_hasMellin hw 0).2
  simp only [ofReal_zero,zero_mul,add_zero] at h0
  rw [(frequency_hasMellin hw ξ).2,h0]
  exact norm_symbol_frequency_le hw ξ

/-- The central Mellin multiplier is the exact maximum, not merely an upper bound. -/
theorem frequency_norm_isGreatest {w : ℂ} (hw : 0 < w.re) :
    IsGreatest (Set.range (fun ξ : ℝ => ‖mellin (cauchyKernel w) (w/2+(ξ : ℂ)*I)‖))
      ‖mellin (cauchyKernel w) (w/2)‖ := by
  constructor
  · exact ⟨0,by simp⟩
  · rintro y ⟨ξ,rfl⟩
    exact norm_mellin_frequency_le hw ξ

/-- The sharp central envelope bounds every Mellin frequency on the central weight line. -/
theorem norm_mellin_frequency_lt {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    ‖mellin (cauchyKernel w) (w/2+(ξ : ℂ)*I)‖ < (2 : ℝ)^((1-w.re)/2) :=
  lt_of_le_of_lt (norm_mellin_frequency_le hw ξ) (norm_mellin_half_lt hw)

/-- Every frequency is strictly contractive at and above spectral abscissa one. -/
theorem frequency_contractive {w : ℂ} (hw : 1 ≤ w.re) (ξ : ℝ) :
    ‖mellin (cauchyKernel w) (w/2+(ξ : ℂ)*I)‖ < 1 :=
  lt_of_le_of_lt (norm_mellin_frequency_le (lt_of_lt_of_le zero_lt_one hw) ξ)
    (central_contractive hw)

#print axioms symbol_frequency_split
#print axioms norm_symbol_frequency_le
#print axioms frequency_hasMellin
#print axioms norm_mellin_frequency_le
#print axioms frequency_norm_isGreatest
#print axioms norm_mellin_frequency_lt
#print axioms frequency_contractive

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyFrequencyMaximum
