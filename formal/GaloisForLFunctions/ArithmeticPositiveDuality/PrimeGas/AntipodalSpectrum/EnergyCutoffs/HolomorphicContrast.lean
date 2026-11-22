import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.AdjacentContrast
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.CriticalPhase
import GaloisForLFunctions.HTGeometry.PrincipalPartMatching
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# Holomorphic response of a matched pair of finite heat measurements

Dividing the heat difference by w−1 cancels the zeta pole analytically.
The physical finite parts give its value at the pole independently.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology

/-- Transfer from the entire function (w−1)ζ(w) to a matched cutoff reading. -/
def contrastTransfer (C : ℕ+) (w : ℂ) : ℂ :=
  -2*(C.val:ℂ)*heat w C*dslope (fun z => heat z C) 1 w/(1-(heat w C)^2)

/-- Holomorphic response of the adjacent comparison, including the removable value at one. -/
def contrastResponse (C : ℕ+) (w : ℂ) : ℂ := _root_.RHTower.zetaPoleUnit w * contrastTransfer C w

private theorem heat_at_one (C : ℕ+) : heat 1 C = (C.val:ℂ)⁻¹ := by
  rw [heat_eq_cpow,Complex.cpow_neg_one]

private theorem heat_analytic (C : ℕ+) (w : ℂ) : AnalyticAt ℂ (fun z => heat z C) w :=
  (analyticAt_id.neg.mul analyticAt_const).cexp

private theorem derivative_at_one (C : ℕ+) :
    deriv (fun z => heat z C) 1 = -(energy C:ℂ)*(C.val:ℂ)⁻¹ := by
  have h := (((hasDerivAt_id (1:ℂ)).neg.mul_const (energy C:ℂ)).cexp).deriv
  change deriv (fun z => heat z C) 1 = heat 1 C * ((-1)*(energy C:ℂ)) at h
  rw [h,heat_at_one]
  ring

private theorem denom_ne {C : ℕ+} (hC : 1 < C.val) {w : ℂ} (hw : 0 < w.re) :
    (1:ℂ)-(heat w C)^2 ≠ 0 := by
  have hq : ‖(heat w C)^2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (heat_contraction C hC w hw) (by norm_num)
  exact sub_ne_zero.mpr fun he => hq.ne (by rw [← he,norm_one])

theorem contrastTransfer_analytic (C : {c : ℕ+ // 1 < c.val}) (w : {z : ℂ // 0 < z.re}) :
    AnalyticAt ℂ (contrastTransfer C.val) w.val := by
  have h := _root_.RHTower.analyticAt_dslope_of_analyticAt (heat_analytic C.val 1) (heat_analytic C.val w.val)
  exact ((analyticAt_const.mul (heat_analytic C.val w.val)).mul h).div
    (analyticAt_const.sub ((heat_analytic C.val w.val).pow 2)) (denom_ne C.property w.property)

theorem contrastResponse_analytic (C : {c : ℕ+ // 1 < c.val}) (w : {z : ℂ // 0 < z.re}) :
    AnalyticAt ℂ (contrastResponse C.val) w.val :=
  (_root_.RHTower.differentiable_zetaPoleUnit.analyticAt w.val).mul (contrastTransfer_analytic C w)

theorem contrastTransfer_one (C : {c : ℕ+ // 1 < c.val}) :
    contrastTransfer C.val 1 = 2*(C.val.val:ℂ)*(Real.log C.val.val:ℂ)/((C.val.val:ℂ)^2-1) := by
  let c : ℂ := C.val.val
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr C.val.ne_zero
  have hc2 : c^2-1 ≠ 0 := sub_ne_zero.mpr (show (C.val.val:ℂ)^2 ≠ 1 by
    exact_mod_cast (one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0)).ne')
  have hd := denom_ne C.property (w := 1) (by norm_num)
  rw [heat_at_one] at hd
  rw [contrastTransfer,dslope_same,derivative_at_one,heat_at_one]
  change -2*c*c⁻¹*(-(energy C.val:ℂ)*c⁻¹)/(1-(c⁻¹)^2) = 2*c*(energy C.val:ℂ)/(c^2-1)
  field_simp [hc,hc2,hd]

theorem contrastResponse_one (C : {c : ℕ+ // 1 < c.val}) :
    contrastResponse C.val 1 = 2*(C.val.val:ℂ)*(Real.log C.val.val:ℂ)/((C.val.val:ℂ)^2-1) := by
  rw [contrastResponse,_root_.RHTower.zetaPoleUnit_one,one_mul,contrastTransfer_one C]

private theorem response_off_one (C : {c : ℕ+ // 1 < c.val}) (w : {z : ℂ // 0 < z.re ∧ z ≠ 1}) :
    let q := heat w.val C.val
    contrastResponse C.val w.val = 2*riemannZeta w.val*q*(1-(C.val.val:ℂ)*q)/(1-q^2) := by
  rw [contrastResponse,_root_.RHTower.zetaPoleUnit_of_ne w.property.2,contrastTransfer,
    dslope_of_ne _ w.property.2,slope_def_field,heat_at_one]
  have hc : (C.val.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.val.ne_zero
  field_simp [hc,sub_ne_zero.mpr w.property.2,denom_ne C.property w.property.1]
  ring

private theorem finite_parts_sub (c L γ : ℂ) (h₁ : c-1 ≠ 0) (h₂ : c^2-1 ≠ 0) :
    2/(c-1)*γ-2*c*L/(c-1)^2-(c+1)*(2/(c^2-1)*γ-2*c^2*(2*L)/(c^2-1)^2) =
      2*c*L/(c^2-1) := by
  field_simp [h₁,h₂]
  ring

/-- The finite heat comparison converges at the zeta pole to a positive, finite value. -/
theorem adjacent_cutoff_at_one (t : ExceptionalTime) (j : ℕ) :
    let C := tailRadix t j
    Tendsto (fun X => adjacentCutoff t j X 1) atTop (𝓝 (2*(C.val:ℂ)*(Real.log C.val:ℂ)/((C.val:ℂ)^2-1))) := by
  let C := tailRadix t j
  let B := tailRadix t (j+1)
  let c : ℂ := C.val
  let d (a : ℕ+) := 2/((a.val:ℂ)-1)
  let k (a : ℕ+) := d a*(Real.eulerMascheroniConstant:ℂ)-2*(a.val:ℂ)*(Real.log a.val:ℂ)/((a.val:ℂ)-1)^2
  have hcp := radix_gt_one t j
  have hc : c-1 ≠ 0 := sub_ne_zero.mpr (show (C.val:ℂ) ≠ 1 by exact_mod_cast hcp.ne')
  have hc2 : c^2-1 ≠ 0 := sub_ne_zero.mpr (show (C.val:ℂ)^2 ≠ 1 by
    exact_mod_cast (one_lt_pow₀ hcp (by norm_num : (2:ℕ) ≠ 0)).ne')
  have hB : B.val = C.val^2 := congrArg PNat.val (tailRadix_succ t j)
  have hd : d C = (c+1)*d B := by
    simp only [d,hB,Nat.cast_pow]
    change 2/(c-1) = (c+1)*(2/(c^2-1))
    field_simp [hc,hc2]
    ring
  have hlog : (Real.log B.val:ℂ) = 2*(Real.log C.val:ℂ) := by
    simp only [hB,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hk : k C-(c+1)*k B = 2*c*(Real.log C.val:ℂ)/(c^2-1) := by
    have hBc : (B.val:ℂ) = c^2 := by rw [hB,Nat.cast_pow]
    simp only [k,d]
    rw [hlog,hBc]
    exact finite_parts_sub c _ _ hc hc2
  have h := (critical_cutoff_finite_part t j).sub ((critical_cutoff_finite_part t (j+1)).const_mul (c+1))
  change Tendsto _ atTop (𝓝 (k C-(c+1)*k B)) at h
  rw [hk] at h
  apply h.congr
  intro X
  change shellCutoff t j X 1-d C*(Real.log X:ℂ)-(c+1)*(shellCutoff t (j+1) X 1-d B*(Real.log X:ℂ)) =
    shellCutoff t j X 1-(c+1)*shellCutoff t (j+1) X 1
  rw [hd]
  ring

theorem adjacent_cutoff_holomorphic_limit (t : ExceptionalTime) (j : ℕ) (w : {z : ℂ // 0 < z.re}) :
    Tendsto (fun X => adjacentCutoff t j X w.val) atTop (𝓝 (contrastResponse (tailRadix t j) w.val)) := by
  let C : {c : ℕ+ // 1 < c.val} := ⟨tailRadix t j,radix_gt_one t j⟩
  rcases eq_or_ne w.val 1 with h | h
  · rw [h,contrastResponse_one C]
    exact adjacent_cutoff_at_one t j
  · rw [response_off_one C ⟨w.val,w.property,h⟩]
    exact adjacent_cutoff_limit t j ⟨w.val,w.property,h⟩

/-- A single transfer loses exactly the nontrivial returns to its heat amplitude at one. -/
theorem contrastTransfer_zero_iff (C : {c : ℕ+ // 1 < c.val}) (w : {z : ℂ // 0 < z.re}) :
    contrastTransfer C.val w.val = 0 ↔ w.val ≠ 1 ∧ heat w.val C.val = heat 1 C.val := by
  have hc : (C.val.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr C.val.ne_zero
  have hq : heat w.val C.val ≠ 0 := Complex.exp_ne_zero _
  have hd := denom_ne C.property w.property
  by_cases he : w.val = 1
  · rw [he,contrastTransfer_one C]
    have hE : (Real.log C.val.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast C.property)).ne'
    have h2 := one_lt_pow₀ C.property (by norm_num : (2:ℕ) ≠ 0)
    have hc2 : (C.val.val:ℂ)^2-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h2.ne')
    exact iff_of_false (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc) hE) hc2) (fun h => h.1 rfl)
  · have hn : -2*(C.val.val:ℂ)*heat w.val C.val ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hc) hq
    rw [and_iff_right he,contrastTransfer,dslope_of_ne _ he,slope_def_field,div_eq_zero_iff,or_iff_left hd,
      mul_eq_zero,or_iff_right hn,div_eq_zero_iff,or_iff_left (sub_ne_zero.mpr he),sub_eq_zero]

/-- Phase returns form the integer frequency lattice with spacing 2π/log C. -/
theorem heat_return_lattice (C : {c : ℕ+ // 1 < c.val}) (w : ℂ) :
    heat w C.val = heat 1 C.val ↔
      ∃ k : ℤ, w = 1+(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)/(energy C.val:ℂ) := by
  have hE : (energy C.val:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast C.property)).ne'
  rw [heat,heat,Complex.exp_eq_exp_iff_exp_sub_eq_one,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨-k,?_⟩
    rw [Int.cast_neg]
    field_simp [hE]
    linear_combination -hk
  · rintro ⟨k,rfl⟩
    refine ⟨-k,?_⟩
    rw [Int.cast_neg]
    field_simp [hE]
    ring

/-- Each nontrivial phase return adds precisely one zero to the analytic divisor. -/
theorem contrastTransfer_order (C : {c : ℕ+ // 1 < c.val}) (w : {z : ℂ // 0 < z.re}) :
    analyticOrderAt (contrastTransfer C.val) w.val =
      if w.val ≠ 1 ∧ heat w.val C.val = heat 1 C.val then 1 else 0 := by
  by_cases hr : w.val ≠ 1 ∧ heat w.val C.val = heat 1 C.val
  · rw [if_pos hr]
    let q (z : ℂ) := heat z C.val
    let u (z : ℂ) := (-2*(C.val.val:ℂ)*q z/(z-1))/(1-(q z)^2)
    let f (z : ℂ) := q z-q 1
    have hq := heat_analytic C.val w.val
    have hd := denom_ne C.property w.property
    have ha : AnalyticAt ℂ u w.val :=
      ((analyticAt_const.mul hq).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hr.1)).div
        (analyticAt_const.sub (hq.pow 2)) hd
    have hu : u w.val ≠ 0 := div_ne_zero (div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr C.val.ne_zero)) (Complex.exp_ne_zero _))
      (sub_ne_zero.mpr hr.1)) hd
    have hlocal : contrastTransfer C.val =ᶠ[𝓝 w.val] u*f := by
      filter_upwards [isOpen_ne.mem_nhds hr.1] with z hz
      simp only [contrastTransfer,dslope_of_ne _ hz,slope_def_field,Pi.mul_apply,u,f,q]
      ring
    have hder := ((((hasDerivAt_id w.val).neg.mul_const (energy C.val:ℂ)).cexp).sub_const (q 1)).deriv
    change deriv f w.val = q w.val*((-1)*(energy C.val:ℂ)) at hder
    have hE : (energy C.val:ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast C.property)).ne'
    have hfA : AnalyticAt ℂ f w.val := hq.sub analyticAt_const
    have hdn : deriv f w.val ≠ 0 := by
      rw [hder]
      exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by norm_num) hE)
    have hf := HTGeometry.analyticOrderAt_eq_one_of_simple_zero hfA (sub_eq_zero.mpr hr.2) hdn
    rw [analyticOrderAt_congr hlocal,analyticOrderAt_mul ha hfA,
      analyticOrderAt_eq_zero.mpr (Or.inr hu),zero_add]
    exact hf
  · rw [if_neg hr]
    exact analyticOrderAt_eq_zero.mpr (Or.inr (fun h => hr ((contrastTransfer_zero_iff C w).mp h)))

/-- On the absolute-convergence boundary the measured divisor consists solely of simple clock returns. -/
theorem boundary_contrast_order (C : {c : ℕ+ // 1 < c.val}) (τ : ℝ) :
    analyticOrderAt (contrastResponse C.val) (⟨1,τ⟩ : ℂ) =
      if (⟨1,τ⟩ : ℂ) ≠ 1 ∧ heat ⟨1,τ⟩ C.val = heat 1 C.val then 1 else 0 := by
  let w : {z : ℂ // 0 < z.re} := ⟨⟨1,τ⟩,zero_lt_one⟩
  have hZ : _root_.RHTower.zetaPoleUnit w.val ≠ 0 := by
    rcases eq_or_ne w.val 1 with he | he
    · rw [he,_root_.RHTower.zetaPoleUnit_one]
      exact one_ne_zero
    · exact _root_.RHTower.zetaPoleUnit_ne_zero he (riemannZeta_ne_zero_of_one_le_re (le_refl 1))
  have h := analyticOrderAt_mul (_root_.RHTower.differentiable_zetaPoleUnit.analyticAt w.val)
    (contrastTransfer_analytic C w)
  change analyticOrderAt (contrastResponse C.val) w.val = _ at h
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hZ),zero_add,contrastTransfer_order C w] at h
  exact h

#print axioms boundary_contrast_order
#print axioms contrastTransfer_order
#print axioms heat_return_lattice
#print axioms contrastResponse_analytic
#print axioms adjacent_cutoff_at_one
#print axioms adjacent_cutoff_holomorphic_limit
#print axioms contrastTransfer_zero_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
