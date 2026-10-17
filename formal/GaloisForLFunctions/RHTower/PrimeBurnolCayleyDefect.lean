import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveSymbol

/-! A literal prime Burnol contraction whose third hereditary defect is rank one. -/

noncomputable section
open Complex Set InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def burnolIdentityAccretiveSymbol : BurnolAccretiveSymbol where
  toFun := id
  analytic := fun _ _ => analyticAt_id
  nonneg := fun _ hz => hz.le

def burnolCayleyFn (z : ℂ) : ℂ := (z-1)/(z+1)

theorem burnolCayley_den_ne_zero {z : ℂ} (hz : 0 < z.re) : z+1 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
  linarith

theorem norm_burnolCayleyFn_lt_one {z : ℂ} (hz : 0 < z.re) :
    ‖burnolCayleyFn z‖ < 1 := by
  rw [burnolCayleyFn,norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (burnolCayley_den_ne_zero hz))).mpr
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.add_re,Complex.add_im,sub_zero,add_zero]
  nlinarith

def primeBurnolCayley : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  1-(2 : ℂ) • burnolIdentityAccretiveSymbol.resolvent

theorem norm_primeBurnolCayley_le : ‖primeBurnolCayley‖ ≤ 1 :=
  burnolIdentityAccretiveSymbol.norm_cayley_le

theorem primeBurnolCayley_feature {z : ℂ} (hz : 0 < z.re) :
    primeBurnolCayley (burnolComplexFeature z hz) =
      burnolCayleyFn z • burnolComplexFeature z hz := by
  change burnolComplexFeature z hz -
    (2 : ℂ) • burnolIdentityAccretiveSymbol.resolvent (burnolComplexFeature z hz) = _
  rw [burnolIdentityAccretiveSymbol.resolvent_feature,smul_smul]
  have hc : 1-2*burnolIdentityAccretiveSymbol.resolventFn z = burnolCayleyFn z := by
    change 1-2*(1+z)⁻¹ = (z-1)/(z+1)
    have hd : 1+z ≠ 0 := by simpa [add_comm] using burnolCayley_den_ne_zero hz
    field_simp [burnolCayley_den_ne_zero hz,hd]
    ring
  rw [← hc,sub_smul,one_smul]

theorem primeBurnolCayley_prime (p : Nat.Primes) :
    primeBurnolCayley (primeLogCriticalLaplaceFeatureL2 p) =
      burnolCayleyFn (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p :=
  (primeBurnol_eigenvalue_iff _ p _).mpr (primeBurnolCayley_feature _)

theorem primeBurnolCayley_pow_feature (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (primeBurnolCayley^n) (burnolComplexFeature z hz) =
      burnolCayleyFn z^n • burnolComplexFeature z hz := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,mul_apply_eq_comp,primeBurnolCayley_feature,map_smul,ih,smul_smul]
      congr 1
      ring

theorem burnol_eq_of_inner_features {x y : BurnolHalfLineL2}
    (h : ∀ (z : ℂ) (hz : 0 < z.re),
      inner ℂ (burnolComplexFeature z hz) x = inner ℂ (burnolComplexFeature z hz) y) :
    x = y := by
  have he : innerSLFlip ℂ x = innerSLFlip ℂ y := by
    apply ContinuousLinearMap.ext_on dense_primeBurnolRawFeature_span
    rintro _ ⟨p,rfl⟩
    exact h _ _
  apply ext_inner_left ℂ
  intro v
  exact DFunLike.congr_fun he v

theorem burnolCayley_kernel_factor {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    1-conj (burnolCayleyFn w)*burnolCayleyFn z =
      2*(z+conj w)/((1+conj w)*(z+1)) := by
  have hw' : 1+conj w ≠ 0 := by
    simpa [add_comm] using burnolCayley_den_ne_zero (show 0 < (conj w).re from hw)
  simp only [burnolCayleyFn,map_div₀,map_sub,map_add,map_one]
  field_simp [burnolCayley_den_ne_zero hz,hw',add_comm (conj w) 1]
  ring

def primeBurnolCayleyDefect : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  1-(3 : ℂ) • (star primeBurnolCayley*primeBurnolCayley) +
    (3 : ℂ) • ((star primeBurnolCayley)^2*primeBurnolCayley^2) -
    (star primeBurnolCayley)^3*primeBurnolCayley^3

def burnolCayleySeed : BurnolHalfLineL2 := burnolComplexFeature 1 (by norm_num)

theorem inner_burnolCayley_hereditary (n : ℕ) {w z : ℂ}
    (hw : 0 < w.re) (hz : 0 < z.re) :
    inner ℂ (burnolComplexFeature w hw)
      (((star primeBurnolCayley)^n*primeBurnolCayley^n) (burnolComplexFeature z hz)) =
      (conj (burnolCayleyFn w)*burnolCayleyFn z)^n *
        (2/(z+conj w)^3) := by
  rw [mul_apply_eq_comp,← star_pow,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,primeBurnolCayley_pow_feature n hw,
    primeBurnolCayley_pow_feature n hz,inner_smul_left,inner_smul_right,
    inner_burnolComplexFeature hw hz,map_pow,mul_pow]
  ring

/-- The third hereditary defect is the actual rank-one seed projection. -/
theorem primeBurnolCayleyDefect_eq_rankOne :
    primeBurnolCayleyDefect = (4 : ℂ) • rankOne ℂ burnolCayleySeed burnolCayleySeed := by
  apply ContinuousLinearMap.ext_on dense_primeBurnolRawFeature_span
  rintro _ ⟨p,rfl⟩
  apply burnol_eq_of_inner_features
  intro w hw
  let z : ℂ := Real.log (p : ℝ)
  have hz : 0 < z.re := Real.log_pos (by exact_mod_cast p.property.one_lt)
  change inner ℂ (burnolComplexFeature w hw)
      (primeBurnolCayleyDefect (burnolComplexFeature z hz)) =
    inner ℂ (burnolComplexFeature w hw)
      (((4 : ℂ) • rankOne ℂ burnolCayleySeed burnolCayleySeed) (burnolComplexFeature z hz))
  have h1 := inner_burnolCayley_hereditary 1 hw hz
  simp only [pow_one] at h1
  simp only [primeBurnolCayleyDefect,sub_apply,add_apply,smul_apply,
    one_apply_eq_self,inner_sub_right,inner_add_right,inner_smul_right,
    h1,inner_burnolCayley_hereditary,inner_burnolComplexFeature hw hz,
    rankOne_apply,burnolCayleySeed]
  rw [inner_burnolComplexFeature (by norm_num : 0 < (1 : ℂ).re) hz,
    inner_burnolComplexFeature hw (by norm_num : 0 < (1 : ℂ).re)]
  simp only [map_one]
  calc
    _ = (1-conj (burnolCayleyFn w)*burnolCayleyFn z)^3 * (2/(z+conj w)^3) := by ring
    _ = _ := by
      rw [burnolCayley_kernel_factor hw hz]
      have hsum : z+conj w ≠ 0 := by
        intro he
        have hr := congrArg Complex.re he
        simp only [Complex.add_re,Complex.conj_re,Complex.zero_re] at hr
        linarith
      have hw' : 1+conj w ≠ 0 := by
        simpa [add_comm] using burnolCayley_den_ne_zero (show 0 < (conj w).re from hw)
      field_simp [hsum,hw',burnolCayley_den_ne_zero hz]
      ring

theorem burnolCayleySeed_inner_self :
    inner ℂ burnolCayleySeed burnolCayleySeed = (1/4 : ℂ) := by
  rw [burnolCayleySeed,inner_burnolComplexFeature]
  norm_num

theorem primeBurnolCayleyDefect_isStarProjection : IsStarProjection primeBurnolCayleyDefect := by
  rw [isStarProjection_iff',primeBurnolCayleyDefect_eq_rankOne]
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    simp only [mul_apply_eq_comp,smul_apply,rankOne_apply,inner_smul_right,
      smul_smul,burnolCayleySeed_inner_self]
    congr 1
    ring
  · rw [star_smul,ContinuousLinearMap.star_eq_adjoint,adjoint_rankOne]
    norm_num

theorem primeBurnolCayleyDefect_ne_zero : primeBurnolCayleyDefect ≠ 0 := by
  rw [primeBurnolCayleyDefect_eq_rankOne]
  exact smul_ne_zero (by norm_num) (rankOne_ne_zero
    (burnolComplexFeature_ne_zero (by norm_num)) (burnolComplexFeature_ne_zero (by norm_num)))

end RHTower
