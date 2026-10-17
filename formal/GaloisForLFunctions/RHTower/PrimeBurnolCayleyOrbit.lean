import GaloisForLFunctions.RHTower.PrimeBurnolCayleyDefect
import Mathlib.Analysis.SpecificLimits.Normed

/-! Every literal Burnol feature has a norm-convergent expansion in one adjoint orbit. -/

noncomputable section
open Complex Set Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def burnolCayleyOrbit (n : ℕ) : BurnolHalfLineL2 :=
  ((star primeBurnolCayley)^n) burnolCayleySeed

theorem norm_burnolCayleyOrbit_le (n : ℕ) : ‖burnolCayleyOrbit n‖ ≤ ‖burnolCayleySeed‖ := by
  have hs : ‖star primeBurnolCayley‖ ≤ 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map]
    exact norm_primeBurnolCayley_le
  induction n with
  | zero => simp [burnolCayleyOrbit]
  | succ n ih =>
      change ‖((star primeBurnolCayley)^(n+1)) burnolCayleySeed‖ ≤ _
      rw [pow_succ',mul_apply_eq_comp]
      change ‖(star primeBurnolCayley) (burnolCayleyOrbit n)‖ ≤ _
      calc
        _ ≤ ‖star primeBurnolCayley‖*‖burnolCayleyOrbit n‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1*‖burnolCayleyOrbit n‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
        _ ≤ ‖burnolCayleySeed‖ := by simpa using ih

theorem inner_burnolComplexFeature_cayleyOrbit (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    inner ℂ (burnolComplexFeature w hw) (burnolCayleyOrbit n) =
      conj (burnolCayleyFn w)^n * (2/(1+conj w)^3) := by
  rw [burnolCayleyOrbit,← star_pow,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,primeBurnolCayley_pow_feature n hw,
    inner_smul_left,map_pow]
  congr 1
  exact inner_burnolComplexFeature hw (by norm_num)

def burnolCayleySeriesTerm (z : ℂ) (n : ℕ) : BurnolHalfLineL2 :=
  (((n+2).choose 2 : ℂ)*burnolCayleyFn z^n) • burnolCayleyOrbit n

theorem summable_burnolCayleySeriesTerm {z : ℂ} (hz : 0 < z.re) :
    Summable (burnolCayleySeriesTerm z) := by
  have hr : ‖(‖burnolCayleyFn z‖ : ℝ)‖ < 1 := by
    simpa only [norm_norm] using norm_burnolCayleyFn_lt_one hz
  apply ((hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr).summable.mul_right
    ‖burnolCayleySeed‖).of_norm_bounded
  intro n
  simp only [burnolCayleySeriesTerm,norm_smul,norm_mul,norm_natCast,norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_burnolCayleyOrbit_le n) (by positivity)

theorem inner_burnolCayleySeries {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    inner ℂ (burnolComplexFeature w hw) (∑' n, burnolCayleySeriesTerm z n) =
      (1/(1-conj (burnolCayleyFn w)*burnolCayleyFn z)^3) * (2/(1+conj w)^3) := by
  have he := (innerSL ℂ (burnolComplexFeature w hw)).map_tsum
    (summable_burnolCayleySeriesTerm hz)
  change inner ℂ (burnolComplexFeature w hw) (∑' n, burnolCayleySeriesTerm z n) = _ at he
  rw [he]
  have hr : ‖conj (burnolCayleyFn w)*burnolCayleyFn z‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    calc
      _ ≤ 1*‖burnolCayleyFn z‖ := mul_le_mul_of_nonneg_right
        (norm_burnolCayleyFn_lt_one hw).le (norm_nonneg _)
      _ < 1 := by simpa using norm_burnolCayleyFn_lt_one hz
  calc
    _ = ∑' n : ℕ, (((n+2).choose 2 : ℂ) *
          (conj (burnolCayleyFn w)*burnolCayleyFn z)^n) * (2/(1+conj w)^3) := by
      apply tsum_congr
      intro n
      change inner ℂ (burnolComplexFeature w hw) (burnolCayleySeriesTerm z n) = _
      rw [burnolCayleySeriesTerm,inner_smul_right,inner_burnolComplexFeature_cayleyOrbit n hw,
        mul_pow]
      ring
    _ = _ := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_right
      (2/(1+conj w)^3) |>.tsum_eq

/-- Every half-plane feature is reconstructed from the literal adjoint seed orbit. -/
theorem burnolComplexFeature_eq_cayleySeries {z : ℂ} (hz : 0 < z.re) :
    burnolComplexFeature z hz = (8/(z+1)^3 : ℂ) • ∑' n, burnolCayleySeriesTerm z n := by
  apply burnol_eq_of_inner_features
  intro w hw
  rw [inner_smul_right,inner_burnolCayleySeries hw hz,inner_burnolComplexFeature hw hz,
    burnolCayley_kernel_factor hw hz]
  have hsum : z+conj w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.conj_re,Complex.zero_re] at hr
    linarith
  have hw' : 1+conj w ≠ 0 := by
    simpa [add_comm] using burnolCayley_den_ne_zero (show 0 < (conj w).re from hw)
  field_simp [hsum,hw',burnolCayley_den_ne_zero hz]
  ring

/-- Cyclicity is a consequence of literal feature reconstruction, not an admission premise. -/
theorem dense_burnolCayleyOrbit_span :
    Dense (Submodule.span ℂ (Set.range burnolCayleyOrbit) : Set BurnolHalfLineL2) := by
  let V := Submodule.span ℂ (Set.range burnolCayleyOrbit)
  have hfeature (z : ℂ) (hz : 0 < z.re) : burnolComplexFeature z hz ∈ V.topologicalClosure := by
    rw [burnolComplexFeature_eq_cayleySeries hz]
    apply V.topologicalClosure.smul_mem
    apply V.isClosed_topologicalClosure.mem_of_tendsto
      (summable_burnolCayleySeriesTerm hz).hasSum
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro n _
    exact V.le_topologicalClosure (V.smul_mem _ (Submodule.subset_span ⟨n,rfl⟩))
  have hle : Submodule.span ℂ (Set.range primeBurnolRawFeature) ≤ V.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact hfeature _ _
  have hd := dense_primeBurnolRawFeature_span.mono hle
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro x _
  exact (V.isClosed_topologicalClosure.closure_subset_iff.mpr (by intro _ h; exact h)) (hd x)

end RHTower
