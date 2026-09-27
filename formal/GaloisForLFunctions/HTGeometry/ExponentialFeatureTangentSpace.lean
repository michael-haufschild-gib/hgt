import Mathlib
import GaloisForLFunctions.HTGeometry.CoordinateMonomialTotality

/-!
# The exponential tangent space `L²((0,∞), t dt)`

The exponential features `f_a(t) = e^{-at/2}`, `a > 0`, lie in `L²((0,∞), t dt)` with Gram

`⟪f_a, f_b⟫ = ∫₀^∞ t e^{-(a+b)t/2} dt = 4/(a+b)²`.

Distinct features are linearly independent (evaluate at `t = 2, 4, …, 2n` and use the Vandermonde
determinant in `e^{-a_j}`), and their span is dense: under `u = e^{-t/2}` a vector orthogonal to every
`f_{n+1}` becomes a vector of `L²([0,1], ν)`, `ν` the image of `t e^{-t} dt`, orthogonal to every
monomial `uⁿ`, hence zero.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The tangent measure `t dt` on `(0, ∞)`. -/
def tangentMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞)

/-- The tangent Hilbert space `L²((0,∞), t dt)`. -/
abbrev ExpTangentSpace := Lp ℂ 2 tangentMeasure

theorem integral_tangentMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ t, g t ∂tangentMeasure = ∫ t in Ioi 0, t • g t := by
  rw [tangentMeasure, integral_withDensity_eq_integral_smul measurable_real_toNNReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (le_of_lt ht)]

theorem integrable_tangentMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} :
    Integrable g tangentMeasure ↔ IntegrableOn (fun t => t • g t) (Ioi 0) := by
  rw [tangentMeasure, integrable_withDensity_iff_integrable_smul measurable_real_toNNReal]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [NNReal.smul_def, Real.coe_toNNReal _ (le_of_lt ht)]

/-- `∫₀^∞ t e^{-ct} dt = 1/c²`. -/
theorem integral_Ioi_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c * t)) = 1 / c ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c) two_pos hc
  have e : ∀ t ∈ Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(c * t)) = t * Real.exp (-(c * t)) := by
    intro t _; norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, Real.Gamma_two, Real.rpow_two]
  field_simp

theorem integrableOn_Ioi_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Ioi 0) :=
  Integrable.of_integral_ne_zero (by rw [integral_Ioi_mul_exp_neg hc]; positivity)

/-- `‖F‖² = ∫ ‖F‖²` in any complex `L²`. -/
theorem norm_sq_L2_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp ℂ 2 μ) : ‖F‖ ^ 2 = ∫ t, ‖(F : α → ℂ) t‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def]
  have e : ∀ t, inner ℂ ((F : α → ℂ) t) ((F : α → ℂ) t) = ((‖(F : α → ℂ) t‖ ^ 2 : ℝ) : ℂ) :=
    fun t => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [e]
  rw [integral_complex_ofReal]
  rfl

/-- `‖F‖² = ∫ ‖F‖² d(t dt)`. -/
theorem norm_sq_tangent (F : ExpTangentSpace) :
    ‖F‖ ^ 2 = ∫ t, ‖(F : ℝ → ℂ) t‖ ^ 2 ∂tangentMeasure :=
  norm_sq_L2_eq_integral F

/-! ### Exponential features -/

/-- The exponential feature `f_a(t) = e^{-at/2}`. -/
def tangentExpFun (a t : ℝ) : ℂ := (Real.exp (-(a * t) / 2) : ℂ)

theorem memLp_tangentExpFun {a : ℝ} (ha : 0 < a) : MemLp (tangentExpFun a) 2 tangentMeasure := by
  have hmeas : AEStronglyMeasurable (tangentExpFun a) tangentMeasure := by
    unfold tangentExpFun; fun_prop
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  rw [integrable_tangentMeasure_iff]
  refine (integrableOn_Ioi_mul_exp_neg ha).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [tangentExpFun, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    smul_eq_mul, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The exponential feature as a vector (zero for `a ≤ 0`). -/
def tangentExpFeature (a : ℝ) : ExpTangentSpace :=
  if h : 0 < a then (memLp_tangentExpFun h).toLp _ else 0

theorem tangentExpFeature_ae {a : ℝ} (ha : 0 < a) :
    (tangentExpFeature a : ℝ → ℂ) =ᵐ[tangentMeasure] tangentExpFun a := by
  rw [tangentExpFeature, dif_pos ha]
  exact (memLp_tangentExpFun ha).coeFn_toLp

/-- **Gram of the features.** `⟪f_a, f_b⟫ = 4/(a+b)²`. -/
theorem inner_tangentExpFeature {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inner ℂ (tangentExpFeature a) (tangentExpFeature b) = ((4 / (a + b) ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hae : (fun t => inner ℂ ((tangentExpFeature a : ℝ → ℂ) t) ((tangentExpFeature b : ℝ → ℂ) t))
      =ᵐ[tangentMeasure] fun t => ((Real.exp (-(((a + b) / 2) * t)) : ℝ) : ℂ) := by
    filter_upwards [tangentExpFeature_ae ha, tangentExpFeature_ae hb] with t h1 h2
    rw [h1, h2, RCLike.inner_apply, tangentExpFun, tangentExpFun, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae hae, integral_tangentMeasure]
  have hab : 0 < (a + b) / 2 := by positivity
  have e : ∀ t : ℝ, t • ((Real.exp (-(((a + b) / 2) * t)) : ℝ) : ℂ) =
      ((t * Real.exp (-(((a + b) / 2) * t)) : ℝ) : ℂ) := fun t => by
    rw [Complex.real_smul, Complex.ofReal_mul]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_Ioi_mul_exp_neg hab]
  congr 1
  field_simp
  ring

theorem norm_sq_tangentExpFeature {a : ℝ} (ha : 0 < a) : ‖tangentExpFeature a‖ ^ 2 = 1 / a ^ 2 := by
  have h := congrArg Complex.re (inner_tangentExpFeature ha ha)
  rw [← RCLike.re_to_complex, inner_self_eq_norm_sq, Complex.ofReal_re] at h
  rw [h]
  field_simp
  ring

/-- The Gram of a finite exponential combination. -/
theorem norm_sq_sum_tangentExpFeature {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (c : Fin n → ℂ) :
    ((‖∑ i, c i • tangentExpFeature (a i)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (c i) * c j * ((4 / (a i + a j) ^ 2 : ℝ) : ℂ) := by
  have hX : ((‖∑ i, c i • tangentExpFeature (a i)‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (∑ i, c i • tangentExpFeature (a i)) (∑ i, c i • tangentExpFeature (a i)) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hX, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_tangentExpFeature (ha i) (ha j)]
  ring

/-- The Gram as the weighted integral `∫₀^∞ t |Σ c_j e^{-a_j t/2}|² dt`. -/
theorem norm_sq_sum_tangentExpFeature_integral {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (c : Fin n → ℂ) :
    ‖∑ i, c i • tangentExpFeature (a i)‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), t * ‖∑ i, c i * tangentExpFun (a i) t‖ ^ 2 := by
  have hsum : (fun t => ((∑ i, c i • tangentExpFeature (a i) : ExpTangentSpace) : ℝ → ℂ) t)
      =ᵐ[tangentMeasure] fun t => ∑ i, c i * tangentExpFun (a i) t := by
    have hc : ∀ i, ((c i • tangentExpFeature (a i) : ExpTangentSpace) : ℝ → ℂ) =ᵐ[tangentMeasure]
        fun t => c i * tangentExpFun (a i) t := fun i => by
      filter_upwards [Lp.coeFn_smul (c i) (tangentExpFeature (a i)), tangentExpFeature_ae (ha i)] with t h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hs := Lp.coeFn_finsetSum (Finset.univ) (fun i => c i • tangentExpFeature (a i))
    filter_upwards [hs, ae_all_iff.mpr hc] with t h1 h2
    rw [h1, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => h2 i
  have hsq : (fun t => ‖((∑ i, c i • tangentExpFeature (a i) : ExpTangentSpace) : ℝ → ℂ) t‖ ^ 2)
      =ᵐ[tangentMeasure] fun t => ‖∑ i, c i * tangentExpFun (a i) t‖ ^ 2 :=
    hsum.mono fun t ht => by simp only at ht ⊢; rw [ht]
  rw [norm_sq_tangent, integral_congr_ae hsq, integral_tangentMeasure]
  rfl

theorem sum_tangentExpFeature_ae {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (c : Fin n → ℂ) :
    (fun t => ((∑ i, c i • tangentExpFeature (a i) : ExpTangentSpace) : ℝ → ℂ) t)
      =ᵐ[tangentMeasure] fun t => ∑ i, c i * tangentExpFun (a i) t := by
  have hc : ∀ i, ((c i • tangentExpFeature (a i) : ExpTangentSpace) : ℝ → ℂ) =ᵐ[tangentMeasure]
      fun t => c i * tangentExpFun (a i) t := fun i => by
    filter_upwards [Lp.coeFn_smul (c i) (tangentExpFeature (a i)), tangentExpFeature_ae (ha i)] with t h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_finsetSum (Finset.univ) (fun i => c i • tangentExpFeature (a i)),
    ae_all_iff.mpr hc] with t h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h2 i

/-- A.e. vanishing for `t dt` on `(0,∞)` is Lebesgue a.e. vanishing on `(0,∞)`. -/
theorem ae_restrict_Ioi_of_ae_tangentMeasure {p : ℝ → Prop} (h : ∀ᵐ t ∂tangentMeasure, p t) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), p t := by
  rw [tangentMeasure, ae_withDensity_iff (by fun_prop)] at h
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with t h1 ht
  refine h1 ?_
  simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
  exact ht

/-- **Linear independence.** Features with distinct positive parameters are linearly independent. -/
theorem linearIndependent_tangentExpFeature {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) : LinearIndependent ℂ fun i => tangentExpFeature (a i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hae : (fun t => ∑ i, c i * tangentExpFun (a i) t) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun _ => (0 : ℂ) := by
    refine ae_restrict_Ioi_of_ae_tangentMeasure ?_
    filter_upwards [sum_tangentExpFeature_ae a ha c, Lp.coeFn_zero ℂ 2 tangentMeasure] with t h1 h2
    rw [← h1, hc]
    exact h2
  have hcont : Continuous fun t => ∑ i, c i * tangentExpFun (a i) t := by
    unfold tangentExpFun; fun_prop
  have heq := Measure.eqOn_of_ae_eq hae hcont.continuousOn continuousOn_const
    (by rw [interior_Ioi]; exact subset_closure)
  set x : Fin n → ℂ := fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)
  have hx : Function.Injective x := by
    intro i j h
    have h' : Real.exp (-(a i)) = Real.exp (-(a j)) := Complex.ofReal_injective h
    exact hinj (by linarith [Real.exp_injective h'])
  have hvec : Matrix.vecMul (fun i => c i * x i) (Matrix.vandermonde x) = 0 := by
    funext k
    have hk := heq (show (2 * ((k : ℕ) + 1) : ℝ) ∈ Ioi 0 by simp only [mem_Ioi]; positivity)
    simp only [Pi.zero_apply] at hk ⊢
    rw [← hk]
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, tangentExpFun, x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_succ', ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hzero : (fun i => c i * x i) = 0 := by
    by_contra hne
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
      (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hvec⟩)
  intro i
  have := congrFun hzero i
  simp only [Pi.zero_apply, x] at this
  exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (Real.exp_pos _).ne')

/-- The Gram of a nonzero combination of distinct features is strictly positive. -/
theorem norm_sum_tangentExpFeature_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) {c : Fin n → ℂ} (hc : c ≠ 0) :
    0 < ‖∑ i, c i • tangentExpFeature (a i)‖ := by
  refine norm_pos_iff.mpr fun h0 => hc ?_
  funext i
  exact Fintype.linearIndependent_iff.mp (linearIndependent_tangentExpFeature ha hinj) c h0 i

/-! ### Density -/

/-- The finite weight `t e^{-t} dt` on `(0,∞)`. -/
def tangentWeightMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => (((t * Real.exp (-t)).toNNReal : ℝ≥0) : ℝ≥0∞)

instance : IsFiniteMeasure tangentWeightMeasure := by
  have h := (integrableOn_Ioi_mul_exp_neg (c := 1) one_pos).hasFiniteIntegral
  simp only [one_mul] at h
  exact isFiniteMeasure_withDensity_ofReal h

/-- The coordinate `u = e^{-t/2}`, clamped into `[0,1]`. -/
def tangentCoordinate (t : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one (Real.exp (-t / 2))

theorem continuous_tangentCoordinate : Continuous tangentCoordinate :=
  continuous_projIcc.comp (by fun_prop)

/-- The image of `t e^{-t} dt` under `u = e^{-t/2}`: a finite measure on `[0,1]`. -/
def tangentPushMeasure : Measure (Icc (0 : ℝ) 1) := tangentWeightMeasure.map tangentCoordinate

instance : IsFiniteMeasure tangentPushMeasure := by
  unfold tangentPushMeasure; infer_instance

theorem tangentCoordinate_of_pos {t : ℝ} (ht : 0 < t) :
    (tangentCoordinate t : ℝ) = Real.exp (-t / 2) := by
  rw [tangentCoordinate, projIcc_of_mem]
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

/-- The pulled-back vector `G(u) = h(-2 log u)/u`. -/
def tangentPullback (h : ℝ → ℂ) (u : Icc (0 : ℝ) 1) : ℂ :=
  h (-2 * Real.log (u : ℝ)) * (((u : ℝ)⁻¹ : ℝ) : ℂ)

theorem tangentPullback_coordinate (h : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    tangentPullback h (tangentCoordinate t) = h t * ((Real.exp (t / 2) : ℝ) : ℂ) := by
  rw [tangentPullback, tangentCoordinate_of_pos ht, Real.log_exp, ← Real.exp_neg]
  congr 3 <;> ring

theorem integral_tangentWeightMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) : ∫ t, g t ∂tangentWeightMeasure = ∫ t in Ioi 0, (t * Real.exp (-t)) • g t := by
  rw [tangentWeightMeasure, integral_withDensity_eq_integral_smul (by fun_prop)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (mul_nonneg (le_of_lt ht) (Real.exp_pos _).le)]

theorem integrable_tangentWeightMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} : Integrable g tangentWeightMeasure ↔
      IntegrableOn (fun t => (t * Real.exp (-t)) • g t) (Ioi 0) := by
  rw [tangentWeightMeasure, integrable_withDensity_iff_integrable_smul (by fun_prop)]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [NNReal.smul_def, Real.coe_toNNReal _ (mul_nonneg (le_of_lt ht) (Real.exp_pos _).le)]

/-- **Density of the exponential features.** The features `f_{n+1}`, `n ∈ ℕ`, already span a dense
subspace of `L²((0,∞), t dt)`. -/
theorem dense_span_tangentExpFeature_nat :
    (Submodule.span ℂ (Set.range fun n : ℕ => tangentExpFeature ((n : ℝ) + 1))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  have horth : ∀ n : ℕ, inner ℂ h (tangentExpFeature ((n : ℝ) + 1)) = 0 := by
    intro n
    have := (Submodule.mem_orthogonal _ h).mp hh _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [← inner_conj_symm, this, map_zero]
  set hf : ℝ → ℂ := (h : ℝ → ℂ)
  have hmeas : StronglyMeasurable hf := Lp.stronglyMeasurable h
  have hφ : AEMeasurable tangentCoordinate tangentWeightMeasure :=
    continuous_tangentCoordinate.measurable.aemeasurable
  set G : Icc (0 : ℝ) 1 → ℂ := tangentPullback hf
  have hGmeas : StronglyMeasurable G := by
    refine (hmeas.comp_measurable ?_).mul ?_
    · exact (measurable_const.mul (Real.measurable_log.comp measurable_subtype_coe))
    · exact (Complex.measurable_ofReal.comp (measurable_subtype_coe.inv)).stronglyMeasurable
  have hGsq : StronglyMeasurable fun u => ‖G u‖ ^ 2 := hGmeas.norm.pow 2
  have hh2 : IntegrableOn (fun t => t • ‖hf t‖ ^ 2) (Ioi 0) := by
    have := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).mp (Lp.memLp h)
    exact integrable_tangentMeasure_iff.mp this
  have hGcomp : ∀ t ∈ Ioi (0 : ℝ), (t * Real.exp (-t)) • ‖G (tangentCoordinate t)‖ ^ 2 =
      t • ‖hf t‖ ^ 2 := by
    intro t ht
    show (t * Real.exp (-t)) • ‖tangentPullback hf (tangentCoordinate t)‖ ^ 2 = _
    rw [tangentPullback_coordinate hf ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul, smul_eq_mul, smul_eq_mul]
    have : Real.exp (-t) * Real.exp (((2 : ℕ) : ℝ) * (t / 2)) = 1 := by
      rw [← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
    calc t * Real.exp (-t) * (‖hf t‖ ^ 2 * Real.exp (((2 : ℕ) : ℝ) * (t / 2)))
        = t * ‖hf t‖ ^ 2 * (Real.exp (-t) * Real.exp (((2 : ℕ) : ℝ) * (t / 2))) := by ring
      _ = t * ‖hf t‖ ^ 2 := by rw [this, mul_one]
  have hGmem : MemLp G 2 tangentPushMeasure := by
    refine (memLp_two_iff_integrable_sq_norm hGmeas.aestronglyMeasurable).mpr ?_
    unfold tangentPushMeasure
    rw [integrable_map_measure hGsq.aestronglyMeasurable hφ, integrable_tangentWeightMeasure_iff]
    exact hh2.congr_fun (fun t ht => (hGcomp t ht).symm) measurableSet_Ioi
  set Gl : Lp ℂ 2 tangentPushMeasure := hGmem.toLp _
  have hGl : (Gl : Icc (0 : ℝ) 1 → ℂ) =ᵐ[tangentPushMeasure] G := hGmem.coeFn_toLp
  let X : C(Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hX : Function.Injective X := Subtype.val_injective
  have hGzero : Gl = 0 := by
    refine eq_zero_of_inner_coordMonomial_eq_zero (μ := tangentPushMeasure) hX Gl fun n => ?_
    rw [L2.inner_def]
    have hae : (fun u => inner ℂ ((Gl : Icc (0 : ℝ) 1 → ℂ) u)
        ((ContinuousMap.toLp (E := ℂ) 2 tangentPushMeasure ℂ (coordMonomialCM X n) :
          Icc (0 : ℝ) 1 → ℂ) u))
        =ᵐ[tangentPushMeasure] fun u => (starRingEnd ℂ) (G u) * ((u : ℝ) : ℂ) ^ n := by
      filter_upwards [hGl, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) tangentPushMeasure
        (coordMonomialCM X n)] with u h1 h2
      rw [h1, h2, RCLike.inner_apply, coordMonomialCM_apply, mul_comm]
      rfl
    rw [integral_congr_ae hae]
    unfold tangentPushMeasure
    rw [integral_map hφ (by
      exact ((Complex.continuous_conj.measurable.comp hGmeas.measurable).mul
        (by fun_prop : Measurable fun u : Icc (0 : ℝ) 1 => ((u : ℝ) : ℂ) ^ n)).aestronglyMeasurable),
      integral_tangentWeightMeasure]
    have hinner := horth n
    rw [L2.inner_def] at hinner
    have hae2 : (fun t => inner ℂ (hf t) ((tangentExpFeature ((n : ℝ) + 1) : ℝ → ℂ) t))
        =ᵐ[tangentMeasure] fun t => (starRingEnd ℂ) (hf t) * tangentExpFun ((n : ℝ) + 1) t := by
      filter_upwards [tangentExpFeature_ae (show (0 : ℝ) < (n : ℝ) + 1 by positivity)] with t ht
      rw [ht, RCLike.inner_apply, mul_comm]
    rw [integral_congr_ae hae2, integral_tangentMeasure] at hinner
    rw [← hinner]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    show (t * Real.exp (-t)) • ((starRingEnd ℂ) (tangentPullback hf (tangentCoordinate t)) *
      ((tangentCoordinate t : ℝ) : ℂ) ^ n) = _
    rw [tangentPullback_coordinate hf ht, tangentCoordinate_of_pos ht, tangentExpFun, map_mul,
      Complex.conj_ofReal, Complex.real_smul, Complex.real_smul, ← Complex.ofReal_pow,
      ← Real.exp_nat_mul]
    have e : Real.exp (-t) * Real.exp (t / 2) * Real.exp ((n : ℝ) * (-t / 2)) =
        Real.exp (-(((n : ℝ) + 1) * t) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc ((t * Real.exp (-t) : ℝ) : ℂ) * ((starRingEnd ℂ) (hf t) *
          ((Real.exp (t / 2) : ℝ) : ℂ) * ((Real.exp ((n : ℝ) * (-t / 2)) : ℝ) : ℂ))
        = (t : ℂ) * ((starRingEnd ℂ) (hf t) *
          ((Real.exp (-t) * Real.exp (t / 2) * Real.exp ((n : ℝ) * (-t / 2)) : ℝ) : ℂ)) := by
          push_cast; ring
      _ = _ := by rw [e]
  have hint0 : ∫ u, ‖G u‖ ^ 2 ∂tangentPushMeasure = 0 := by
    have h1 := norm_sq_L2_eq_integral Gl
    have h2 : ‖Gl‖ ^ 2 = 0 := by rw [hGzero, norm_zero]; norm_num
    calc ∫ u, ‖G u‖ ^ 2 ∂tangentPushMeasure
        = ∫ u, ‖(Gl : Icc (0 : ℝ) 1 → ℂ) u‖ ^ 2 ∂tangentPushMeasure :=
          integral_congr_ae (hGl.mono fun u hu => by simp only at hu ⊢; rw [hu])
      _ = 0 := by rw [← h1, h2]
  unfold tangentPushMeasure at hint0
  rw [integral_map hφ hGsq.aestronglyMeasurable, integral_tangentWeightMeasure,
    setIntegral_congr_fun measurableSet_Ioi hGcomp] at hint0
  have hnorm : ‖h‖ ^ 2 = 0 := by
    rw [norm_sq_tangent, integral_tangentMeasure]
    exact hint0
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hnorm)

/-- **Density.** The features `f_a`, `a > 0`, span a dense subspace of `L²((0,∞), t dt)`. -/
theorem dense_span_tangentExpFeature :
    (Submodule.span ℂ (Set.range fun a : Ioi (0 : ℝ) => tangentExpFeature a)).topologicalClosure = ⊤ := by
  refine eq_top_iff.mpr (dense_span_tangentExpFeature_nat ▸ Submodule.topologicalClosure_mono ?_)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨n, rfl⟩
  exact Submodule.subset_span ⟨⟨(n : ℝ) + 1, by simp only [mem_Ioi]; positivity⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
