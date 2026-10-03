import GaloisForLFunctions.HTGeometry.BurnolWeightedShiftSingularSequence
import GaloisForLFunctions.HTGeometry.ContractionCayleyTransform

/-!
# The closed valuation Cayley realization on the Burnol half-line

For `|ζ| = 1` and `h > 0` put `V = ζ K_h`.  Neither `V` nor `V^*` has eigenvalue `-1` (both strictly
decrease nonzero norms), so the Cayley transform `T_{ζ,h} = (I-V)(I+V)⁻¹` on `Ran(I+V)` is densely
defined, closed, unbounded and maximal accretive, and every depth span
`D_ℓ = span{t e^{-(n+1)ℓt}}` is a graph core.  For `0 ≤ r < 1` the attenuated transform
`T_{ζ,h,r}` has norm and essential norm `(1+r)/(1-r)`, and no bounded `B` solves
`B(I+V+C) = I-V-C` with `C` compact.

The valuation contrast `A_{a,ℓ} f_{ℓ,k} = tanh(akℓ/2) f_{ℓ,k}` on `D_ℓ` extends boundedly exactly
when `a = 0`; for `a ≠ 0` its closure is `sgn(a) T_{1,|a|}`, and for every `M` some finite packet
with arbitrary nonzero amplitudes is stretched by more than `M`.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry CayleyTransform

/-! ## Independence of a depth tower -/

theorem linearIndependent_burnolRateFeature_fintype {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hpos : ∀ i, 0 < lam i) (hinj : Function.Injective lam) :
    LinearIndependent ℂ (fun i => burnolRateFeature (lam i) (hpos i)) := by
  set e := Fintype.equivFin ι
  have h := linearIndependent_burnolRateFeature (lam ∘ e.symm) (fun i => hpos _)
    (hinj.comp e.symm.injective)
  exact (linearIndependent_equiv e.symm).1 h

/-- Each depth tower `t e^{-(n+1)ℓt}` is linearly independent. -/
theorem linearIndependent_burnolDepthFeatureL2 (ell : Ioi (0 : ℝ)) :
    LinearIndependent ℂ (burnolDepthFeatureL2 ell) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hrate : Function.Injective fun i : s => ((i : ℕ) + 1 : ℝ) * ell := by
    intro i j hij
    have hell : (ell : ℝ) ≠ 0 := ne_of_gt ell.2
    have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := mul_right_cancel₀ hell hij
      linarith
    exact Subtype.ext (by exact_mod_cast this)
  have h := linearIndependent_burnolRateFeature_fintype (fun i : s => ((i : ℕ) + 1 : ℝ) * ell)
    (fun i => mul_pos (by positivity) ell.2) hrate
  convert h using 1
  funext i
  exact burnolDepthFeatureL2_eq_rateFeature ell i

/-- The basis of `D_ℓ` given by its depth features. -/
def burnolDepthBasis (ell : Ioi (0 : ℝ)) : Module.Basis ℕ ℂ (burnolDepthSpan ell) :=
  Module.Basis.span (linearIndependent_burnolDepthFeatureL2 ell)

theorem burnolDepthBasis_apply (ell : Ioi (0 : ℝ)) (n : ℕ) :
    (burnolDepthBasis ell n : BurnolHalfLineL2) = burnolDepthFeatureL2 ell n :=
  congrArg Subtype.val (Module.Basis.span_apply (linearIndependent_burnolDepthFeatureL2 ell) n)

theorem depthFeature_mem_span (ell : Ioi (0 : ℝ)) (n : ℕ) :
    burnolDepthFeatureL2 ell n ∈ burnolDepthSpan ell :=
  Submodule.subset_span (Set.mem_range_self n)

/-! ## The contraction `V = ζ K_h` -/

/-- `V = ζ K_h`. -/
def cayleyShift (ζ : ℂ) (h : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  ζ • burnolWeightedShift h

variable {h : ℝ≥0} {ζ : ℂ}

theorem norm_cayleyShift_apply (hζ : ‖ζ‖ = 1) (x : BurnolHalfLineL2) :
    ‖cayleyShift ζ h x‖ = ‖burnolWeightedShift h x‖ := by
  rw [cayleyShift, smul_apply, norm_smul, hζ, one_mul]

theorem norm_cayleyShift_le (hζ : ‖ζ‖ = 1) : ‖cayleyShift ζ h‖ ≤ 1 := by
  rw [cayleyShift, norm_smul, hζ, one_mul]
  exact norm_burnolWeightedShift_le h

theorem cayleyShift_eq_neg (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    ∀ x, cayleyShift ζ h x = -x → x = 0 := by
  intro x hx
  by_contra hx0
  have h1 := norm_burnolWeightedShift_lt hh hx0
  have h2 := norm_cayleyShift_apply (h := h) hζ x
  rw [hx, norm_neg] at h2
  linarith

theorem adjoint_cayleyShift (ζ : ℂ) (h : ℝ≥0) :
    ContinuousLinearMap.adjoint (cayleyShift ζ h) =
      (starRingEnd ℂ ζ) • ContinuousLinearMap.adjoint (burnolWeightedShift h) :=
  LinearIsometryEquiv.map_smulₛₗ ContinuousLinearMap.adjoint ζ _

theorem adjoint_cayleyShift_eq_neg (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    ∀ x, ContinuousLinearMap.adjoint (cayleyShift ζ h) x = -x → x = 0 := by
  intro x hx
  by_contra hx0
  have h1 := norm_adjoint_burnolWeightedShift_lt hh hx0
  have h2 : ‖ContinuousLinearMap.adjoint (cayleyShift ζ h) x‖ =
      ‖ContinuousLinearMap.adjoint (burnolWeightedShift h) x‖ := by
    rw [adjoint_cayleyShift, smul_apply, norm_smul, Complex.norm_conj, hζ,
      one_mul]
  rw [hx, norm_neg] at h2
  linarith

/-- A weakly null unit sequence with `(I + V)u_N → 0`. -/
theorem exists_singular_one_add_cayleyShift (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    ∃ u : ℕ → BurnolHalfLineL2, (∀ N, ‖u N‖ = 1) ∧
      (∀ z, Tendsto (fun N => ⟪z, u N⟫_ℂ) atTop (𝓝 0)) ∧
      Tendsto (fun N => (1 + cayleyShift ζ h) (u N)) atTop (𝓝 0) := by
  have hη : ‖-(starRingEnd ℂ ζ)‖ = 1 := by rw [norm_neg, Complex.norm_conj, hζ]
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singularSequence_burnolWeightedShift hh hη
  refine ⟨u, hu1, hweak, squeeze_zero_norm (fun N => ?_) tendsto_singularSequence_bound⟩
  have hζη : ζ * -(starRingEnd ℂ ζ) = -1 := by
    rw [mul_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  have heq : (1 + cayleyShift ζ h) (u N) =
      ζ • (burnolWeightedShift h (u N) - (-(starRingEnd ℂ ζ)) • u N) := by
    rw [smul_sub, smul_smul, hζη, cayleyShift, add_apply,
      one_apply_eq_self, smul_apply]
    module
  rw [heq, norm_smul, hζ, one_mul]
  exact hu N

/-! ## Theorem B: the closed Cayley realization -/

/-- The Cayley transform `T_{ζ,h} = (I - ζK_h)(I + ζK_h)⁻¹` on `Ran(I + ζK_h)`. -/
def burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) : BurnolHalfLineL2 →ₗ.[ℂ] BurnolHalfLineL2 :=
  cayleyPMap (cayleyShift ζ h) (cayleyShift_eq_neg hh hζ)

theorem burnolCayley_isClosed (hh : 0 < h) (hζ : ‖ζ‖ = 1) : (burnolCayley hh hζ).IsClosed :=
  cayleyPMap_isClosed _

theorem dense_domain_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    Dense ((burnolCayley hh hζ).domain : Set BurnolHalfLineL2) :=
  dense_domain_cayleyPMap _ (adjoint_cayleyShift_eq_neg hh hζ)

theorem isAccretive_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    IsAccretivePMap (burnolCayley hh hζ) :=
  isAccretive_cayleyPMap _ (norm_cayleyShift_le hζ)

theorem eq_burnolCayley_of_isAccretive_of_le (hh : 0 < h) (hζ : ‖ζ‖ = 1)
    {S : BurnolHalfLineL2 →ₗ.[ℂ] BurnolHalfLineL2} (hS : IsAccretivePMap S)
    (hle : burnolCayley hh hζ ≤ S) : S = burnolCayley hh hζ :=
  eq_of_isAccretive_of_le _ hS hle

theorem surjective_one_add_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) (y : BurnolHalfLineL2) :
    ∃ x : (burnolCayley hh hζ).domain, (x : BurnolHalfLineL2) + burnolCayley hh hζ x = y :=
  surjective_one_add_cayleyPMap _ y

theorem not_bounded_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) :
    ¬ ∃ C : ℝ, ∀ x : (burnolCayley hh hζ).domain,
      ‖burnolCayley hh hζ x‖ ≤ C * ‖(x : BurnolHalfLineL2)‖ := by
  obtain ⟨u, hu1, -, hu⟩ := exists_singular_one_add_cayleyShift hh hζ
  exact not_bounded_cayleyPMap _ hu1 hu

/-- `V f_{ℓ,n} = ζ e^{-h(n+1)ℓ} f_{ℓ,n}`. -/
theorem cayleyShift_depthFeature (ζ : ℂ) (h : ℝ≥0) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    cayleyShift ζ h (burnolDepthFeatureL2 ell n) =
      (ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ)) • burnolDepthFeatureL2 ell n := by
  rw [cayleyShift, smul_apply, burnolWeightedShift_depthFeature, smul_smul]

theorem one_add_cayleyShift_coeff_ne_zero (hh : 0 < h) (hζ : ‖ζ‖ = 1) (ell : Ioi (0 : ℝ))
    (n : ℕ) : (1 + ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ)) ≠ 0 := by
  intro h0
  have hlt : Real.exp (-(h * ((n + 1 : ℝ) * ell))) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    have : (0 : ℝ) < h := hh
    exact mul_pos this (mul_pos (by positivity) ell.2)
  have heq : ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ) = -1 := by
    linear_combination h0
  have := congrArg norm heq
  rw [norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_neg,
    norm_one] at this
  linarith

/-- `(I + V) D_ℓ = D_ℓ`. -/
theorem map_one_add_cayleyShift_burnolDepthSpan (hh : 0 < h) (hζ : ‖ζ‖ = 1) (ell : Ioi (0 : ℝ)) :
    (burnolDepthSpan ell).map ((1 + cayleyShift ζ h : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
      BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2) = burnolDepthSpan ell := by
  rw [burnolDepthSpan, Submodule.map_span, ← Set.range_comp]
  have hfun : (((1 + cayleyShift ζ h : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
      BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2) ∘ burnolDepthFeatureL2 ell) =
      fun n : ℕ => (1 + ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ)) •
        burnolDepthFeatureL2 ell n := by
    funext n
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, add_apply,
      one_apply_eq_self, cayleyShift_depthFeature, add_smul, one_smul]
  rw [hfun]
  exact (burnolDepthSpan_eq_span_scaled ell _ (one_add_cayleyShift_coeff_ne_zero hh hζ ell)).symm

/-- **Graph core.**  `D_ℓ` is a core for `T_{ζ,h}`. -/
theorem burnolCayley_graph_core (hh : 0 < h) (hζ : ‖ζ‖ = 1) (ell : Ioi (0 : ℝ)) :
    ((burnolCayley hh hζ).domRestrict (burnolDepthSpan ell)).graph.topologicalClosure =
      (burnolCayley hh hζ).graph := by
  have := graph_domRestrict_closure (cayleyShift_eq_neg hh hζ) (burnolDepthSpan ell)
    (dense_burnolDepthSpan ell)
  rwa [map_one_add_cayleyShift_burnolDepthSpan hh hζ ell] at this

theorem depthFeature_mem_domain_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) (ell : Ioi (0 : ℝ))
    (n : ℕ) : burnolDepthFeatureL2 ell n ∈ (burnolCayley hh hζ).domain := by
  have hmem : burnolDepthFeatureL2 ell n ∈ (burnolDepthSpan ell).map
      ((1 + cayleyShift ζ h : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
        BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2) := by
    rw [map_one_add_cayleyShift_burnolDepthSpan hh hζ ell]
    exact Submodule.subset_span ⟨n, rfl⟩
  obtain ⟨g, -, hg⟩ := hmem
  exact ⟨g, hg⟩

/-- `T_{ζ,h} f_{ℓ,n} = (1 - ζq)/(1 + ζq) f_{ℓ,n}` with `q = e^{-h(n+1)ℓ}`. -/
theorem burnolCayley_depthFeature (hh : 0 < h) (hζ : ‖ζ‖ = 1) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    burnolCayley hh hζ ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_domain_burnolCayley hh hζ ell n⟩ =
      ((1 - ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ)) /
        (1 + ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ))) • burnolDepthFeatureL2 ell n := by
  set c := ζ * ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ)
  have hc := one_add_cayleyShift_coeff_ne_zero hh hζ ell n
  have hVf : cayleyShift ζ h (burnolDepthFeatureL2 ell n) = c • burnolDepthFeatureL2 ell n :=
    cayleyShift_depthFeature ζ h ell n
  set g := (1 + c)⁻¹ • burnolDepthFeatureL2 ell n
  have hg : (1 + cayleyShift ζ h) g = burnolDepthFeatureL2 ell n := by
    simp only [g, add_apply, one_apply_eq_self, map_smul, hVf]
    rw [show burnolDepthFeatureL2 ell n + c • burnolDepthFeatureL2 ell n =
      (1 + c) • burnolDepthFeatureL2 ell n by rw [add_smul, one_smul], smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hx : (⟨burnolDepthFeatureL2 ell n, depthFeature_mem_domain_burnolCayley hh hζ ell n⟩ :
      (burnolCayley hh hζ).domain) =
      ⟨(1 + cayleyShift ζ h) g, mem_domain_cayleyPMap (cayleyShift_eq_neg hh hζ) g⟩ :=
    Subtype.ext hg.symm
  have key : burnolCayley hh hζ
      ⟨(1 + cayleyShift ζ h) g, mem_domain_cayleyPMap (cayleyShift_eq_neg hh hζ) g⟩ =
      (1 - cayleyShift ζ h) g := cayleyPMap_apply _ g
  rw [hx, key]
  simp only [g, sub_apply, one_apply_eq_self, map_smul, hVf]
  rw [show burnolDepthFeatureL2 ell n - c • burnolDepthFeatureL2 ell n =
    (1 - c) • burnolDepthFeatureL2 ell n by rw [sub_smul, one_smul], smul_smul, inv_mul_eq_div]

/-! ## Theorem B: attenuated norms -/

/-- `T_{ζ,h,r} = (I - rζK_h)(I + rζK_h)⁻¹`. -/
def burnolAttenuatedCayley (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  attenuatedCayley (cayleyShift ζ h) (norm_cayleyShift_le hζ) hr0 hr

theorem norm_burnolAttenuatedCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ‖burnolAttenuatedCayley (h := h) hζ hr0 hr‖ = (1 + r) / (1 - r) := by
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singular_one_add_cayleyShift hh hζ
  exact norm_attenuatedCayley _ hr0 hr hu1 hweak hu

theorem le_norm_burnolAttenuatedCayley_sub_compact (hh : 0 < h) (hζ : ‖ζ‖ = 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) {C : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2}
    (hC : IsCompactOperator C) :
    (1 + r) / (1 - r) ≤ ‖burnolAttenuatedCayley (h := h) hζ hr0 hr - C‖ := by
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singular_one_add_cayleyShift hh hζ
  exact le_norm_attenuatedCayley_sub_compact _ hr0 hr hu1 hweak hu hC

/-- **Essential norm.**  `inf_{C compact} ‖T_{ζ,h,r} - C‖ = (1+r)/(1-r)`. -/
theorem essNorm_burnolAttenuatedCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) :
    sInf {s | ∃ C : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, IsCompactOperator C ∧
      s = ‖burnolAttenuatedCayley (h := h) hζ hr0 hr - C‖} = (1 + r) / (1 - r) := by
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singular_one_add_cayleyShift hh hζ
  exact sInf_norm_attenuatedCayley_sub_compact _ hr0 hr hu1 hweak hu

/-- **No compact repair** of the Cayley equation `B(I+V+C) = I-V-C`. -/
theorem no_bounded_compact_repair_burnolCayley (hh : 0 < h) (hζ : ‖ζ‖ = 1)
    (B : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) {C : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2}
    (hC : IsCompactOperator C) :
    B * (1 + cayleyShift ζ h + C) ≠ 1 - cayleyShift ζ h - C := by
  obtain ⟨u, hu1, hweak, hu⟩ := exists_singular_one_add_cayleyShift hh hζ
  exact no_bounded_compact_repair hu1 hweak hu B hC

/-! ## Theorem C: the valuation contrast -/

/-- The valuation contrast `A_{a,ℓ} f_{ℓ,k} = tanh(akℓ/2) f_{ℓ,k}` on `D_ℓ` (`k = n+1`), defined on
the basis of depth features. -/
def valuationContrast (a : ℝ) (ell : Ioi (0 : ℝ)) : BurnolHalfLineL2 →ₗ.[ℂ] BurnolHalfLineL2 where
  domain := burnolDepthSpan ell
  toFun := (burnolDepthBasis ell).constr ℂ fun n =>
    ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n

theorem valuationContrast_depthFeature (a : ℝ) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    valuationContrast a ell ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ =
      ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n := by
  have hb : (⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ : burnolDepthSpan ell) =
      burnolDepthBasis ell n := Subtype.ext (burnolDepthBasis_apply ell n).symm
  exact (congrArg ((burnolDepthBasis ell).constr ℂ fun n : ℕ =>
    ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n) hb).trans
    (Module.Basis.constr_basis _ _ _ _)

/-- The Cayley factor on features is a hyperbolic tangent: `(1-e^{-x})/(1+e^{-x}) = tanh(x/2)`. -/
theorem one_sub_exp_div_one_add_exp (x : ℝ) :
    (1 - Real.exp (-x)) / (1 + Real.exp (-x)) = Real.tanh (x / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have he : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 := Real.exp_pos (x / 2)
  have h3 := Real.exp_pos (-(x / 2))
  have hmul : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [he]
  field_simp
  nlinarith [hmul]

theorem sign_mul_tanh_abs (a x : ℝ) : Real.sign a * Real.tanh (|a| * x / 2) = Real.tanh (a * x / 2) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, show -a * x / 2 = -(a * x / 2) by ring, Real.tanh_neg]
    ring
  · subst ha
    simp
  · rw [Real.sign_of_pos ha, abs_of_pos ha, one_mul]

theorem nnabs_pos_of_ne {a : ℝ} (ha : a ≠ 0) : 0 < Real.nnabs a := by
  rw [← NNReal.coe_pos, Real.coe_nnabs]
  exact abs_pos.2 ha

/-- The valuation shift `T_{1,|a|}` for `a ≠ 0`. -/
abbrev valuationCayley {a : ℝ} (ha : a ≠ 0) : BurnolHalfLineL2 →ₗ.[ℂ] BurnolHalfLineL2 :=
  burnolCayley (h := Real.nnabs a) (nnabs_pos_of_ne ha) norm_one

theorem not_bounded_valuationCayley {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ C : ℝ, ∀ x : (valuationCayley ha).domain,
      ‖valuationCayley ha x‖ ≤ C * ‖(x : BurnolHalfLineL2)‖ :=
  not_bounded_burnolCayley _ _

theorem burnolDepthSpan_le_domain_valuationCayley {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    burnolDepthSpan ell ≤ (valuationCayley ha).domain := by
  rw [burnolDepthSpan, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact depthFeature_mem_domain_burnolCayley _ _ ell n

theorem valuationCayley_depthFeature {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    valuationCayley ha ⟨burnolDepthFeatureL2 ell n,
        burnolDepthSpan_le_domain_valuationCayley ha ell (depthFeature_mem_span ell n)⟩ =
      ((Real.tanh (|a| * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n := by
  have := burnolCayley_depthFeature (h := Real.nnabs a) (nnabs_pos_of_ne ha) norm_one ell n
  refine this.trans ?_
  congr 1
  simp only [one_mul, Real.coe_nnabs]
  rw [← one_sub_exp_div_one_add_exp]
  push_cast
  ring_nf

/-- For `a ≠ 0`, `A_{a,ℓ} = sgn(a) T_{1,|a|}` on `D_ℓ`. -/
theorem valuationContrast_apply {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ))
    (x : (valuationContrast a ell).domain) :
    valuationContrast a ell x = (Real.sign a : ℂ) •
      valuationCayley ha ⟨x, burnolDepthSpan_le_domain_valuationCayley ha ell x.2⟩ := by
  have hdom := burnolDepthSpan_le_domain_valuationCayley ha ell
  let L2 : burnolDepthSpan ell →ₗ[ℂ] BurnolHalfLineL2 :=
    (Real.sign a : ℂ) • ((valuationCayley ha).toFun ∘ₗ Submodule.inclusion hdom)
  have hL : (valuationContrast a ell).toFun = L2 := (burnolDepthBasis ell).ext fun n => by
    have hb : burnolDepthBasis ell n = ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ :=
      Subtype.ext (burnolDepthBasis_apply ell n)
    rw [hb]
    refine (valuationContrast_depthFeature a ell n).trans ?_
    change _ = (Real.sign a : ℂ) • valuationCayley ha ⟨burnolDepthFeatureL2 ell n,
      hdom (depthFeature_mem_span ell n)⟩
    rw [valuationCayley_depthFeature, smul_smul]
    congr 1
    rw [← sign_mul_tanh_abs]
    push_cast
    ring
  exact LinearMap.congr_fun hL x

/-- The graph of `A_{a,ℓ}` is the image of the graph of `T_{1,|a|}|_{D_ℓ}` under
`(x, y) ↦ (x, sgn(a) y)`. -/
theorem graph_valuationContrast {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    (valuationContrast a ell).graph = ((valuationCayley ha).domRestrict (burnolDepthSpan ell)).graph.map
      (LinearMap.id.prodMap ((Real.sign a : ℂ) • LinearMap.id)) := by
  have hdom := burnolDepthSpan_le_domain_valuationCayley ha ell
  ext ⟨x, y⟩
  simp only [LinearPMap.mem_graph_iff, Submodule.mem_map, LinearMap.prodMap_apply, LinearMap.id_apply,
    LinearMap.smul_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨z, hz, hAz⟩
    refine ⟨x, valuationCayley ha ⟨x, hdom (hz ▸ z.2)⟩, ⟨⟨x, Submodule.mem_inf.2 ⟨hz ▸ z.2,
      hdom (hz ▸ z.2)⟩⟩, rfl, ?_⟩, rfl, ?_⟩
    · exact LinearPMap.domRestrict_apply rfl
    · rw [← hAz, valuationContrast_apply ha ell z]
      congr 2
      exact Subtype.ext hz.symm
  · rintro ⟨x', y', ⟨w, hw, hTw⟩, rfl, rfl⟩
    refine ⟨⟨w, (Submodule.mem_inf.1 w.2).1⟩, hw, ?_⟩
    rw [valuationContrast_apply ha ell, ← hTw,
      LinearPMap.domRestrict_apply (x := w) (y := ⟨w, (Submodule.mem_inf.1 w.2).2⟩) rfl]

theorem closure_map_prodSmul {c : ℂ} (hc : c ≠ 0)
    (S : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2)) :
    (S.map (LinearMap.id.prodMap (c • LinearMap.id))).topologicalClosure =
      S.topologicalClosure.map (LinearMap.id.prodMap (c • LinearMap.id)) := by
  let φ : (BurnolHalfLineL2 × BurnolHalfLineL2) ≃ₜ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
    (Homeomorph.refl _).prodCongr (Homeomorph.smulOfNeZero c hc)
  have hφ : ⇑(LinearMap.id.prodMap (c • LinearMap.id) :
      (BurnolHalfLineL2 × BurnolHalfLineL2) →ₗ[ℂ] (BurnolHalfLineL2 × BurnolHalfLineL2)) = φ := by
    funext z
    rfl
  refine SetLike.coe_injective ?_
  rw [Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.map_coe,
    Submodule.topologicalClosure_coe, hφ, φ.image_closure]

theorem norm_sign_smul {a : ℝ} (ha : a ≠ 0) (y : BurnolHalfLineL2) :
    ‖(Real.sign a : ℂ) • y‖ = ‖y‖ := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [Real.sign_of_neg h]
    simp
  · rw [Real.sign_of_pos h]
    simp

theorem sign_ne_zero {a : ℝ} (ha : a ≠ 0) : (Real.sign a : ℂ) ≠ 0 := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [Real.sign_of_neg h]
    norm_num
  · rw [Real.sign_of_pos h]
    norm_num

/-- **Theorem C, closure.**  For `a ≠ 0` the closure of `A_{a,ℓ}` is `sgn(a) T_{1,|a|}`. -/
theorem valuationContrast_closure {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    (valuationContrast a ell).graph.topologicalClosure =
      ((Real.sign a : ℂ) • valuationCayley ha).graph := by
  rw [graph_valuationContrast ha ell, closure_map_prodSmul (sign_ne_zero ha), LinearPMap.smul_graph]
  congr 1
  exact burnolCayley_graph_core _ _ ell

/-- **Theorem C, unboundedness.**  For `a ≠ 0`, `A_{a,ℓ}` is unbounded on `D_ℓ`. -/
theorem not_bounded_valuationContrast {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    ¬ ∃ M : ℝ, ∀ x : (valuationContrast a ell).domain,
      ‖valuationContrast a ell x‖ ≤ M * ‖(x : BurnolHalfLineL2)‖ := by
  rintro ⟨M, hM⟩
  have hset : IsClosed {z : BurnolHalfLineL2 × BurnolHalfLineL2 | ‖z.2‖ ≤ M * ‖z.1‖} :=
    isClosed_le (continuous_snd.norm) (continuous_const.mul continuous_fst.norm)
  have hcore : (((valuationCayley ha).domRestrict (burnolDepthSpan ell)).graph : Set _) ⊆
      {z : BurnolHalfLineL2 × BurnolHalfLineL2 | ‖z.2‖ ≤ M * ‖z.1‖} := by
    rintro ⟨x, y⟩ hxy
    have hmem : (x, (Real.sign a : ℂ) • y) ∈ (valuationContrast a ell).graph := by
      rw [graph_valuationContrast ha ell]
      exact ⟨(x, y), hxy, rfl⟩
    obtain ⟨z, hz, hAz⟩ := (LinearPMap.mem_graph_iff _).1 hmem
    have := hM z
    rw [hAz, hz, norm_sign_smul ha] at this
    exact this
  have hgc : ((valuationCayley ha).domRestrict (burnolDepthSpan ell)).graph.topologicalClosure =
      (valuationCayley ha).graph := burnolCayley_graph_core _ _ ell
  have hall : (((valuationCayley ha).graph : Set _)) ⊆
      {z : BurnolHalfLineL2 × BurnolHalfLineL2 | ‖z.2‖ ≤ M * ‖z.1‖} := by
    rw [← hgc, Submodule.topologicalClosure_coe]
    exact closure_minimal hcore hset
  refine not_bounded_valuationCayley ha ⟨M, fun x => ?_⟩
  have hx := hall (LinearPMap.mem_graph (valuationCayley ha) x)
  simpa only [Set.mem_setOf_eq] using hx

/-- **Theorem C, bounded extension.**  `A_{a,ℓ}` extends to a bounded operator exactly when
`a = 0`. -/
theorem exists_bounded_extension_valuationContrast_iff (a : ℝ) (ell : Ioi (0 : ℝ)) :
    (∃ B : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ∀ x : (valuationContrast a ell).domain, B x = valuationContrast a ell x) ↔ a = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra ha
    refine not_bounded_valuationContrast ha ell ⟨‖B‖, fun x => ?_⟩
    rw [← hB x]
    exact B.le_opNorm _
  · rintro rfl
    refine ⟨0, fun x => ?_⟩
    have h0 : (valuationContrast 0 ell).toFun = 0 := (burnolDepthBasis ell).ext fun n => by
      have hb : burnolDepthBasis ell n = ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ :=
        Subtype.ext (burnolDepthBasis_apply ell n)
      rw [hb]
      refine (valuationContrast_depthFeature 0 ell n).trans ?_
      rw [zero_mul, zero_div, Real.tanh_zero, Complex.ofReal_zero, zero_smul]
      rfl
    rw [zero_apply]
    exact (LinearMap.congr_fun h0 x).symm

/-- **Theorem C, packets.**  For `a ≠ 0`, nonzero amplitudes `b` and every `M`, some finite packet
is stretched by more than `M`. -/
theorem exists_packet_valuationContrast_gt {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) (b : ℕ → ℂ)
    (hb : ∀ n, b n ≠ 0) (M : ℝ) :
    ∃ s : Finset ℕ, ∃ c : ℕ → ℂ,
      M * ‖∑ n ∈ s, c n • b n • burnolDepthFeatureL2 ell n‖ <
        ‖∑ n ∈ s, (c n * ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ)) •
          b n • burnolDepthFeatureL2 ell n‖ := by
  by_contra hcon
  push Not at hcon
  refine not_bounded_valuationContrast ha ell ⟨M, fun x => ?_⟩
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 x.2
  set s := d.support
  have hx : x = ∑ n ∈ s, d n • (⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ :
      (valuationContrast a ell).domain) := by
    refine Subtype.ext ?_
    rw [← hd, Finsupp.sum, Submodule.coe_sum]
    rfl
  have hAx : valuationContrast a ell x = ∑ n ∈ s,
      (d n * ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ)) • burnolDepthFeatureL2 ell n := by
    rw [hx]
    change (valuationContrast a ell).toFun _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul]
    change d n • valuationContrast a ell _ = _
    rw [valuationContrast_depthFeature, smul_smul]
  have h1 := hcon s (fun n => d n / b n)
  have e1 : ∑ n ∈ s, (d n / b n) • b n • burnolDepthFeatureL2 ell n = (x : BurnolHalfLineL2) := by
    rw [← hd, Finsupp.sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_smul, div_mul_cancel₀ _ (hb n)]
  have e2 : ∑ n ∈ s, (d n / b n * ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ)) •
      b n • burnolDepthFeatureL2 ell n = valuationContrast a ell x := by
    rw [hAx]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_smul]
    congr 1
    field_simp [hb n]
  rw [e1, e2] at h1
  exact h1

end GaloisForLFunctions.HTGeometry
