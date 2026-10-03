import GaloisForLFunctions.HTGeometry.BurnolValuationCayleyFrame

/-!
# The doubled valuation frame and its circular Cayley closure

On `E = H × H` the doubled valuation frame acts on `D_ℓ × D_ℓ` by the rotation-type blocks
`U(x) = [[sech x, -tanh x], [tanh x, sech x]]`, `x = akℓ/2`, on each depth feature `f_{ℓ,k}`:
`Φ_a = [[S_a, -A_a], [A_a, S_a]]` with `S_a f_k = sech(akℓ/2) f_k` and `A_a` the valuation contrast.
In the circular coordinates `W(x, y) = (x + iy, x - iy)`, which diagonalize `J = [[0,-1],[1,0]]`,
`W Φ_a W⁻¹ = (S_a + iA_a) ⊕ (S_a - iA_a)`, and with `ζ = sgn(a) i`, `h = |a|/2`,
`sech x + i tanh x = ζ(1 - ζe^{-h k ℓ})/(1 + ζe^{-h k ℓ})`.  Hence the closure of the conjugated
frame is `ζ T_{ζ,h} ⊕ (-ζ) T_{-ζ,h}`, with domain `Ran(I + ζK_h) ⊕ Ran(I - ζK_h)`; for `a < 0` the
two summands are exchanged.  The doubled frame is closable and unbounded.
-/

open Filter Topology Set
open scoped NNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry CayleyTransform

local notation "𝓗" => BurnolHalfLineL2

/-! ## Direct sums of partially defined operators -/

/-- `T₁ ⊕ T₂` on `dom T₁ × dom T₂`. -/
def pmapDiagSum (T₁ T₂ : 𝓗 →ₗ.[ℂ] 𝓗) : (𝓗 × 𝓗) →ₗ.[ℂ] (𝓗 × 𝓗) where
  domain := T₁.domain.prod T₂.domain
  toFun :=
    (T₁.toFun ∘ₗ LinearMap.codRestrict T₁.domain
        (LinearMap.fst ℂ 𝓗 𝓗 ∘ₗ (T₁.domain.prod T₂.domain).subtype)
        (fun z => (Submodule.mem_prod.1 z.2).1)).prod
    (T₂.toFun ∘ₗ LinearMap.codRestrict T₂.domain
        (LinearMap.snd ℂ 𝓗 𝓗 ∘ₗ (T₁.domain.prod T₂.domain).subtype)
        (fun z => (Submodule.mem_prod.1 z.2).2))

theorem diagSum_apply (T₁ T₂ : 𝓗 →ₗ.[ℂ] 𝓗) (z : (pmapDiagSum T₁ T₂).domain) :
    pmapDiagSum T₁ T₂ z = (T₁ ⟨(z : 𝓗 × 𝓗).1, (Submodule.mem_prod.1 z.2).1⟩,
      T₂ ⟨(z : 𝓗 × 𝓗).2, (Submodule.mem_prod.1 z.2).2⟩) := rfl

/-- The shuffle `((x₁,x₂),(y₁,y₂)) ↦ ((x₁,y₁),(x₂,y₂))`. -/
def graphShuffle : ((𝓗 × 𝓗) × (𝓗 × 𝓗)) ≃ₜ ((𝓗 × 𝓗) × (𝓗 × 𝓗)) :=
  Homeomorph.prodProdProdComm 𝓗 𝓗 𝓗 𝓗

theorem graphShuffle_apply (x₁ x₂ y₁ y₂ : 𝓗) :
    graphShuffle ((x₁, x₂), (y₁, y₂)) = ((x₁, y₁), (x₂, y₂)) := rfl

theorem graph_diagSum (T₁ T₂ : 𝓗 →ₗ.[ℂ] 𝓗) :
    ((pmapDiagSum T₁ T₂).graph : Set ((𝓗 × 𝓗) × (𝓗 × 𝓗))) =
      graphShuffle ⁻¹' ((T₁.graph : Set (𝓗 × 𝓗)) ×ˢ (T₂.graph : Set (𝓗 × 𝓗))) := by
  ext ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  rw [mem_preimage, graphShuffle_apply, mem_prod, SetLike.mem_coe, SetLike.mem_coe,
    SetLike.mem_coe, LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hTz⟩
    rw [diagSum_apply] at hTz
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    have h3 := congrArg Prod.fst hTz
    have h4 := congrArg Prod.snd hTz
    exact ⟨⟨_, h1, h3⟩, ⟨_, h2, h4⟩⟩
  · rintro ⟨⟨u, hu, hTu⟩, ⟨v, hv, hTv⟩⟩
    refine ⟨⟨((u : 𝓗), (v : 𝓗)), Submodule.mem_prod.2 ⟨u.2, v.2⟩⟩, ?_, ?_⟩
    · exact Prod.ext hu hv
    · exact Prod.ext hTu hTv

/-- **Closure of a direct sum.**  `cl Graph(T₁ ⊕ T₂) = shuffle⁻¹(cl Graph T₁ × cl Graph T₂)`. -/
theorem closure_graph_diagSum (T₁ T₂ : 𝓗 →ₗ.[ℂ] 𝓗) :
    ((pmapDiagSum T₁ T₂).graph.topologicalClosure : Set ((𝓗 × 𝓗) × (𝓗 × 𝓗))) =
      graphShuffle ⁻¹' ((T₁.graph.topologicalClosure : Set (𝓗 × 𝓗)) ×ˢ
        (T₂.graph.topologicalClosure : Set (𝓗 × 𝓗))) := by
  rw [Submodule.topologicalClosure_coe, graph_diagSum, Submodule.topologicalClosure_coe,
    Submodule.topologicalClosure_coe, ← closure_prod_eq, graphShuffle.preimage_closure]

theorem diagSum_domRestrict_closure {T₁ T₂ : 𝓗 →ₗ.[ℂ] 𝓗} {D₁ D₂ : Submodule ℂ 𝓗}
    (h₁ : (T₁.domRestrict D₁).graph.topologicalClosure = T₁.graph)
    (h₂ : (T₂.domRestrict D₂).graph.topologicalClosure = T₂.graph) :
    (pmapDiagSum (T₁.domRestrict D₁) (T₂.domRestrict D₂)).graph.topologicalClosure =
      (pmapDiagSum T₁ T₂).graph := by
  refine SetLike.coe_injective ?_
  rw [closure_graph_diagSum, h₁, h₂, graph_diagSum]

/-! ## Circular coordinates -/

/-- `W(x, y) = (x + iy, x - iy)`. -/
def circularForward : (𝓗 × 𝓗) →L[ℂ] (𝓗 × 𝓗) :=
  (ContinuousLinearMap.fst ℂ 𝓗 𝓗 + Complex.I • ContinuousLinearMap.snd ℂ 𝓗 𝓗).prod
    (ContinuousLinearMap.fst ℂ 𝓗 𝓗 - Complex.I • ContinuousLinearMap.snd ℂ 𝓗 𝓗)

/-- `W⁻¹(α, β) = ((α + β)/2, i(β - α)/2)`. -/
def circularBackward : (𝓗 × 𝓗) →L[ℂ] (𝓗 × 𝓗) :=
  ((2 : ℂ)⁻¹ • (ContinuousLinearMap.fst ℂ 𝓗 𝓗 + ContinuousLinearMap.snd ℂ 𝓗 𝓗)).prod
    ((Complex.I / 2) • (ContinuousLinearMap.snd ℂ 𝓗 𝓗 - ContinuousLinearMap.fst ℂ 𝓗 𝓗))

theorem circularForward_apply (z : 𝓗 × 𝓗) :
    circularForward z = (z.1 + Complex.I • z.2, z.1 - Complex.I • z.2) := rfl

theorem circularBackward_apply (w : 𝓗 × 𝓗) :
    circularBackward w = ((2 : ℂ)⁻¹ • (w.1 + w.2), (Complex.I / 2) • (w.2 - w.1)) := rfl

theorem I_mul_I_div_two : Complex.I * (Complex.I / 2) = -(2 : ℂ)⁻¹ := by
  rw [← mul_div_assoc, Complex.I_mul_I]
  ring

theorem circularBackward_forward (z : 𝓗 × 𝓗) : circularBackward (circularForward z) = z := by
  rw [circularForward_apply, circularBackward_apply]
  refine Prod.ext ?_ ?_
  · show (2 : ℂ)⁻¹ • (z.1 + Complex.I • z.2 + (z.1 - Complex.I • z.2)) = z.1
    rw [show z.1 + Complex.I • z.2 + (z.1 - Complex.I • z.2) = (2 : ℂ) • z.1 by module, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  · show (Complex.I / 2) • (z.1 - Complex.I • z.2 - (z.1 + Complex.I • z.2)) = z.2
    rw [show z.1 - Complex.I • z.2 - (z.1 + Complex.I • z.2) = (-2 * Complex.I) • z.2 by module,
      smul_smul, show Complex.I / 2 * (-2 * Complex.I) = -(Complex.I * Complex.I) by ring,
      Complex.I_mul_I, neg_neg, one_smul]

theorem circularForward_backward (w : 𝓗 × 𝓗) : circularForward (circularBackward w) = w := by
  rw [circularBackward_apply, circularForward_apply]
  refine Prod.ext ?_ ?_
  · show (2 : ℂ)⁻¹ • (w.1 + w.2) + Complex.I • ((Complex.I / 2) • (w.2 - w.1)) = w.1
    rw [smul_smul, I_mul_I_div_two]
    module
  · show (2 : ℂ)⁻¹ • (w.1 + w.2) - Complex.I • ((Complex.I / 2) • (w.2 - w.1)) = w.2
    rw [smul_smul, I_mul_I_div_two]
    module

/-- The circular coordinates as a continuous linear equivalence. -/
def circularCoordinates : (𝓗 × 𝓗) ≃L[ℂ] (𝓗 × 𝓗) :=
  ContinuousLinearEquiv.equivOfInverse circularForward circularBackward circularBackward_forward
    circularForward_backward

theorem circularCoordinates_apply (z : 𝓗 × 𝓗) :
    circularCoordinates z = (z.1 + Complex.I • z.2, z.1 - Complex.I • z.2) := rfl

theorem circularCoordinates_symm_apply (w : 𝓗 × 𝓗) :
    circularCoordinates.symm w = ((2 : ℂ)⁻¹ • (w.1 + w.2), (Complex.I / 2) • (w.2 - w.1)) := rfl

/-! ## The doubled frame -/

/-- The visibility `S_a f_n = sech(a(n+1)ℓ/2) f_n` on `D_ℓ`. -/
def valuationVisibility (a : ℝ) (ell : Ioi (0 : ℝ)) : burnolDepthSpan ell →ₗ[ℂ] 𝓗 :=
  (burnolDepthBasis ell).constr ℂ fun n =>
    (((Real.cosh (a * ((n + 1 : ℝ) * ell) / 2))⁻¹ : ℝ) : ℂ) • burnolDepthFeatureL2 ell n

theorem valuationVisibility_depthFeature (a : ℝ) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    valuationVisibility a ell ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ =
      (((Real.cosh (a * ((n + 1 : ℝ) * ell) / 2))⁻¹ : ℝ) : ℂ) • burnolDepthFeatureL2 ell n := by
  have hb : (⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ : burnolDepthSpan ell) =
      burnolDepthBasis ell n := Subtype.ext (burnolDepthBasis_apply ell n).symm
  rw [hb, valuationVisibility, Module.Basis.constr_basis]

/-- The contrast `A_a` as a linear map on `D_ℓ`. -/
def valuationContrastLM (a : ℝ) (ell : Ioi (0 : ℝ)) : burnolDepthSpan ell →ₗ[ℂ] 𝓗 :=
  (valuationContrast a ell).toFun

theorem valuationContrastLM_depthFeature (a : ℝ) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    valuationContrastLM a ell ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ =
      ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n :=
  valuationContrast_depthFeature a ell n

/-- The two coordinate projections `D_ℓ × D_ℓ → D_ℓ`. -/
def depthProdFst (ell : Ioi (0 : ℝ)) : ((burnolDepthSpan ell).prod (burnolDepthSpan ell)) →ₗ[ℂ]
    burnolDepthSpan ell :=
  LinearMap.codRestrict _ (LinearMap.fst ℂ 𝓗 𝓗 ∘ₗ ((burnolDepthSpan ell).prod
    (burnolDepthSpan ell)).subtype) (fun z => (Submodule.mem_prod.1 z.2).1)

def depthProdSnd (ell : Ioi (0 : ℝ)) : ((burnolDepthSpan ell).prod (burnolDepthSpan ell)) →ₗ[ℂ]
    burnolDepthSpan ell :=
  LinearMap.codRestrict _ (LinearMap.snd ℂ 𝓗 𝓗 ∘ₗ ((burnolDepthSpan ell).prod
    (burnolDepthSpan ell)).subtype) (fun z => (Submodule.mem_prod.1 z.2).2)

/-- **The doubled valuation frame** `Φ_a = [[S_a, -A_a], [A_a, S_a]]` on `D_ℓ × D_ℓ`. -/
def doubledValuationFrame (a : ℝ) (ell : Ioi (0 : ℝ)) : (𝓗 × 𝓗) →ₗ.[ℂ] (𝓗 × 𝓗) where
  domain := (burnolDepthSpan ell).prod (burnolDepthSpan ell)
  toFun :=
    (valuationVisibility a ell ∘ₗ depthProdFst ell - valuationContrastLM a ell ∘ₗ depthProdSnd ell).prod
      (valuationContrastLM a ell ∘ₗ depthProdFst ell + valuationVisibility a ell ∘ₗ depthProdSnd ell)

theorem doubledValuationFrame_apply (a : ℝ) (ell : Ioi (0 : ℝ))
    (z : (doubledValuationFrame a ell).domain) :
    doubledValuationFrame a ell z =
      (valuationVisibility a ell (depthProdFst ell z) - valuationContrastLM a ell (depthProdSnd ell z),
        valuationContrastLM a ell (depthProdFst ell z) + valuationVisibility a ell (depthProdSnd ell z)) :=
  rfl

/-- **Doubled features.**  `Φ_a (α f_k, β f_k) = f_k ⊗ U(akℓ/2)(α, β)`. -/
theorem doubledValuationFrame_feature (a : ℝ) (ell : Ioi (0 : ℝ)) (n : ℕ) (α β : ℂ) :
    doubledValuationFrame a ell ⟨(α • burnolDepthFeatureL2 ell n, β • burnolDepthFeatureL2 ell n),
        Submodule.mem_prod.2 ⟨Submodule.smul_mem _ α (depthFeature_mem_span ell n),
          Submodule.smul_mem _ β (depthFeature_mem_span ell n)⟩⟩ =
      (((((Real.cosh (a * ((n + 1 : ℝ) * ell) / 2))⁻¹ : ℝ) : ℂ) * α -
          ((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) * β) • burnolDepthFeatureL2 ell n,
        (((Real.tanh (a * ((n + 1 : ℝ) * ell) / 2) : ℝ) : ℂ) * α +
          (((Real.cosh (a * ((n + 1 : ℝ) * ell) / 2))⁻¹ : ℝ) : ℂ) * β) • burnolDepthFeatureL2 ell n) := by
  change (valuationVisibility a ell (α • ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩) -
      valuationContrastLM a ell (β • ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩),
    valuationContrastLM a ell (α • ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩) +
      valuationVisibility a ell (β • ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩)) = _
  rw [map_smul, map_smul, map_smul, map_smul, valuationVisibility_depthFeature,
    valuationContrastLM_depthFeature, smul_smul, smul_smul, smul_smul, smul_smul, ← sub_smul,
    ← add_smul]
  congr 2 <;> ring

/-! ## The circular Cayley summands -/

/-- `ζ = sgn(a) i`. -/
def circularPhase (a : ℝ) : ℂ := (Real.sign a : ℂ) * Complex.I

theorem norm_circularPhase {a : ℝ} (ha : a ≠ 0) : ‖circularPhase a‖ = 1 := by
  rw [circularPhase, norm_mul, Complex.norm_I, mul_one]
  rcases lt_or_gt_of_ne ha with h | h
  · rw [Real.sign_of_neg h]; simp
  · rw [Real.sign_of_pos h]; simp

theorem norm_neg_circularPhase {a : ℝ} (ha : a ≠ 0) : ‖-circularPhase a‖ = 1 := by
  rw [norm_neg, norm_circularPhase ha]

/-- The half-rate `h = |a|/2`. -/
def circularRate (a : ℝ) : ℝ≥0 := Real.nnabs a / 2

theorem circularRate_pos {a : ℝ} (ha : a ≠ 0) : 0 < circularRate a :=
  div_pos (nnabs_pos_of_ne ha) two_pos

theorem coe_circularRate (a : ℝ) : (circularRate a : ℝ) = |a| / 2 := by
  rw [circularRate, NNReal.coe_div, Real.coe_nnabs]
  rfl

/-- The first circular summand `ζ T_{ζ, |a|/2}`. -/
def circularSummandPlus {a : ℝ} (ha : a ≠ 0) : 𝓗 →ₗ.[ℂ] 𝓗 :=
  circularPhase a • burnolCayley (circularRate_pos ha) (norm_circularPhase ha)

/-- The second circular summand `(-ζ) T_{-ζ, |a|/2}`. -/
def circularSummandMinus {a : ℝ} (ha : a ≠ 0) : 𝓗 →ₗ.[ℂ] 𝓗 :=
  (-circularPhase a) • burnolCayley (circularRate_pos ha) (norm_neg_circularPhase ha)

theorem cosh_inv_eq_exp_abs {x : ℝ} (hx : x ≠ 0) :
    (Real.cosh x)⁻¹ = 2 * Real.exp (-|x|) / (1 + Real.exp (-|x|) ^ 2) := by
  have hq := Real.exp_pos (-|x|)
  have hc : Real.cosh x = ((Real.exp (-|x|))⁻¹ + Real.exp (-|x|)) / 2 := by
    rw [Real.cosh_eq]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h, neg_neg, Real.exp_neg]
      ring
    · rw [abs_of_pos h, Real.exp_neg, inv_inv]
  rw [hc]
  field_simp

theorem tanh_eq_exp_abs {x : ℝ} (hx : x ≠ 0) :
    Real.tanh x = Real.sign x * ((1 - Real.exp (-|x|) ^ 2) / (1 + Real.exp (-|x|) ^ 2)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have he := Real.exp_pos x
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h, neg_neg, Real.exp_neg]
    field_simp
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h, Real.exp_neg]
    field_simp

theorem cayley_plus_identity (q : ℝ) :
    ((2 * q / (1 + q ^ 2) : ℝ) : ℂ) + Complex.I * (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ) =
      Complex.I * ((1 - Complex.I * q) / (1 + Complex.I * q)) := by
  have hden : (1 : ℂ) + Complex.I * q ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hq1 : (1 : ℂ) + (q : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (by positivity : (1 : ℝ) + q ^ 2 ≠ 0)
  rw [mul_div_assoc', eq_div_iff hden]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem cayley_minus_identity (q : ℝ) :
    ((2 * q / (1 + q ^ 2) : ℝ) : ℂ) - Complex.I * (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ) =
      -Complex.I * ((1 + Complex.I * q) / (1 - Complex.I * q)) := by
  have hden : (1 : ℂ) - Complex.I * q ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hq1 : (1 : ℂ) + (q : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (by positivity : (1 : ℝ) + q ^ 2 ≠ 0)
  rw [mul_div_assoc', eq_div_iff hden]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `sech x ± i tanh x` in Cayley form, with `ζ = sgn(x) i` and `q = e^{-|x|}`. -/
theorem sech_add_I_tanh {x : ℝ} (hx : x ≠ 0) :
    (((Real.cosh x)⁻¹ : ℝ) : ℂ) + Complex.I * ((Real.tanh x : ℝ) : ℂ) =
        ((Real.sign x : ℂ) * Complex.I) *
          ((1 - ((Real.sign x : ℂ) * Complex.I) * ((Real.exp (-|x|) : ℝ) : ℂ)) /
            (1 + ((Real.sign x : ℂ) * Complex.I) * ((Real.exp (-|x|) : ℝ) : ℂ))) ∧
      (((Real.cosh x)⁻¹ : ℝ) : ℂ) - Complex.I * ((Real.tanh x : ℝ) : ℂ) =
        (-((Real.sign x : ℂ) * Complex.I)) *
          ((1 - (-((Real.sign x : ℂ) * Complex.I)) * ((Real.exp (-|x|) : ℝ) : ℂ)) /
            (1 + (-((Real.sign x : ℂ) * Complex.I)) * ((Real.exp (-|x|) : ℝ) : ℂ))) := by
  rw [cosh_inv_eq_exp_abs hx, tanh_eq_exp_abs hx]
  generalize Real.exp (-|x|) = q
  have hp := cayley_plus_identity q
  have hm := cayley_minus_identity q
  rcases lt_or_gt_of_ne hx with h | h
  · simp only [Real.sign_of_neg h, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_mul]
    constructor
    · rw [show (((2 * q / (1 + q ^ 2)) : ℝ) : ℂ) + Complex.I * (-1 *
          (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ)) = (((2 * q / (1 + q ^ 2)) : ℝ) : ℂ) -
          Complex.I * (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ) by ring, hm]
      ring_nf
    · rw [show (((2 * q / (1 + q ^ 2)) : ℝ) : ℂ) - Complex.I * (-1 *
          (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ)) = (((2 * q / (1 + q ^ 2)) : ℝ) : ℂ) +
          Complex.I * (((1 - q ^ 2) / (1 + q ^ 2) : ℝ) : ℂ) by ring, hp]
      ring_nf
  · simp only [Real.sign_of_pos h, Complex.ofReal_one, one_mul]
    refine ⟨hp, hm.trans ?_⟩
    ring_nf

/-! ## The circular summands on the core -/

theorem burnolDepthSpan_le_domain_burnolCayley {h : ℝ≥0} {ζ : ℂ} (hh : 0 < h) (hζ : ‖ζ‖ = 1)
    (ell : Ioi (0 : ℝ)) : burnolDepthSpan ell ≤ (burnolCayley hh hζ).domain := by
  rw [burnolDepthSpan, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact depthFeature_mem_domain_burnolCayley hh hζ ell n

theorem domain_circularSummandPlus {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    burnolDepthSpan ell ≤ (circularSummandPlus ha).domain := by
  rw [circularSummandPlus, LinearPMap.smul_domain]
  exact burnolDepthSpan_le_domain_burnolCayley _ _ ell

theorem domain_circularSummandMinus {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    burnolDepthSpan ell ≤ (circularSummandMinus ha).domain := by
  rw [circularSummandMinus, LinearPMap.smul_domain]
  exact burnolDepthSpan_le_domain_burnolCayley _ _ ell

/-- The first summand on `D_ℓ`. -/
def plusCore {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) : burnolDepthSpan ell →ₗ[ℂ] 𝓗 :=
  (circularSummandPlus ha).toFun ∘ₗ Submodule.inclusion (domain_circularSummandPlus ha ell)

/-- The second summand on `D_ℓ`. -/
def minusCore {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) : burnolDepthSpan ell →ₗ[ℂ] 𝓗 :=
  (circularSummandMinus ha).toFun ∘ₗ Submodule.inclusion (domain_circularSummandMinus ha ell)

theorem sign_mul_of_pos (a : ℝ) {c : ℝ} (hc : 0 < c) : Real.sign (a * c) = Real.sign a := by
  rcases lt_trichotomy a 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_neg_of_pos h hc)]
  · subst h
    simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos h hc)]

theorem feature_rate_abs {a : ℝ} (ell : Ioi (0 : ℝ)) (n : ℕ) :
    -|a * ((n + 1 : ℝ) * ell) / 2| = -((circularRate a : ℝ) * ((n + 1 : ℝ) * ell)) := by
  have hc : (0 : ℝ) < (n + 1 : ℝ) * ell := mul_pos (by positivity) ell.2
  rw [coe_circularRate, abs_div, abs_mul, abs_of_pos hc, abs_two]
  ring

theorem feature_rate_ne_zero {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    a * ((n + 1 : ℝ) * ell) / 2 ≠ 0 := by
  have hc : (0 : ℝ) < (n + 1 : ℝ) * ell := mul_pos (by positivity) ell.2
  exact div_ne_zero (mul_ne_zero ha hc.ne') two_ne_zero

theorem feature_rate_sign {a : ℝ} (ell : Ioi (0 : ℝ)) (n : ℕ) :
    Real.sign (a * ((n + 1 : ℝ) * ell) / 2) = Real.sign a := by
  have hc : (0 : ℝ) < (n + 1 : ℝ) * ell := mul_pos (by positivity) ell.2
  rw [mul_div_assoc]
  exact sign_mul_of_pos a (by positivity)

/-- On `D_ℓ`, `ζ T_{ζ,|a|/2} = S_a + i A_a`. -/
theorem plusCore_eq {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    plusCore ha ell = valuationVisibility a ell + Complex.I • valuationContrastLM a ell := by
  refine (burnolDepthBasis ell).ext fun n => ?_
  have hb : burnolDepthBasis ell n = ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ :=
    Subtype.ext (burnolDepthBasis_apply ell n)
  rw [hb, LinearMap.add_apply, LinearMap.smul_apply, valuationVisibility_depthFeature,
    valuationContrastLM_depthFeature, smul_smul, ← add_smul]
  change circularPhase a • burnolCayley (circularRate_pos ha) (norm_circularPhase ha)
    ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_domain_burnolCayley _ _ ell n⟩ = _
  rw [burnolCayley_depthFeature, smul_smul]
  congr 1
  have hid := (sech_add_I_tanh (feature_rate_ne_zero ha ell n)).1
  rw [feature_rate_sign, feature_rate_abs] at hid
  rw [hid, circularPhase]

/-- On `D_ℓ`, `(-ζ) T_{-ζ,|a|/2} = S_a - i A_a`. -/
theorem minusCore_eq {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    minusCore ha ell = valuationVisibility a ell - Complex.I • valuationContrastLM a ell := by
  refine (burnolDepthBasis ell).ext fun n => ?_
  have hb : burnolDepthBasis ell n = ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_span ell n⟩ :=
    Subtype.ext (burnolDepthBasis_apply ell n)
  rw [hb, LinearMap.sub_apply, LinearMap.smul_apply, valuationVisibility_depthFeature,
    valuationContrastLM_depthFeature, smul_smul, ← sub_smul]
  change (-circularPhase a) • burnolCayley (circularRate_pos ha) (norm_neg_circularPhase ha)
    ⟨burnolDepthFeatureL2 ell n, depthFeature_mem_domain_burnolCayley _ _ ell n⟩ = _
  rw [burnolCayley_depthFeature, smul_smul]
  congr 1
  have hid := (sech_add_I_tanh (feature_rate_ne_zero ha ell n)).2
  rw [feature_rate_sign, feature_rate_abs] at hid
  rw [hid, circularPhase]

/-! ## Conjugation into circular coordinates -/

/-- `W Φ_a = ((S+iA)(x+iy), (S-iA)(x-iy))` on `D_ℓ × D_ℓ`. -/
theorem circularCoordinates_doubledValuationFrame {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ))
    (z : (doubledValuationFrame a ell).domain) :
    circularCoordinates (doubledValuationFrame a ell z) =
      (plusCore ha ell (depthProdFst ell z + Complex.I • depthProdSnd ell z),
        minusCore ha ell (depthProdFst ell z - Complex.I • depthProdSnd ell z)) := by
  rw [doubledValuationFrame_apply, circularCoordinates_apply, plusCore_eq, minusCore_eq]
  refine Prod.ext ?_ ?_
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_add, smul_smul,
      Complex.I_mul_I]
    module
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_sub, smul_smul,
      Complex.I_mul_I]
    module

theorem circularCoordinates_mem_prod {ell : Ioi (0 : ℝ)} {z : 𝓗 × 𝓗}
    (hz : z ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell)) :
    circularCoordinates z ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell) := by
  obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hz
  rw [circularCoordinates_apply]
  exact Submodule.mem_prod.2 ⟨Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2),
    Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)⟩

theorem circularCoordinates_symm_mem_prod {ell : Ioi (0 : ℝ)} {w : 𝓗 × 𝓗}
    (hw : w ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell)) :
    circularCoordinates.symm w ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell) := by
  obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hw
  rw [circularCoordinates_symm_apply]
  exact Submodule.mem_prod.2 ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ h1 h2),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ h2 h1)⟩

/-- The pair map `(u, v) ↦ (W u, W v)` on graphs. -/
def circularGraphMap : ((𝓗 × 𝓗) × (𝓗 × 𝓗)) →ₗ[ℂ] ((𝓗 × 𝓗) × (𝓗 × 𝓗)) :=
  (circularCoordinates : (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗)).prodMap
    (circularCoordinates : (𝓗 × 𝓗) →ₗ[ℂ] (𝓗 × 𝓗))

theorem mem_graph_domRestrict_iff {T : 𝓗 →ₗ.[ℂ] 𝓗} {D : Submodule ℂ 𝓗} (hD : D ≤ T.domain)
    {x y : 𝓗} : (x, y) ∈ (T.domRestrict D).graph ↔ ∃ hx : x ∈ D, y = T ⟨x, hD hx⟩ := by
  constructor
  · intro hxy
    obtain ⟨w, hw, hTw⟩ := (LinearPMap.mem_graph_iff _).1 hxy
    simp only at hw hTw
    subst hw
    have hwD : (w : 𝓗) ∈ D ⊓ T.domain := w.2
    refine ⟨(Submodule.mem_inf.1 hwD).1, ?_⟩
    rw [← hTw, LinearPMap.domRestrict_apply (x := w) (y := ⟨w, hD (Submodule.mem_inf.1 hwD).1⟩)
      rfl]
  · rintro ⟨hx, rfl⟩
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨x, Submodule.mem_inf.2 ⟨hx, hD hx⟩⟩, rfl,
      LinearPMap.domRestrict_apply rfl⟩

theorem circularCoordinates_coe {ell : Ioi (0 : ℝ)} (z : (doubledValuationFrame a ell).domain) :
    circularCoordinates (z : 𝓗 × 𝓗) =
      (((depthProdFst ell z + Complex.I • depthProdSnd ell z : burnolDepthSpan ell) : 𝓗),
        ((depthProdFst ell z - Complex.I • depthProdSnd ell z : burnolDepthSpan ell) : 𝓗)) := rfl

/-- **Conjugated graph.**  In circular coordinates the doubled frame is the direct sum of the two
Cayley summands restricted to `D_ℓ`. -/
theorem map_graph_doubledValuationFrame {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    (doubledValuationFrame a ell).graph.map circularGraphMap =
      (pmapDiagSum ((circularSummandPlus ha).domRestrict (burnolDepthSpan ell))
        ((circularSummandMinus ha).domRestrict (burnolDepthSpan ell))).graph := by
  refine SetLike.coe_injective ?_
  ext ⟨u, v⟩
  rw [graph_diagSum, mem_preimage, graphShuffle_apply, mem_prod]
  dsimp only
  simp only [SetLike.mem_coe]
  rw [mem_graph_domRestrict_iff (domain_circularSummandPlus ha ell),
    mem_graph_domRestrict_iff (domain_circularSummandMinus ha ell), Submodule.mem_map]
  constructor
  · rintro ⟨⟨y₁, y₂⟩, hy, hyuv⟩
    obtain ⟨z, hz, hΦz⟩ := (LinearPMap.mem_graph_iff _).1 hy
    simp only at hz hΦz
    subst hz hΦz
    have hu : u = circularCoordinates (z : 𝓗 × 𝓗) := (congrArg Prod.fst hyuv).symm
    have hv : v = circularCoordinates (doubledValuationFrame a ell z) :=
      (congrArg Prod.snd hyuv).symm
    rw [circularCoordinates_doubledValuationFrame ha ell z] at hv
    rw [circularCoordinates_coe] at hu
    subst hu hv
    exact ⟨⟨(depthProdFst ell z + Complex.I • depthProdSnd ell z).2, rfl⟩,
      ⟨(depthProdFst ell z - Complex.I • depthProdSnd ell z).2, rfl⟩⟩
  · rintro ⟨⟨h1, hv1⟩, ⟨h2, hv2⟩⟩
    have hwD : u ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell) := Submodule.mem_prod.2 ⟨h1, h2⟩
    let z : (doubledValuationFrame a ell).domain :=
      ⟨circularCoordinates.symm u, circularCoordinates_symm_mem_prod hwD⟩
    have hWz : circularCoordinates (z : 𝓗 × 𝓗) = u := circularCoordinates.apply_symm_apply _
    refine ⟨((z : 𝓗 × 𝓗), doubledValuationFrame a ell z), LinearPMap.mem_graph _ z, ?_⟩
    have hp : (depthProdFst ell z + Complex.I • depthProdSnd ell z : burnolDepthSpan ell) = ⟨u.1, h1⟩ :=
      Subtype.ext (congrArg Prod.fst ((circularCoordinates_coe z).symm.trans hWz))
    have hm : (depthProdFst ell z - Complex.I • depthProdSnd ell z : burnolDepthSpan ell) = ⟨u.2, h2⟩ :=
      Subtype.ext (congrArg Prod.snd ((circularCoordinates_coe z).symm.trans hWz))
    refine Prod.ext hWz ?_
    change circularCoordinates (doubledValuationFrame a ell z) = v
    rw [circularCoordinates_doubledValuationFrame ha ell z, hp, hm]
    exact Prod.ext hv1.symm hv2.symm

/-- The closure of a scaled core restriction. -/
theorem smul_domRestrict_closure {c : ℂ} (hc : c ≠ 0) (T : 𝓗 →ₗ.[ℂ] 𝓗) {D : Submodule ℂ 𝓗}
    (hD : D ≤ T.domain) (hcore : (T.domRestrict D).graph.topologicalClosure = T.graph) :
    ((c • T).domRestrict D).graph.topologicalClosure = (c • T).graph := by
  have hD' : D ≤ (c • T).domain := by rwa [LinearPMap.smul_domain]
  have heq : ((c • T).domRestrict D).graph =
      (T.domRestrict D).graph.map (LinearMap.id.prodMap (c • LinearMap.id)) := by
    ext ⟨x, y⟩
    rw [mem_graph_domRestrict_iff hD', Submodule.mem_map]
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨(x, T ⟨x, hD hx⟩), (mem_graph_domRestrict_iff hD).2 ⟨hx, rfl⟩,
        by rw [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.id_apply,
          LinearPMap.smul_apply]⟩
    · rintro ⟨⟨x', y'⟩, hxy, hmap⟩
      obtain ⟨hx', rfl⟩ := (mem_graph_domRestrict_iff hD).1 hxy
      rw [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Prod.mk.injEq] at hmap
      obtain ⟨rfl, rfl⟩ := hmap
      exact ⟨hx', by rw [LinearPMap.smul_apply]⟩
  rw [heq, closure_map_prodSmul hc, hcore, ← LinearPMap.smul_graph]

theorem circularPhase_ne_zero {a : ℝ} (ha : a ≠ 0) : circularPhase a ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [norm_circularPhase ha]; norm_num)

/-- **Circular closure.**  The closure of the conjugated doubled frame is
`ζ T_{ζ,|a|/2} ⊕ (-ζ) T_{-ζ,|a|/2}`, `ζ = sgn(a) i`; for `a > 0` this is `i T_{i,a/2} ⊕ -i T_{-i,a/2}`
and for `a < 0` the summands are exchanged. -/
theorem closure_map_graph_doubledValuationFrame {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    ((doubledValuationFrame a ell).graph.map circularGraphMap).topologicalClosure =
      (pmapDiagSum (circularSummandPlus ha) (circularSummandMinus ha)).graph := by
  rw [map_graph_doubledValuationFrame ha ell]
  exact diagSum_domRestrict_closure
    (smul_domRestrict_closure (circularPhase_ne_zero ha) _
      (burnolDepthSpan_le_domain_burnolCayley _ _ ell) (burnolCayley_graph_core _ _ ell))
    (smul_domRestrict_closure (neg_ne_zero.2 (circularPhase_ne_zero ha)) _
      (burnolDepthSpan_le_domain_burnolCayley _ _ ell) (burnolCayley_graph_core _ _ ell))

/-- The domain of the closure is `Ran(I + ζK_h) × Ran(I - ζK_h)`. -/
theorem domain_diagSum_circular {a : ℝ} (ha : a ≠ 0) :
    (pmapDiagSum (circularSummandPlus ha) (circularSummandMinus ha)).domain =
      (LinearMap.range ((1 + cayleyShift (circularPhase a) (circularRate a) :
          𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ[ℂ] 𝓗)).prod
        (LinearMap.range ((1 + cayleyShift (-circularPhase a) (circularRate a) :
          𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ[ℂ] 𝓗)) := rfl

/-- The graph-map is a homeomorphism. -/
def circularGraphHomeomorph : ((𝓗 × 𝓗) × (𝓗 × 𝓗)) ≃ₜ ((𝓗 × 𝓗) × (𝓗 × 𝓗)) :=
  circularCoordinates.toHomeomorph.prodCongr circularCoordinates.toHomeomorph

theorem coe_circularGraphMap : ⇑circularGraphMap = circularGraphHomeomorph := rfl

/-- **Closability.**  The doubled valuation frame is closable. -/
theorem doubledValuationFrame_isClosable {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    (doubledValuationFrame a ell).IsClosable := by
  set G := (doubledValuationFrame a ell).graph.topologicalClosure
  have hG : ∀ x ∈ G, x.1 = 0 → x.2 = 0 := by
    rintro ⟨x, y⟩ hxy hx
    simp only at hx ⊢
    subst hx
    have hmap : circularGraphMap ((0 : 𝓗 × 𝓗), y) ∈
        ((pmapDiagSum (circularSummandPlus ha) (circularSummandMinus ha)).graph : Set _) := by
      rw [← closure_map_graph_doubledValuationFrame ha ell, Submodule.topologicalClosure_coe,
        Submodule.map_coe, coe_circularGraphMap, ← circularGraphHomeomorph.image_closure,
        ← Submodule.topologicalClosure_coe]
      exact Set.mem_image_of_mem _ hxy
    rw [graph_diagSum] at hmap
    change ((circularCoordinates (0 : 𝓗 × 𝓗)).1, (circularCoordinates y).1) ∈ _ ∧
      ((circularCoordinates (0 : 𝓗 × 𝓗)).2, (circularCoordinates y).2) ∈ _ at hmap
    rw [map_zero] at hmap
    have e1 := (circularSummandPlus ha).graph_fst_eq_zero_snd hmap.1 rfl
    have e2 := (circularSummandMinus ha).graph_fst_eq_zero_snd hmap.2 rfl
    have hWy : circularCoordinates y = 0 := Prod.ext e1 e2
    simpa using congrArg circularCoordinates.symm hWy
  exact ⟨G.toLinearPMap, (Submodule.toLinearPMap_graph_eq G hG).symm⟩

/-- A Cayley transform is unbounded on any depth core. -/
theorem not_bounded_on_core_burnolCayley {h : ℝ≥0} {ζ : ℂ} (hh : 0 < h) (hζ : ‖ζ‖ = 1)
    (ell : Ioi (0 : ℝ)) :
    ¬ ∃ M : ℝ, ∀ x : burnolDepthSpan ell,
      ‖burnolCayley hh hζ ⟨x, burnolDepthSpan_le_domain_burnolCayley hh hζ ell x.2⟩‖ ≤
        M * ‖(x : 𝓗)‖ := by
  rintro ⟨M, hM⟩
  have hset : IsClosed {z : 𝓗 × 𝓗 | ‖z.2‖ ≤ M * ‖z.1‖} :=
    isClosed_le continuous_snd.norm (continuous_const.mul continuous_fst.norm)
  have hcore : (((burnolCayley hh hζ).domRestrict (burnolDepthSpan ell)).graph : Set _) ⊆
      {z : 𝓗 × 𝓗 | ‖z.2‖ ≤ M * ‖z.1‖} := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, rfl⟩ := (mem_graph_domRestrict_iff
      (burnolDepthSpan_le_domain_burnolCayley hh hζ ell)).1 hxy
    exact hM ⟨x, hx⟩
  have hgc := burnolCayley_graph_core hh hζ ell
  have hall : (((burnolCayley hh hζ).graph : Set _)) ⊆ {z : 𝓗 × 𝓗 | ‖z.2‖ ≤ M * ‖z.1‖} := by
    rw [← hgc, Submodule.topologicalClosure_coe]
    exact closure_minimal hcore hset
  refine not_bounded_burnolCayley hh hζ ⟨M, fun x => ?_⟩
  have hx := hall (LinearPMap.mem_graph (burnolCayley hh hζ) x)
  simpa only [Set.mem_setOf_eq] using hx

theorem norm_circularCoordinates_symm_left (y : 𝓗) :
    ‖circularCoordinates.symm (y, 0)‖ = ‖y‖ / 2 := by
  rw [circularCoordinates_symm_apply, Prod.norm_def]
  simp only [add_zero, zero_sub, smul_neg, norm_neg, norm_smul, norm_inv, Complex.norm_ofNat,
    norm_div, Complex.norm_I]
  rw [one_div, max_self]
  ring

/-- **Unboundedness.**  The doubled valuation frame is unbounded. -/
theorem not_bounded_doubledValuationFrame {a : ℝ} (ha : a ≠ 0) (ell : Ioi (0 : ℝ)) :
    ¬ ∃ M : ℝ, ∀ z : (doubledValuationFrame a ell).domain,
      ‖doubledValuationFrame a ell z‖ ≤ M * ‖(z : 𝓗 × 𝓗)‖ := by
  rintro ⟨M, hM⟩
  refine not_bounded_on_core_burnolCayley (circularRate_pos ha) (norm_circularPhase ha) ell
    ⟨M, fun x => ?_⟩
  have hx0 : ((x : 𝓗), (0 : 𝓗)) ∈ (burnolDepthSpan ell).prod (burnolDepthSpan ell) :=
    Submodule.mem_prod.2 ⟨x.2, Submodule.zero_mem _⟩
  let z : (doubledValuationFrame a ell).domain :=
    ⟨circularCoordinates.symm ((x : 𝓗), 0), circularCoordinates_symm_mem_prod hx0⟩
  have hWz : circularCoordinates (z : 𝓗 × 𝓗) = ((x : 𝓗), 0) := circularCoordinates.apply_symm_apply _
  have hp : (depthProdFst ell z + Complex.I • depthProdSnd ell z : burnolDepthSpan ell) = x :=
    Subtype.ext (congrArg Prod.fst ((circularCoordinates_coe z).symm.trans hWz))
  have hm : (depthProdFst ell z - Complex.I • depthProdSnd ell z : burnolDepthSpan ell) = 0 :=
    Subtype.ext (congrArg Prod.snd ((circularCoordinates_coe z).symm.trans hWz))
  have hΦ : doubledValuationFrame a ell z = circularCoordinates.symm (plusCore ha ell x, 0) := by
    have h1 := circularCoordinates_doubledValuationFrame ha ell z
    rw [hp, hm, map_zero] at h1
    rw [← h1, circularCoordinates.symm_apply_apply]
  have hb := hM z
  rw [hΦ, norm_circularCoordinates_symm_left] at hb
  change _ ≤ M * ‖circularCoordinates.symm ((x : 𝓗), 0)‖ at hb
  rw [norm_circularCoordinates_symm_left] at hb
  have hplus : plusCore ha ell x = circularPhase a • burnolCayley (circularRate_pos ha)
      (norm_circularPhase ha) ⟨x, burnolDepthSpan_le_domain_burnolCayley _ _ ell x.2⟩ := rfl
  rw [hplus, norm_smul, norm_circularPhase ha, one_mul] at hb
  linarith

end GaloisForLFunctions.HTGeometry
