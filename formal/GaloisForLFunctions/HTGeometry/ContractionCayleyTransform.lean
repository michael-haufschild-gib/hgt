import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The Cayley transform of a contraction without eigenvalue `-1`

Let `V` be a contraction on a complex Hilbert space such that neither `V` nor `V^*` has the
eigenvalue `-1`.  Then `I + V` is injective with dense range and the Cayley transform
`T = (I - V)(I + V)⁻¹`, with domain `Ran(I + V)`, is densely defined, closed and maximal accretive:
its graph is `{((I+V)g, (I-V)g)}`, `‖(I+V)g‖² + ‖(I-V)g‖² = 2(‖g‖² + ‖Vg‖²)`,
`Re⟨T x, x⟩ = ‖g‖² - ‖Vg‖²`, and `I + T` is onto.  The image under `I + V` of any dense subspace is
a graph core.  A unit sequence with `(I + V)u_n → 0` makes `T` unbounded.

For `0 ≤ r < 1` the attenuated transform `T_r = (I - rV)(I + rV)⁻¹` is bounded by
`(1+r)/(1-r)`, and the identity `T_r - α = -(2r/(1-r))(I + V)(I + rV)⁻¹`, `α = (1+r)/(1-r)`, shows
that a weakly null unit sequence with `(I+V)u_n → 0` forces `‖T_r - C‖ ≥ α` for every compact `C`:
norm and essential norm are both `α`, and no bounded `B` solves `B(I+V+C) = I-V-C`.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace CayleyTransform

variable (V : H →L[ℂ] H)

/-! ## The domain `Ran(I + V)` -/

theorem injective_one_add (hV : ∀ x, V x = -x → x = 0) :
    Function.Injective (⇑(1 + V : H →L[ℂ] H)) := by
  intro x y hxy
  have h : V (x - y) = -(x - y) := by
    have : (1 + V) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    simp only [add_apply, one_apply_eq_self] at this
    linear_combination (norm := module) this
  exact sub_eq_zero.1 (hV _ h)

theorem denseRange_one_add [CompleteSpace H] (hVa : ∀ x, ContinuousLinearMap.adjoint V x = -x → x = 0) :
    Dense (LinearMap.range ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.orthogonal_range, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine hVa x ?_
  have : (ContinuousLinearMap.adjoint (1 + V)) x = 0 := hx
  rw [map_add, ContinuousLinearMap.adjoint_one, add_apply,
    one_apply_eq_self] at this
  linear_combination (norm := module) this

/-- The Cayley transform `T = (I - V)(I + V)⁻¹` with domain `Ran(I + V)`. -/
def cayleyPMap (hV : ∀ x, V x = -x → x = 0) : H →ₗ.[ℂ] H where
  domain := LinearMap.range ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H)
  toFun := ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ
    (LinearEquiv.ofInjective ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H)
      (injective_one_add V hV)).symm.toLinearMap

variable {V}

theorem mem_domain_cayleyPMap (hV : ∀ x, V x = -x → x = 0) (g : H) :
    (1 + V) g ∈ (cayleyPMap V hV).domain := ⟨g, rfl⟩

theorem cayleyPMap_apply (hV : ∀ x, V x = -x → x = 0) (g : H) :
    cayleyPMap V hV ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩ = (1 - V) g := by
  have hsymm : (LinearEquiv.ofInjective ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H)
      (injective_one_add V hV)).symm ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩ = g := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    rfl
  change ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H)
    ((LinearEquiv.ofInjective ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H)
      (injective_one_add V hV)).symm ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩) = _
  rw [hsymm]
  rfl

theorem exists_eq_of_mem_domain (hV : ∀ x, V x = -x → x = 0) (x : (cayleyPMap V hV).domain) :
    ∃ g, (x : H) = (1 + V) g ∧ cayleyPMap V hV x = (1 - V) g := by
  obtain ⟨g, hg⟩ := x.2
  refine ⟨g, hg.symm, ?_⟩
  have hx : x = ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩ := Subtype.ext hg.symm
  rw [hx, cayleyPMap_apply]

/-- The graph map `g ↦ ((I+V)g, (I-V)g)`. -/
def graphMap (V : H →L[ℂ] H) : H →L[ℂ] H × H := (1 + V).prod (1 - V)

theorem graph_cayleyPMap (hV : ∀ x, V x = -x → x = 0) :
    ((cayleyPMap V hV).graph : Set (H × H)) = Set.range (graphMap V) := by
  ext ⟨x, y⟩
  simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_range, graphMap,
    ContinuousLinearMap.prod_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, hTz⟩
    obtain ⟨g, hg, hTg⟩ := exists_eq_of_mem_domain hV z
    exact ⟨g, hg ▸ hz, hTg ▸ hTz⟩
  · rintro ⟨g, hx, hy⟩
    exact ⟨⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩, hx, by rw [cayleyPMap_apply, hy]⟩

/-- `g = ((I+V)g + (I-V)g)/2`: the graph map has a continuous left inverse. -/
theorem graphMap_leftInverse (g : H) :
    (2 : ℂ)⁻¹ • ((graphMap V g).1 + (graphMap V g).2) = g := by
  simp only [graphMap, ContinuousLinearMap.prod_apply, add_apply,
    sub_apply, one_apply_eq_self]
  rw [show g + V g + (g - V g) = (2 : ℂ) • g by rw [two_smul]; abel, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

theorem isClosed_range_graphMap : IsClosed (Set.range (graphMap V)) := by
  have hrange : Set.range (graphMap V) =
      {z : H × H | graphMap V ((2 : ℂ)⁻¹ • (z.1 + z.2)) = z} := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      simp only [Set.mem_setOf_eq, graphMap_leftInverse]
    · intro hz
      exact ⟨_, hz⟩
  rw [hrange]
  exact isClosed_eq ((graphMap V).continuous.comp ((continuous_fst.add continuous_snd).const_smul _))
    continuous_id

/-- **Closedness.** -/
theorem cayleyPMap_isClosed (hV : ∀ x, V x = -x → x = 0) : (cayleyPMap V hV).IsClosed := by
  change IsClosed ((cayleyPMap V hV).graph : Set (H × H))
  rw [graph_cayleyPMap]
  exact isClosed_range_graphMap

/-- **Dense domain.** -/
theorem dense_domain_cayleyPMap [CompleteSpace H] (hV : ∀ x, V x = -x → x = 0)
    (hVa : ∀ x, ContinuousLinearMap.adjoint V x = -x → x = 0) :
    Dense ((cayleyPMap V hV).domain : Set H) :=
  denseRange_one_add V hVa

/-- **Graph-norm identity.**  `‖(I+V)g‖² + ‖(I-V)g‖² = 2(‖g‖² + ‖Vg‖²)`. -/
theorem norm_sq_add_norm_sq_graph (g : H) :
    ‖(1 + V) g‖ ^ 2 + ‖(1 - V) g‖ ^ 2 = 2 * (‖g‖ ^ 2 + ‖V g‖ ^ 2) := by
  simp only [add_apply, sub_apply,
    one_apply_eq_self]
  have := parallelogram_law_with_norm ℂ g (V g)
  nlinarith [this]

/-- `Re⟨(I-V)g, (I+V)g⟩ = ‖g‖² - ‖Vg‖²`. -/
theorem re_inner_cayley (g : H) :
    (⟪(1 - V) g, (1 + V) g⟫_ℂ).re = ‖g‖ ^ 2 - ‖V g‖ ^ 2 := by
  simp only [add_apply, sub_apply,
    one_apply_eq_self, inner_sub_left, inner_add_right, Complex.sub_re,
    Complex.add_re]
  have h1 : (⟪g, g⟫_ℂ).re = ‖g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : (⟪V g, V g⟫_ℂ).re = ‖V g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h3 : (⟪g, V g⟫_ℂ).re = (⟪V g, g⟫_ℂ).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  rw [h1, h2, h3]
  ring

/-- Accretivity of a partially defined operator. -/
def IsAccretivePMap (S : H →ₗ.[ℂ] H) : Prop := ∀ x : S.domain, 0 ≤ (⟪S x, (x : H)⟫_ℂ).re

/-- **Accretivity.**  `Re⟨T x, x⟩ = ‖g‖² - ‖Vg‖² ≥ 0` for `x = (I+V)g`. -/
theorem isAccretive_cayleyPMap (hV : ∀ x, V x = -x → x = 0) (hn : ‖V‖ ≤ 1) :
    IsAccretivePMap (cayleyPMap V hV) := by
  intro x
  obtain ⟨g, hg, hTg⟩ := exists_eq_of_mem_domain hV x
  rw [hTg, hg, re_inner_cayley, sub_nonneg]
  have h1 : ‖V g‖ ≤ ‖g‖ := (V.le_opNorm g).trans (by nlinarith [norm_nonneg g])
  nlinarith [norm_nonneg (V g)]

/-- **`I + T` is onto.**  `(I+T)(I+V)g = 2g`. -/
theorem surjective_one_add_cayleyPMap (hV : ∀ x, V x = -x → x = 0) (y : H) :
    ∃ x : (cayleyPMap V hV).domain, (x : H) + cayleyPMap V hV x = y := by
  refine ⟨⟨(1 + V) ((2 : ℂ)⁻¹ • y), mem_domain_cayleyPMap hV _⟩, ?_⟩
  rw [cayleyPMap_apply]
  simp only [add_apply, sub_apply, one_apply_eq_self]
  rw [show (2 : ℂ)⁻¹ • y + V ((2 : ℂ)⁻¹ • y) + ((2 : ℂ)⁻¹ • y - V ((2 : ℂ)⁻¹ • y)) =
    ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹) • y by rw [add_smul]; abel]
  rw [show ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹) = 1 by norm_num, one_smul]

/-- **Maximal accretivity.**  Every accretive extension of `T` equals `T`. -/
theorem eq_of_isAccretive_of_le (hV : ∀ x, V x = -x → x = 0) {S : H →ₗ.[ℂ] H}
    (hS : IsAccretivePMap S) (hle : cayleyPMap V hV ≤ S) : S = cayleyPMap V hV := by
  have hdom : S.domain ≤ (cayleyPMap V hV).domain := by
    intro x hx
    obtain ⟨u, hu⟩ := surjective_one_add_cayleyPMap hV (x + S ⟨x, hx⟩)
    have huS : (u : H) ∈ S.domain := hle.1 u.2
    have hSu : S ⟨u, huS⟩ = cayleyPMap V hV u := (hle.2 rfl).symm
    have hSv : S (⟨x, hx⟩ - ⟨u, huS⟩) = -(x - u) := by
      rw [show S (⟨x, hx⟩ - ⟨u, huS⟩) = S ⟨x, hx⟩ - S ⟨u, huS⟩ from
        S.toFun.map_sub _ _, hSu]
      linear_combination (norm := module) (-1 : ℂ) • hu
    have hre := hS (⟨x, hx⟩ - ⟨u, huS⟩)
    have hcoe : ((⟨x, hx⟩ - ⟨u, huS⟩ : S.domain) : H) = x - u := rfl
    have hself : (⟪x - (u : H), x - u⟫_ℂ).re = ‖x - (u : H)‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [hSv, hcoe, inner_neg_left, Complex.neg_re, hself] at hre
    have hv0 : x - (u : H) = 0 := by
      have : ‖x - (u : H)‖ ^ 2 ≤ 0 := by linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
    rw [sub_eq_zero.1 hv0]
    exact u.2
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

/-- **Graph core.**  For a dense subspace `D`, the restriction of `T` to `(I+V)D` has closure `T`. -/
theorem graph_domRestrict_closure (hV : ∀ x, V x = -x → x = 0) (D : Submodule ℂ H)
    (hD : Dense (D : Set H)) :
    ((cayleyPMap V hV).domRestrict (D.map ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H))).graph.topologicalClosure
      = (cayleyPMap V hV).graph := by
  have hgr : (((cayleyPMap V hV).domRestrict
      (D.map ((1 + V : H →L[ℂ] H) : H →ₗ[ℂ] H))).graph : Set (H × H)) = graphMap V '' D := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_image, graphMap,
      ContinuousLinearMap.prod_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨z, hz, hTz⟩
      obtain ⟨g, hgD, hg⟩ := (Submodule.mem_inf.1 z.2).1
      have hzT : (z : H) ∈ (cayleyPMap V hV).domain := (Submodule.mem_inf.1 z.2).2
      refine ⟨g, hgD, hg.trans hz, ?_⟩
      rw [← hTz, LinearPMap.domRestrict_apply (x := z) (y := ⟨z, hzT⟩) rfl]
      have hzeq : (⟨z, hzT⟩ : (cayleyPMap V hV).domain) =
          ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩ := Subtype.ext hg.symm
      rw [hzeq, cayleyPMap_apply]
    · rintro ⟨g, hgD, hx, hy⟩
      refine ⟨⟨(1 + V) g, Submodule.mem_inf.2 ⟨⟨g, hgD, rfl⟩, mem_domain_cayleyPMap hV g⟩⟩, hx, ?_⟩
      rw [LinearPMap.domRestrict_apply (y := ⟨(1 + V) g, mem_domain_cayleyPMap hV g⟩) rfl,
        cayleyPMap_apply, hy]
  refine SetLike.coe_injective ?_
  rw [Submodule.topologicalClosure_coe, hgr, graph_cayleyPMap]
  apply le_antisymm
  · exact closure_minimal (Set.image_subset_range _ _) isClosed_range_graphMap
  · rintro _ ⟨g, rfl⟩
    have := map_mem_closure (graphMap V).continuous (hD g) (fun z hz => Set.mem_image_of_mem _ hz)
    exact this

/-- **Unboundedness.**  A unit sequence with `(I+V)u_n → 0` makes `T` unbounded. -/
theorem not_bounded_cayleyPMap (hV : ∀ x, V x = -x → x = 0) {u : ℕ → H}
    (hu1 : ∀ n, ‖u n‖ = 1) (hu : Tendsto (fun n => (1 + V) (u n)) atTop (𝓝 0)) :
    ¬ ∃ C : ℝ, ∀ x : (cayleyPMap V hV).domain, ‖cayleyPMap V hV x‖ ≤ C * ‖(x : H)‖ := by
  rintro ⟨C, hC⟩
  have hbound : ∀ n, 2 - ‖(1 + V) (u n)‖ ≤ C * ‖(1 + V) (u n)‖ := fun n => by
    have h := hC ⟨(1 + V) (u n), mem_domain_cayleyPMap hV (u n)⟩
    rw [cayleyPMap_apply] at h
    have hsum : (1 - V) (u n) = (2 : ℂ) • u n - (1 + V) (u n) := by
      simp only [add_apply, sub_apply,
        one_apply_eq_self, two_smul]
      abel
    have h2 : 2 - ‖(1 + V) (u n)‖ ≤ ‖(1 - V) (u n)‖ := by
      rw [hsum]
      have := norm_sub_norm_le ((2 : ℂ) • u n) ((1 + V) (u n))
      rw [norm_smul, hu1, mul_one, Complex.norm_ofNat] at this
      linarith
    exact h2.trans h
  have hn := hu.norm
  rw [norm_zero] at hn
  have hlim : Tendsto (fun n => C * ‖(1 + V) (u n)‖ + ‖(1 + V) (u n)‖) atTop (𝓝 0) := by
    simpa using (hn.const_mul C).add hn
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 2 by norm_num))
  obtain ⟨n, hn'⟩ := hev.exists
  linarith [hbound n]

/-! ## The attenuated Cayley transform -/

variable (V)

theorem norm_smul_lt_one (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ‖-((r : ℂ) • V)‖ < 1 := by
  rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0]
  exact lt_of_le_of_lt (mul_le_of_le_one_right hr0 hn) hr

variable [CompleteSpace H]

/-- The unit `I + rV`. -/
def attenuationUnit (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : (H →L[ℂ] H)ˣ :=
  Units.oneSub (-((r : ℂ) • V)) (norm_smul_lt_one V hn hr0 hr)

theorem attenuationUnit_val (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    (attenuationUnit V hn hr0 hr : H →L[ℂ] H) = 1 + (r : ℂ) • V := by
  rw [attenuationUnit, Units.val_oneSub, sub_neg_eq_add]

/-- The attenuated Cayley transform `T_r = (I - rV)(I + rV)⁻¹`. -/
def attenuatedCayley (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : H →L[ℂ] H :=
  (1 - (r : ℂ) • V) * ↑(attenuationUnit V hn hr0 hr)⁻¹

variable {V}

theorem norm_attenuationUnit_inv_apply_le (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (x : H) : ‖(↑(attenuationUnit V hn hr0 hr)⁻¹ : H →L[ℂ] H) x‖ ≤ ‖x‖ / (1 - r) := by
  set y := (↑(attenuationUnit V hn hr0 hr)⁻¹ : H →L[ℂ] H) x
  have hxy : x = (1 + (r : ℂ) • V) y := by
    rw [← attenuationUnit_val V hn hr0 hr]
    simp only [y, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
  have hlow : (1 - r) * ‖y‖ ≤ ‖x‖ := by
    rw [hxy, add_apply, one_apply_eq_self,
      smul_apply]
    have h1 : ‖(r : ℂ) • V y‖ ≤ r * ‖y‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left ((V.le_opNorm y).trans
        (mul_le_of_le_one_left (norm_nonneg y) hn)) hr0
    have h2 := norm_sub_norm_le y (-((r : ℂ) • V y))
    rw [sub_neg_eq_add, norm_neg] at h2
    linarith
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Neumann bound.**  `‖T_r‖ ≤ (1+r)/(1-r)`. -/
theorem norm_attenuatedCayley_le (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ‖attenuatedCayley V hn hr0 hr‖ ≤ (1 + r) / (1 - r) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by linarith) (by linarith))
    fun x => ?_
  rw [attenuatedCayley, mul_apply_eq_comp]
  set y := (↑(attenuationUnit V hn hr0 hr)⁻¹ : H →L[ℂ] H) x
  have hy := norm_attenuationUnit_inv_apply_le hn hr0 hr x
  have h1 : ‖(1 - (r : ℂ) • V) y‖ ≤ (1 + r) * ‖y‖ := by
    rw [sub_apply, one_apply_eq_self, smul_apply]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0]
    have := mul_le_mul_of_nonneg_left ((V.le_opNorm y).trans
      (mul_le_of_le_one_left (norm_nonneg y) hn)) hr0
    linarith
  calc ‖(1 - (r : ℂ) • V) y‖ ≤ (1 + r) * ‖y‖ := h1
    _ ≤ (1 + r) * (‖x‖ / (1 - r)) := mul_le_mul_of_nonneg_left hy (by linarith)
    _ = (1 + r) / (1 - r) * ‖x‖ := by ring

/-- `T_r - α = -(2r/(1-r)) (I+rV)⁻¹ (I+V)`, `α = (1+r)/(1-r)`. -/
theorem attenuatedCayley_sub_smul (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    attenuatedCayley V hn hr0 hr - (((1 + r) / (1 - r) : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      -(((2 * r / (1 - r) : ℝ) : ℂ)) • ((↑(attenuationUnit V hn hr0 hr)⁻¹ : H →L[ℂ] H) * (1 + V)) := by
  have hr1 : (1 - r : ℝ) ≠ 0 := by linarith
  set u := attenuationUnit V hn hr0 hr
  have hcomm : Commute (1 + V) (u : H →L[ℂ] H) := by
    rw [attenuationUnit_val]
    have hV1 : Commute (1 + V) V := (Commute.one_left V).add_left (Commute.refl V)
    exact (Commute.one_right _).add_right (hV1.smul_right _)
  have hcomm' : Commute (1 + V) (↑u⁻¹ : H →L[ℂ] H) := hcomm.units_inv_right
  have hinv : (1 : H →L[ℂ] H) = (u : H →L[ℂ] H) * ↑u⁻¹ := u.mul_inv.symm
  have key : attenuatedCayley V hn hr0 hr - (((1 + r) / (1 - r) : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      ((1 - (r : ℂ) • V) - (((1 + r) / (1 - r) : ℝ) : ℂ) • (1 + (r : ℂ) • V)) * ↑u⁻¹ := by
    rw [sub_mul, smul_mul_assoc, ← attenuationUnit_val V hn hr0 hr, ← hinv]
    rfl
  have hlin : (1 - (r : ℂ) • V) - (((1 + r) / (1 - r) : ℝ) : ℂ) • (1 + (r : ℂ) • V) =
      -(((2 * r / (1 - r) : ℝ) : ℂ)) • (1 + V) := by
    have e1r : (1 + r) / (1 - r) = 1 + 2 * r / (1 - r) := by
      field_simp
      ring
    have e2r : (1 + r) / (1 - r) * r = 2 * r / (1 - r) - r := by
      field_simp
      ring
    have e1 : (((1 + r) / (1 - r) : ℝ) : ℂ) = 1 + ((2 * r / (1 - r) : ℝ) : ℂ) := by
      rw [e1r]
      push_cast
      ring
    have e2 : (((1 + r) / (1 - r) : ℝ) : ℂ) * (r : ℂ) = ((2 * r / (1 - r) : ℝ) : ℂ) - (r : ℂ) := by
      rw [← Complex.ofReal_mul, e2r]
      push_cast
      ring
    rw [smul_add, smul_smul, e2, e1]
    module
  rw [key, hlin, smul_mul_assoc, hcomm'.eq]

/-- **Essential norm.**  A weakly null unit sequence with `(I+V)u_n → 0` forces
`‖T_r - C‖ ≥ (1+r)/(1-r)` for every compact `C`. -/
theorem le_norm_attenuatedCayley_sub_compact (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {u : ℕ → H} (hu1 : ∀ n, ‖u n‖ = 1) (hweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0))
    (hu : Tendsto (fun n => (1 + V) (u n)) atTop (𝓝 0)) {C : H →L[ℂ] H} (hC : IsCompactOperator C) :
    (1 + r) / (1 - r) ≤ ‖attenuatedCayley V hn hr0 hr - C‖ := by
  set α := (1 + r) / (1 - r)
  set T := attenuatedCayley V hn hr0 hr
  have hdiff : Tendsto (fun n => (T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n)) atTop (𝓝 0) := by
    rw [attenuatedCayley_sub_smul]
    have := ((↑(attenuationUnit V hn hr0 hr)⁻¹ : H →L[ℂ] H).continuous.tendsto 0).comp hu
    rw [map_zero] at this
    have h2 := this.const_smul (-(((2 * r / (1 - r) : ℝ) : ℂ)))
    rw [smul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, smul_apply, mul_apply_eq_comp]
  have hCu := tendsto_norm_compact_of_weaklyNull C hC u (fun n => (hu1 n).le) hweak
  have hlow : ∀ n, α - ‖(T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n)‖ - ‖C (u n)‖ ≤ ‖T - C‖ :=
    fun n => by
      have hsplit : (T - C) (u n) = ((α : ℝ) : ℂ) • u n +
          (T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n) - C (u n) := by
        simp only [sub_apply, smul_apply,
          one_apply_eq_self]
        abel
      have h1 : ‖(T - C) (u n)‖ ≤ ‖T - C‖ := by
        have := (T - C).le_opNorm (u n)
        rwa [hu1, mul_one] at this
      have h2 : α - ‖(T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n)‖ - ‖C (u n)‖ ≤ ‖(T - C) (u n)‖ := by
        rw [hsplit]
        have hα : ‖((α : ℝ) : ℂ) • u n‖ = α := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by
            have : 0 < 1 - r := by linarith
            positivity), hu1, mul_one]
        have e1 := norm_sub_norm_le (((α : ℝ) : ℂ) • u n + (T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n))
          (C (u n))
        have e2 := norm_sub_norm_le (((α : ℝ) : ℂ) • u n)
          (-((T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n)))
        rw [sub_neg_eq_add, norm_neg, hα] at e2
        linarith
      exact h2.trans h1
  have hlim : Tendsto (fun n => α - ‖(T - ((α : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (u n)‖ - ‖C (u n)‖)
      atTop (𝓝 α) := by
    simpa using (tendsto_const_nhds.sub hdiff.norm).sub hCu.norm
  exact le_of_tendsto hlim (Eventually.of_forall hlow)

/-- **Norm.**  `‖T_r‖ = (1+r)/(1-r)`. -/
theorem norm_attenuatedCayley (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {u : ℕ → H} (hu1 : ∀ n, ‖u n‖ = 1) (hweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0))
    (hu : Tendsto (fun n => (1 + V) (u n)) atTop (𝓝 0)) :
    ‖attenuatedCayley V hn hr0 hr‖ = (1 + r) / (1 - r) := by
  refine le_antisymm (norm_attenuatedCayley_le hn hr0 hr) ?_
  have := le_norm_attenuatedCayley_sub_compact hn hr0 hr hu1 hweak hu
    (C := 0) isCompactOperator_zero
  rwa [sub_zero] at this

/-- **Essential norm.**  `inf_{C compact} ‖T_r - C‖ = (1+r)/(1-r)`. -/
theorem sInf_norm_attenuatedCayley_sub_compact (hn : ‖V‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {u : ℕ → H} (hu1 : ∀ n, ‖u n‖ = 1) (hweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0))
    (hu : Tendsto (fun n => (1 + V) (u n)) atTop (𝓝 0)) :
    sInf {s | ∃ C : H →L[ℂ] H, IsCompactOperator C ∧ s = ‖attenuatedCayley V hn hr0 hr - C‖} =
      (1 + r) / (1 - r) := by
  refine le_antisymm (csInf_le ⟨0, ?_⟩ ⟨0, isCompactOperator_zero, ?_⟩) (le_csInf ⟨_, 0,
    isCompactOperator_zero, rfl⟩ ?_)
  · rintro _ ⟨C, -, rfl⟩
    exact norm_nonneg _
  · rw [sub_zero, norm_attenuatedCayley hn hr0 hr hu1 hweak hu]
  · rintro _ ⟨C, hC, rfl⟩
    exact le_norm_attenuatedCayley_sub_compact hn hr0 hr hu1 hweak hu hC

/-- **No compact repair.**  No bounded `B` satisfies `B(I+V+C) = I-V-C` with `C` compact. -/
theorem no_bounded_compact_repair {u : ℕ → H} (hu1 : ∀ n, ‖u n‖ = 1)
    (hweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0))
    (hu : Tendsto (fun n => (1 + V) (u n)) atTop (𝓝 0)) (B : H →L[ℂ] H) {C : H →L[ℂ] H}
    (hC : IsCompactOperator C) : B * (1 + V + C) ≠ 1 - V - C := by
  intro hBC
  have hCu := tendsto_norm_compact_of_weaklyNull C hC u (fun n => (hu1 n).le) hweak
  have hL : Tendsto (fun n => (B * (1 + V + C)) (u n)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => (1 + V) (u n) + C (u n)) atTop (𝓝 0) := by
      simpa using hu.add hCu
    have := (B.continuous.tendsto 0).comp hsum
    rw [map_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, mul_apply_eq_comp, add_apply]
  have hR : ∀ n, 2 - ‖(1 + V) (u n)‖ - ‖C (u n)‖ ≤ ‖(1 - V - C) (u n)‖ := fun n => by
    have hsplit : (1 - V - C) (u n) = (2 : ℂ) • u n - (1 + V) (u n) - C (u n) := by
      simp only [sub_apply, add_apply,
        one_apply_eq_self, two_smul]
      abel
    rw [hsplit]
    have e1 := norm_sub_norm_le ((2 : ℂ) • u n - (1 + V) (u n)) (C (u n))
    have e2 := norm_sub_norm_le ((2 : ℂ) • u n) ((1 + V) (u n))
    rw [norm_smul, hu1, mul_one, Complex.norm_ofNat] at e2
    linarith
  rw [hBC] at hL
  have hn1 := hu.norm
  have hn2 := hCu.norm
  rw [norm_zero] at hn1 hn2
  have hlim : Tendsto (fun n => 2 - ‖(1 + V) (u n)‖ - ‖C (u n)‖) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.sub hn1).sub hn2
  have h2 : (2 : ℝ) ≤ 0 := by
    have := hL.norm
    rw [norm_zero] at this
    exact le_of_tendsto_of_tendsto hlim this (Eventually.of_forall hR)
  norm_num at h2

end CayleyTransform

end GaloisForLFunctions.HTGeometry
