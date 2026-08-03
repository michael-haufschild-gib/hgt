import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Small perturbations of a spanning family reach a neighbourhood

A finite family spanning a finite-dimensional real space is the column set of a surjective linear
map from coefficient space.  Surjective continuous linear maps between complete spaces are open, so
the image of any coefficient box is a neighbourhood of the origin: arbitrarily small coefficients
already reach every nearby vector.

Multiplicative perturbations of positive masses have the same reach, because the factors `exp s - 1`
cover an interval around zero.  This is the elementary content of jet controllability under small
mass perturbations, with no implicit function theorem involved.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The linear combination map of a finite family. -/
def spanCombination (w : Fin K → E) : (Fin K → ℝ) →ₗ[ℝ] E where
  toFun r := ∑ k, r k • w k
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    simp [smul_smul, Finset.smul_sum]

omit [FiniteDimensional ℝ E] in
theorem spanCombination_apply (w : Fin K → E) (r : Fin K → ℝ) :
    spanCombination w r = ∑ k, r k • w k := rfl

omit [FiniteDimensional ℝ E] in
theorem surjective_spanCombination {w : Fin K → E}
    (hspan : Submodule.span ℝ (Set.range w) = ⊤) :
    Function.Surjective (spanCombination w) := by
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range w) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  exact ⟨c, hc⟩

/-- **A spanning family reaches a neighbourhood with arbitrarily small coefficients.** -/
theorem spanCombination_smallBox_mem_nhds {w : Fin K → E}
    (hspan : Submodule.span ℝ (Set.range w) = ⊤) {δ : ℝ} (hδ : 0 < δ) :
    {x : E | ∃ r : Fin K → ℝ, (∀ k, |r k| < δ) ∧ ∑ k, r k • w k = x} ∈ nhds (0 : E) := by
  classical
  set L : (Fin K → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap (spanCombination w) with hL
  have hLsurj : Function.Surjective (L : (Fin K → ℝ) → E) := surjective_spanCombination hspan
  have hopen : IsOpen (L '' Metric.ball (0 : Fin K → ℝ) δ) :=
    L.isOpenMap hLsurj _ Metric.isOpen_ball
  have hmem : (0 : E) ∈ L '' Metric.ball (0 : Fin K → ℝ) δ := by
    refine ⟨0, Metric.mem_ball_self hδ, ?_⟩
    simp [hL, spanCombination_apply]
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  rintro x ⟨r, hr, rfl⟩
  refine ⟨r, fun k => ?_, ?_⟩
  · have hnorm : ‖r‖ < δ := by
      simpa [Metric.mem_ball, dist_zero_right] using hr
    have := (pi_norm_lt_iff hδ).mp hnorm k
    simpa [Real.norm_eq_abs] using this
  · rfl

/-- **Multiplicative perturbations of a spanning family reach a neighbourhood.**  Rescaling the
coefficients by factors `exp s` with `s` arbitrarily small already covers a neighbourhood of the
origin. -/
theorem spanCombination_expBox_mem_nhds {w : Fin K → E}
    (hspan : Submodule.span ℝ (Set.range w) = ⊤) {δ : ℝ} (hδ : 0 < δ) :
    {x : E | ∃ s : Fin K → ℝ, (∀ k, |s k| < δ) ∧ ∑ k, (Real.exp (s k) - 1) • w k = x}
      ∈ nhds (0 : E) := by
  classical
  set δ' : ℝ := min (1 - Real.exp (-δ)) (Real.exp δ - 1) with hδ'
  have hexpδ : 1 < Real.exp δ := by
    have hlt := Real.exp_lt_exp.mpr hδ
    simpa using hlt
  have hexpnegδ : Real.exp (-δ) < 1 := by
    have hlt := Real.exp_lt_exp.mpr (show -δ < 0 by linarith)
    simpa using hlt
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    exact lt_min (by linarith) (by linarith)
  refine Filter.mem_of_superset (spanCombination_smallBox_mem_nhds hspan hδ'pos) ?_
  rintro x ⟨r, hr, rfl⟩
  refine ⟨fun k => Real.log (1 + r k), fun k => ?_, ?_⟩
  · have hrk := hr k
    have hlow : Real.exp (-δ) < 1 + r k := by
      have h1 : |r k| < 1 - Real.exp (-δ) := lt_of_lt_of_le hrk (min_le_left _ _)
      have h2 := abs_lt.mp h1
      linarith [h2.1]
    have hhigh : 1 + r k < Real.exp δ := by
      have h1 : |r k| < Real.exp δ - 1 := lt_of_lt_of_le hrk (min_le_right _ _)
      have h2 := abs_lt.mp h1
      linarith [h2.2]
    have hpos : 0 < 1 + r k := lt_trans (Real.exp_pos _) hlow
    have hlog : Real.exp (Real.log (1 + r k)) = 1 + r k := Real.exp_log hpos
    refine abs_lt.mpr ⟨?_, ?_⟩
    · refine Real.exp_lt_exp.mp ?_
      rw [hlog]
      exact hlow
    · refine Real.exp_lt_exp.mp ?_
      rw [hlog]
      exact hhigh
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hrk := hr k
    have hlow : Real.exp (-δ) < 1 + r k := by
      have h1 : |r k| < 1 - Real.exp (-δ) := lt_of_lt_of_le hrk (min_le_left _ _)
      have h2 := abs_lt.mp h1
      linarith [h2.1]
    have hpos : 0 < 1 + r k := lt_trans (Real.exp_pos _) hlow
    rw [Real.exp_log hpos]
    congr 1
    ring

/-! ## Finite spanning subfamilies -/

/-- A spanning set of a finite-dimensional space has a finite spanning subset. -/
theorem exists_finset_subset_span_eq_top {s : Set E} (hs : Submodule.span ℝ s = ⊤) :
    ∃ t : Finset E, ↑t ⊆ s ∧ Submodule.span ℝ (t : Set E) = ⊤ := by
  classical
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℝ E).FG := Module.finite_def.mp inferInstance
  have hmem : ∀ x : E, x ∈ Submodule.span ℝ s := by
    intro x
    rw [hs]
    exact Submodule.mem_top
  choose S hSsub hSmem using fun x : E => Submodule.mem_span_finite_of_mem_span (hmem x)
  refine ⟨T.biUnion fun x => S x, ?_, ?_⟩
  · intro y hy
    rw [Finset.coe_biUnion] at hy
    obtain ⟨x, -, hx⟩ := Set.mem_iUnion₂.mp hy
    exact hSsub x hx
  · refine le_antisymm le_top ?_
    rw [← hT]
    refine Submodule.span_le.mpr fun x hx => ?_
    refine Submodule.span_mono ?_ (hSmem x)
    intro y hy
    rw [Finset.coe_biUnion]
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hy⟩

/-- **A spanning family has a finite spanning subfamily whose multiplicative perturbations reach a
neighbourhood.**  This is the form the mass parameter of a discrete Cauchy transform takes. -/
theorem exists_expBox_reach_of_span_range {κ : Type*} (v : κ → E)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (a : Fin K → κ), Function.Injective a ∧
      {x : E | ∃ s : Fin K → ℝ, (∀ k, |s k| < δ) ∧ ∑ k, (Real.exp (s k) - 1) • v (a k) = x}
        ∈ nhds (0 : E) := by
  classical
  obtain ⟨t, htsub, htspan⟩ := exists_finset_subset_span_eq_top hspan
  choose g hg using fun x : {y // y ∈ t} => htsub x.2
  refine ⟨t.card, fun k => g (t.equivFin.symm k), ?_, ?_⟩
  · intro k k' hkk
    have hkk' : g (t.equivFin.symm k) = g (t.equivFin.symm k') := hkk
    have hv : v (g (t.equivFin.symm k)) = v (g (t.equivFin.symm k')) := by rw [hkk']
    rw [hg, hg] at hv
    exact t.equivFin.symm.injective (Subtype.ext hv)
  refine spanCombination_expBox_mem_nhds ?_ hδ
  refine le_antisymm le_top ?_
  rw [← htspan]
  refine Submodule.span_le.mpr fun x hx => ?_
  refine Submodule.subset_span ?_
  refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  show v (g (t.equivFin.symm (t.equivFin ⟨x, hx⟩))) = x
  rw [Equiv.symm_apply_apply]
  exact hg ⟨x, hx⟩

/-! ## Rescaling a spanning family -/

omit [FiniteDimensional ℝ E] in
/-- Rescaling each member of a spanning family by a nonzero scalar preserves spanning. -/
theorem span_range_smul_eq_top {κ : Type*} (v : κ → E) (c : κ → ℝ) (hc : ∀ a, c a ≠ 0)
    (h : Submodule.span ℝ (Set.range v) = ⊤) :
    Submodule.span ℝ (Set.range fun a => c a • v a) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← h]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨a, rfl⟩
  have hv : v a = (c a)⁻¹ • (c a • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (hc a), one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- Coordinatewise rescaling by nonzero scalars, as a real-linear equivalence. -/
def diagScaleEquiv {σ : Type*} (d : σ → ℂ) (hd : ∀ s, d s ≠ 0) : (σ → ℂ) ≃ₗ[ℝ] (σ → ℂ) where
  toFun y := fun s => d s * y s
  invFun y := fun s => (d s)⁻¹ * y s
  map_add' := by
    intro a b
    funext s
    simp [mul_add]
  map_smul' := by
    intro c a
    funext s
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
    ring
  left_inv := by
    intro y
    funext s
    show (d s)⁻¹ * (d s * y s) = y s
    rw [← mul_assoc, inv_mul_cancel₀ (hd s), one_mul]
  right_inv := by
    intro y
    funext s
    show d s * ((d s)⁻¹ * y s) = y s
    rw [← mul_assoc, mul_inv_cancel₀ (hd s), one_mul]

/-- Coordinatewise rescaling by nonzero scalars preserves spanning. -/
theorem span_range_diagScale_eq_top {σ κ : Type*} (d : σ → ℂ) (hd : ∀ s, d s ≠ 0)
    (v : κ → σ → ℂ) (h : Submodule.span ℝ (Set.range v) = ⊤) :
    Submodule.span ℝ (Set.range fun a => fun s => d s * v a s) = ⊤ := by
  have hmap := Submodule.map_span (diagScaleEquiv d hd).toLinearMap (Set.range v)
  have himg : (diagScaleEquiv d hd).toLinearMap '' Set.range v
      = Set.range fun a => fun s => d s * v a s := by
    rw [← Set.range_comp]
    rfl
  rw [himg, h] at hmap
  rw [← hmap, Submodule.map_top, LinearMap.range_eq_top]
  exact (diagScaleEquiv d hd).surjective

end

end GaloisForLFunctions.HTGeometry
