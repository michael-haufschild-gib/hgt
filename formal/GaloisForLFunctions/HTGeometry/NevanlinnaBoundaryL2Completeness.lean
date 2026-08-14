import GaloisForLFunctions.HTGeometry.NevanlinnaPickGramSplitting
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The constants and the leaf Cauchy transforms span the boundary space

Resolvent completeness in its Hilbert form: inside `L²` of the projective boundary law, the closed
span of the constant function together with the leaf Cauchy transforms is everything.  Equivalently
the centered leaf transforms have closed span the whole mean-zero subspace, so the boundary-law
covariance kernel has exactly the rank of that subspace.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint InnerProductSpace

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
  (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]

/-- Conjugating the spectral parameter conjugates the leaf Cauchy transform. -/
theorem leafCauchy_conj (z : ℂ) (t : OnePoint ℝ) :
    (starRingEnd ℂ) (F.leafCauchy z t) = F.leafCauchy ((starRingEnd ℂ) z) t := by
  rw [leafCauchy, leafCauchy, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (starRingEnd ℂ) (((x : ℂ) - z)⁻¹) = ((x : ℂ) - (starRingEnd ℂ) z)⁻¹
  rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- The leaf Cauchy transform is square integrable against a probability boundary law. -/
theorem memLp_leafCauchy {z : ℂ} (hz : z.im ≠ 0) : MemLp (F.leafCauchy z) 2 eta :=
  MemLp.of_bound F.measurable_leafCauchy.aestronglyMeasurable |z.im|⁻¹
    (Filter.Eventually.of_forall (F.norm_leafCauchy_le hz))

/-- The leaf Cauchy transform as an `L²` class. -/
def leafCauchyL2 (z : {z : ℂ // z.im ≠ 0}) : Lp ℂ 2 eta :=
  (F.memLp_leafCauchy eta z.2).toLp _

/-- The constant function as an `L²` class. -/
def constL2 : Lp ℂ 2 eta := (memLp_const (1 : ℂ)).toLp _

/-- The span of the constants and the leaf Cauchy transforms. -/
def resolventSubmodule : Submodule ℂ (Lp ℂ 2 eta) :=
  Submodule.span ℂ (insert (constL2 eta) (Set.range (F.leafCauchyL2 eta)))

/-- **Resolvent completeness in the boundary Hilbert space.**  The constant function and the leaf
Cauchy transforms span a dense subspace of `L²` of the boundary law. -/
theorem resolventSubmodule_topologicalClosure_eq_top
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0) :
    (F.resolventSubmodule eta).topologicalClosure = ⊤ := by
  classical
  rw [Submodule.topologicalClosure_eq_top_iff]
  refine (Submodule.eq_bot_iff _).2 fun g hg => ?_
  -- a measurable representative of `g`
  set g₀ : OnePoint ℝ → ℂ := (Lp.aestronglyMeasurable g).mk g with hg₀
  have hg₀meas : Measurable g₀ :=
    ((Lp.aestronglyMeasurable g).stronglyMeasurable_mk).measurable
  have hg₀ae : (g : OnePoint ℝ → ℂ) =ᵐ[eta] g₀ := (Lp.aestronglyMeasurable g).ae_eq_mk
  have hgint : Integrable (g : OnePoint ℝ → ℂ) eta :=
    (Lp.memLp g).integrable (by norm_num)
  have hg₀int : Integrable g₀ eta := hgint.congr hg₀ae
  -- orthogonality to the constant and to every leaf transform
  have hconstInner : ⟪constL2 eta, g⟫_ℂ = 0 :=
    hg _ (Submodule.subset_span (Set.mem_insert _ _))
  have hleafInner : ∀ z : {z : ℂ // z.im ≠ 0}, ⟪F.leafCauchyL2 eta z, g⟫_ℂ = 0 :=
    fun z => hg _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨z, rfl⟩))
  have hconst : ∫ t, g₀ t ∂eta = 0 := by
    have hinner := hconstInner
    rw [L2.inner_def] at hinner
    have hrw : ∫ t, ⟪(constL2 eta : OnePoint ℝ → ℂ) t, (g : OnePoint ℝ → ℂ) t⟫_ℂ ∂eta
        = ∫ t, g₀ t ∂eta := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_const (1 : ℂ)).coeFn_toLp, hg₀ae] with t ht hgt
      rw [RCLike.inner_apply]
      show (g : OnePoint ℝ → ℂ) t * (starRingEnd ℂ) ((constL2 eta : OnePoint ℝ → ℂ) t) = g₀ t
      rw [show (constL2 eta : OnePoint ℝ → ℂ) t = (1 : ℂ) from ht, hgt]
      simp
    rw [hrw] at hinner
    exact hinner
  have hcauchy : ∀ z : ℂ, z.im ≠ 0 → ∫ t, F.leafCauchy z t * g₀ t ∂eta = 0 := by
    intro z hz
    have hzconj : ((starRingEnd ℂ) z).im ≠ 0 := by
      simpa using hz
    have hinner := hleafInner ⟨(starRingEnd ℂ) z, hzconj⟩
    rw [L2.inner_def] at hinner
    have hrw : ∫ t, ⟪(F.leafCauchyL2 eta ⟨(starRingEnd ℂ) z, hzconj⟩ : OnePoint ℝ → ℂ) t,
          (g : OnePoint ℝ → ℂ) t⟫_ℂ ∂eta
        = ∫ t, F.leafCauchy z t * g₀ t ∂eta := by
      refine integral_congr_ae ?_
      filter_upwards [(F.memLp_leafCauchy eta hzconj).coeFn_toLp, hg₀ae] with t ht hgt
      rw [RCLike.inner_apply]
      show (g : OnePoint ℝ → ℂ) t * (starRingEnd ℂ) ((F.leafCauchyL2 eta
          ⟨(starRingEnd ℂ) z, hzconj⟩ : OnePoint ℝ → ℂ) t) = F.leafCauchy z t * g₀ t
      rw [show (F.leafCauchyL2 eta ⟨(starRingEnd ℂ) z, hzconj⟩ : OnePoint ℝ → ℂ) t
          = F.leafCauchy ((starRingEnd ℂ) z) t from ht, hgt,
        F.leafCauchy_conj ((starRingEnd ℂ) z) t]
      simp [mul_comm]
    rw [hrw] at hinner
    exact hinner
  have hzero := F.eq_zero_ae_of_annihilates_leafCauchy hcne hup hlow eta hg₀meas hg₀int hconst
    hcauchy
  have hgae : (g : OnePoint ℝ → ℂ) =ᵐ[eta] 0 := hg₀ae.trans hzero
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hgae

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint InnerProductSpace

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
  (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]

/-- The centered leaf Cauchy transform as an `L²` class. -/
def centeredLeafCauchyL2 (z : {z : ℂ // z.im ≠ 0}) : Lp ℂ 2 eta :=
  F.leafCauchyL2 eta z - (F.boundaryMean eta z.1) • constL2 eta

/-- The span of the centered leaf Cauchy transforms: the feature family of the boundary-law
covariance kernel. -/
def centeredSubmodule : Submodule ℂ (Lp ℂ 2 eta) :=
  Submodule.span ℂ (Set.range (F.centeredLeafCauchyL2 eta))

theorem inner_constL2_self : ⟪constL2 eta, constL2 eta⟫_ℂ = 1 := by
  rw [L2.inner_def]
  have hrw : ∫ t, ⟪(constL2 eta : OnePoint ℝ → ℂ) t, (constL2 eta : OnePoint ℝ → ℂ) t⟫_ℂ ∂eta
      = ∫ _t : OnePoint ℝ, (1 : ℂ) ∂eta := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_const (1 : ℂ)).coeFn_toLp] with t ht
    rw [RCLike.inner_apply,
      show (constL2 eta : OnePoint ℝ → ℂ) t = (1 : ℂ) from ht]
    simp
  rw [hrw, integral_const]
  simp

theorem inner_constL2_leafCauchyL2 (z : {z : ℂ // z.im ≠ 0}) :
    ⟪constL2 eta, F.leafCauchyL2 eta z⟫_ℂ = F.boundaryMean eta z.1 := by
  rw [L2.inner_def]
  have hrw : ∫ t, ⟪(constL2 eta : OnePoint ℝ → ℂ) t,
        (F.leafCauchyL2 eta z : OnePoint ℝ → ℂ) t⟫_ℂ ∂eta
      = ∫ t, F.leafCauchy z.1 t ∂eta := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_const (1 : ℂ)).coeFn_toLp,
      (F.memLp_leafCauchy eta z.2).coeFn_toLp] with t ht htz
    rw [RCLike.inner_apply,
      show (constL2 eta : OnePoint ℝ → ℂ) t = (1 : ℂ) from ht,
      show (F.leafCauchyL2 eta z : OnePoint ℝ → ℂ) t = F.leafCauchy z.1 t from htz]
    simp
  rw [hrw, ← boundaryMean]

theorem inner_constL2_centered (z : {z : ℂ // z.im ≠ 0}) :
    ⟪constL2 eta, F.centeredLeafCauchyL2 eta z⟫_ℂ = 0 := by
  rw [centeredLeafCauchyL2, inner_sub_right, inner_smul_right,
    F.inner_constL2_leafCauchyL2 eta z, inner_constL2_self]
  ring

/-- **The centered feature family has orthogonal complement exactly the constants.** -/
theorem centeredSubmodule_orthogonal
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0) :
    (F.centeredSubmodule eta)ᗮ = Submodule.span ℂ {constL2 eta} := by
  have hres : (F.resolventSubmodule eta)ᗮ = ⊥ :=
    Submodule.topologicalClosure_eq_top_iff.1
      (F.resolventSubmodule_topologicalClosure_eq_top eta hcne hup hlow)
  refine le_antisymm (fun f hf => ?_) ?_
  · -- an orthogonal vector is a multiple of the constant
    set c : ℂ := ⟪constL2 eta, f⟫_ℂ with hc
    set h : Lp ℂ 2 eta := f - c • constL2 eta with hh
    have hconstOrth : ⟪constL2 eta, h⟫_ℂ = 0 := by
      rw [hh, inner_sub_right, inner_smul_right, inner_constL2_self, ← hc]
      ring
    have hcenteredOrth : ∀ z : {z : ℂ // z.im ≠ 0},
        ⟪F.centeredLeafCauchyL2 eta z, h⟫_ℂ = 0 := by
      intro z
      have h1 : ⟪F.centeredLeafCauchyL2 eta z, f⟫_ℂ = 0 :=
        hf _ (Submodule.subset_span ⟨z, rfl⟩)
      have h2 : ⟪F.centeredLeafCauchyL2 eta z, constL2 eta⟫_ℂ = 0 := by
        rw [← inner_conj_symm, F.inner_constL2_centered eta z]
        simp
      rw [hh, inner_sub_right, inner_smul_right, h1, h2]
      ring
    have hleafOrth : ∀ z : {z : ℂ // z.im ≠ 0}, ⟪F.leafCauchyL2 eta z, h⟫_ℂ = 0 := by
      intro z
      have hsplit : F.leafCauchyL2 eta z =
          F.centeredLeafCauchyL2 eta z + (F.boundaryMean eta z.1) • constL2 eta := by
        rw [centeredLeafCauchyL2]
        abel
      rw [hsplit, inner_add_left, inner_smul_left, hcenteredOrth z, hconstOrth]
      ring
    have hmem : h ∈ (F.resolventSubmodule eta)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro v (rfl | ⟨z, rfl⟩)
        · exact hconstOrth
        · exact hleafOrth z
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_left, hx, hy]
        ring
      · intro a x _ hx
        rw [inner_smul_left, hx]
        ring
    have hzero : h = 0 := by
      have := hres ▸ hmem
      simpa using this
    have hf' : f = c • constL2 eta := by
      rw [hh] at hzero
      linear_combination (norm := module) hzero
    rw [hf']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · -- the constant is orthogonal to every centered feature
    rw [Submodule.span_le]
    rintro v rfl
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro w ⟨z, rfl⟩
      rw [← inner_conj_symm, F.inner_constL2_centered eta z]
      simp
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy]
      ring
    · intro a x _ hx
      rw [inner_smul_left, hx]
      ring

/-- **The closed span of the centered features is the mean-zero subspace.**  This is the exact
rank statement for the boundary-law covariance kernel: its feature vectors span the orthogonal
complement of the constants. -/
theorem centeredSubmodule_topologicalClosure
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0) :
    (F.centeredSubmodule eta).topologicalClosure =
      (Submodule.span ℂ {constL2 eta})ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    F.centeredSubmodule_orthogonal eta hcne hup hlow]

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint InnerProductSpace

noncomputable section

/-- A polynomial vanishing almost everywhere against a measure with infinite support is zero. -/
theorem polynomial_eq_zero_of_ae_eq_zero_of_support_infinite {mu : Measure ℝ}
    (hsupp : mu.support.Infinite) {p : Polynomial ℝ}
    (hp : ∀ᵐ x ∂mu, Polynomial.eval x p = 0) : p = 0 := by
  by_contra hne
  have hfin : Set.Finite {x : ℝ | Polynomial.eval x p = 0} :=
    Polynomial.finite_setOf_isRoot hne
  have hclosed : IsClosed {x : ℝ | Polynomial.eval x p = 0} := hfin.isClosed
  have hsub : mu.support ⊆ {x : ℝ | Polynomial.eval x p = 0} :=
    Measure.support_subset_of_isClosed hclosed hp
  exact hsupp (hfin.subset hsub)

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
  (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]

/-- The rank-one mean layer: the constants form a one-dimensional subspace. -/
theorem constL2_ne_zero : constL2 eta ≠ 0 := by
  intro h
  have hnorm : ⟪constL2 eta, constL2 eta⟫_ℂ = 1 := inner_constL2_self eta
  rw [h] at hnorm
  simp at hnorm

theorem finrank_span_constL2 : Module.finrank ℂ (Submodule.span ℂ {constL2 eta}) = 1 :=
  finrank_span_singleton (constL2_ne_zero eta)

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
