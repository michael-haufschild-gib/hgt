import GaloisForLFunctions.RHTower.WeightedEulerCarrierGraph
import GaloisForLFunctions.HTGeometry.CauchyTransformGluing
import GaloisForLFunctions.HTGeometry.CauchyTransformGluingVertical

/-!
# The Cauchy transform of the carrier functional vanishes off its carrier

The total functional kills every power of the coordinate, so its Cauchy transform vanishes outside
a disc containing the total carrier, hence — by the identity theorem on the convex strip separating
the two halves of that carrier — on the whole strip.  The vertical gluing then removes the
functional-equation reflection, and the horizontal gluing removes the Schwarz reflection.

* `RHTower.QuadrantCarrierData.cauchyTransform_Lc_eq_zero`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

namespace QuadrantCarrierData

variable {f₂ : holoQuadrant →L[ℝ] ℝ} (D : QuadrantCarrierData f₂)

theorem cauchyTransform_neg {K : Set ℂ} [CompactSpace K] (A : C(K, ℂ) →L[ℂ] ℂ) (v : ℂ) :
    functionalCauchyTransform (-A) v = -functionalCauchyTransform A v := rfl

/-- The radius of a disc containing the total carrier. -/
def rad : ℝ := (|1 - D.b| + |D.b|) + (|(-D.d)| + |D.d|)

theorem norm_le_rad {z : ℂ} (hz : z ∈ D.Ktot) : ‖z‖ ≤ D.rad := D.norm_le_of_mem_Ktot hz

theorem rad_nonneg : 0 ≤ D.rad := le_trans (norm_nonneg _) (D.norm_le_rad D.mem_Ktot_corner)

theorem vertStrip_subset : {v : ℂ | 1 - D.a < v.re ∧ v.re < D.a} ⊆ (D.Ktot)ᶜ := by
  intro v hv hcon
  rcases hcon with hcon | hcon
  · exact absurd (D.Kt_re hcon) (not_le.mpr hv.2)
  · exact absurd (D.Kt'_re hcon) (not_le.mpr hv.1)

/-- **The transform of the total functional vanishes on the separating vertical strip.** -/
theorem cauchyTransform_total_eq_zero_on_strip (f₁ : PrimeTangent →L[ℝ] ℝ)
    (hgr : ∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0)
    {v : ℂ} (h1 : 1 - D.a < v.re) (h2 : v.re < D.a) :
    functionalCauchyTransform D.total v = 0 := by
  have hfar : ∀ w : ℂ, D.rad < ‖w‖ → functionalCauchyTransform D.total w = 0 := fun w hw =>
    cauchyTransform_eq_zero_of_lt D.total (fun m => D.total_coord_pow_eq_zero f₁ hgr m)
      D.rad_nonneg (fun z hz => D.norm_le_rad hz) hw
  have hopenfar : IsOpen {w : ℂ | D.rad < ‖w‖} := isOpen_lt continuous_const continuous_norm
  set v₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((D.rad + 1 : ℝ) : ℂ) * Complex.I with hv₀
  have hv₀re : v₀.re = 1 / 2 := by rw [hv₀]; simp
  have hv₀im : v₀.im = D.rad + 1 := by rw [hv₀]; simp
  have hv₀far : D.rad < ‖v₀‖ := by
    have h := Complex.abs_im_le_norm v₀
    rw [hv₀im] at h
    have h2' : |D.rad + 1| = D.rad + 1 := abs_of_nonneg (by linarith [D.rad_nonneg])
    rw [h2'] at h
    linarith
  have hv₀strip : v₀ ∈ {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} := by
    rw [Set.mem_setOf_eq, hv₀re]
    exact ⟨by linarith [D.ha], D.ha⟩
  have hanal : AnalyticOnNhd ℂ (functionalCauchyTransform D.total)
      {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} :=
    (analyticOnNhd_functionalCauchyTransform D.isCompact_Ktot D.total).mono D.vertStrip_subset
  have hpre : IsPreconnected {w : ℂ | 1 - D.a < w.re ∧ w.re < D.a} :=
    ((convex_halfSpace_re_gt (1 - D.a)).inter (convex_halfSpace_re_lt D.a)).isPreconnected
  have hev : functionalCauchyTransform D.total =ᶠ[nhds v₀] 0 := by
    filter_upwards [hopenfar.mem_nhds hv₀far] with w hw
    exact hfar w hw
  exact hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hv₀strip hev ⟨h1, h2⟩

theorem conj_mem_Kc {z : ℂ} (hz : z ∈ D.Kc) : (starRingEnd ℂ) z ∈ D.Kcbar := by
  rw [Kc, mem_rect] at hz
  rw [Kcbar, mem_rect]
  refine ⟨by simpa using hz.1, ?_, ?_⟩ <;> simp <;> linarith [hz.2.1, hz.2.2]

theorem Kcbar_subset_Kt : D.Kcbar ⊆ D.Kt := by
  intro z hz
  rw [Kcbar, mem_rect] at hz
  rw [Kt, mem_doubledRect]
  exact ⟨hz.1, Or.inl hz.2⟩

/-- **The transform of the doubled functional vanishes off the right pair of blocks.** -/
theorem cauchyTransform_doubled_eq_zero (f₁ : PrimeTangent →L[ℝ] ℝ)
    (hgr : ∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) :
    ∀ v ∉ D.Kt, functionalCauchyTransform D.doubled v = 0 := by
  refine cauchyTransform_eq_zero_of_glue_re (Kc' := D.Kt') D.isCompact_Kt
    (c₁ := 1 - D.a) (c₂ := D.a) (R := D.rad) D.one_sub_a_lt_a
    (fun z hz => D.Kt_re hz) (fun z hz => D.Kt'_re hz)
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot hz))
    (fun z hz => D.norm_le_rad (D.Kt'_subset_Ktot hz))
    D.doubled (-D.reflected) ?_ (isPreconnected_compl_doubledRect D.hc D.hcd)
  intro v h1 h2
  have hv : v ∉ D.Ktot := D.vertStrip_subset ⟨h1, h2⟩
  have hvt' : v ∉ D.Kt' := fun hc => hv (D.Kt'_subset_Ktot hc)
  have hT := D.cauchyTransform_total hv
  have hR := D.cauchyTransform_reflected hvt'
  have hz := D.cauchyTransform_total_eq_zero_on_strip f₁ hgr h1 h2
  rw [hT] at hz
  rw [cauchyTransform_neg, hR]
  linear_combination hz

/-- **The transform of the carrier functional vanishes off its carrier.** -/
theorem cauchyTransform_Lc_eq_zero (f₁ : PrimeTangent →L[ℝ] ℝ)
    (hgr : ∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) :
    ∀ v ∉ D.Kc, functionalCauchyTransform D.Lc v = 0 := by
  refine cauchyTransform_eq_zero_of_glue (Kc' := D.Kcbar) D.isCompact_Kc
    (c := D.c) (R := D.rad) D.hc
    (fun z hz => D.Kc_im hz) (fun z hz => D.Kcbar_im hz)
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot (D.Kc_subset_Kt hz)))
    (fun z hz => D.norm_le_rad (D.Kt_subset_Ktot (D.Kcbar_subset_Kt hz)))
    D.Lc (conjFunctional (fun _ hz => D.conj_mem_Kc hz) D.Lc) ?_
    (isPreconnected_compl_rect D.a D.b D.c D.d)
  intro v h1 h2
  have hvKt : v ∉ D.Kt := midStrip_subset_compl_doubledRect ⟨h1, h2⟩
  have hvKc : v ∉ D.Kc := fun hc => hvKt (D.Kc_subset_Kt hc)
  have hvKcbar : v ∉ D.Kcbar := fun hc => hvKt (D.Kcbar_subset_Kt hc)
  have hd := D.cauchyTransform_doubled hvKt
  have hc := cauchyTransform_conjFunctional (fun _ hz => D.conj_mem_Kc hz) D.Lc hvKcbar
  have hzero := D.cauchyTransform_doubled_eq_zero f₁ hgr v hvKt
  rw [hd] at hzero
  rw [hc]
  linear_combination hzero

end QuadrantCarrierData

end RHTower
