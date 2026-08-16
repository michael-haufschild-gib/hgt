import GaloisForLFunctions.HTGeometry.AnalyticGermMaximalIdeal

/-!
# The ring of analytic germs is a domain, and every nonzero germ is regular in some direction

Two facts about `AnalyticGerm p` that the local factorization theory rests on.

The ring has no zero divisors: if a product of germs vanishes and one factor has a nonzero germ,
the other factor vanishes on a neighbourhood of every point where the first does not, and the
identity theorem on a ball propagates that to the whole ball.

Every germ that is not zero is *regular in some direction*: there is a vector `v` such that the
one-variable restriction `t ↦ f (p + t • v)` is not identically zero near the origin.  A
representative is nonzero somewhere on a ball, and the segment through that point is a disc on
which the one-variable identity theorem applies.  This is the input that lets a Weierstrass
preparation be set up after a linear change of coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function analytic at a point is analytic on a whole ball around it. -/
theorem exists_ball_analyticOnNhd {p : E} {f : E → ℂ} (hf : AnalyticAt ℂ f p) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ f (ball p r) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  exact ⟨r, hr, fun y hy => hball (by simpa using hy)⟩

/-- **A nonzero analytic germ has a nonzero value arbitrarily close to the point.** -/
theorem exists_ne_zero_of_not_eventuallyEq_zero {p : E} {f : E → ℂ}
    (hne : ¬ f =ᶠ[𝓝 p] 0) {r : ℝ} (hr : 0 < r) :
    ∃ w ∈ ball p r, f w ≠ 0 := by
  by_contra hall
  refine hne ?_
  filter_upwards [ball_mem_nhds p hr] with y hy
  by_contra hy0
  exact hall ⟨y, hy, hy0⟩

/-- **The ring of analytic germs has no zero divisors.** -/
theorem eventuallyEq_zero_of_mul_eventuallyEq_zero {p : E} {f g : E → ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (hne : ¬ f =ᶠ[𝓝 p] 0)
    (hmul : (fun x => f x * g x) =ᶠ[𝓝 p] 0) : g =ᶠ[𝓝 p] 0 := by
  obtain ⟨r₁, hr₁, hfr⟩ := exists_ball_analyticOnNhd hf
  obtain ⟨r₂, hr₂, hgr⟩ := exists_ball_analyticOnNhd hg
  obtain ⟨r₃, hr₃, hzero⟩ := Metric.eventually_nhds_iff.mp hmul
  set r : ℝ := min r₁ (min r₂ r₃) with hrdef
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  have hsub₁ : ball p r ⊆ ball p r₁ := ball_subset_ball (by simp [hrdef])
  have hsub₂ : ball p r ⊆ ball p r₂ :=
    ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgball : ∀ z ∈ ball p r, g z = 0 := by
    intro z hz
    by_contra hgz
    -- `g` is nonzero near `z`, so `f` vanishes near `z`, hence on the whole ball
    have hgcont : ContinuousAt g z := (hgr z (hsub₂ hz)).continuousAt
    have hnearz : ∀ᶠ y in 𝓝 z, g y ≠ 0 := hgcont.eventually_ne hgz
    have hballz : ∀ᶠ y in 𝓝 z, y ∈ ball p r := (isOpen_ball.mem_nhds hz)
    have hfz : f =ᶠ[𝓝 z] 0 := by
      filter_upwards [hnearz, hballz] with y hy hyb
      have := hzero (show dist y p < r₃ from
        lt_of_lt_of_le (mem_ball.mp hyb) (le_trans (min_le_right _ _) (min_le_right _ _)))
      simpa [hy] using mul_eq_zero.mp this
    have hEq : Set.EqOn f 0 (ball p r) :=
      (hfr.mono hsub₁).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball p r).isPreconnected hz hfz
    refine hne ?_
    filter_upwards [ball_mem_nhds p hr] with y hy using hEq hy
  filter_upwards [ball_mem_nhds p hr] with y hy using hgball y hy

instance instNontrivialAnalyticGerm (p : E) : Nontrivial (AnalyticGerm p) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h1 : ((0 : E → ℂ) : Germ (𝓝 p) ℂ) = ((1 : E → ℂ) : Germ (𝓝 p) ℂ) := congrArg Subtype.val h
  have h2 : (0 : E → ℂ) =ᶠ[𝓝 p] (1 : E → ℂ) := Germ.coe_eq.mp h1
  have h3 : (0 : ℂ) = 1 := h2.self_of_nhds
  exact zero_ne_one h3

instance instNoZeroDivisorsAnalyticGerm (p : E) : NoZeroDivisors (AnalyticGerm p) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
  intro a b hab
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  have hfne : ¬ f =ᶠ[𝓝 p] 0 := by
    intro hc
    refine ha (Subtype.ext ?_)
    rw [← hfa]
    exact Germ.coe_eq.mpr hc
  have hmul : (fun x => f x * g x) =ᶠ[𝓝 p] 0 := by
    have : ((fun x => f x * g x : E → ℂ) : Germ (𝓝 p) ℂ) = ((0 : E → ℂ) : Germ (𝓝 p) ℂ) := by
      have hval : (a : Germ (𝓝 p) ℂ) * (b : Germ (𝓝 p) ℂ) = 0 := by
        rw [← Subring.coe_mul, hab, ZeroMemClass.coe_zero]
      rw [← hfa, ← hgb] at hval
      simpa using hval
    exact Germ.coe_eq.mp this
  refine Subtype.ext ?_
  rw [← hgb, ZeroMemClass.coe_zero]
  exact Germ.coe_eq.mpr (eventuallyEq_zero_of_mul_eventuallyEq_zero hf hg hfne hmul)

/-! ## Regularity in a direction -/

/-- The affine line through `p` in the direction `v`. -/
noncomputable def lineMap (p : E) (v : E) : ℂ → E := fun t => p + t • v

theorem analyticAt_lineMap (p v : E) (t : ℂ) : AnalyticAt ℂ (lineMap p v) t := by
  have hL : AnalyticAt ℂ (fun s : ℂ => s • v) t :=
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) v).analyticAt t)
  have h := (analyticAt_const (v := p)).add hL
  simpa only [Pi.add_def, lineMap] using h

/-- **Every nonzero analytic germ is regular in some direction.** -/
theorem exists_regular_direction {p : E} {f : E → ℂ} (hf : AnalyticAt ℂ f p)
    (hne : ¬ f =ᶠ[𝓝 p] 0) :
    ∃ v : E, ¬ (fun t : ℂ => f (lineMap p v t)) =ᶠ[𝓝 (0 : ℂ)] 0 := by
  by_cases hp : f p ≠ 0
  · refine ⟨0, ?_⟩
    intro hc
    exact hp (by simpa [lineMap] using hc.self_of_nhds)
  obtain ⟨r, hr, hfr⟩ := exists_ball_analyticOnNhd hf
  obtain ⟨w, hw, hwne⟩ := exists_ne_zero_of_not_eventuallyEq_zero hne hr
  refine ⟨w - p, ?_⟩
  intro hc
  set v : E := w - p with hv
  have hvne : v ≠ 0 := by
    intro h
    exact hp (by simpa [hv, sub_eq_zero.mp h] using hwne)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hvlt : ‖v‖ < r := by simpa [hv, dist_eq_norm] using mem_ball.mp hw
  set R : ℝ := r / ‖v‖ with hR
  have hR1 : 1 < R := (one_lt_div hvnorm).mpr hvlt
  have hRpos : 0 < R := lt_trans one_pos hR1
  have hmaps : ∀ t : ℂ, t ∈ ball (0 : ℂ) R → lineMap p v t ∈ ball p r := by
    intro t ht
    have hnt : ‖t‖ < R := by simpa [Complex.dist_eq] using mem_ball.mp ht
    rw [mem_ball, dist_eq_norm]
    have : ‖lineMap p v t - p‖ = ‖t‖ * ‖v‖ := by
      simp [lineMap, norm_smul]
    rw [this]
    calc ‖t‖ * ‖v‖ < R * ‖v‖ := by exact mul_lt_mul_of_pos_right hnt hvnorm
      _ = r := by field_simp [hR]
  have hcomp : AnalyticOnNhd ℂ (fun t : ℂ => f (lineMap p v t)) (ball (0 : ℂ) R) := by
    intro t ht
    exact (hfr _ (hmaps t ht)).comp (analyticAt_lineMap p v t)
  have hEq : Set.EqOn (fun t : ℂ => f (lineMap p v t)) 0 (ball (0 : ℂ) R) :=
    hcomp.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) R).isPreconnected
      (mem_ball_self hRpos) hc
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball, Complex.dist_eq]
    simpa using hR1
  have := hEq h1
  simp only [Pi.zero_apply, lineMap, one_smul] at this
  exact hwne (by simpa [hv] using this)

end GaloisForLFunctions.HTGeometry
