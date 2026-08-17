import Mathlib

/-!
# The divergence of a compactly supported field integrates to zero

Gauss--Green on a box says the integral of a divergence is a sum of boundary fluxes.  If the field
vanishes outside a compact set, a box containing that set in its interior has zero flux through
every face, so the total divergence integral vanishes.

This is the flat model of the statement an integration-by-parts argument needs on a closed
manifold: no boundary, no boundary term.
-/

open Set Finset MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

section Flat

variable {n : ℕ}

/-- The divergence of a differentiable field, read off the derivative. -/
def divergence (f' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)))
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, f' x (Pi.single i 1) i

/-- Outside the support the derivative vanishes, hence so does the divergence. -/
theorem divergence_eq_zero_of_notMem_tsupport
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {f' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    (hd : ∀ x, HasFDerivAt f (f' x) x) {x : Fin (n + 1) → ℝ} (hx : x ∉ tsupport f) :
    divergence f' x = 0 := by
  have hzero : f =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [isOpen_compl_iff.mpr (isClosed_tsupport f) |>.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hconst : HasFDerivAt (fun _ : Fin (n + 1) → ℝ => (0 : Fin (n + 1) → ℝ)) 0 x :=
    hasFDerivAt_const (𝕜 := ℝ) (0 : Fin (n + 1) → ℝ) x
  have hderiv : HasFDerivAt f 0 x := hconst.congr_of_eventuallyEq hzero
  have : f' x = 0 := (hd x).unique hderiv
  rw [divergence, this]
  simp

/-- **The divergence theorem for a compactly supported field.**  A continuously differentiable
field that vanishes outside a compact set has vanishing total divergence. -/
theorem integral_divergence_eq_zero_of_hasCompactSupport
    (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (f' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)))
    (hd : ∀ x, HasFDerivAt f (f' x) x)
    (hcont : Continuous (divergence f'))
    (hsupp : HasCompactSupport f) :
    ∫ x, divergence f' x = 0 := by
  classical
  -- a box containing the support in its interior
  obtain ⟨R, hR⟩ := (hsupp.isBounded).subset_closedBall (0 : Fin (n + 1) → ℝ)
  set a : Fin (n + 1) → ℝ := fun _ => -(|R| + 1) with ha
  set b : Fin (n + 1) → ℝ := fun _ => |R| + 1 with hb
  have hRle : R ≤ |R| := le_abs_self R
  have hab : a ≤ b := by
    intro i
    simp only [ha, hb]
    have : (0 : ℝ) ≤ |R| := abs_nonneg R
    linarith
  have houtside : ∀ x : Fin (n + 1) → ℝ, (∃ i, |x i| = |R| + 1) → f x = 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := hx
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    have hball := hR hmem
    rw [mem_closedBall, dist_zero_right] at hball
    have hxi : |x i| ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      simpa using this
    have : |R| + 1 ≤ R := by
      rw [← hi]
      exact le_trans hxi hball
    linarith
  -- the boundary flux vanishes
  have hface : ∀ i : Fin (n + 1), ∀ y : Fin n → ℝ,
      f (Fin.insertNth i (b i) y) i = 0 ∧ f (Fin.insertNth i (a i) y) i = 0 := by
    intro i y
    have hbi : |(Fin.insertNth i (b i) y : Fin (n + 1) → ℝ) i| = |R| + 1 := by
      rw [Fin.insertNth_apply_same, hb]
      exact abs_of_nonneg (by positivity)
    have hai : |(Fin.insertNth i (a i) y : Fin (n + 1) → ℝ) i| = |R| + 1 := by
      rw [Fin.insertNth_apply_same, ha]
      rw [abs_neg]
      exact abs_of_nonneg (by positivity)
    exact ⟨by rw [houtside _ ⟨i, hbi⟩]; rfl, by rw [houtside _ ⟨i, hai⟩]; rfl⟩
  have hint : IntegrableOn (fun x => ∑ i, f' x (Pi.single i 1) i) (Icc a b) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact hcont.continuousOn
  have hbox := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    a b hab f f' ∅ Set.countable_empty
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x) hint
  have hzero : (∫ x in Icc a b, divergence f' x) = 0 := by
    show (∫ x in Icc a b, ∑ i, f' x (Pi.single i 1) i) = 0
    rw [hbox]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f (Fin.insertNth i (b i) y) i) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards with y
      exact (hface i y).1
    have h2 : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f (Fin.insertNth i (a i) y) i) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards with y
      exact (hface i y).2
    rw [h1, h2, sub_self]
  -- the divergence vanishes off the box
  rw [← hzero]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  refine divergence_eq_zero_of_notMem_tsupport hd ?_
  intro hmem
  apply hx
  have hball := hR hmem
  rw [mem_closedBall, dist_zero_right] at hball
  refine ⟨?_, ?_⟩
  · intro i
    have hxi : |x i| ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      simpa using this
    have : |x i| ≤ |R| := le_trans (le_trans hxi hball) hRle
    have habs := abs_le.mp this
    simp only [ha]
    linarith [habs.1]
  · intro i
    have hxi : |x i| ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      simpa using this
    have : |x i| ≤ |R| := le_trans (le_trans hxi hball) hRle
    have habs := abs_le.mp this
    simp only [hb]
    linarith [habs.2]

/-! ## Homogeneous fields -/

section Homogeneous

variable {n : ℕ}

/-- **A degree-zero homogeneous field has degree `-1` homogeneous divergence.**  Scaling the point
scales the derivative, hence the divergence, by the reciprocal. -/
theorem divergence_smul_of_homogeneous
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {f' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    (hd : ∀ x, HasFDerivAt f (f' x) x)
    (hhom : ∀ (c : ℝ) (x : Fin (n + 1) → ℝ), 0 < c → f (c • x) = f x)
    {c : ℝ} (hc : 0 < c) (x : Fin (n + 1) → ℝ) :
    divergence f' (c • x) = c⁻¹ * divergence f' x := by
  classical
  -- the derivative of the scaled map, computed two ways
  have hscale : HasFDerivAt (fun y : Fin (n + 1) → ℝ => f (c • y))
      ((f' (c • x)).comp (c • ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ))) x := by
    have hinner : HasFDerivAt (fun y : Fin (n + 1) → ℝ => c • y)
        (c • ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ)) x := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) x).const_smul c
    exact (hd (c • x)).comp x hinner
  have hfun : (fun y : Fin (n + 1) → ℝ => f (c • y)) = f := by
    funext y
    exact hhom c y hc
  rw [hfun] at hscale
  have hEq : (f' (c • x)).comp (c • ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ)) = f' x :=
    hscale.unique (hd x)
  have hpoint : ∀ v : Fin (n + 1) → ℝ, c • (f' (c • x)) v = f' x v := by
    intro v
    have := congrArg (fun L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) => L v) hEq
    simpa [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul] using this
  have hentry : ∀ i, f' (c • x) (Pi.single i 1) i = c⁻¹ * (f' x (Pi.single i 1) i) := by
    intro i
    have h := congrFun (hpoint (Pi.single i 1)) i
    have hcne : c ≠ 0 := ne_of_gt hc
    have hval : c * (f' (c • x) (Pi.single i 1) i) = f' x (Pi.single i 1) i := by
      simpa using h
    field_simp
    linarith [hval]
  rw [divergence, divergence, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hentry i

end Homogeneous

end Flat

end GaloisForLFunctions.HTGeometry
