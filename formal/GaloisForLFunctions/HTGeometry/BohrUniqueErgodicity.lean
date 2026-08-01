import GaloisForLFunctions.HTGeometry.BohrHullDual

/-!
# Unique ergodicity of the hull

The Bohr mean of an observable pulled back to the line equals its Haar integral over the hull.

Both functionals are `1`-Lipschitz for the sup norm and they agree on characters — a nontrivial
character integrates to zero by translation invariance, and its pullback `e^{iλt}` has Bohr mean
zero for the same reason — so they agree on the dense span of the characters, hence everywhere.
-/

open MeasureTheory TopologicalSpace

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

section CharIntegral

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- **A nontrivial character integrates to zero.** -/
theorem integral_char_eq_zero {χ : C(G, ℂ)} (hχ : CompactAbelian.IsGroupChar χ) {x₀ : G}
    (hx₀ : χ x₀ ≠ 1) : ∫ x, χ x ∂(CompactAbelian.haarProb G) = 0 := by
  have hcont : Continuous fun x : G => χ x := χ.continuous
  have hint : Integrable (fun x : G => χ x) (CompactAbelian.haarProb G) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ x, χ (x + x₀) ∂(CompactAbelian.haarProb G) = ∫ x, χ x ∂(CompactAbelian.haarProb G) :=
    CompactAbelian.integral_add_right (fun x => χ x) x₀
  have h2 : ∫ x, χ (x + x₀) ∂(CompactAbelian.haarProb G)
      = χ x₀ * ∫ x, χ x ∂(CompactAbelian.haarProb G) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show χ (x + x₀) = χ x₀ * χ x
    rw [hχ.map_add]
    ring
  have h3 : (χ x₀ - 1) * ∫ x, χ x ∂(CompactAbelian.haarProb G) = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (by linear_combination h) hx₀
  · exact h

end CharIntegral

section Hull

variable {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
  (htb : HasTotallyBoundedOrbit (fun x => f x))

include hf htb in
/-- The Bohr mean of a character pulled back to the line, and its Haar integral, agree. -/
theorem bohrMean_char_comp_bohrIota [CompactSpace (BohrHull f)] [MeasurableSpace (BohrHull f)]
    [BorelSpace (BohrHull f)] {χ : C(BohrHull f, ℂ)} (hχ : CompactAbelian.IsGroupChar χ) :
    bohrMean (fun t => χ (bohrIota f t))
      = ∫ x, χ x ∂(CompactAbelian.haarProb (BohrHull f)) := by
  obtain ⟨lam, hlam, hχeq⟩ := exists_frequency_of_hull_character hf htb χ.continuous
    hχ.map_add hχ.norm_one
  have hpull : ∀ t : ℝ, χ (bohrIota f t) = expChar lam t := by
    intro t
    rw [hχeq, bohrHullChar_bohrIota hlam]
  rcases eq_or_ne lam 0 with h0 | h0
  · -- the trivial character
    have hone : ∀ t : ℝ, χ (bohrIota f t) = 1 := by
      intro t
      rw [hpull t, h0]
      unfold expChar
      norm_num
    have hfun : (fun x : BohrHull f => χ x) = fun _ : BohrHull f => (1 : ℂ) :=
      Continuous.ext_on (denseRange_bohrIota f) χ.continuous continuous_const
        (by rintro x ⟨t, rfl⟩; exact hone t)
    have hχ1 : χ = 1 := ContinuousMap.ext fun x => congrFun hfun x
    have hL : bohrMean (fun t => χ (bohrIota f t)) = 1 := by
      have h1 : (fun t : ℝ => χ (bohrIota f t)) = bohrChar 0 := by
        funext t
        rw [hone t]
        unfold bohrChar
        norm_num
      rw [h1, bohrMean_bohrChar]
      norm_num
    have hR : ∫ x, χ x ∂(CompactAbelian.haarProb (BohrHull f)) = 1 := by
      rw [hχ1]
      simp
    rw [hL, hR]
  · -- a nontrivial character
    have hne : ∃ x₀ : BohrHull f, χ x₀ ≠ 1 := by
      refine ⟨bohrIota f (Real.pi / lam), ?_⟩
      rw [hpull]
      unfold expChar
      have hval : (lam * (Real.pi / lam) : ℝ) = Real.pi := by
        field_simp
      rw [hval, Complex.exp_pi_mul_I]
      norm_num
    obtain ⟨x₀, hx₀⟩ := hne
    have hR : ∫ x, χ x ∂(CompactAbelian.haarProb (BohrHull f)) = 0 :=
      integral_char_eq_zero hχ hx₀
    have hL : bohrMean (fun t => χ (bohrIota f t)) = 0 := by
      have heq : (fun t : ℝ => χ (bohrIota f t)) = fun t : ℝ => expChar lam t := funext hpull
      have heq2 : (fun t : ℝ => expChar lam t) = bohrChar (-lam) :=
        funext fun t => expChar_eq_bohrChar lam t
      rw [heq, heq2, bohrMean_bohrChar]
      rw [if_neg]
      intro h
      exact h0 (by linarith [neg_eq_zero.mp h])
    rw [hL, hR]

include hf htb in
/-- **Unique ergodicity of the hull.**  The Bohr mean of a pulled-back observable equals its Haar
integral over the hull. -/
theorem bohrMean_comp_bohrIota_eq_integral [CompactSpace (BohrHull f)]
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] (F : C(BohrHull f, ℂ)) :
    bohrMean (fun t => F (bohrIota f t))
      = ∫ x, F x ∂(CompactAbelian.haarProb (BohrHull f)) := by
  classical
  by_contra hne
  set d : ℝ := ‖bohrMean (fun t => F (bohrIota f t))
    - ∫ x, F x ∂(CompactAbelian.haarProb (BohrHull f))‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, c, χ, hχ, hclose⟩ :=
    CompactAbelian.exists_char_combination_approx F (ε := d / 3) (by positivity)
  set P : C(BohrHull f, ℂ) := ∑ j, c j • χ j with hP
  have hcontj : ∀ j : Fin n, Continuous fun t : ℝ => c j * χ j (bohrIota f t) := fun j =>
    continuous_const.mul ((χ j).continuous.comp (continuous_bohrIota hf))
  have hapj : ∀ j : Fin n, HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => c j * χ j (bohrIota f t) :=
    fun j => isBohrAlmostPeriodic_const_mul _
      (isBohrAlmostPeriodic_comp_bohrIota htb (χ j).continuous)
  have hcontP : Continuous fun t : ℝ => P (bohrIota f t) :=
    P.continuous.comp (continuous_bohrIota hf)
  have hapP : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => P (bohrIota f t) :=
    isBohrAlmostPeriodic_comp_bohrIota htb P.continuous
  have hcontF : Continuous fun t : ℝ => F (bohrIota f t) :=
    F.continuous.comp (continuous_bohrIota hf)
  have hapF : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => F (bohrIota f t) :=
    isBohrAlmostPeriodic_comp_bohrIota htb F.continuous
  -- the two functionals agree on `P`
  have hMP : bohrMean (fun t => P (bohrIota f t))
      = ∫ x, P x ∂(CompactAbelian.haarProb (BohrHull f)) := by
    have hsplit : (fun t : ℝ => P (bohrIota f t))
        = fun t : ℝ => ∑ j, c j * χ j (bohrIota f t) := by
      funext t
      rw [hP, ContinuousMap.coe_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [ContinuousMap.smul_apply, smul_eq_mul]
    have hL : bohrMean (fun t => P (bohrIota f t))
        = ∑ j, c j * bohrMean (fun t => χ j (bohrIota f t)) := by
      rw [hsplit, bohrMean_sum Finset.univ (fun j _ => hcontj j) (fun j _ => hapj j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact bohrMean_const_mul _ ((χ j).continuous.comp (continuous_bohrIota hf))
        (isBohrAlmostPeriodic_comp_bohrIota htb (χ j).continuous)
    have hR : ∫ x, P x ∂(CompactAbelian.haarProb (BohrHull f))
        = ∑ j, c j * ∫ x, χ j x ∂(CompactAbelian.haarProb (BohrHull f)) := by
      have hPapp : ∀ x : BohrHull f, P x = ∑ j, c j * χ j x := by
        intro x
        rw [hP, ContinuousMap.coe_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [ContinuousMap.smul_apply, smul_eq_mul]
      have hint : ∀ j : Fin n, Integrable (fun x : BohrHull f => c j * χ j x)
          (CompactAbelian.haarProb (BohrHull f)) := by
        intro j
        exact ((χ j).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).const_mul (c j)
      rw [integral_congr_ae (Filter.Eventually.of_forall hPapp),
        integral_finsetSum _ (fun j _ => hint j)]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    rw [hL, hR]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bohrMean_char_comp_bohrIota hf htb (hχ j)]
  -- the mean side
  have hF1 : ‖bohrMean (fun t => F (bohrIota f t)) - bohrMean (fun t => P (bohrIota f t))‖
      ≤ d / 3 := by
    rw [← bohrMean_sub (f := fun t : ℝ => F (bohrIota f t)) (g := fun t : ℝ => P (bohrIota f t))
      hcontF hapF hcontP hapP]
    refine norm_bohrMean_le (hcontF.sub hcontP)
      (isBohrAlmostPeriodic_sub hcontF hapF hcontP hapP) fun t => ?_
    have := ContinuousMap.norm_coe_le_norm (F - P) (bohrIota f t)
    rw [ContinuousMap.sub_apply] at this
    exact le_trans this hclose.le
  -- the integral side
  have hF2 : ‖∫ x, F x ∂(CompactAbelian.haarProb (BohrHull f))
      - ∫ x, P x ∂(CompactAbelian.haarProb (BohrHull f))‖ ≤ d / 3 := by
    have hFi : Integrable (fun x : BohrHull f => F x) (CompactAbelian.haarProb (BohrHull f)) :=
      F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hPi : Integrable (fun x : BohrHull f => P x) (CompactAbelian.haarProb (BohrHull f)) :=
      P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hFi hPi]
    have hbound : ∀ x : BohrHull f, ‖F x - P x‖ ≤ d / 3 := by
      intro x
      have := ContinuousMap.norm_coe_le_norm (F - P) x
      rw [ContinuousMap.sub_apply] at this
      exact le_trans this hclose.le
    calc ‖∫ x, (F x - P x) ∂(CompactAbelian.haarProb (BohrHull f))‖
        ≤ ∫ x, ‖F x - P x‖ ∂(CompactAbelian.haarProb (BohrHull f)) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _ : BohrHull f, d / 3 ∂(CompactAbelian.haarProb (BohrHull f)) := by
          refine integral_mono ((hFi.sub hPi).norm) (integrable_const _) hbound
      _ = d / 3 := by simp
  have hfinal : d ≤ d / 3 + d / 3 := by
    calc d = ‖(bohrMean (fun t => F (bohrIota f t)) - bohrMean (fun t => P (bohrIota f t)))
              + (∫ x, P x ∂(CompactAbelian.haarProb (BohrHull f))
                - ∫ x, F x ∂(CompactAbelian.haarProb (BohrHull f)))‖ := by
          rw [hd]
          congr 1
          rw [hMP]
          ring
      _ ≤ ‖bohrMean (fun t => F (bohrIota f t)) - bohrMean (fun t => P (bohrIota f t))‖
            + ‖∫ x, P x ∂(CompactAbelian.haarProb (BohrHull f))
              - ∫ x, F x ∂(CompactAbelian.haarProb (BohrHull f))‖ := norm_add_le _ _
      _ ≤ d / 3 + d / 3 := by
          refine add_le_add hF1 ?_
          rw [← norm_neg]
          simpa using hF2
  linarith


end Hull

end

end GaloisForLFunctions
