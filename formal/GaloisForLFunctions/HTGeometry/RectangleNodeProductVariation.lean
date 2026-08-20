import GaloisForLFunctions.HTGeometry.RectangleBoundaryPole

/-!
# The three-edge argument variation of a node product with nodes on the left edge

The logarithmic derivative of `∏_w (z − w)^{m_w}` is `∑_w m_w (z − w)^{-1}`, so the
right-plus-bottom-minus-top combination of its argument variation over `[c,d]×[T₁,T₂]` is the sum
of the single-pole contributions.  When every node sits on the *open* left edge each of them
contributes exactly `π`, and the total is `π · ∑_w m_w`.

This is the exact correction that converts the argument principle for a cofactor into the argument
principle for a function with zeros on the contour: dividing the nodes out costs `π` per unit of
multiplicity on the three regular edges, while the left-edge integral is unchanged because the
singular part `m/(i(τ−τ_w))` is purely imaginary there.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

/-- The logarithmic derivative of a node product is the sum of its simple poles. -/
theorem logDeriv_nodeProduct {pts : Finset ℂ} (m : ℂ → ℕ) {s : ℂ} (hs : ∀ w ∈ pts, s ≠ w) :
    logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) s
      = ∑ w ∈ pts, (m w : ℂ) * (s - w)⁻¹ := by
  classical
  rw [logDeriv_prod (f := fun (w : ℂ) (z : ℂ) => (z - w) ^ (m w))
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (hs w hw)))
    (fun w _ => by fun_prop)]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
  simp

theorem continuous_pole_edge_re {w : ℂ} {d : ℝ} (hw : w.re < d) :
    Continuous fun t : ℝ => ((((d : ℂ) + (t : ℂ) * I) - w)⁻¹).re := by
  have hne : ∀ t : ℝ, (((d : ℂ) + (t : ℂ) * I) - w) ≠ 0 := by
    intro t h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.zero_re] at hh
    linarith
  refine Complex.continuous_re.comp (Continuous.inv₀ ?_ hne)
  fun_prop

theorem continuous_pole_edge_im {w : ℂ} {T : ℝ} (hw : w.im ≠ T) :
    Continuous fun x : ℝ => ((((x : ℂ) + (T : ℂ) * I) - w)⁻¹).im := by
  have hne : ∀ x : ℝ, (((x : ℂ) + (T : ℂ) * I) - w) ≠ 0 := by
    intro x h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
      Complex.zero_im] at hh
    exact hw (by linarith)
  refine Complex.continuous_im.comp (Continuous.inv₀ ?_ hne)
  fun_prop

/-- **Nodes on the left edge contribute exactly `π` each.** -/
theorem nodeProduct_three_edge_variation {pts : Finset ℂ} (m : ℂ → ℕ)
    {c d T₁ T₂ : ℝ} (hcd : c < d)
    (hnodes : ∀ w ∈ pts, w.re = c ∧ T₁ < w.im ∧ w.im < T₂) :
    (∫ t in T₁..T₂,
        (logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) ((d : ℂ) + (t : ℂ) * I)).re)
      + (∫ x in c..d,
          (logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) ((x : ℂ) + (T₁ : ℂ) * I)).im)
      - (∫ x in c..d,
          (logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) ((x : ℂ) + (T₂ : ℂ) * I)).im)
      = Real.pi * (∑ w ∈ pts, (m w : ℝ)) := by
  classical
  have hnode_eq : ∀ w ∈ pts, w = ((c : ℂ) + ((w.im : ℝ) : ℂ) * I) := by
    intro w hw
    apply Complex.ext
    · simp [(hnodes w hw).1]
    · simp
  have hre : ∀ t : ℝ,
      (logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) ((d : ℂ) + (t : ℂ) * I)).re
        = ∑ w ∈ pts, (m w : ℝ) * ((((d : ℂ) + (t : ℂ) * I) - w)⁻¹).re := by
    intro t
    have hne : ∀ w ∈ pts, ((d : ℂ) + (t : ℂ) * I) ≠ w := by
      intro w hw h
      have hh := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hh
      rw [(hnodes w hw).1] at hh
      linarith
    rw [logDeriv_nodeProduct m hne, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Complex.mul_re]
  have him : ∀ (T : ℝ), (∀ w ∈ pts, w.im ≠ T) → ∀ x : ℝ,
      (logDeriv (fun z : ℂ => ∏ w ∈ pts, (z - w) ^ (m w)) ((x : ℂ) + (T : ℂ) * I)).im
        = ∑ w ∈ pts, (m w : ℝ) * ((((x : ℂ) + (T : ℂ) * I) - w)⁻¹).im := by
    intro T hT x
    have hne : ∀ w ∈ pts, ((x : ℂ) + (T : ℂ) * I) ≠ w := by
      intro w hw h
      have hh := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at hh
      exact hT w hw (by linarith)
    rw [logDeriv_nodeProduct m hne, Complex.im_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Complex.mul_im]
  have hT1 : ∀ w ∈ pts, w.im ≠ T₁ := fun w hw => ne_of_gt (hnodes w hw).2.1
  have hT2 : ∀ w ∈ pts, w.im ≠ T₂ := fun w hw => ne_of_lt (hnodes w hw).2.2
  rw [intervalIntegral.integral_congr (fun t _ => hre t),
    intervalIntegral.integral_congr (fun x _ => him T₁ hT1 x),
    intervalIntegral.integral_congr (fun x _ => him T₂ hT2 x)]
  rw [intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum,
    intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    obtain ⟨hwre, hw1, hw2⟩ := hnodes w hw
    have hkey := simplePole_three_edge_variation (c := c) (d := d) (τ := w.im)
      (T₁ := T₁) (T₂ := T₂) hcd hw1 hw2
    rw [← hnode_eq w hw] at hkey
    calc (m w : ℝ) * (∫ t in T₁..T₂, ((((d : ℂ) + (t : ℂ) * I) - w)⁻¹).re)
          + (m w : ℝ) * (∫ x in c..d, ((((x : ℂ) + (T₁ : ℂ) * I) - w)⁻¹).im)
          - (m w : ℝ) * (∫ x in c..d, ((((x : ℂ) + (T₂ : ℂ) * I) - w)⁻¹).im)
        = (m w : ℝ) * ((∫ t in T₁..T₂, ((((d : ℂ) + (t : ℂ) * I) - w)⁻¹).re)
            + (∫ x in c..d, ((((x : ℂ) + (T₁ : ℂ) * I) - w)⁻¹).im)
            - (∫ x in c..d, ((((x : ℂ) + (T₂ : ℂ) * I) - w)⁻¹).im)) := by ring
      _ = Real.pi * (m w : ℝ) := by rw [hkey]; ring
  · exact fun w hw => ((continuous_pole_edge_im (hT2 w hw)).const_mul _).intervalIntegrable _ _
  · exact fun w hw => ((continuous_pole_edge_im (hT1 w hw)).const_mul _).intervalIntegrable _ _
  · exact fun w hw => ((continuous_pole_edge_re
      (by rw [(hnodes w hw).1]; exact hcd)).const_mul _).intervalIntegrable _ _

end RHTower

end
