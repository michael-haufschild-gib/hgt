import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteHorizontalEdges

/-!
# Chen--Gupta--Li Lemma 6.2: finite reflected vertical integrability

The finite reflected integrand is absolutely integrable on both vertical sides
of CGL's pole-free rectangle.  The compact middle is continuous and the two
tails are dominated by the closed `|v|⁻²` estimate already proved for the
literal finite integrand.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Certified vertical abscissae in CGL's finite reflected displacement
strip. -/
structure CGLLemma62FiniteVerticalAbscissa where
  value : ℝ
  lower : (-1 : ℝ) ≤ value
  upper : value ≤ 1 / 2

private theorem cglLemma62_abs_rpow_tail_integrable {r c : ℝ}
    (hr : r < -1) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => |y| ^ r) {y : ℝ | c < |y|} := by
  have hset : {y : ℝ | c < |y|} = Iio (-c) ∪ Ioi c := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      rcases le_or_gt y 0 with hy | hy
      · left
        rw [abs_of_nonpos hy] at h
        linarith
      · right
        rw [abs_of_pos hy] at h
        exact h
    · rintro (h | h)
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact h
  rw [hset]
  have hpos : IntegrableOn (fun y : ℝ => |y| ^ r) (Ioi c) := by
    have hbase : IntegrableOn (fun y : ℝ => y ^ r) (Ioi c) :=
      (integrableOn_Ioi_rpow_iff hc).mpr hr
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro y hy
    show y ^ r = |y| ^ r
    rw [abs_of_pos (lt_trans hc hy)]
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ r) (Iio (-c)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (f := fun y : ℝ => |y| ^ r) (s := Iio (-c)) (measurableEmbedding_neg (α := ℝ))
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Iio (-c) : Set ℝ) = Ioi c := by
      ext y
      simp
    rw [hpre] at h
    have hfun : ((fun y : ℝ => |y| ^ r) ∘ (Neg.neg : ℝ → ℝ)) =
        fun y : ℝ => |y| ^ r := by
      funext y
      simp
    rw [hfun] at h
    exact h.mp hpos
  exact hneg.union hpos

private theorem cglLemma62FiniteContour_line_continuous
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ)
    (sigma : CGLLemma62FiniteVerticalAbscissa) :
    Continuous (fun v : ℝ => cglLemma62FiniteContourIntegrand w N B t M
      ((sigma.value : ℂ) + (v : ℂ) * I)) := by
  let line : ℝ → ℂ := fun v => (sigma.value : ℂ) + (v : ℂ) * I
  have hline : Continuous line := by
    dsimp [line]
    fun_prop
  have hmaps : ∀ v : ℝ, line v ∈
      GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2) := by
    intro v
    change (-1 : ℝ) ≤ (line v).re ∧ (line v).re ≤ 1 / 2
    dsimp [line]
    simp
    constructor
    · exact sigma.lower
    · norm_num at sigma ⊢
      exact sigma.upper
  have hcont := (cglLemma62FiniteContourIntegrand_differentiableOn w N B t M).continuousOn
  change Continuous (cglLemma62FiniteContourIntegrand w N B t M ∘ line)
  exact hcont.comp_continuous hline hmaps

/-- The literal finite CGL integrand is integrable on every certified vertical
line in the reflected displacement strip. -/
theorem cglLemma62_finiteContourIntegrand_vertical_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ)
    (sigma : CGLLemma62FiniteVerticalAbscissa) :
    Integrable (fun v : ℝ => cglLemma62FiniteContourIntegrand w N B t M
      ((sigma.value : ℂ) + (v : ℂ) * I)) := by
  rcases cglLemma62_finiteContour_horizontal_point_bound w N B t M with ⟨C, hC, hpoint⟩
  let R : ℝ := |t| + 2
  let f : ℝ → ℂ := fun v => cglLemma62FiniteContourIntegrand w N B t M
    ((sigma.value : ℂ) + (v : ℂ) * I)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hcont : Continuous f := by
    dsimp [f]
    exact cglLemma62FiniteContour_line_continuous w N B t M sigma
  have htailmajor : IntegrableOn (fun v : ℝ => C * |v| ^ (-(2 : ℝ)))
      {v : ℝ | R < |v|} :=
    (cglLemma62_abs_rpow_tail_integrable (r := -(2 : ℝ)) (c := R) (by norm_num) hR).const_mul C
  have htailMeas : MeasurableSet {v : ℝ | R < |v|} :=
    measurableSet_lt continuous_const.measurable continuous_abs.measurable
  have htail : IntegrableOn f {v : ℝ | R < |v|} := by
    refine Integrable.mono' htailmajor (hcont.continuousOn.aestronglyMeasurable htailMeas) ?_
    filter_upwards [ae_restrict_mem htailMeas] with v hv
    have hylarge : 1 ≤ |v| := by
      dsimp [R] at hv
      linarith [abs_nonneg t]
    have hshift : 2 ≤ |v - t| := by
      have htri : |v| ≤ |v - t| + |t| := by
        calc
          |v| = |(v - t) + t| := by congr 1; ring
          _ ≤ |v - t| + |t| := abs_add_le _ _
      dsimp [R] at hv
      linarith
    let p : CGLLemma62FiniteHorizontalPoint t :=
      ⟨sigma.value, v, sigma.lower, sigma.upper, hylarge, hshift⟩
    have hpoint' := hpoint p
    have hvpos : 0 < |v| := lt_of_lt_of_le zero_lt_one hylarge
    have hrewrite : C / |v| ^ 2 = C * |v| ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hvpos), Real.rpow_two, div_eq_mul_inv]
    change ‖f v‖ ≤ C * |v| ^ (-(2 : ℝ))
    rw [← hrewrite]
    simpa [f, p] using hpoint'
  have hmiddle : IntegrableOn f (Icc (-R) R) :=
    hcont.continuousOn.integrableOn_Icc
  have hcover : {v : ℝ | R < |v|} ∪ Icc (-R) R = univ := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_univ, iff_true]
    by_cases hv : R < |v|
    · exact Or.inl hv
    · right
      have hv' : |v| ≤ R := le_of_not_gt hv
      exact abs_le.mp hv'
  rw [← integrableOn_univ, ← hcover]
  exact htail.union hmiddle

/-- The initial left vertical side of CGL's finite reflected contour is
absolutely integrable. -/
theorem cglLemma62_finiteContourIntegrand_left_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ => cglLemma62FiniteContourIntegrand w N B t M
      ((-1 : ℂ) + (v : ℂ) * I)) := by
  simpa using cglLemma62_finiteContourIntegrand_vertical_integrable w N B t M
    ⟨-1, by norm_num, by norm_num⟩

/-- The final right vertical side of CGL's finite reflected contour is
absolutely integrable. -/
theorem cglLemma62_finiteContourIntegrand_right_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ => cglLemma62FiniteContourIntegrand w N B t M
      ((1 / 2 : ℂ) + (v : ℂ) * I)) := by
  simpa using cglLemma62_finiteContourIntegrand_vertical_integrable w N B t M
    ⟨1 / 2, by norm_num, by norm_num⟩

end

end RHTower
