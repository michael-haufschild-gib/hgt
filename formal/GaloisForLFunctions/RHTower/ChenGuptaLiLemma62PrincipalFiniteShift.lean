import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalFiniteStripBounds
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Chen--Gupta--Li Lemma 6.2: principal finite carrier moved to the critical line

The regularized principal finite carrier is holomorphic on the displacement
strip `-1 ≤ Re s ≤ 1/2`, integrable on both boundary lines, and its horizontal
segments vanish at infinite height by the quadratic strip decay.  Cauchy's
theorem on tall rectangles therefore moves the reflected finite integral from
`Re s = -1` to `Re s = 1/2` with no residue.
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

private theorem cglLemma62_principal_horizontal_decay (C : ℝ) :
    Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
  have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  refine Filter.Tendsto.congr' ?_ hscaled
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]

/-- The upper horizontal side of the principal finite displacement rectangle
vanishes at infinite height. -/
theorem cglLemma62_principalRegularizedFinite_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalRegularizedFinite_strip_bound w N Q t M
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => y)
  · filter_upwards [eventually_ge_atTop (|t| + 1)] with y hy x hx
    have hx' : x ∈ Icc (-1 : ℝ) (1 / 2) := by
      rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)]
      exact uIoc_subset_uIcc hx
    have hy0 : 0 ≤ y := by linarith [abs_nonneg t]
    have hyabs : 1 ≤ |y| := by
      rw [abs_of_nonneg hy0]
      linarith [abs_nonneg t]
    have hyt : 1 ≤ |y - t| := by
      calc
        1 ≤ y - |t| := by linarith
        _ ≤ y - t := sub_le_sub_left (le_abs_self t) y
        _ ≤ |y - t| := le_abs_self _
    have h := hpoint x y hx'.1 hx'.2 hyabs hyt
    simpa [abs_of_nonneg hy0] using h
  · exact cglLemma62_principal_horizontal_decay C

/-- The lower horizontal side of the principal finite displacement rectangle
vanishes at infinite depth. -/
theorem cglLemma62_principalRegularizedFinite_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalRegularizedFinite_strip_bound w N Q t M
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((x : ℂ) + ((-y : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (|t| + 1)] with y hy x hx
      have hx' : x ∈ Icc (-1 : ℝ) (1 / 2) := by
        rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)]
        exact uIoc_subset_uIcc hx
      have hy0 : 0 ≤ y := by linarith [abs_nonneg t]
      have hyabs : 1 ≤ |-y| := by
        rw [abs_neg, abs_of_nonneg hy0]
        linarith [abs_nonneg t]
      have hyt : 1 ≤ |-y - t| := by
        rw [show -y - t = -(y + t) by ring, abs_neg]
        calc
          1 ≤ y - |t| := by linarith
          _ ≤ y + t := by linarith [neg_abs_le t]
          _ ≤ |y + t| := le_abs_self _
      have h := hpoint x (-y) hx'.1 hx'.2 hyabs hyt
      simpa [abs_neg, abs_of_nonneg hy0] using h
    · exact cglLemma62_principal_horizontal_decay C
  refine Filter.Tendsto.congr' ?_ (hneg.comp tendsto_neg_atBot_atTop)
  filter_upwards with y
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x
  intro _
  congr 1
  push_cast
  ring

private theorem cglLemma62_abs_rpow_tail_integrable' {r c : ℝ}
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

/-- The regularized principal finite carrier is continuous along every
vertical line of the displacement strip. -/
theorem cglLemma62_principalRegularizedFinite_line_continuous
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) {σ : ℝ}
    (hlo : -1 ≤ σ) (hhi : σ ≤ 1 / 2) :
    Continuous (fun v : ℝ => cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
      ((σ : ℂ) + (v : ℂ) * I)) := by
  let line : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
  have hline : Continuous line := by
    dsimp [line]
    fun_prop
  have hmaps : ∀ v : ℝ, line v ∈
      GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2) := by
    intro v
    change (-1 : ℝ) ≤ (line v).re ∧ (line v).re ≤ 1 / 2
    dsimp [line]
    simp
    exact ⟨hlo, by simpa using hhi⟩
  have hcont :=
    (cglLemma62PrincipalRegularizedFiniteContourIntegrand_differentiableOn w N Q t M).continuousOn
  change Continuous (cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ∘ line)
  exact hcont.comp_continuous hline hmaps

/-- The regularized principal finite carrier is integrable on every vertical
line of the displacement strip. -/
theorem cglLemma62_principalRegularizedFinite_vertical_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) {σ : ℝ}
    (hlo : -1 ≤ σ) (hhi : σ ≤ 1 / 2) :
    Integrable (fun v : ℝ => cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
      ((σ : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalRegularizedFinite_strip_bound w N Q t M
  let R : ℝ := |t| + 2
  let f : ℝ → ℂ := fun v => cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
    ((σ : ℂ) + (v : ℂ) * I)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hcont : Continuous f :=
    cglLemma62_principalRegularizedFinite_line_continuous w N Q t M hlo hhi
  have htailmajor : IntegrableOn (fun v : ℝ => C * |v| ^ (-(2 : ℝ)))
      {v : ℝ | R < |v|} :=
    (cglLemma62_abs_rpow_tail_integrable' (r := -(2 : ℝ)) (c := R) (by norm_num) hR).const_mul C
  have htailMeas : MeasurableSet {v : ℝ | R < |v|} :=
    measurableSet_lt continuous_const.measurable continuous_abs.measurable
  have htail : IntegrableOn f {v : ℝ | R < |v|} := by
    refine Integrable.mono' htailmajor (hcont.continuousOn.aestronglyMeasurable htailMeas) ?_
    filter_upwards [ae_restrict_mem htailMeas] with v hv
    have hylarge : 1 ≤ |v| := by
      dsimp [R] at hv
      linarith [abs_nonneg t]
    have hshift : 1 ≤ |v - t| := by
      have htri : |v| ≤ |v - t| + |t| := by
        calc
          |v| = |(v - t) + t| := by congr 1; ring
          _ ≤ |v - t| + |t| := abs_add_le _ _
      dsimp [R] at hv
      linarith
    have hpoint' := hpoint σ v hlo hhi hylarge hshift
    have hvpos : 0 < |v| := lt_of_lt_of_le zero_lt_one hylarge
    have hrewrite : C / |v| ^ 2 = C * |v| ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hvpos), Real.rpow_two, div_eq_mul_inv]
    change ‖f v‖ ≤ C * |v| ^ (-(2 : ℝ))
    rw [← hrewrite]
    exact hpoint'
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

/-- Cauchy's theorem moves the regularized principal finite carrier from the
reflected left line to the critical line with no residue. -/
theorem cglLemma62_principalRegularizedFinite_critical_eq_left
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    (∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        ((1 / 2 : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        ((-1 : ℂ) + (v : ℂ) * I) := by
  have hleft : Integrable (fun v : ℝ =>
      cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    cglLemma62_principalRegularizedFinite_vertical_integrable w N Q t M (by norm_num) (by norm_num)
  have hright : Integrable (fun v : ℝ =>
      cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    cglLemma62_principalRegularizedFinite_vertical_integrable w N Q t M (by norm_num) (by norm_num)
  have h := GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (G := cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M)
    (c := (-1 : ℝ)) (d := (1 / 2 : ℝ)) (by norm_num)
    (cglLemma62PrincipalRegularizedFiniteContourIntegrand_differentiableOn w N Q t M)
    hleft hright ?_ ?_
  · simpa using h
  · have hb := (cglLemma62_principalRegularizedFinite_horizontal_bottom w N Q t M).comp
      tendsto_neg_atTop_atBot
    refine Filter.Tendsto.congr' ?_ hb
    filter_upwards with T
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u
    intro _
    congr 1
  · exact cglLemma62_principalRegularizedFinite_horizontal_top w N Q t M

/-- CGL's principal finite reflected Dirichlet polynomial integral equals the
critical-line integral of its regularized carrier. -/
theorem cglLemma62_principalReflectedFinite_integral_eq_critical
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    (∫ v : ℝ, cglLemma62PrincipalReflectedFiniteIntegrand w N Q t M v) =
      ∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        ((1 / 2 : ℂ) + (v : ℂ) * I) := by
  rw [cglLemma62_principalRegularizedFinite_critical_eq_left]
  apply integral_congr_ae
  filter_upwards with v
  exact (cglLemma62PrincipalRegularizedFiniteContourIntegrand_eq_line w N Q t v M).symm

end

end RHTower
