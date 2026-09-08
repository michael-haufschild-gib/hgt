import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalTailStripBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailRapidTruncation
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Chen--Gupta--Li Lemma 6.2: principal tail moved to the deep line

Cauchy's theorem on tall rectangles moves the principal reflected `m > M`
tail from `Re s = -1` to the deep line `Re s = -2k`, where it is the
absolutely convergent complementary Dirichlet series with arbitrary polynomial
ordinate decay; a symmetric truncation of that deep integral costs only its
two-sided power tail.
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

private theorem cglLemma62_principalTail_horizontal_decay (C : ℝ) :
    Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
  have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  refine Filter.Tendsto.congr' ?_ hscaled
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]

/-- The upper horizontal side of the principal tail rectangle vanishes. -/
theorem cglLemma62_principalTail_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62PrincipalTailContourIntegrand w N Q t M.value
          ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalTail_strip_bound w N Q t M d 2
  have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => y)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy x hx
    have hx' : x ∈ Icc (-2 * (d.value : ℝ)) (-1) := by
      rw [← uIcc_of_le (by linarith : (-2 * (d.value : ℝ)) ≤ -1)]
      exact uIoc_subset_uIcc hx
    have hy0 : 0 ≤ y := by linarith
    have hyabs : 1 ≤ |y| := by rwa [abs_of_nonneg hy0]
    have h := hpoint x y hx'.1 hx'.2 hyabs
    simpa [abs_of_nonneg hy0] using h
  · exact cglLemma62_principalTail_horizontal_decay C

/-- The lower horizontal side of the principal tail rectangle vanishes. -/
theorem cglLemma62_principalTail_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62PrincipalTailContourIntegrand w N Q t M.value
          ((x : ℂ) + (y : ℂ) * I)) atBot (𝓝 0) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalTail_strip_bound w N Q t M d 2
  have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62PrincipalTailContourIntegrand w N Q t M.value
          ((x : ℂ) + ((-y : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy x hx
      have hx' : x ∈ Icc (-2 * (d.value : ℝ)) (-1) := by
        rw [← uIcc_of_le (by linarith : (-2 * (d.value : ℝ)) ≤ -1)]
        exact uIoc_subset_uIcc hx
      have hy0 : 0 ≤ y := by linarith
      have hyabs : 1 ≤ |-y| := by rwa [abs_neg, abs_of_nonneg hy0]
      have h := hpoint x (-y) hx'.1 hx'.2 hyabs
      simpa [abs_neg, abs_of_nonneg hy0] using h
    · exact cglLemma62_principalTail_horizontal_decay C
  refine Filter.Tendsto.congr' ?_ (hneg.comp tendsto_neg_atBot_atTop)
  filter_upwards with y
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x
  intro _
  congr 1
  push_cast
  ring

private theorem cglLemma62_principalTail_abs_rpow_tail_integrable {r c : ℝ}
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

/-- The continued principal tail carrier is continuous along every vertical
line of the deep strip. -/
theorem cglLemma62_principalTail_line_continuous
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) (d : CGLLemma62TailContourDepth) {σ : ℝ}
    (hlo : -2 * (d.value : ℝ) ≤ σ) (hhi : σ ≤ -1) :
    Continuous (fun v : ℝ => cglLemma62PrincipalTailContourIntegrand w N Q t M
      ((σ : ℂ) + (v : ℂ) * I)) := by
  let line : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
  have hline : Continuous line := by
    dsimp [line]
    fun_prop
  have hmaps : ∀ v : ℝ, line v ∈
      GaloisForLFunctions.HTGeometry.verticalStrip (-2 * (d.value : ℝ)) (-1) := by
    intro v
    change (-2 * (d.value : ℝ)) ≤ (line v).re ∧ (line v).re ≤ -1
    dsimp [line]
    simp
    exact ⟨by linarith, hhi⟩
  have hcont :=
    (cglLemma62PrincipalTailContourIntegrand_differentiableOn w N Q t M d.value).continuousOn
  change Continuous (cglLemma62PrincipalTailContourIntegrand w N Q t M ∘ line)
  exact hcont.comp_continuous hline hmaps

/-- The continued principal tail carrier is integrable on every vertical line
of the deep strip. -/
theorem cglLemma62_principalTail_vertical_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) {σ : ℝ}
    (hlo : -2 * (d.value : ℝ) ≤ σ) (hhi : σ ≤ -1) :
    Integrable (fun v : ℝ => cglLemma62PrincipalTailContourIntegrand w N Q t M.value
      ((σ : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalTail_strip_bound w N Q t M d 2
  let f : ℝ → ℂ := fun v => cglLemma62PrincipalTailContourIntegrand w N Q t M.value
    ((σ : ℂ) + (v : ℂ) * I)
  have hcont : Continuous f :=
    cglLemma62_principalTail_line_continuous w N Q t M.value d hlo hhi
  have htailmajor : IntegrableOn (fun v : ℝ => C * |v| ^ (-(2 : ℝ)))
      {v : ℝ | (1 : ℝ) < |v|} :=
    (cglLemma62_principalTail_abs_rpow_tail_integrable (r := -(2 : ℝ)) (c := 1)
      (by norm_num) one_pos).const_mul C
  have htailMeas : MeasurableSet {v : ℝ | (1 : ℝ) < |v|} :=
    measurableSet_lt continuous_const.measurable continuous_abs.measurable
  have htail : IntegrableOn f {v : ℝ | (1 : ℝ) < |v|} := by
    refine Integrable.mono' htailmajor (hcont.continuousOn.aestronglyMeasurable htailMeas) ?_
    filter_upwards [ae_restrict_mem htailMeas] with v hv
    have hylarge : 1 ≤ |v| := le_of_lt hv
    have hpoint' := hpoint σ v hlo hhi hylarge
    have hvpos : 0 < |v| := lt_of_lt_of_le zero_lt_one hylarge
    have hrewrite : C / |v| ^ 2 = C * |v| ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hvpos), Real.rpow_two, div_eq_mul_inv]
    change ‖f v‖ ≤ C * |v| ^ (-(2 : ℝ))
    rw [← hrewrite]
    exact hpoint'
  have hmiddle : IntegrableOn f (Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_Icc
  have hcover : {v : ℝ | (1 : ℝ) < |v|} ∪ Icc (-1) 1 = univ := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_univ, iff_true]
    by_cases hv : (1 : ℝ) < |v|
    · exact Or.inl hv
    · right
      have hv' : |v| ≤ 1 := le_of_not_gt hv
      exact abs_le.mp hv'
  rw [← integrableOn_univ, ← hcover]
  exact htail.union hmiddle

/-- Cauchy's theorem moves the continued principal tail carrier from the
reflected line to the deep line with no residue. -/
theorem cglLemma62_principalTail_left_eq_deep
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        ((-1 : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        (((-2 * (d.value : ℝ) : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
  have hdeep : Integrable (fun v : ℝ =>
      cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        (((-2 * (d.value : ℝ) : ℝ) : ℂ) + (v : ℂ) * I)) :=
    cglLemma62_principalTail_vertical_integrable w N Q t M d le_rfl (by linarith)
  have hleft : Integrable (fun v : ℝ =>
      cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    cglLemma62_principalTail_vertical_integrable w N Q t M d (by linarith) le_rfl
  have h := GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (G := cglLemma62PrincipalTailContourIntegrand w N Q t M.value)
    (c := (-2 * (d.value : ℝ))) (d := (-1 : ℝ)) (by linarith)
    (cglLemma62PrincipalTailContourIntegrand_differentiableOn w N Q t M.value d.value)
    hdeep hleft ?_ ?_
  · simpa using h
  · have hb := (cglLemma62_principalTail_horizontal_bottom w N Q t M d).comp
      tendsto_neg_atTop_atBot
    refine Filter.Tendsto.congr' ?_ hb
    filter_upwards with T
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u
    intro _
    congr 1
  · exact cglLemma62_principalTail_horizontal_top w N Q t M d

/-- CGL's principal reflected complementary tail equals its absolutely
convergent deep-line form. -/
theorem cglLemma62_principalReflectedTail_integral_eq_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62PrincipalReflectedTailIntegrand w N Q t M.value v) =
      ∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v := by
  have hleft : (∫ v : ℝ, cglLemma62PrincipalReflectedTailIntegrand w N Q t M.value v) =
      ∫ v : ℝ, cglLemma62PrincipalTailContourIntegrand w N Q t M.value
        ((-1 : ℂ) + (v : ℂ) * I) := by
    apply integral_congr_ae
    filter_upwards with v
    exact (cglLemma62PrincipalTailContourIntegrand_eq_line w N Q t v M.value).symm
  rw [hleft, cglLemma62_principalTail_left_eq_deep w N Q t M d]
  apply integral_congr_ae
  filter_upwards with v
  have h := cglLemma62PrincipalTailContourIntegrand_eq_farTail w N Q t M.value d v
  unfold cglLemma62FarLeftPoint at h
  convert h using 2
  push_cast
  ring

/-- The principal deep-line tail is integrable. -/
theorem cglLemma62_principalFarTail_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    Integrable (fun v : ℝ => cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v) := by
  have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
  refine (cglLemma62_principalTail_vertical_integrable w N Q t M d le_rfl (by linarith)).congr ?_
  filter_upwards with v
  have h := cglLemma62PrincipalTailContourIntegrand_eq_farTail w N Q t M.value d v
  unfold cglLemma62FarLeftPoint at h
  convert h using 2
  push_cast
  ring

/-- Arbitrary polynomial ordinate decay of the principal deep-line tail. -/
theorem cglLemma62_principalFarTail_rapid_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 1 ≤ |v| →
      ‖cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v‖ ≤ C / |v| ^ r := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_exists_principalTail_strip_bound w N Q t M d r
  have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
  refine ⟨C, hC, ?_⟩
  intro v hv
  have h := cglLemma62PrincipalTailContourIntegrand_eq_farTail w N Q t M.value d v
  unfold cglLemma62FarLeftPoint at h
  rw [← h]
  have h' := hpoint (-2 * (d.value : ℝ)) v le_rfl (by linarith) hv
  convert h' using 3
  push_cast
  ring

/-- A symmetric truncation of the principal deep-line tail integral costs
only its exact two-sided power tail. -/
theorem cglLemma62_principalFarTail_integral_sub_truncation_le_power
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) (U : CGLLemma62TailTruncationCertificate) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v) -
          ∫ v : ℝ in -U.radius..U.radius,
            cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v‖ ≤
        2 * C * (U.radius ^ (1 - (U.decayRate : ℝ)) / ((U.decayRate : ℝ) - 1)) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_principalFarTail_rapid_point_bound w N Q t M d U.decayRate
  have hintegrable := cglLemma62_principalFarTail_integrable w N Q t M d
  have hrate : (1 : ℝ) < U.decayRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) U.decayRate_two)
  have hradius : 0 < U.radius := lt_of_lt_of_le zero_lt_one U.radius_one
  have hbound : ∀ v : ℝ, U.radius ≤ |v| →
      ‖cglLemma62PrincipalFarTailIntegrand w N Q t M.value d v‖ ≤
        C * |v| ^ (-(U.decayRate : ℝ)) := by
    intro v hv
    calc
      _ ≤ C / |v| ^ U.decayRate := hpoint v (U.radius_one.trans hv)
      _ = _ := by
        rw [Real.rpow_neg (abs_nonneg v), Real.rpow_natCast]
        ring
  exact ⟨C, hC, RHTower.Sieve.norm_integral_sub_interval_le_powerTail
    hintegrable hC hrate hradius hbound⟩

end

end RHTower
