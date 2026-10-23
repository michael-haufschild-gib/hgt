import GaloisForLFunctions.HTGeometry.LogNormalEquationTrace

/-!
# `(9)`: differentiating the logarithmic normal equation

The primitive inside `P` cancels one copy of the profile:

`(P F)′ = (2LF)′ − F = 2F + 2LF′ − F = F + 2LF′`,

and the Gamma transport commutes with differentiation because its kernel does not see the
evaluation point.  Hence `P F + R F = G` differentiates to `(2L + R)F′ + F = G′`, and any constant
in the source disappears.

The domination for differentiating under the integral sign is the kernel's *first moment*: a
Lipschitz derivative makes the second difference `O(s)` uniformly in the evaluation point, and
`s·k(s)` is integrable on the whole positive ray — at the origin because the factor `s` cancels the
pole, at infinity because the kernel decays exponentially.  No boundedness of the second derivative
is needed, and no boundedness of `F′` beyond what the Lipschitz bound on `F` requires.
-/

open MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A profile with a bounded derivative is Lipschitz. -/
theorem abs_sub_le_of_deriv_bound {F F' : ℝ → ℝ} {M : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hM : ∀ x, |F' x| ≤ M) (a b : ℝ) :
    |F a - F b| ≤ M * |a - b| := by
  have hdiff : ∀ θ ∈ uIcc b a, DifferentiableAt ℝ F θ := fun θ _ => (hF θ).differentiableAt
  have hbound : ∀ θ ∈ uIcc b a, ‖deriv F θ‖ ≤ M := by
    intro θ _
    rw [(hF θ).deriv, Real.norm_eq_abs]
    exact hM θ
  have h := (convex_uIcc b a).norm_image_sub_le_of_norm_deriv_le hdiff hbound
    left_mem_uIcc right_mem_uIcc
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- The second difference of a profile with a bounded derivative is `O(s)`. -/
theorem abs_secondDifference_le_of_deriv_bound {F F' : ℝ → ℝ} {M : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hM : ∀ x, |F' x| ≤ M) (L s : ℝ) :
    |secondDifference F L s| ≤ 2 * M * |s| := by
  have h1 : |F L - F (L + s)| ≤ M * |s| := by
    have := abs_sub_le_of_deriv_bound hF hM L (L + s)
    simpa using this
  have h2 : |F L - F (L - s)| ≤ M * |s| := by
    have := abs_sub_le_of_deriv_bound hF hM L (L - s)
    simpa using this
  have hsum : secondDifference F L s = (F L - F (L + s)) + (F L - F (L - s)) := by
    rw [secondDifference]; ring
  rw [hsum]
  calc |(F L - F (L + s)) + (F L - F (L - s))|
      ≤ |F L - F (L + s)| + |F L - F (L - s)| := abs_add_le _ _
    _ ≤ M * |s| + M * |s| := add_le_add h1 h2
    _ = 2 * M * |s| := by ring

/-- The Gamma transport is absolutely convergent for a Lipschitz profile. -/
theorem integrableOn_secondDifference_mul_kernel {F F' : ℝ → ℝ} {M : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hM : ∀ x, |F' x| ≤ M) (L : ℝ) :
    IntegrableOn (fun s => secondDifference F L s * gammaTransportKernel s) (Ioi 0) := by
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact (hF x).continuousAt
  have hmeas : AEStronglyMeasurable
      (fun s => secondDifference F L s * gammaTransportKernel s) (volume.restrict (Ioi 0)) := by
    have hsd : Continuous fun s : ℝ => secondDifference F L s := by
      have : Continuous fun s : ℝ => 2 * F L - F (L + s) - F (L - s) :=
        ((continuous_const.sub (hFc.comp (continuous_const.add continuous_id))).sub
          (hFc.comp (continuous_const.sub continuous_id)))
      exact this
    exact (hsd.aestronglyMeasurable.mul
      measurable_gammaTransportKernel.aestronglyMeasurable)
  refine Integrable.mono' (integrableOn_id_mul_gammaTransportKernel_Ioi_zero.const_mul (2 * M))
    hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hspos : (0 : ℝ) < s := hs
  have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hspos
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
  have hsd := abs_secondDifference_le_of_deriv_bound hF hM L s
  rw [abs_of_pos hspos] at hsd
  calc |secondDifference F L s| * gammaTransportKernel s
      ≤ (2 * M * s) * gammaTransportKernel s :=
        mul_le_mul_of_nonneg_right hsd hkpos.le
    _ = 2 * M * (s * gammaTransportKernel s) := by ring

/-- **The Gamma transport commutes with differentiation.**  Its kernel does not see the evaluation
point, and a Lipschitz derivative makes the differentiated second difference `O(s)` uniformly. -/
theorem hasDerivAt_gammaTransport {F F' F'' : ℝ → ℝ} {M K : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hM : ∀ x, |F' x| ≤ M) (hK : ∀ x, |F'' x| ≤ K) (L : ℝ) :
    HasDerivAt (gammaTransport F) (gammaTransport F' L) L := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hF'c : Continuous F' := continuous_iff_continuousAt.mpr fun x => (hF' x).continuousAt
  have hcont : ∀ y : ℝ, Continuous fun s : ℝ => secondDifference F y s := by
    intro y
    have : Continuous fun s : ℝ => 2 * F y - F (y + s) - F (y - s) :=
      ((continuous_const.sub (hFc.comp (continuous_const.add continuous_id))).sub
        (hFc.comp (continuous_const.sub continuous_id)))
    exact this
  have hcont' : Continuous fun s : ℝ => secondDifference F' L s := by
    have : Continuous fun s : ℝ => 2 * F' L - F' (L + s) - F' (L - s) :=
      ((continuous_const.sub (hF'c.comp (continuous_const.add continuous_id))).sub
        (hF'c.comp (continuous_const.sub continuous_id)))
    exact this
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (y : ℝ) (s : ℝ) => secondDifference F y s * gammaTransportKernel s)
    (F' := fun (y : ℝ) (s : ℝ) => secondDifference F' y s * gammaTransportKernel s)
    (x₀ := L) (bound := fun s : ℝ => 2 * K * (s * gammaTransportKernel s))
    (s := Metric.ball L 1) (Metric.ball_mem_nhds L one_pos)
    (Filter.Eventually.of_forall fun y =>
      ((hcont y).aestronglyMeasurable.mul
        measurable_gammaTransportKernel.aestronglyMeasurable))
    (integrableOn_secondDifference_mul_kernel hF hM L)
    (hcont'.aestronglyMeasurable.mul measurable_gammaTransportKernel.aestronglyMeasurable)
    ?_ (integrableOn_id_mul_gammaTransportKernel_Ioi_zero.const_mul (2 * K)) ?_
  · exact hkey.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs y _
    have hspos : (0 : ℝ) < s := hs
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hspos
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hkpos]
    have hsd := abs_secondDifference_le_of_deriv_bound hF' hK y s
    rw [abs_of_pos hspos] at hsd
    calc |secondDifference F' y s| * gammaTransportKernel s
        ≤ (2 * K * s) * gammaTransportKernel s := mul_le_mul_of_nonneg_right hsd hkpos.le
      _ = 2 * K * (s * gammaTransportKernel s) := by ring
  · filter_upwards with s y _
    have h1 : HasDerivAt (fun y : ℝ => 2 * F y - F (y + s) - F (y - s))
        (2 * F' y - F' (y + s) - F' (y - s)) y := by
      have ha : HasDerivAt (fun y : ℝ => F (y + s)) (F' (y + s)) y :=
        HasDerivAt.comp_add_const y s (hF (y + s))
      have hb : HasDerivAt (fun y : ℝ => F (y - s)) (F' (y - s)) y :=
        HasDerivAt.comp_sub_const y s (hF (y - s))
      exact (((hF y).const_mul 2).sub ha).sub hb
    exact h1.mul_const (gammaTransportKernel s)

/-- **The full primitive differentiates to the profile.** -/
theorem hasDerivAt_fullPrimitive {F : ℝ → ℝ} (hFc : Continuous F)
    (hint : ∀ y : ℝ, IntegrableOn F (Iic y)) (L : ℝ) :
    HasDerivAt (fullPrimitive F) (F L) L := by
  have hsplit : ∀ y : ℝ, fullPrimitive F y = fullPrimitive F 0 + ∫ x in (0 : ℝ)..y, F x := by
    intro y
    rcases le_or_gt (0 : ℝ) y with hy | hy
    · have hdisj : Disjoint (Iic (0 : ℝ)) (Ioc (0 : ℝ) y) := by
        rw [Set.disjoint_left]
        intro t ht ht'
        exact absurd ht'.1 (not_lt.mpr ht)
      have hunion : Iic y = Iic (0 : ℝ) ∪ Ioc (0 : ℝ) y := (Iic_union_Ioc_eq_Iic hy).symm
      have h1 : IntegrableOn F (Iic (0 : ℝ)) := hint 0
      have h2 : IntegrableOn F (Ioc (0 : ℝ) y) :=
        (hint y).mono_set (by rw [hunion]; exact subset_union_right)
      rw [fullPrimitive, hunion, setIntegral_union hdisj measurableSet_Ioc h1 h2,
        intervalIntegral.integral_of_le hy]
      rfl
    · have hy' : y ≤ 0 := hy.le
      have hdisj : Disjoint (Iic y) (Ioc y (0 : ℝ)) := by
        rw [Set.disjoint_left]
        intro t ht ht'
        exact absurd ht'.1 (not_lt.mpr ht)
      have hunion : Iic (0 : ℝ) = Iic y ∪ Ioc y (0 : ℝ) := (Iic_union_Ioc_eq_Iic hy').symm
      have h1 : IntegrableOn F (Iic y) := hint y
      have h2 : IntegrableOn F (Ioc y (0 : ℝ)) :=
        (hint 0).mono_set (by rw [hunion]; exact subset_union_right)
      have hbase : fullPrimitive F 0 = fullPrimitive F y + ∫ x in y..(0 : ℝ), F x := by
        rw [fullPrimitive, hunion, setIntegral_union hdisj measurableSet_Ioc h1 h2,
          intervalIntegral.integral_of_le hy']
        rfl
      rw [hbase, intervalIntegral.integral_symm]
      ring
  have hfun : fullPrimitive F = fun y : ℝ => fullPrimitive F 0 + ∫ x in (0 : ℝ)..y, F x := by
    funext y
    exact hsplit y
  rw [hfun]
  have hFTC : HasDerivAt (fun y : ℝ => ∫ x in (0 : ℝ)..y, F x) (F L) L := by
    refine intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable 0 L) ?_
      hFc.continuousAt
    exact hFc.stronglyMeasurableAtFilter _ _
  exact hFTC.const_add _

/-- **`(9)`: the differentiated logarithmic normal equation.**  On the open ray where the equation
holds, the source is differentiable and its derivative is `(2L + R)F′ + F`. -/
theorem hasDerivAt_source_of_logNormalEquation {F F' F'' G : ℝ → ℝ} {L₀ M K : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hM : ∀ x, |F' x| ≤ M) (hK : ∀ x, |F'' x| ≤ K)
    (hint : ∀ y : ℝ, IntegrableOn F (Iic y))
    (hEq : ∀ y ∈ Ioi L₀, fullLogDirichlet F y + gammaTransport F y = G y)
    {L : ℝ} (hL : L ∈ Ioi L₀) :
    HasDerivAt G (2 * L * F' L + F L + gammaTransport F' L) L := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hP : HasDerivAt (fun y : ℝ => 2 * y * F y - fullPrimitive F y)
      (2 * F L + 2 * L * F' L - F L) L := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y * F y) (2 * F L + 2 * L * F' L) L := by
      have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 L := by
        simpa using (hasDerivAt_id L).const_mul (2 : ℝ)
      exact (hlin.mul (hF L)).congr_deriv (by ring)
    exact h1.sub (hasDerivAt_fullPrimitive hFc hint L)
  have hR : HasDerivAt (gammaTransport F) (gammaTransport F' L) L :=
    hasDerivAt_gammaTransport hF hF' hM hK L
  have hsum : HasDerivAt (fun y : ℝ => fullLogDirichlet F y + gammaTransport F y)
      (2 * L * F' L + F L + gammaTransport F' L) L := by
    have h := hP.add hR
    refine h.congr_deriv ?_
    ring
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hL] with y hy
  exact (hEq y hy).symm

end GaloisForLFunctions.HTGeometry
