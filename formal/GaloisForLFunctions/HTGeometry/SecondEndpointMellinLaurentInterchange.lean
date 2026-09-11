import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLaurentInterchange
import GaloisForLFunctions.HTGeometry.NormalizedFirstEndpointMellin

/-!
# Two-counterterm horizon finite parts and Laurent extraction

A horizon density `t^(w-1) * F w t` with `F w t = F w 0 + F₁ w * t + O(t²)` needs two
counterterms below `Re w = -1`.  Dividing the first difference by `t` turns the second-order
remainder into the first-order remainder of `H w t := (F w t - F w 0)/t`, `H w 0 := F₁ w`, so the
whole first-endpoint theory applies verbatim: the two-counterterm finite part is the cutoff limit,
is holomorphic in the frequency, and residue extraction commutes with it.

This is the abstract form of the radial finite part used by the HB temporal current, whose
integrated Laurent density carries exactly the counterterms `z^w/(2w) - z^(w+1)/(4(w+1))`.  It
evaluates no physical current.
-/

namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set Metric
noncomputable section
set_option autoImplicit false

/-- The divided first difference, with the slope restored at the horizon. -/
def dividedDifference (F : ℂ → ℝ → ℂ) (F₁ : ℂ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  if t = 0 then F₁ w else (F w t - F w 0) / t

/-- The two-counterterm finite part of `∫₀^b t^(w-1) F w t dt`. -/
def secondEndpointMellin (F : ℂ → ℝ → ℂ) (F₁ : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  F w 0 * (b:ℂ) ^ w / w + firstEndpointMellin (dividedDifference F F₁) b w

theorem dividedDifference_zero (F : ℂ → ℝ → ℂ) (F₁ : ℂ → ℂ) (w : ℂ) :
    dividedDifference F F₁ w 0 = F₁ w := by simp [dividedDifference]

theorem dividedDifference_of_ne (F : ℂ → ℝ → ℂ) (F₁ : ℂ → ℂ) (w : ℂ) {t : ℝ} (ht : t ≠ 0) :
    dividedDifference F F₁ w t = (F w t - F w 0) / t := by simp [dividedDifference, ht]

/-- A second-order horizon bound on `F` is a first-order bound on the divided difference. -/
theorem dividedDifference_lipschitz {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t - F w 0 - F₁ w * t‖ ≤ C * t ^ 2) :
    ∀ t ∈ Ioc (0:ℝ) b, ‖dividedDifference F F₁ w t - dividedDifference F F₁ w 0‖ ≤ C * t := by
  intro t ht
  have htne : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  rw [dividedDifference_of_ne F F₁ w ht.1.ne', dividedDifference_zero]
  have h : (F w t - F w 0) / t - F₁ w = (F w t - F w 0 - F₁ w * t) / t := by
    rw [eq_div_iff htne, sub_mul, div_mul_cancel₀ _ htne]
  rw [h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
    div_le_iff₀ ht.1]
  calc ‖F w t - F w 0 - F₁ w * t‖ ≤ C * t ^ 2 := hC t ht
    _ = C * t * t := by ring

theorem measurable_dividedDifference {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} (hm : Measurable (F w)) :
    Measurable (dividedDifference F F₁ w) := by
  unfold dividedDifference
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact (hm.sub measurable_const).div Complex.measurable_ofReal

theorem differentiableAt_dividedDifference {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hF : DifferentiableAt ℂ (fun v => F v t) u) (hF0 : DifferentiableAt ℂ (fun v => F v 0) u)
    (hF₁ : DifferentiableAt ℂ F₁ u) :
    DifferentiableAt ℂ (fun v => dividedDifference F F₁ v t) u := by
  by_cases ht : t = 0
  · subst ht
    simp only [dividedDifference_zero]
    exact hF₁
  · simp only [dividedDifference_of_ne F F₁ _ ht]
    exact (hF.sub hF0).div_const _

/-- The two-counterterm finite part is the cutoff limit of the ordinary integral. -/
theorem secondEndpointMellin_cutoff_tendsto {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0)
    (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t - F w 0 - F₁ w * t‖ ≤ C * t ^ 2) :
    Tendsto (fun ε : ℝ => (∫ t in Ioc ε b, (t:ℂ) ^ (w - 1) * F w t) +
        F w 0 * (ε:ℂ) ^ w / w + F₁ w * (ε:ℂ) ^ (w + 1) / (w + 1))
      (𝓝[>] (0:ℝ)) (𝓝 (secondEndpointMellin F F₁ b w)) := by
  set H := dividedDifference F F₁ with hH
  have hHm : Measurable (H w) := measurable_dividedDifference hm
  have hHC := dividedDifference_lipschitz hC
  have hint : IntegrableOn (fun t : ℝ => (t:ℂ) ^ w * (H w t - H w 0)) (Ioc 0 b) :=
    firstEndpointMellinRemainder_integrable hb.le hw hHm hHC
  -- the tail of the remainder vanishes
  have htail : Tendsto (fun ε : ℝ => ∫ t in Ioc 0 ε, (t:ℂ) ^ w * (H w t - H w 0))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hCnn : 0 ≤ C := by
      have := hC b ⟨hb, le_rfl⟩
      have hb2 : 0 < b ^ 2 := by positivity
      nlinarith [norm_nonneg (F w b - F w 0 - F₁ w * b)]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    obtain ⟨η, hη0, hηb, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ b ∧ C * η ^ (w.re + 2) / (w.re + 2) < δ := by
      have hlim : Tendsto (fun η : ℝ => C * η ^ (w.re + 2) / (w.re + 2)) (𝓝[>] 0) (𝓝 0) := by
        have h0 : Tendsto (fun η : ℝ => η ^ (w.re + 2)) (𝓝[>] 0) (𝓝 0) := by
          have := (Real.continuousAt_rpow_const 0 (w.re + 2) (Or.inr (by linarith))).tendsto
          rw [Real.zero_rpow (by linarith)] at this
          exact this.mono_left nhdsWithin_le_nhds
        simpa using (h0.const_mul C).div_const (w.re + 2)
      obtain ⟨r, hr, hrr⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlim) δ hδ
      have hm2 : 0 < min r b / 2 := half_pos (lt_min hr hb)
      refine ⟨min r b / 2, hm2, by linarith [min_le_right r b], ?_⟩
      have h1 := hrr (show min r b / 2 ∈ Ioi (0:ℝ) from hm2)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hm2]; linarith [min_le_left r b])
      rw [Real.dist_eq, sub_zero] at h1
      exact (abs_lt.mp h1).2
    refine ⟨η, hη0, fun ε hε hd => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (mem_Ioi.mp hε)] at hd
    rw [dist_zero_right]
    have hεb : ε ≤ b := by linarith
    have hbound := normalizedMellinRemainder_norm_le (F := H) (w := w) (b := ε) (C := C)
      (mem_Ioi.mp hε) hw hHm (fun t ht => hHC t ⟨ht.1, ht.2.trans hεb⟩)
    calc ‖∫ t in Ioc 0 ε, (t:ℂ) ^ w * (H w t - H w 0)‖ ≤ C * ε ^ (w.re + 2) / (w.re + 2) := hbound
      _ ≤ C * η ^ (w.re + 2) / (w.re + 2) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mem_Ioi.mp hε).le hd.le (by linarith)) hCnn
      _ < δ := hηδ
  -- decompose the cutoff integral for 0 < ε ≤ b
  have hdecomp : ∀ ε ∈ Ioc (0:ℝ) b,
      (∫ t in Ioc ε b, (t:ℂ) ^ (w - 1) * F w t) + F w 0 * (ε:ℂ) ^ w / w +
        F₁ w * (ε:ℂ) ^ (w + 1) / (w + 1) =
      secondEndpointMellin F F₁ b w - ∫ t in Ioc 0 ε, (t:ℂ) ^ w * (H w t - H w 0) := by
    intro ε hε
    have hεb := hε.2
    have hε0 := hε.1
    have hpt : ∀ t ∈ Ioc ε b, (t:ℂ) ^ (w - 1) * F w t =
        (t:ℂ) ^ w * (H w t - H w 0) + F w 0 * (t:ℂ) ^ (w - 1) + F₁ w * (t:ℂ) ^ w := by
      intro t ht
      have ht0 : (0:ℝ) < t := hε0.trans ht.1
      have htne : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      rw [hH, dividedDifference_of_ne F F₁ w ht0.ne', dividedDifference_zero]
      have hpow : (t:ℂ) ^ w = (t:ℂ) ^ (w - 1) * t := by
        conv_lhs => rw [← sub_add_cancel w 1]
        rw [Complex.cpow_add _ _ htne, Complex.cpow_one]
      rw [hpow]
      field_simp
      ring
    have hI1 : IntegrableOn (fun t : ℝ => (t:ℂ) ^ w * (H w t - H w 0)) (Ioc ε b) :=
      hint.mono_set (Ioc_subset_Ioc_left hε0.le)
    have hcont : ∀ (c : ℂ), IntegrableOn (fun t : ℝ => (t:ℂ) ^ c) (Ioc ε b) := by
      intro c
      refine (ContinuousOn.integrableOn_Icc (fun t ht => ?_)).mono_set Ioc_subset_Icc_self
      exact (Complex.continuousAt_ofReal_cpow_const t c
        (Or.inr (hε0.trans_le ht.1).ne')).continuousWithinAt
    have hA : IntegrableOn (fun t : ℝ => (t:ℂ) ^ w * (H w t - H w 0) + F w 0 * (t:ℂ) ^ (w - 1))
        (Ioc ε b) := hI1.add ((hcont (w - 1)).const_mul (F w 0))
    have hB : IntegrableOn (fun t : ℝ => F₁ w * (t:ℂ) ^ w) (Ioc ε b) :=
      (hcont w).const_mul (F₁ w)
    have hC' : IntegrableOn (fun t : ℝ => F w 0 * (t:ℂ) ^ (w - 1)) (Ioc ε b) :=
      (hcont (w - 1)).const_mul (F w 0)
    have hsplit : (∫ t in Ioc ε b, (t:ℂ) ^ (w - 1) * F w t) =
        (∫ t in Ioc ε b, (t:ℂ) ^ w * (H w t - H w 0)) +
        F w 0 * (∫ t in Ioc ε b, (t:ℂ) ^ (w - 1)) + F₁ w * (∫ t in Ioc ε b, (t:ℂ) ^ w) := by
      rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hA hB, integral_add hI1 hC',
        integral_const_mul, integral_const_mul]
    have h0uIcc : (0:ℝ) ∉ uIcc ε b := by
      rw [uIcc_of_le hεb]
      exact fun h => absurd h.1 (not_le.mpr hε0)
    have hp1 : (∫ t in Ioc ε b, (t:ℂ) ^ (w - 1)) = ((b:ℂ) ^ w - (ε:ℂ) ^ w) / w := by
      rw [← intervalIntegral.integral_of_le hεb,
        integral_cpow (Or.inr ⟨fun h => hw0 (by linear_combination h), h0uIcc⟩), sub_add_cancel]
    have hp2 : (∫ t in Ioc ε b, (t:ℂ) ^ w) = ((b:ℂ) ^ (w + 1) - (ε:ℂ) ^ (w + 1)) / (w + 1) := by
      rw [← intervalIntegral.integral_of_le hεb,
        integral_cpow (Or.inr ⟨fun h => hw1 (by rw [h]; ring), h0uIcc⟩)]
    have hrem : (∫ t in Ioc ε b, (t:ℂ) ^ w * (H w t - H w 0)) =
        (∫ t in Ioc 0 b, (t:ℂ) ^ w * (H w t - H w 0)) -
        ∫ t in Ioc 0 ε, (t:ℂ) ^ w * (H w t - H w 0) := by
      have hu : Ioc (0:ℝ) ε ∪ Ioc ε b = Ioc 0 b := Ioc_union_Ioc_eq_Ioc hε0.le hεb
      have hd : Disjoint (Ioc (0:ℝ) ε) (Ioc ε b) := Ioc_disjoint_Ioc_of_le le_rfl
      rw [← hu, setIntegral_union hd measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hεb))
        (hint.mono_set (Ioc_subset_Ioc_left hε0.le))]
      ring
    rw [hsplit, hp1, hp2, hrem, secondEndpointMellin, firstEndpointMellin,
      firstEndpointMellinRemainder, hH, dividedDifference_zero]
    field_simp
    ring
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Ioc (0:ℝ) b := Ioc_mem_nhdsGT hb
  have hlim := (tendsto_const_nhds (x := secondEndpointMellin F F₁ b w)).sub htail
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with ε hε
  exact (hdecomp ε hε).symm

/-- Holomorphy of the two-counterterm finite part in the frequency. -/
theorem secondEndpointMellin_differentiableAt
    {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hd₁ : ∀ u ∈ ball w R, DifferentiableAt ℂ F₁ u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0 - F₁ u * t‖ ≤ C * t ^ 2)
    (hw0 : w ≠ 0) (hw1 : w + 1 ≠ 0) :
    DifferentiableAt ℂ (secondEndpointMellin F F₁ b) w := by
  have hH := firstEndpointMellin_differentiableAt (F := dividedDifference F F₁) hb hb1 hR hC0 hβ
    hreal (fun u hu => measurable_dividedDifference (hm u hu))
    (fun t ht u hu => differentiableAt_dividedDifference (hd t ht u hu) (hd 0 ⟨le_rfl, hb.le⟩ u hu)
      (hd₁ u hu))
    (fun u hu t ht => dividedDifference_lipschitz (hC u hu) t ht) hw1
  have hF0 : DifferentiableAt ℂ (fun v => F v 0) w := hd 0 ⟨le_rfl, hb.le⟩ w (mem_ball_self hR)
  have hpow : DifferentiableAt ℂ (fun v : ℂ => (b:ℂ) ^ v) w :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))
  have h1 : DifferentiableAt ℂ (fun v => F v 0 * (b:ℂ) ^ v / v) w :=
    (hF0.mul hpow).div differentiableAt_id hw0
  show DifferentiableAt ℂ (fun v => F v 0 * (b:ℂ) ^ v / v + firstEndpointMellin (dividedDifference F F₁) b v) w
  exact h1.add hH

/-- Analyticity of the two-counterterm finite part on a ball avoiding `0` and `-1`. -/
theorem secondEndpointMellin_analyticAt
    {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hd₁ : ∀ u ∈ ball w R, DifferentiableAt ℂ F₁ u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0 - F₁ u * t‖ ≤ C * t ^ 2)
    (hw0 : ∀ u ∈ ball w R, u ≠ 0) (hw1 : ∀ u ∈ ball w R, u + 1 ≠ 0) :
    AnalyticAt ℂ (secondEndpointMellin F F₁ b) w := by
  have hdiff : DifferentiableOn ℂ (secondEndpointMellin F F₁ b) (ball w (R / 2)) := by
    intro u hu
    have hsub : ball u (R / 2) ⊆ ball w R := by
      apply ball_subset_ball'
      have := mem_ball.mp hu
      linarith
    have huw : u ∈ ball w R := ball_subset_ball (by linarith) hu
    exact (secondEndpointMellin_differentiableAt hb hb1 (half_pos hR) hC0 hβ
      (fun v hv => hreal v (hsub hv)) (fun v hv => hm v (hsub hv))
      (fun t ht v hv => hd t ht v (hsub hv)) (fun v hv => hd₁ v (hsub hv))
      (fun v hv t ht => hC v (hsub hv) t ht) (hw0 u huw) (hw1 u huw)).differentiableWithinAt
  exact hdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)))

/-- Scalars pass through the two-counterterm finite part. -/
theorem secondEndpointMellin_const_mul (c : ℂ → ℂ) (F : ℂ → ℝ → ℂ) (F₁ : ℂ → ℂ) (b : ℝ) (w : ℂ) :
    secondEndpointMellin (fun u t => c u * F u t) (fun u => c u * F₁ u) b w =
      c w * secondEndpointMellin F F₁ b w := by
  have he : dividedDifference (fun u t => c u * F u t) (fun u => c u * F₁ u) =
      fun u t => c u * dividedDifference F F₁ u t := by
    funext u t
    by_cases ht : t = 0
    · subst ht; simp [dividedDifference]
    · simp [dividedDifference, ht]; ring
  rw [secondEndpointMellin, secondEndpointMellin, he, firstEndpointMellin_const_mul]
  ring

/-- Residue extraction commutes with the two-counterterm horizon finite part. -/
theorem laurentCoeff_secondEndpointMellin_div_sub
    {F : ℂ → ℝ → ℂ} {F₁ : ℂ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hd₁ : ∀ u ∈ ball w R, DifferentiableAt ℂ F₁ u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t - F u 0 - F₁ u * t‖ ≤ C * t ^ 2)
    (hw0 : ∀ u ∈ ball w R, u ≠ 0) (hw1 : ∀ u ∈ ball w R, u + 1 ≠ 0) :
    laurentCoeff (fun u => secondEndpointMellin (fun v t => F v t / (v - w))
      (fun v => F₁ v / (v - w)) b u) w (-1) = secondEndpointMellin F F₁ b w := by
  have he : (fun u => secondEndpointMellin (fun v t => F v t / (v - w))
      (fun v => F₁ v / (v - w)) b u) = fun u => secondEndpointMellin F F₁ b u / (u - w) := by
    funext u
    have h1 : (fun v t => F v t / (v - w)) = fun v t => (1 / (v - w)) * F v t := by
      funext v t; ring
    have h2 : (fun v => F₁ v / (v - w)) = fun v => (1 / (v - w)) * F₁ v := by
      funext v; ring
    rw [h1, h2, secondEndpointMellin_const_mul]
    ring
  rw [he]
  exact laurentCoeff_analytic_div_sub
    (secondEndpointMellin_analyticAt hb hb1 hR hC0 hβ hreal hm hd hd₁ hC hw0 hw1)

end
end GaloisForLFunctions.HTGeometry
