import Mathlib

/-!
# The Mellin step for an antiderivative

For a locally integrable `r` on `[1,∞)` and `Re μ > 0`,

```text
μ ∫_1^∞ ( ∫_1^x r(t) dt ) x^{-μ-1} dx  =  ∫_1^∞ r(t) t^{-μ} dt ,
```

which is the step that trades one factor of `x^{-1}` for an antiderivative in Andersson's iterated
Mellin representation.  The proof is Fubini on `{(x,t) : 1 < t ≤ x}`, not integration by parts, so
no differentiability of the antiderivative is needed — which matters because the first antiderivative
in the chain is a step function.
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

theorem integral_Ioi_cpow_tail {μ : ℂ} (hμ : 0 < μ.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi t, (x : ℂ) ^ (-μ - 1)) = (t : ℂ) ^ (-μ) / μ := by
  have hlt : (-μ - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [integral_Ioi_cpow_of_lt hlt ht]
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    simp at hμ
  have hexp : -μ - 1 + 1 = -μ := by ring
  rw [hexp]
  field_simp

/-- The kernel whose double integral realizes the Mellin step. -/
def mellinStepKernel (r : ℝ → ℂ) (μ : ℂ) (x t : ℝ) : ℂ :=
  Set.indicator (Set.Iic x) (fun t => r t * (x : ℂ) ^ (-μ - 1)) t

theorem norm_mellinStepKernel (r : ℝ → ℂ) (μ : ℂ) {x t : ℝ} (hx : 0 < x) :
    ‖mellinStepKernel r μ x t‖
      = Set.indicator (Set.Iic x) (fun t => ‖r t‖ * x ^ (-μ.re - 1)) t := by
  classical
  rw [mellinStepKernel]
  by_cases h : t ∈ Set.Iic x
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, norm_mul,
      norm_cpow_eq_rpow_re_of_pos hx]
    simp [Complex.sub_re, Complex.neg_re]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]

theorem integral_mellinStepKernel_snd {r : ℝ → ℂ} {μ : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1) := by
  classical
  have hsplit : (∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = ∫ t in Set.Ioi (1:ℝ) ∩ Set.Iic x, r t * (x : ℂ) ^ (-μ - 1) := by
    simp only [mellinStepKernel]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic]
  rw [hsplit]
  have hset : Set.Ioi (1:ℝ) ∩ Set.Iic x = Set.Ioc 1 x := by
    ext y
    simp [Set.mem_inter_iff, Set.mem_Ioc]
  rw [hset, intervalIntegral.integral_of_le hx, MeasureTheory.integral_mul_const]

theorem mellinStepKernel_eq_indicator_fst (r : ℝ → ℂ) (μ : ℂ) (t : ℝ) :
    (fun x : ℝ => mellinStepKernel r μ x t)
      = Set.indicator (Set.Ici t) (fun x : ℝ => r t * (x : ℂ) ^ (-μ - 1)) := by
  classical
  funext x
  rw [mellinStepKernel]
  by_cases h : t ≤ x
  · rw [Set.indicator_of_mem (by exact h : t ∈ Set.Iic x),
      Set.indicator_of_mem (by exact h : x ∈ Set.Ici t)]
  · rw [Set.indicator_of_notMem (by simpa using h : t ∉ Set.Iic x),
      Set.indicator_of_notMem (by simpa using h : x ∉ Set.Ici t)]

theorem integral_mellinStepKernel_fst {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 < μ.re) {t : ℝ} (ht : 1 < t) :
    (∫ x in Set.Ioi (1:ℝ), mellinStepKernel r μ x t) = r t * ((t : ℂ) ^ (-μ) / μ) := by
  classical
  rw [mellinStepKernel_eq_indicator_fst r μ t,
    MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioi (1:ℝ) ∩ Set.Ici t = Set.Ici t := by
    ext y
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_lt_of_le ht h, h⟩
  rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_const_mul,
    integral_Ioi_cpow_tail hμ (lt_trans one_pos ht)]

theorem norm_integral_mellinStepKernel_fst {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 < μ.re) {t : ℝ}
    (ht : 1 < t) :
    (∫ x in Set.Ioi (1:ℝ), ‖mellinStepKernel r μ x t‖)
      = ‖r t‖ * (t ^ (-μ.re) / μ.re) := by
  classical
  have hnorm : (fun x : ℝ => ‖mellinStepKernel r μ x t‖)
      = Set.indicator (Set.Ici t) (fun x : ℝ => ‖r t‖ * x ^ (-μ.re - 1)) := by
    funext x
    rw [congrFun (mellinStepKernel_eq_indicator_fst r μ t) x]
    by_cases h : t ≤ x
    · rw [Set.indicator_of_mem (by exact h : x ∈ Set.Ici t),
        Set.indicator_of_mem (by exact h : x ∈ Set.Ici t), norm_mul,
        norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le (lt_trans one_pos ht) h)]
      congr 1
    · rw [Set.indicator_of_notMem (by simpa using h : x ∉ Set.Ici t),
        Set.indicator_of_notMem (by simpa using h : x ∉ Set.Ici t), norm_zero]
  rw [hnorm, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioi (1:ℝ) ∩ Set.Ici t = Set.Ici t := by
    ext y
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_lt_of_le ht h, h⟩
  have htpos : (0:ℝ) < t := lt_trans one_pos ht
  have hlt : -μ.re - 1 < -1 := by linarith
  rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt hlt htpos]
  congr 1
  have hexp : -μ.re - 1 + 1 = -μ.re := by ring
  rw [hexp]
  field_simp

theorem continuousOn_ofReal_cpow (μ : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ μ) (Set.Ioi (1:ℝ)) := by
  intro t ht
  have htpos : (0:ℝ) < t := lt_trans one_pos ht
  exact (Complex.continuousAt_ofReal_cpow_const t μ (Or.inr (ne_of_gt htpos))).continuousWithinAt

/-- A Mellin-integrable datum is measurable on the half line. -/
theorem aestronglyMeasurable_of_mellin {r : ℝ → ℂ} {μ : ℂ}
    (hint : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioi (1:ℝ))) :
    AEStronglyMeasurable r (volume.restrict (Set.Ioi (1:ℝ))) := by
  have hc : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ μ) (volume.restrict (Set.Ioi (1:ℝ))) :=
    (continuousOn_ofReal_cpow μ).aestronglyMeasurable measurableSet_Ioi
  have hprod : AEStronglyMeasurable (fun t : ℝ => r t * (t : ℂ) ^ (-μ) * (t : ℂ) ^ μ)
      (volume.restrict (Set.Ioi (1:ℝ))) := hint.1.mul hc
  refine hprod.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have htpos : (0:ℝ) < t := lt_trans one_pos ht
  have hne : (t : ℂ) ≠ 0 := by
    simpa using ne_of_gt htpos
  rw [mul_assoc, ← Complex.cpow_add _ _ hne]
  simp

/-- A Mellin-integrable datum with nonnegative exponent is integrable on every bounded window. -/
theorem integrableOn_Ioc_of_mellin {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 ≤ μ.re)
    (hint : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioi (1:ℝ)))
    {x : ℝ} : IntegrableOn r (Set.Ioc 1 x) := by
  have hsub : Set.Ioc (1:ℝ) x ⊆ Set.Ioi (1:ℝ) := fun y hy => hy.1
  have hint' : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioc 1 x) :=
    hint.mono_set hsub
  have hmeas : AEStronglyMeasurable r (volume.restrict (Set.Ioc (1:ℝ) x)) :=
    (aestronglyMeasurable_of_mellin hint).mono_set hsub
  refine MeasureTheory.Integrable.mono' (hint'.norm.const_mul (x ^ μ.re)) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  have htpos : (0:ℝ) < t := lt_trans one_pos ht.1
  have hne : (t : ℂ) ≠ 0 := by simpa using ne_of_gt htpos
  have hsplit : r t = r t * (t : ℂ) ^ (-μ) * (t : ℂ) ^ μ := by
    rw [mul_assoc, ← Complex.cpow_add _ _ hne]
    simp
  conv_lhs => rw [hsplit]
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos, mul_comm (x ^ μ.re)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt htpos) ht.2 hμ) (norm_nonneg _)

theorem uncurry_mellinStepKernel_eq (r : ℝ → ℂ) (μ : ℂ) :
    Function.uncurry (mellinStepKernel r μ)
      = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => r p.2 * (p.1 : ℂ) ^ (-μ - 1)) := by
  classical
  funext p
  by_cases h : p.2 ≤ p.1
  · rw [Set.indicator_of_mem (by exact h : p ∈ {p : ℝ × ℝ | p.2 ≤ p.1})]
    show mellinStepKernel r μ p.1 p.2 = _
    rw [mellinStepKernel, Set.indicator_of_mem (by exact h : p.2 ∈ Set.Iic p.1)]
  · rw [Set.indicator_of_notMem (by simpa using h : p ∉ {p : ℝ × ℝ | p.2 ≤ p.1})]
    show mellinStepKernel r μ p.1 p.2 = _
    rw [mellinStepKernel, Set.indicator_of_notMem (by simpa using h : p.2 ∉ Set.Iic p.1)]

theorem aestronglyMeasurable_uncurry_mellinStepKernel {r : ℝ → ℂ} {μ : ℂ}
    (hAE : AEStronglyMeasurable r (volume.restrict (Set.Ioi (1:ℝ)))) :
    AEStronglyMeasurable (Function.uncurry (mellinStepKernel r μ))
      ((volume.restrict (Set.Ioi (1:ℝ))).prod (volume.restrict (Set.Ioi (1:ℝ)))) := by
  rw [uncurry_mellinStepKernel_eq]
  refine MeasureTheory.AEStronglyMeasurable.indicator ?_
    (measurableSet_le measurable_snd measurable_fst)
  have hc : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-μ - 1))
      (volume.restrict (Set.Ioi (1:ℝ))) :=
    (continuousOn_ofReal_cpow (-μ - 1)).aestronglyMeasurable measurableSet_Ioi
  exact (hAE.comp_snd).mul hc.comp_fst

theorem integrable_uncurry_mellinStepKernel {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 < μ.re)
    (hint : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioi (1:ℝ))) :
    Integrable (Function.uncurry (mellinStepKernel r μ))
      ((volume.restrict (Set.Ioi (1:ℝ))).prod (volume.restrict (Set.Ioi (1:ℝ)))) := by
  classical
  have hAE := aestronglyMeasurable_of_mellin hint
  rw [MeasureTheory.integrable_prod_iff' (aestronglyMeasurable_uncurry_mellinStepKernel hAE)]
  have hlt : (-μ - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : (0:ℝ) < t := lt_trans one_pos ht
    have hkey : IntegrableOn (fun x : ℝ => r t * (x : ℂ) ^ (-μ - 1)) (Set.Ici t) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact (integrableOn_Ioi_cpow_of_lt hlt htpos).const_mul (r t)
    have hind : Integrable
        (Set.indicator (Set.Ici t) (fun x : ℝ => r t * (x : ℂ) ^ (-μ - 1))) volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ici).2 hkey
    have : IntegrableOn
        (Set.indicator (Set.Ici t) (fun x : ℝ => r t * (x : ℂ) ^ (-μ - 1))) (Set.Ioi (1:ℝ)) :=
      hind.integrableOn
    have hfun : (fun x : ℝ => Function.uncurry (mellinStepKernel r μ) (x, t))
        = Set.indicator (Set.Ici t) (fun x : ℝ => r t * (x : ℂ) ^ (-μ - 1)) :=
      mellinStepKernel_eq_indicator_fst r μ t
    rw [hfun]
    exact this
  · have hcongr : (fun t : ℝ => ∫ x in Set.Ioi (1:ℝ),
        ‖Function.uncurry (mellinStepKernel r μ) (x, t)‖)
        =ᵐ[volume.restrict (Set.Ioi (1:ℝ))]
        fun t : ℝ => (μ.re)⁻¹ * ‖r t * (t : ℂ) ^ (-μ)‖ := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have htpos : (0:ℝ) < t := lt_trans one_pos ht
      have h1 : (∫ x in Set.Ioi (1:ℝ), ‖Function.uncurry (mellinStepKernel r μ) (x, t)‖)
          = ∫ x in Set.Ioi (1:ℝ), ‖mellinStepKernel r μ x t‖ := rfl
      rw [h1, norm_integral_mellinStepKernel_fst hμ ht, norm_mul,
        norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-μ).re = -μ.re := by simp
      rw [hre]
      field_simp
    refine MeasureTheory.Integrable.congr ?_ hcongr.symm
    exact hint.norm.const_mul _

/-- **The Mellin step.**  For `Re μ > 0` the Mellin transform at `μ + 1` of the antiderivative
`x ↦ ∫_1^x r` is `1/μ` times the Mellin transform of `r` at `μ`.  Proved by Fubini on the
half-plane region `1 < t ≤ x`, so no regularity of `r` beyond integrability is used. -/
theorem mellin_antiderivative_step {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 < μ.re)
    (hint : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioi (1:ℝ))) :
    μ * (∫ x in Set.Ioi (1:ℝ), (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1))
      = ∫ t in Set.Ioi (1:ℝ), r t * (t : ℂ) ^ (-μ) := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    simp at hμ
  have hswap := MeasureTheory.integral_integral_swap (integrable_uncurry_mellinStepKernel hμ hint)
  have hL : (∫ x in Set.Ioi (1:ℝ), ∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = ∫ x in Set.Ioi (1:ℝ), (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    exact integral_mellinStepKernel_snd (le_of_lt hx)
  have hR : (∫ t in Set.Ioi (1:ℝ), ∫ x in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = ∫ t in Set.Ioi (1:ℝ), μ⁻¹ * (r t * (t : ℂ) ^ (-μ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    show (∫ x in Set.Ioi (1:ℝ), mellinStepKernel r μ x t) = μ⁻¹ * (r t * (t : ℂ) ^ (-μ))
    rw [integral_mellinStepKernel_fst hμ ht]
    field_simp
  rw [← hL, hswap, hR, MeasureTheory.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]

/-- The Mellin integrand of the antiderivative is itself integrable. -/
theorem integrableOn_antideriv_mellin {r : ℝ → ℂ} {μ : ℂ} (hμ : 0 < μ.re)
    (hint : IntegrableOn (fun t => r t * (t : ℂ) ^ (-μ)) (Set.Ioi (1:ℝ))) :
    IntegrableOn (fun x : ℝ => (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1))
      (Set.Ioi (1:ℝ)) := by
  have h := (integrable_uncurry_mellinStepKernel hμ hint).integral_prod_left
  refine h.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  show (∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
    = (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1)
  exact integral_mellinStepKernel_snd (le_of_lt hx)

/-- **Iterated Mellin step.**  For a chain of antiderivatives `r (j+1) x = ∫_1^x r j`, the Mellin
transform of `r 0` at `s` is the rising factorial `s(s+1)⋯(s+j-1)` times the transform of `r j`
at `s + j`. -/
theorem mellin_iterated_step {r : ℕ → ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hrec : ∀ j : ℕ, ∀ x ∈ Set.Ioi (1:ℝ), r (j + 1) x = ∫ t in (1:ℝ)..x, r j t)
    (hint : ∀ j : ℕ, IntegrableOn (fun t => r j t * (t : ℂ) ^ (-(s + j))) (Set.Ioi (1:ℝ)))
    (j : ℕ) :
    (∫ x in Set.Ioi (1:ℝ), r 0 x * (x : ℂ) ^ (-s))
      = (∏ i ∈ Finset.range j, (s + i)) *
        ∫ x in Set.Ioi (1:ℝ), r j x * (x : ℂ) ^ (-(s + j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjre : 0 < (s + (j : ℂ)).re := by
      have : ((j : ℂ)).re = (j : ℝ) := by simp
      rw [Complex.add_re, this]
      have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hstep := mellin_antiderivative_step (r := r j) (μ := s + (j : ℂ)) hjre (hint j)
    have hcongr : (∫ x in Set.Ioi (1:ℝ), (∫ t in (1:ℝ)..x, r j t) * (x : ℂ) ^ (-(s + (j : ℂ)) - 1))
        = ∫ x in Set.Ioi (1:ℝ), r (j + 1) x * (x : ℂ) ^ (-(s + ((j + 1 : ℕ) : ℂ))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hexp : -(s + (j : ℂ)) - 1 = -(s + ((j + 1 : ℕ) : ℂ)) := by
        push_cast
        ring
      show (∫ t in (1:ℝ)..x, r j t) * (x : ℂ) ^ (-(s + (j : ℂ)) - 1)
        = r (j + 1) x * (x : ℂ) ^ (-(s + ((j + 1 : ℕ) : ℂ)))
      rw [hexp, hrec j x hx]
    rw [hcongr] at hstep
    rw [ih, ← hstep, Finset.prod_range_succ]
    ring

end GaloisForLFunctions.HTGeometry

end
