import GaloisForLFunctions.RHTower.HardyZSignChange
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareFourthMomentPolylog
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The fourth-moment sign-change detector

`hardy-critical-line-moment-anchor`, the assembly step.

The card's final architecture replaces the two-term chain `∫|Z| ≥ ∫Z²/sup|Z|` — which provably
cannot close — by the Hölder chain

```text
∫|Z| ≥ (∫Z²)^{3/2} / (∫Z⁴)^{1/2}.
```

Its algebraic content is the interpolation inequality

```text
(∫ f²)³ ≤ (∫ |f|)² · (∫ f⁴),
```

proved here from two applications of the Cauchy–Schwarz inequality for real integrals.  A function
with no sign change on `[α, β]` satisfies `∫|f| = |∫f|`, so a large second moment, a controlled
fourth moment and a small first moment are contradictory: the function must change sign.  With the
Hardy-Z/zeta zero interface this turns the three moment estimates of the card directly into an
actual critical-line zero.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The interpolation inequality -/

variable {μ : Measure ℝ}

theorem sq_integral_sq_le_integral_abs_mul_integral_abs_cube {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ)
    (h1 : Integrable (fun x => |f x|) μ)
    (h3 : Integrable (fun x => |f x| ^ 3) μ) :
    (∫ x, f x ^ 2 ∂μ) ^ 2 ≤ (∫ x, |f x| ∂μ) * ∫ x, |f x| ^ 3 ∂μ := by
  set g : ℝ → ℝ := fun x => Real.sqrt |f x| with hg
  set h : ℝ → ℝ := fun x => |f x| * Real.sqrt |f x| with hh
  have hfabs : AEStronglyMeasurable (fun x => |f x|) μ :=
    continuous_abs.comp_aestronglyMeasurable hfm
  have hgm : AEStronglyMeasurable g μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hfabs
  have hhm : AEStronglyMeasurable h μ :=
    hfabs.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hfabs)
  have hg2 : ∀ x, g x ^ 2 = |f x| := by
    intro x
    rw [hg]
    exact Real.sq_sqrt (abs_nonneg _)
  have hh2 : ∀ x, h x ^ 2 = |f x| ^ 3 := by
    intro x
    rw [hh, mul_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  have hgh : ∀ x, g x * h x = f x ^ 2 := by
    intro x
    show Real.sqrt |f x| * (|f x| * Real.sqrt |f x|) = f x ^ 2
    have hs : Real.sqrt |f x| * Real.sqrt |f x| = |f x| := Real.mul_self_sqrt (abs_nonneg _)
    calc Real.sqrt |f x| * (|f x| * Real.sqrt |f x|)
        = |f x| * (Real.sqrt |f x| * Real.sqrt |f x|) := by ring
      _ = |f x| * |f x| := by rw [hs]
      _ = f x ^ 2 := by rw [← sq_abs (f x)]; ring
  have hgi : Integrable (fun x => g x ^ 2) μ := by
    refine h1.congr ?_
    filter_upwards with x
    rw [hg2 x]
  have hhi : Integrable (fun x => h x ^ 2) μ := by
    refine h3.congr ?_
    filter_upwards with x
    rw [hh2 x]
  have hcs := sq_integral_mul_le (μ := μ) hgm hhm hgi hhi
  rw [integral_congr_ae (Filter.Eventually.of_forall hgh),
    integral_congr_ae (Filter.Eventually.of_forall hg2),
    integral_congr_ae (Filter.Eventually.of_forall hh2)] at hcs
  exact hcs

theorem sq_integral_abs_cube_le {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ)
    (h2 : Integrable (fun x => f x ^ 2) μ)
    (h4 : Integrable (fun x => f x ^ 4) μ) :
    (∫ x, |f x| ^ 3 ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, f x ^ 4 ∂μ := by
  set g : ℝ → ℝ := fun x => |f x| with hg
  set h : ℝ → ℝ := fun x => f x ^ 2 with hh
  have hgm : AEStronglyMeasurable g μ := continuous_abs.comp_aestronglyMeasurable hfm
  have hhm : AEStronglyMeasurable h μ := (continuous_pow 2).comp_aestronglyMeasurable hfm
  have hg2 : ∀ x, g x ^ 2 = f x ^ 2 := by
    intro x
    rw [hg, sq_abs]
  have hh2 : ∀ x, h x ^ 2 = f x ^ 4 := by
    intro x
    rw [hh, ← pow_mul]
  have hgh : ∀ x, g x * h x = |f x| ^ 3 := by
    intro x
    show |f x| * f x ^ 2 = |f x| ^ 3
    rw [← sq_abs (f x)]
    ring
  have hgi : Integrable (fun x => g x ^ 2) μ := by
    refine h2.congr ?_
    filter_upwards with x
    rw [hg2 x]
  have hhi : Integrable (fun x => h x ^ 2) μ := by
    refine h4.congr ?_
    filter_upwards with x
    rw [hh2 x]
  have hcs := sq_integral_mul_le (μ := μ) hgm hhm hgi hhi
  rw [integral_congr_ae (Filter.Eventually.of_forall hgh),
    integral_congr_ae (Filter.Eventually.of_forall hg2),
    integral_congr_ae (Filter.Eventually.of_forall hh2)] at hcs
  exact hcs

/-- **The interpolation inequality `(∫f²)³ ≤ (∫|f|)²(∫f⁴)`.** -/
theorem cube_integral_sq_le {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ)
    (h1 : Integrable (fun x => |f x|) μ)
    (h2 : Integrable (fun x => f x ^ 2) μ)
    (h3 : Integrable (fun x => |f x| ^ 3) μ)
    (h4 : Integrable (fun x => f x ^ 4) μ) :
    (∫ x, f x ^ 2 ∂μ) ^ 3 ≤ (∫ x, |f x| ∂μ) ^ 2 * ∫ x, f x ^ 4 ∂μ := by
  set A : ℝ := ∫ x, |f x| ∂μ with hA
  set B : ℝ := ∫ x, f x ^ 2 ∂μ with hB
  set C : ℝ := ∫ x, |f x| ^ 3 ∂μ with hC
  set D : ℝ := ∫ x, f x ^ 4 ∂μ with hD
  have hAnn : 0 ≤ A := integral_nonneg fun x => abs_nonneg _
  have hBnn : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hCnn : 0 ≤ C := integral_nonneg fun x => by positivity
  have hDnn : 0 ≤ D := integral_nonneg fun x => by positivity
  have hstep1 : B ^ 2 ≤ A * C := sq_integral_sq_le_integral_abs_mul_integral_abs_cube hfm h1 h3
  have hstep2 : C ^ 2 ≤ B * D := sq_integral_abs_cube_le hfm h2 h4
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · rw [← hB0]
    have hz : (0:ℝ) ^ 3 = 0 := by norm_num
    rw [hz]
    positivity
  · have hsq : B ^ 4 ≤ A ^ 2 * (B * D) := by
      calc B ^ 4 = (B ^ 2) ^ 2 := by ring
        _ ≤ (A * C) ^ 2 := by
            refine pow_le_pow_left₀ (by positivity) hstep1 2
        _ = A ^ 2 * C ^ 2 := by ring
        _ ≤ A ^ 2 * (B * D) := by
            exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
    have hfinal : B ^ 3 * B ≤ (A ^ 2 * D) * B := by
      calc B ^ 3 * B = B ^ 4 := by ring
        _ ≤ A ^ 2 * (B * D) := hsq
        _ = (A ^ 2 * D) * B := by ring
    exact le_of_mul_le_mul_right hfinal hBpos

/-! ## The sign-change detector -/

theorem integrableOn_Ioc_of_continuousOn_Icc {g : ℝ → ℝ} {α β : ℝ}
    (hg : ContinuousOn g (Set.Icc α β)) : IntegrableOn g (Set.Ioc α β) := by
  exact (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **The fourth-moment sign-change detector.**  A continuous function whose second moment is at
least `S`, whose fourth moment is at most `F`, and whose first moment satisfies
`(∫f)² · F < S³`, must change sign on the interval. -/
theorem exists_sign_bracket_of_fourth_moment_gap {f : ℝ → ℝ} {α β S F : ℝ}
    (hαβ : α ≤ β) (hcont : ContinuousOn f (Set.Icc α β)) (hS : 0 < S)
    (h2 : S ≤ ∫ u in α..β, (f u) ^ 2)
    (h4 : (∫ u in α..β, (f u) ^ 4) ≤ F)
    (hgap : (∫ u in α..β, f u) ^ 2 * F < S ^ 3) :
    ∃ t₁ ∈ Set.Icc α β, ∃ t₂ ∈ Set.Icc α β, t₁ ≤ t₂ ∧ f t₁ * f t₂ ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  -- every pair of values has a strictly positive product, hence a common strict sign
  have hpair : ∀ t₁ ∈ Set.Icc α β, ∀ t₂ ∈ Set.Icc α β, 0 < f t₁ * f t₂ := by
    intro t₁ ht₁ t₂ ht₂
    rcases le_total t₁ t₂ with h | h
    · exact hcon t₁ ht₁ t₂ ht₂ h
    · have := hcon t₂ ht₂ t₁ ht₁ h
      linarith [this, mul_comm (f t₁) (f t₂)]
  have hαmem : α ∈ Set.Icc α β := ⟨le_rfl, hαβ⟩
  have hsame : (∀ t ∈ Set.Icc α β, 0 < f t) ∨ (∀ t ∈ Set.Icc α β, f t < 0) := by
    have hα := hpair α hαmem α hαmem
    rcases lt_trichotomy (f α) 0 with hneg | hzero | hpos
    · right
      intro t ht
      have := hpair α hαmem t ht
      nlinarith [this, hneg]
    · exact absurd hα (by rw [hzero]; simp)
    · left
      intro t ht
      have := hpair α hαmem t ht
      nlinarith [this, hpos]
  -- integrability on the interval
  have hcabs : ContinuousOn (fun u => |f u|) (Set.Icc α β) := hcont.abs
  have hc2 : ContinuousOn (fun u => f u ^ 2) (Set.Icc α β) := hcont.pow 2
  have hc3 : ContinuousOn (fun u => |f u| ^ 3) (Set.Icc α β) := hcabs.pow 3
  have hc4 : ContinuousOn (fun u => f u ^ 4) (Set.Icc α β) := hcont.pow 4
  have hi1 : IntegrableOn (fun u => |f u|) (Set.Ioc α β) :=
    integrableOn_Ioc_of_continuousOn_Icc hcabs
  have hi2 : IntegrableOn (fun u => f u ^ 2) (Set.Ioc α β) :=
    integrableOn_Ioc_of_continuousOn_Icc hc2
  have hi3 : IntegrableOn (fun u => |f u| ^ 3) (Set.Ioc α β) :=
    integrableOn_Ioc_of_continuousOn_Icc hc3
  have hi4 : IntegrableOn (fun u => f u ^ 4) (Set.Ioc α β) :=
    integrableOn_Ioc_of_continuousOn_Icc hc4
  have hfm : AEStronglyMeasurable f (Measure.restrict volume (Set.Ioc α β)) :=
    (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  -- the interpolation inequality on the interval
  have hinterp := cube_integral_sq_le (μ := Measure.restrict volume (Set.Ioc α β))
    hfm hi1 hi2 hi3 hi4
  -- the first moment equals the absolute first moment
  have habs : ∫ u in Set.Ioc α β, |f u| = |∫ u in Set.Ioc α β, f u| := by
    rcases hsame with hpos | hneg
    · have hcongr : ∫ u in Set.Ioc α β, |f u| = ∫ u in Set.Ioc α β, f u := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        exact abs_of_pos (hpos u (Set.Ioc_subset_Icc_self hu))
      rw [hcongr, abs_of_nonneg]
      refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
      exact le_of_lt (hpos u (Set.Ioc_subset_Icc_self hu))
    · have hcongr : ∫ u in Set.Ioc α β, |f u| = ∫ u in Set.Ioc α β, (-f u) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        exact abs_of_neg (hneg u (Set.Ioc_subset_Icc_self hu))
      have hnegint : ∫ u in Set.Ioc α β, (-f u) = -∫ u in Set.Ioc α β, f u := by
        simpa using integral_neg (μ := Measure.restrict volume (Set.Ioc α β)) f
      rw [hcongr, hnegint, abs_of_nonpos]
      refine setIntegral_nonpos measurableSet_Ioc fun u hu => ?_
      exact le_of_lt (hneg u (Set.Ioc_subset_Icc_self hu))
  -- convert the interval integrals
  rw [intervalIntegral.integral_of_le hαβ] at h2 h4 hgap
  rw [habs] at hinterp
  have hS3 : S ^ 3 ≤ (∫ u in Set.Ioc α β, f u ^ 2) ^ 3 :=
    pow_le_pow_left₀ (le_of_lt hS) h2 3
  have hFnn : 0 ≤ (∫ u in Set.Ioc α β, f u ^ 4) :=
    setIntegral_nonneg measurableSet_Ioc fun u _ => by positivity
  have hsq : (0:ℝ) ≤ |∫ u in Set.Ioc α β, f u| ^ 2 := by positivity
  have hchain : S ^ 3 ≤ (∫ u in Set.Ioc α β, f u) ^ 2 * F := by
    calc S ^ 3 ≤ (∫ u in Set.Ioc α β, f u ^ 2) ^ 3 := hS3
      _ ≤ |∫ u in Set.Ioc α β, f u| ^ 2 * ∫ u in Set.Ioc α β, f u ^ 4 := hinterp
      _ = (∫ u in Set.Ioc α β, f u) ^ 2 * ∫ u in Set.Ioc α β, f u ^ 4 := by
          rw [sq_abs]
      _ ≤ (∫ u in Set.Ioc α β, f u) ^ 2 * F := by
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
  linarith [hchain, hgap]

/-- **The card's assembly step.**  The three moment estimates of the Hardy lane — a second-moment
lower bound, a fourth-moment upper bound and a first-moment gap — produce an actual zero of
`ζ` on the critical line inside the window. -/
theorem exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap {α β S F : ℝ}
    (hαβ : α ≤ β) (hS : 0 < S)
    (h2 : S ≤ ∫ u in α..β, (hardyZ u) ^ 2)
    (h4 : (∫ u in α..β, (hardyZ u) ^ 4) ≤ F)
    (hgap : (∫ u in α..β, hardyZ u) ^ 2 * F < S ^ 3) :
    ∃ τ ∈ Set.Icc α β, riemannZeta (linePt τ) = 0 := by
  obtain ⟨t₁, ht₁, t₂, ht₂, h12, hsign⟩ :=
    exists_sign_bracket_of_fourth_moment_gap hαβ continuous_hardyZ.continuousOn hS h2 h4 hgap
  obtain ⟨τ, hτ, hz⟩ := exists_riemannZeta_line_zero_of_hardyZ_sign_bracket h12 hsign
  exact ⟨τ, ⟨le_trans ht₁.1 hτ.1, le_trans hτ.2 ht₂.2⟩, hz⟩

/-! ## Lemma F in the form the detector consumes -/

theorem hardyZ_pow_four_eq_norm_pow_four (τ : ℝ) :
    (hardyZ τ) ^ 4 = ‖riemannZeta (linePt τ)‖ ^ 4 := by
  have h : ‖riemannZeta (linePt τ)‖ = |hardyZ τ| := norm_riemannZeta_line_eq_abs_hardyZ τ
  rw [h]
  calc (hardyZ τ) ^ 4 = ((hardyZ τ) ^ 2) ^ 2 := by ring
    _ = (|hardyZ τ| ^ 2) ^ 2 := by rw [sq_abs]
    _ = |hardyZ τ| ^ 4 := by ring

/-- **Lemma F.**  The dyadic fourth moment of Hardy's `Z` is `O(T log⁴ T)`, unconditionally. -/
theorem exists_integral_hardyZ_pow_four_dyadic_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in (N : ℝ)..(2 * N : ℝ), (hardyZ t) ^ 4)
        ≤ C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNle : (N : ℝ) ≤ 2 * (N : ℝ) := by
    have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hb := hbound hN
  have heq : (∫ t in (N : ℝ)..(2 * N : ℝ), (hardyZ t) ^ 4)
      = ∫ t in Set.Icc (N : ℝ) (2 * N : ℝ), ‖riemannZeta (linePt t)‖ ^ 4 := by
    rw [intervalIntegral.integral_of_le hNle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => hardyZ_pow_four_eq_norm_pow_four t
  rw [heq]
  exact hb

end RHTower
