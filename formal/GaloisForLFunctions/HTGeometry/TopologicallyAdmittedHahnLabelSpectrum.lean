import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel
import GaloisForLFunctions.HTGeometry.MutuallySingularTotalVariation
import GaloisForLFunctions.HTGeometry.HellingerAffinityProduct

/-!
# Hahn-label approximation spectrum, observer deficit and tensor convergence

For probability measures `μ₀, μ₁` on a measurable space, with `λ = μ₀ + μ₁`, `ν = μ₁ - μ₀`,
`h = dν/dλ` and the Hahn label `σ = sign h`, the corpus proves
`TV - ½∫ g h dλ = ½ ∫ |g - σ| |h| dλ` for measurable soft labels `g ∈ [-1, 1]`.  This module
completes the law.

* `∫ g h dλ = ∫ g dμ₁ - ∫ g dμ₀`, so for an effect `e ∈ [0, 1]` the deficit
  `TV - ∫ e dν` is half the label distance of `2e - 1`; `TV = sup_A (μ₁ A - μ₀ A)`, attained at
  `{h ≥ 0}`.
* For mutually singular laws `|h| = 1` almost everywhere and `TV = 1`.
* Dictionaries: the best contrast of a dictionary is `TV` minus half its label width; compact
  dictionaries of continuous effects have positive width when both singular laws have full
  support; the resolution price is half the approximation spectrum at `2(TV - r)`.
* Tensor formation: an exact formation of `p₀^{⊗d}, p₁^{⊗d}` and a Neyman–Pearson event produce
  an effect whose label distance is exactly `2(1 - TV(p₀^{⊗d}, p₁^{⊗d})) ≤ 2A^d`, with `A` the
  Hellinger affinity.
* Observers: the best label distance of `f ∘ π` is `2(TV - TV(π_*μ₀, π_*μ₁))`, the deficits of
  composed observers add, and measurable relabellings preserve every label distance.
-/

open MeasureTheory Set Filter
open scoped ENNReal Pointwise

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [MeasurableSpace X]

/-! ## The density identity -/

theorem measurableHahnDensity_ae_eq (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableHahnDensity P Q =ᵐ[currentControl P Q]
      fun x => (Q.rnDeriv (currentControl P Q) x).toReal
        - (P.rnDeriv (currentControl P Q) x).toReal := by
  letI : IsFiniteMeasure (currentControl P Q) := by unfold currentControl; infer_instance
  have hPac : P ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_right le_rfl)
  have hQac : Q ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_left le_rfl)
  have hQint : Integrable (fun x => (Q.rnDeriv (currentControl P Q) x).toReal)
      (currentControl P Q) := Measure.integrable_toReal_rnDeriv
  have hPint : Integrable (fun x => (P.rnDeriv (currentControl P Q) x).toReal)
      (currentControl P Q) := Measure.integrable_toReal_rnDeriv
  have hQ : (currentControl P Q).withDensityᵥ (fun x => (Q.rnDeriv (currentControl P Q) x).toReal)
      = Q.toSignedMeasure := by
    rw [withDensityᵥ_toReal (Measure.measurable_rnDeriv _ _).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top _ _).ne]
    simp only [Measure.withDensity_rnDeriv_eq _ _ hQac]
  have hP : (currentControl P Q).withDensityᵥ (fun x => (P.rnDeriv (currentControl P Q) x).toReal)
      = P.toSignedMeasure := by
    rw [withDensityᵥ_toReal (Measure.measurable_rnDeriv _ _).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top _ _).ne]
    simp only [Measure.withDensity_rnDeriv_eq _ _ hPac]
  have hsub := withDensityᵥ_sub hQint hPint
  rw [hQ, hP] at hsub
  refine (Integrable.withDensityᵥ_eq_iff (integrable_measurableHahnDensity P Q)
    (hQint.sub hPint)).mp ?_
  rw [currentControl_withDensity_measurableHahnDensity, hsub]
  rfl

/-- `∫ g h dλ = ∫ g dμ₁ - ∫ g dμ₀` for bounded measurable `g`. -/
theorem integral_mul_measurableHahnDensity (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    ∫ x, g x * measurableHahnDensity P Q x ∂(currentControl P Q) = ∫ x, g x ∂Q - ∫ x, g x ∂P := by
  letI : IsFiniteMeasure (currentControl P Q) := by unfold currentControl; infer_instance
  have hPac : P ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_right le_rfl)
  have hQac : Q ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_left le_rfl)
  have hgP : Integrable g P := integrable_of_bound hg hgb
  have hgQ : Integrable g Q := integrable_of_bound hg hgb
  have hQ := integral_rnDeriv_smul (f := g) hQac
  have hP := integral_rnDeriv_smul (f := g) hPac
  have hQi : Integrable (fun x => (Q.rnDeriv (currentControl P Q) x).toReal • g x)
      (currentControl P Q) := (integrable_rnDeriv_smul_iff hQac).mpr hgQ
  have hPi : Integrable (fun x => (P.rnDeriv (currentControl P Q) x).toReal • g x)
      (currentControl P Q) := (integrable_rnDeriv_smul_iff hPac).mpr hgP
  rw [← hQ, ← hP, ← integral_sub hQi hPi]
  refine integral_congr_ae ?_
  filter_upwards [measurableHahnDensity_ae_eq P Q] with x hx
  rw [hx, smul_eq_mul, smul_eq_mul]
  ring

/-! ## Effects and the label distance -/

/-- The contrast `∫ e dμ₁ - ∫ e dμ₀` carried by an effect. -/
def hahnEffectCurrent (P Q : Measure X) (e : X → ℝ) : ℝ := ∫ x, e x ∂Q - ∫ x, e x ∂P

/-- The weighted `L¹` distance `∫ |g - σ| d|ν|` of a soft label to the Hahn label. -/
def hahnLabelDistance (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : X → ℝ) : ℝ :=
  ∫ x, |g x - measurableHahnLabel P Q x| * |measurableHahnDensity P Q x| ∂(currentControl P Q)

theorem hahnLabelDistance_nonneg (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : X → ℝ) : 0 ≤ hahnLabelDistance P Q g :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- **(HLA.6), soft-label form.**  `TV - ½(∫ g dμ₁ - ∫ g dμ₀) = ½ ∫ |g - σ| d|ν|`. -/
theorem measurableHahnTV_sub_half_current (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {g : X → ℝ} (hg : Measurable g) (hgb : ∀ x, g x ∈ Icc (-1 : ℝ) 1) :
    measurableHahnTV P Q - (1 / 2 : ℝ) * hahnEffectCurrent P Q g
      = (1 / 2 : ℝ) * hahnLabelDistance P Q g := by
  have h := measurableHahnTV_sub_decisionCurrent_eq_labelError P Q (fun x => ⟨g x, hgb x⟩) hg
  have hcur : measurableDecisionCurrent P Q (fun x => ⟨g x, hgb x⟩)
      = (1 / 2 : ℝ) * hahnEffectCurrent P Q g := by
    rw [measurableDecisionCurrent, hahnEffectCurrent]
    congr 1
    exact integral_mul_measurableHahnDensity P Q hg (C := 1) fun x => abs_le.mpr (hgb x)
  rw [hcur] at h
  rw [h]
  rfl

/-- **Theorem 3.1 (HLA.6).**  For an effect `e ∈ [0, 1]`,
`TV - ∫ e d(μ₁ - μ₀) = ½ ∫ |2e - 1 - σ| d|ν|`. -/
theorem measurableHahnTV_sub_effectCurrent (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {e : X → ℝ} (he : Measurable e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    measurableHahnTV P Q - hahnEffectCurrent P Q e
      = (1 / 2 : ℝ) * hahnLabelDistance P Q (fun x => 2 * e x - 1) := by
  have hg : Measurable fun x => 2 * e x - 1 := (he.const_mul 2).sub_const 1
  have hgb : ∀ x, 2 * e x - 1 ∈ Icc (-1 : ℝ) 1 := fun x => by
    obtain ⟨h0, h1⟩ := heb x
    constructor <;> linarith
  have h := measurableHahnTV_sub_half_current P Q hg hgb
  have hcur : hahnEffectCurrent P Q (fun x => 2 * e x - 1) = 2 * hahnEffectCurrent P Q e := by
    have heP : Integrable e P := integrable_of_bound he (C := 1) fun x =>
      abs_le.mpr ⟨by linarith [(heb x).1], (heb x).2⟩
    have heQ : Integrable e Q := integrable_of_bound he (C := 1) fun x =>
      abs_le.mpr ⟨by linarith [(heb x).1], (heb x).2⟩
    rw [hahnEffectCurrent, hahnEffectCurrent, integral_sub (heQ.const_mul 2) (integrable_const 1),
      integral_sub (heP.const_mul 2) (integrable_const 1), integral_const_mul, integral_const_mul]
    simp
    ring
  rw [hcur] at h
  linarith

/-- The effect current of any effect is at most `TV`. -/
theorem hahnEffectCurrent_le_measurableHahnTV (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {e : X → ℝ} (he : Measurable e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    hahnEffectCurrent P Q e ≤ measurableHahnTV P Q := by
  have h := measurableHahnTV_sub_effectCurrent P Q he heb
  have := hahnLabelDistance_nonneg P Q (fun x => 2 * e x - 1)
  linarith

/-- The positive Hahn set `{h ≥ 0}`. -/
def hahnPositiveSet (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] : Set X :=
  {x | 0 ≤ measurableHahnDensity P Q x}

theorem measurableSet_hahnPositiveSet (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    MeasurableSet (hahnPositiveSet P Q) :=
  measurableSet_le measurable_const (measurable_measurableHahnDensity P Q)

theorem indicator_hahnPositiveSet_label (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (x : X) : 2 * (hahnPositiveSet P Q).indicator (fun _ => (1 : ℝ)) x - 1
      = measurableHahnLabel P Q x := by
  by_cases hx : 0 ≤ measurableHahnDensity P Q x
  · rw [indicator_of_mem (show x ∈ hahnPositiveSet P Q from hx), measurableHahnLabel,
      hahnSign_of_nonneg hx]
    norm_num
  · rw [indicator_of_notMem (show x ∉ hahnPositiveSet P Q from hx), measurableHahnLabel,
      hahnSign_of_neg (lt_of_not_ge hx)]
    norm_num

/-- The Neyman–Pearson event `{h ≥ 0}` attains the total variation. -/
theorem hahnEffectCurrent_hahnPositiveSet (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    hahnEffectCurrent P Q ((hahnPositiveSet P Q).indicator fun _ => (1 : ℝ))
      = measurableHahnTV P Q := by
  have hmeas : Measurable ((hahnPositiveSet P Q).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator (measurableSet_hahnPositiveSet P Q)
  have hb : ∀ x, (hahnPositiveSet P Q).indicator (fun _ => (1 : ℝ)) x ∈ Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ hahnPositiveSet P Q
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  have h := measurableHahnTV_sub_effectCurrent P Q hmeas hb
  have hzero : hahnLabelDistance P Q
      (fun x => 2 * (hahnPositiveSet P Q).indicator (fun _ => (1 : ℝ)) x - 1) = 0 := by
    rw [hahnLabelDistance]
    simp [indicator_hahnPositiveSet_label]
  rw [hzero, mul_zero, sub_eq_zero] at h
  exact h.symm

/-- **(HLA.5).**  `TV(μ₀, μ₁) = sup_A (μ₁ A - μ₀ A)`, attained at `{h ≥ 0}`. -/
theorem isGreatest_measurableHahnTV (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    IsGreatest {r | ∃ A, MeasurableSet A ∧ r = Q.real A - P.real A} (measurableHahnTV P Q) := by
  have hind : ∀ A : Set X, MeasurableSet A →
      hahnEffectCurrent P Q (A.indicator fun _ => (1 : ℝ)) = Q.real A - P.real A := by
    intro A hA
    rw [hahnEffectCurrent, integral_indicator_const (1 : ℝ) hA,
      integral_indicator_const (1 : ℝ) hA, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  refine ⟨⟨hahnPositiveSet P Q, measurableSet_hahnPositiveSet P Q, ?_⟩, ?_⟩
  · rw [← hind _ (measurableSet_hahnPositiveSet P Q), hahnEffectCurrent_hahnPositiveSet]
  · rintro r ⟨A, hA, rfl⟩
    rw [← hind A hA]
    refine hahnEffectCurrent_le_measurableHahnTV P Q (measurable_const.indicator hA) fun x => ?_
    by_cases hx : x ∈ A
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]

/-- `|h| ≤ 1` almost everywhere. -/
theorem ae_abs_measurableHahnDensity_le_one (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(currentControl P Q), |measurableHahnDensity P Q x| ≤ 1 := by
  letI : IsFiniteMeasure (currentControl P Q) := by unfold currentControl; infer_instance
  have hsum : (P + Q).rnDeriv (currentControl P Q) =ᵐ[currentControl P Q]
      P.rnDeriv (currentControl P Q) + Q.rnDeriv (currentControl P Q) :=
    Measure.rnDeriv_add P Q (currentControl P Q)
  have hself : (currentControl P Q).rnDeriv (currentControl P Q) =ᵐ[currentControl P Q]
      fun _ => 1 := Measure.rnDeriv_self _
  filter_upwards [measurableHahnDensity_ae_eq P Q, hsum, hself,
    Measure.rnDeriv_lt_top P (currentControl P Q), Measure.rnDeriv_lt_top Q (currentControl P Q)]
    with x hx hs h1 hPt hQt
  rw [hx]
  have hs' : (currentControl P Q).rnDeriv (currentControl P Q) x
      = P.rnDeriv (currentControl P Q) x + Q.rnDeriv (currentControl P Q) x := hs
  rw [h1] at hs'
  have h := congrArg ENNReal.toReal hs'
  rw [ENNReal.toReal_add hPt.ne hQt.ne, ENNReal.toReal_one] at h
  have hP0 : 0 ≤ (P.rnDeriv (currentControl P Q) x).toReal := ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ (Q.rnDeriv (currentControl P Q) x).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-! ## Mutually singular sources -/

theorem ae_rnDeriv_eq_zero_of_null {μ lam : Measure X} [IsFiniteMeasure μ] [SigmaFinite lam]
    (hac : μ ≪ lam) {s : Set X} (hs : MeasurableSet s) (hμs : μ s = 0) :
    ∀ᵐ x ∂lam, x ∈ s → μ.rnDeriv lam x = 0 := by
  have h : ∫⁻ x in s, μ.rnDeriv lam x ∂lam = 0 := by
    rw [Measure.setLIntegral_rnDeriv hac, hμs]
  rw [lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _)] at h
  exact (ae_restrict_iff' hs).mp h

/-- For mutually singular laws, `h = 1` on the null set of `μ₀` and `h = -1` off it. -/
theorem ae_measurableHahnDensity_of_singular {P Q : Measure X} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPQ : P ⟂ₘ Q) :
    ∀ᵐ x ∂(currentControl P Q), (x ∈ hPQ.nullSet → measurableHahnDensity P Q x = 1) ∧
      (x ∉ hPQ.nullSet → measurableHahnDensity P Q x = -1) := by
  letI : IsFiniteMeasure (currentControl P Q) := by unfold currentControl; infer_instance
  have hPac : P ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_right le_rfl)
  have hQac : Q ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_left le_rfl)
  have hs := hPQ.measurableSet_nullSet
  have hP0 := ae_rnDeriv_eq_zero_of_null hPac hs hPQ.measure_nullSet
  have hQ0 := ae_rnDeriv_eq_zero_of_null hQac hs.compl hPQ.measure_compl_nullSet
  have hsum : (P + Q).rnDeriv (currentControl P Q) =ᵐ[currentControl P Q]
      P.rnDeriv (currentControl P Q) + Q.rnDeriv (currentControl P Q) :=
    Measure.rnDeriv_add P Q (currentControl P Q)
  have hself : (currentControl P Q).rnDeriv (currentControl P Q) =ᵐ[currentControl P Q]
      fun _ => 1 := Measure.rnDeriv_self _
  filter_upwards [measurableHahnDensity_ae_eq P Q, hsum, hself, hP0, hQ0,
    Measure.rnDeriv_lt_top P (currentControl P Q), Measure.rnDeriv_lt_top Q (currentControl P Q)]
    with x hx hs' h1 hPx hQx hPt hQt
  have hs'' : (currentControl P Q).rnDeriv (currentControl P Q) x
      = P.rnDeriv (currentControl P Q) x + Q.rnDeriv (currentControl P Q) x := hs'
  rw [h1] at hs''
  have h := congrArg ENNReal.toReal hs''
  rw [ENNReal.toReal_add hPt.ne hQt.ne, ENNReal.toReal_one] at h
  refine ⟨fun hxs => ?_, fun hxs => ?_⟩
  · rw [hx, hPx hxs, ENNReal.toReal_zero] at *
    linarith
  · rw [hx, hQx hxs, ENNReal.toReal_zero] at *
    linarith

theorem ae_abs_measurableHahnDensity_eq_one {P Q : Measure X} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPQ : P ⟂ₘ Q) :
    ∀ᵐ x ∂(currentControl P Q), |measurableHahnDensity P Q x| = 1 := by
  filter_upwards [ae_measurableHahnDensity_of_singular hPQ] with x hx
  by_cases hxs : x ∈ hPQ.nullSet
  · rw [hx.1 hxs, abs_one]
  · rw [hx.2 hxs, abs_neg, abs_one]

/-- `TV(μ₀, μ₁) = 1` for mutually singular probability laws. -/
theorem measurableHahnTV_eq_one_of_singular {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) : measurableHahnTV P Q = 1 := by
  rw [measurableHahnTV, integral_congr_ae (ae_abs_measurableHahnDensity_eq_one hPQ),
    integral_const, currentControl, smul_eq_mul, mul_one, measureReal_def, Measure.add_apply,
    measure_univ, measure_univ]
  norm_num

/-- For singular laws the label distance is the plain `L¹(μ₀ + μ₁)` distance. -/
theorem hahnLabelDistance_eq_of_singular {P Q : Measure X} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ⟂ₘ Q) (g : X → ℝ) :
    hahnLabelDistance P Q g = ∫ x, |g x - measurableHahnLabel P Q x| ∂(P + Q) := by
  rw [hahnLabelDistance]
  refine integral_congr_ae ?_
  filter_upwards [ae_abs_measurableHahnDensity_eq_one hPQ] with x hx
  rw [hx, mul_one]

/-- **Corollary 3.2 (HLA.7).**  For singular laws,
`1 - ∫ e d(μ₁ - μ₀) = ½ ‖2e - 1 - σ‖_{L¹(μ₀ + μ₁)}`. -/
theorem one_sub_hahnEffectCurrent_of_singular {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) {e : X → ℝ} (he : Measurable e)
    (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    1 - hahnEffectCurrent P Q e
      = (1 / 2 : ℝ) * ∫ x, |2 * e x - 1 - measurableHahnLabel P Q x| ∂(P + Q) := by
  have h := measurableHahnTV_sub_effectCurrent P Q he heb
  rw [measurableHahnTV_eq_one_of_singular hPQ, hahnLabelDistance_eq_of_singular hPQ] at h
  exact h

/-- For singular laws the Hahn label is `1` almost surely under `μ₁`. -/
theorem ae_measurableHahnLabel_eq_one {P Q : Measure X} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ⟂ₘ Q) : ∀ᵐ x ∂Q, measurableHahnLabel P Q x = 1 := by
  have hQac : Q ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_left le_rfl)
  have hin : ∀ᵐ x ∂Q, x ∈ hPQ.nullSet := by
    rw [ae_iff]
    exact hPQ.measure_compl_nullSet
  filter_upwards [hQac.ae_le (ae_measurableHahnDensity_of_singular hPQ), hin] with x hx hxs
  rw [measurableHahnLabel, hx.1 hxs, hahnSign_of_nonneg zero_le_one]

/-- For singular laws the Hahn label is `-1` almost surely under `μ₀`. -/
theorem ae_measurableHahnLabel_eq_neg_one {P Q : Measure X} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPQ : P ⟂ₘ Q) : ∀ᵐ x ∂P, measurableHahnLabel P Q x = -1 := by
  have hPac : P ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_right le_rfl)
  have hout : ∀ᵐ x ∂P, x ∉ hPQ.nullSet := by
    rw [ae_iff]
    simp
  filter_upwards [hPac.ae_le (ae_measurableHahnDensity_of_singular hPQ), hout] with x hx hxs
  rw [measurableHahnLabel, hx.2 hxs, hahnSign_of_neg (by norm_num)]

/-! ## Dictionaries -/

/-- **Theorem 4.1 (HLA.9).**  The best contrast of a nonempty dictionary of effects is `TV` minus
half its Hahn-label width. -/
theorem iSup_hahnEffectCurrent_eq (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {E : Set (X → ℝ)} (hE : E.Nonempty)
    (hmeas : ∀ e ∈ E, Measurable e) (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    ⨆ e : E, hahnEffectCurrent P Q e
      = measurableHahnTV P Q - (1 / 2 : ℝ) * ⨅ e : E, hahnLabelDistance P Q
          (fun x => 2 * (e : X → ℝ) x - 1) := by
  haveI : Nonempty E := hE.to_subtype
  have hid : ∀ e : E, hahnEffectCurrent P Q e = measurableHahnTV P Q
      - (1 / 2 : ℝ) * hahnLabelDistance P Q (fun x => 2 * (e : X → ℝ) x - 1) := fun e => by
    have := measurableHahnTV_sub_effectCurrent P Q (hmeas e e.2) (hb e e.2)
    linarith
  have hbdd : BddBelow (Set.range fun e : E => hahnLabelDistance P Q
      (fun x => 2 * (e : X → ℝ) x - 1)) :=
    ⟨0, by rintro _ ⟨e, rfl⟩; exact hahnLabelDistance_nonneg P Q _⟩
  have hbddA : BddAbove (Set.range fun e : E => hahnEffectCurrent P Q e) :=
    ⟨measurableHahnTV P Q, by
      rintro _ ⟨e, rfl⟩
      exact hahnEffectCurrent_le_measurableHahnTV P Q (hmeas e e.2) (hb e e.2)⟩
  apply le_antisymm
  · refine ciSup_le fun e => ?_
    rw [hid e]
    have := ciInf_le hbdd e
    linarith
  · have h : 2 * (measurableHahnTV P Q - ⨆ e : E, hahnEffectCurrent P Q e)
        ≤ ⨅ e : E, hahnLabelDistance P Q (fun x => 2 * (e : X → ℝ) x - 1) := by
      refine le_ciInf fun e => ?_
      have := le_ciSup hbddA e
      rw [hid e] at this
      linarith
    linarith

theorem integrable_hahnLabelWeight (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    Integrable (fun x => |g x - measurableHahnLabel P Q x| * |measurableHahnDensity P Q x|)
      (currentControl P Q) := by
  refine ((integrable_abs_measurableHahnDensity P Q).const_mul (C + 1)).mono'
    (((hg.sub (measurable_measurableHahnLabel P Q)).abs).mul
      (measurable_measurableHahnDensity P Q).abs).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hσ : |measurableHahnLabel P Q x| ≤ 1 := by
    rw [measurableHahnLabel]
    exact abs_le.mpr (hahnSign_mem_Icc _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
  have h1 : |g x - measurableHahnLabel P Q x| ≤ C + 1 :=
    (abs_sub _ _).trans (by linarith [hgb x])
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The label distance is `2∫|h|`-Lipschitz in the sup norm. -/
theorem abs_hahnLabelDistance_sub_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {g g' : X → ℝ} (hg : Measurable g) (hg' : Measurable g') {C : ℝ} (hgb : ∀ x, |g x| ≤ C)
    (hgb' : ∀ x, |g' x| ≤ C) {D : ℝ} (hD : ∀ x, |g x - g' x| ≤ D) :
    |hahnLabelDistance P Q g - hahnLabelDistance P Q g'|
      ≤ D * ∫ x, |measurableHahnDensity P Q x| ∂(currentControl P Q) := by
  rw [hahnLabelDistance, hahnLabelDistance, ← integral_sub (integrable_hahnLabelWeight P Q hg hgb)
    (integrable_hahnLabelWeight P Q hg' hgb'), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => abs_nonneg _)
    ((integrable_abs_measurableHahnDensity P Q).const_mul D) (Eventually.of_forall fun x => ?_))
  dsimp only
  rw [← sub_mul, abs_mul, abs_abs]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  have : g x - measurableHahnLabel P Q x - (g' x - measurableHahnLabel P Q x) = g x - g' x := by
    ring
  rw [this]
  exact hD x

section CompactDictionary

variable [TopologicalSpace X] [OpensMeasurableSpace X] [CompactSpace X]

/-- **Corollary 4.2 (HLA.10).**  For mutually singular laws of full support on a compact space, a
nonempty compact dictionary of continuous effects has positive Hahn-label width. -/
theorem hahnLabelWidth_pos {P Q : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ⟂ₘ Q) [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] {E : Set C(X, ℝ)}
    (hEc : IsCompact E) (hEn : E.Nonempty) (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    0 < ⨅ e : E, hahnLabelDistance P Q (fun x => 2 * (e : C(X, ℝ)) x - 1) := by
  haveI : Nonempty E := hEn.to_subtype
  set F : C(X, ℝ) → ℝ := fun e => hahnLabelDistance P Q (fun x => 2 * e x - 1) with hFdef
  set M : ℝ := ∫ x, |measurableHahnDensity P Q x| ∂(currentControl P Q) with hMdef
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hFlip : ∀ e e' : C(X, ℝ), dist (F e) (F e') ≤ (2 * M) * dist e e' := by
    intro e e'
    rw [Real.dist_eq, dist_eq_norm]
    have hbound : ∀ x, |(2 * e x - 1) - (2 * e' x - 1)| ≤ 2 * ‖e - e'‖ := by
      intro x
      have h := ContinuousMap.norm_coe_le_norm (e - e') x
      rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at h
      rw [show (2 * e x - 1) - (2 * e' x - 1) = 2 * (e x - e' x) by ring, abs_mul, abs_two]
      linarith
    have hge : ∀ x, |2 * e x - 1| ≤ 2 * ‖e‖ + 1 := by
      intro x
      have h := ContinuousMap.norm_coe_le_norm e x
      rw [Real.norm_eq_abs] at h
      calc |2 * e x - 1| ≤ |2 * e x| + |(1 : ℝ)| := abs_sub _ _
        _ = 2 * |e x| + 1 := by rw [abs_mul, abs_two, abs_one]
        _ ≤ 2 * ‖e‖ + 1 := by linarith
    have hge' : ∀ x, |2 * e' x - 1| ≤ 2 * ‖e'‖ + 1 := by
      intro x
      have h := ContinuousMap.norm_coe_le_norm e' x
      rw [Real.norm_eq_abs] at h
      calc |2 * e' x - 1| ≤ |2 * e' x| + |(1 : ℝ)| := abs_sub _ _
        _ = 2 * |e' x| + 1 := by rw [abs_mul, abs_two, abs_one]
        _ ≤ 2 * ‖e'‖ + 1 := by linarith
    have hmeas : Measurable fun x => 2 * e x - 1 :=
      (e.continuous.measurable.const_mul 2).sub_const 1
    have hmeas' : Measurable fun x => 2 * e' x - 1 :=
      (e'.continuous.measurable.const_mul 2).sub_const 1
    have h := abs_hahnLabelDistance_sub_le P Q hmeas hmeas'
      (C := 2 * ‖e‖ + 2 * ‖e'‖ + 1) (fun x => (hge x).trans (by linarith [norm_nonneg e']))
      (fun x => (hge' x).trans (by linarith [norm_nonneg e])) hbound
    calc |F e - F e'| ≤ 2 * ‖e - e'‖ * M := h
      _ = 2 * M * ‖e - e'‖ := by ring
  have hFcont : Continuous F :=
    (LipschitzWith.of_dist_le_mul (K := ⟨2 * M, by positivity⟩) fun e e' => hFlip e e').continuous
  obtain ⟨e₀, he₀, hmin⟩ := hEc.exists_isMinOn hEn hFcont.continuousOn
  have hbdd : BddBelow (Set.range fun e : E => F e) :=
    ⟨0, by rintro _ ⟨e, rfl⟩; exact hahnLabelDistance_nonneg P Q _⟩
  have hinf : ⨅ e : E, F e = F e₀ :=
    le_antisymm (ciInf_le hbdd ⟨e₀, he₀⟩) (le_ciInf fun e => hmin e.2)
  change 0 < ⨅ e : E, F e
  rw [hinf]
  rcases (hahnLabelDistance_nonneg P Q (fun x => 2 * e₀ x - 1)).lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  have hmeas : Measurable fun x => 2 * e₀ x - 1 :=
    (e₀.continuous.measurable.const_mul 2).sub_const 1
  have hbnd : ∀ x, |2 * e₀ x - 1| ≤ 1 := fun x => by
    obtain ⟨h0, h1⟩ := hb e₀ he₀ x
    rw [abs_le]
    constructor <;> linarith
  have hae : (fun x => |2 * e₀ x - 1 - measurableHahnLabel P Q x| * |measurableHahnDensity P Q x|)
      =ᵐ[currentControl P Q] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (integrable_hahnLabelWeight P Q hmeas hbnd)).mp hzero.symm
  have hlab : ∀ᵐ x ∂(currentControl P Q), 2 * e₀ x - 1 = measurableHahnLabel P Q x := by
    filter_upwards [hae, ae_abs_measurableHahnDensity_eq_one hPQ] with x hx h1
    simp only [Pi.zero_apply, h1, mul_one, abs_eq_zero] at hx
    linarith
  have hQac : Q ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_left le_rfl)
  have hPac : P ≪ currentControl P Q := Measure.absolutelyContinuous_of_le
    (Measure.le_add_right le_rfl)
  have hQ1 : ∀ᵐ x ∂Q, e₀ x = 1 := by
    filter_upwards [hQac.ae_le hlab, ae_measurableHahnLabel_eq_one hPQ] with x hx h1
    linarith
  have hP0 : ∀ᵐ x ∂P, e₀ x = 0 := by
    filter_upwards [hPac.ae_le hlab, ae_measurableHahnLabel_eq_neg_one hPQ] with x hx h1
    linarith
  have hopen1 : IsOpen {x | e₀ x ≠ 1} := isOpen_ne_fun e₀.continuous continuous_const
  have hopen0 : IsOpen {x | e₀ x ≠ 0} := isOpen_ne_fun e₀.continuous continuous_const
  have hall1 : ∀ x, e₀ x = 1 := by
    have h := (hopen1.measure_eq_zero_iff Q).mp (by rw [← ae_iff]; exact hQ1)
    intro x
    by_contra hx
    exact (Set.eq_empty_iff_forall_notMem.mp h) x hx
  have hall0 : ∀ x, e₀ x = 0 := by
    have h := (hopen0.measure_eq_zero_iff P).mp (by rw [← ae_iff]; exact hP0)
    intro x
    by_contra hx
    exact (Set.eq_empty_iff_forall_notMem.mp h) x hx
  obtain ⟨x⟩ : Nonempty X := nonempty_of_isProbabilityMeasure P
  have := (hall1 x).symm.trans (hall0 x)
  norm_num at this

end CompactDictionary

/-! ## The resolution spectrum -/

section Spectrum

variable (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
variable {E : Submodule ℝ (X → ℝ)} (q : Seminorm ℝ E)

/-- The feasible prices of effects in `E` carrying contrast at least `r`. -/
def resolutionPriceSet (r : ℝ) : Set ℝ :=
  {y | ∃ e : E, (∀ x, (e : X → ℝ) x ∈ Icc (0 : ℝ) 1) ∧ r ≤ hahnEffectCurrent P Q e ∧ y = q e}

/-- The feasible prices of soft labels in `E` within label distance `ε`. -/
def approximationSpectrumSet (ε : ℝ) : Set ℝ :=
  {y | ∃ g : E, (∀ x, (g : X → ℝ) x ∈ Icc (-1 : ℝ) 1) ∧ hahnLabelDistance P Q g ≤ ε ∧ y = q g}

/-- The resolution price `ℛ^q_μ(r)`. -/
def resolutionPrice (r : ℝ) : ℝ := sInf (resolutionPriceSet P Q q r)

/-- The Hahn approximation spectrum `𝒬^q_μ(ε)`. -/
def approximationSpectrum (ε : ℝ) : ℝ := sInf (approximationSpectrumSet P Q q ε)

variable {P Q}

omit [MeasurableSpace X] in
theorem seminorm_sub_const {q : Seminorm ℝ E} {c : E} (hc : q c = 0) (f : E) : q (f - c) = q f := by
  apply le_antisymm
  · calc q (f - c) ≤ q f + q c := map_sub_le_add q f c
      _ = q f := by rw [hc, add_zero]
  · calc q f = q ((f - c) + c) := by rw [sub_add_cancel]
      _ ≤ q (f - c) + q c := map_add_le_add q _ _
      _ = q (f - c) := by rw [hc, add_zero]

omit [MeasurableSpace X] in
theorem seminorm_add_const {q : Seminorm ℝ E} {c : E} (hc : q c = 0) (f : E) : q (f + c) = q f := by
  rw [← sub_neg_eq_add, seminorm_sub_const (by rw [map_neg_eq_map, hc]) f]

/-- **Theorem 5.1 (HLA.13), set form.**  The feasible resolution prices at contrast `r` are half
the feasible approximation prices at label distance `2(TV - r)`. -/
theorem resolutionPriceSet_eq (hmeas : ∀ f ∈ E, Measurable f)
    (hconst : ∀ c : ℝ, (fun _ : X => c) ∈ E) (hq : ∀ c : ℝ, q ⟨fun _ => c, hconst c⟩ = 0)
    (r : ℝ) :
    resolutionPriceSet P Q q r
      = (1 / 2 : ℝ) • approximationSpectrumSet P Q q (2 * (measurableHahnTV P Q - r)) := by
  set one : E := ⟨fun _ => 1, hconst 1⟩ with hone
  have hq1 : q one = 0 := hq 1
  ext y
  constructor
  · rintro ⟨e, heb, her, rfl⟩
    refine ⟨q ((2 : ℝ) • e - one), ⟨(2 : ℝ) • e - one, fun x => ?_, ?_, rfl⟩, ?_⟩
    · obtain ⟨h0, h1⟩ := heb x
      change 2 * (e : X → ℝ) x - 1 ∈ Icc (-1 : ℝ) 1
      constructor <;> linarith
    · change hahnLabelDistance P Q (fun x => 2 * (e : X → ℝ) x - 1)
        ≤ 2 * (measurableHahnTV P Q - r)
      have h := measurableHahnTV_sub_effectCurrent P Q (hmeas e e.2) heb
      linarith
    · change (1 / 2 : ℝ) * q ((2 : ℝ) • e - one) = q e
      rw [seminorm_sub_const hq1, map_smul_eq_mul, Real.norm_two]
      ring
  · rintro ⟨z, ⟨g, hgb, hgε, rfl⟩, rfl⟩
    refine ⟨(1 / 2 : ℝ) • (g + one), fun x => ?_, ?_, ?_⟩
    · obtain ⟨h0, h1⟩ := hgb x
      change (1 / 2 : ℝ) * ((g : X → ℝ) x + 1) ∈ Icc (0 : ℝ) 1
      constructor <;> linarith
    · have hb : ∀ x, (((1 / 2 : ℝ) • (g + one) : E) : X → ℝ) x ∈ Icc (0 : ℝ) 1 := fun x => by
        obtain ⟨h0, h1⟩ := hgb x
        change (1 / 2 : ℝ) * ((g : X → ℝ) x + 1) ∈ Icc (0 : ℝ) 1
        constructor <;> linarith
      have h := measurableHahnTV_sub_effectCurrent P Q
        (hmeas _ ((1 / 2 : ℝ) • (g + one)).2) hb
      have hfun : (fun x => 2 * (((1 / 2 : ℝ) • (g + one) : E) : X → ℝ) x - 1)
          = (g : X → ℝ) := by
        funext x
        change 2 * ((1 / 2 : ℝ) * ((g : X → ℝ) x + 1)) - 1 = (g : X → ℝ) x
        ring
      rw [hfun] at h
      linarith
    · change (1 / 2 : ℝ) • q g = q ((1 / 2 : ℝ) • (g + one))
      rw [map_smul_eq_mul, seminorm_add_const hq1, smul_eq_mul, Real.norm_of_nonneg (by norm_num)]

/-- **Theorem 5.1 (HLA.13).**  `ℛ^q_μ(r) = ½ 𝒬^q_μ(2(TV - r))`. -/
theorem resolutionPrice_eq (hmeas : ∀ f ∈ E, Measurable f)
    (hconst : ∀ c : ℝ, (fun _ : X => c) ∈ E) (hq : ∀ c : ℝ, q ⟨fun _ => c, hconst c⟩ = 0)
    (r : ℝ) :
    resolutionPrice P Q q r
      = (1 / 2 : ℝ) * approximationSpectrum P Q q (2 * (measurableHahnTV P Q - r)) := by
  rw [resolutionPrice, approximationSpectrum, resolutionPriceSet_eq q hmeas hconst hq,
    Real.sInf_smul_of_nonneg (by norm_num), smul_eq_mul]

end Spectrum

/-! ## Observers -/

section Observers

variable {Z : Type*} [MeasurableSpace Z]

/-- The observed contrast of `f ∘ π` is the contrast of `f` under the pushed-forward laws. -/
theorem hahnEffectCurrent_comp (P Q : Measure X) {π : X → Z} (hπ : Measurable π) {f : Z → ℝ}
    (hf : Measurable f) :
    hahnEffectCurrent P Q (f ∘ π) = hahnEffectCurrent (P.map π) (Q.map π) f := by
  rw [hahnEffectCurrent, hahnEffectCurrent, integral_map hπ.aemeasurable hf.aestronglyMeasurable,
    integral_map hπ.aemeasurable hf.aestronglyMeasurable]
  rfl

theorem hahnLabelDistance_eq_two_mul (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {g : X → ℝ} (hg : Measurable g) (hgb : ∀ x, g x ∈ Icc (-1 : ℝ) 1) :
    hahnLabelDistance P Q g = 2 * measurableHahnTV P Q - hahnEffectCurrent P Q g := by
  have h := measurableHahnTV_sub_half_current P Q hg hgb
  linarith

/-- **Observer decomposition.**  For a measurable observer `π` and a measurable soft label `f` on
its target, `‖f ∘ π - σ_μ‖ = 2(TV(μ) - TV(π_*μ)) + ‖f - σ_{π_*μ}‖`. -/
theorem hahnLabelDistance_comp (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {π : X → Z} (hπ : Measurable π) {f : Z → ℝ} (hf : Measurable f)
    (hfb : ∀ z, f z ∈ Icc (-1 : ℝ) 1) :
    hahnLabelDistance P Q (f ∘ π)
      = 2 * (measurableHahnTV P Q - measurableHahnTV (P.map π) (Q.map π))
        + hahnLabelDistance (P.map π) (Q.map π) f := by
  haveI : IsFiniteMeasure (P.map π) := Measure.isFiniteMeasure_map P π
  haveI : IsFiniteMeasure (Q.map π) := Measure.isFiniteMeasure_map Q π
  rw [hahnLabelDistance_eq_two_mul P Q (hf.comp hπ) (fun x => hfb (π x)),
    hahnLabelDistance_eq_two_mul (P.map π) (Q.map π) hf hfb, hahnEffectCurrent_comp P Q hπ hf]
  ring

/-- Data processing: an observer cannot increase total variation. -/
theorem measurableHahnTV_map_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {π : X → Z} (hπ : Measurable π) :
    measurableHahnTV (P.map π) (Q.map π) ≤ measurableHahnTV P Q := by
  haveI : IsFiniteMeasure (P.map π) := Measure.isFiniteMeasure_map P π
  haveI : IsFiniteMeasure (Q.map π) := Measure.isFiniteMeasure_map Q π
  have h := hahnLabelDistance_comp P Q hπ (measurable_measurableHahnLabel (P.map π) (Q.map π))
    (fun z => by rw [measurableHahnLabel]; exact hahnSign_mem_Icc _)
  have h0 : hahnLabelDistance (P.map π) (Q.map π) (measurableHahnLabel (P.map π) (Q.map π))
      = 0 := by
    rw [hahnLabelDistance]
    simp
  rw [h0, add_zero] at h
  have := hahnLabelDistance_nonneg P Q (measurableHahnLabel (P.map π) (Q.map π) ∘ π)
  linarith

/-- **Theorem 7.1 (HLA.17).**  The best label distance attainable through a measurable observer
is `2(TV(μ₀, μ₁) - TV(π_*μ₀, π_*μ₁))`, attained by the pulled-back target label. -/
theorem isLeast_observerLabelDistance (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {π : X → Z} (hπ : Measurable π) :
    IsLeast {r | ∃ f : Z → ℝ, Measurable f ∧ (∀ z, f z ∈ Icc (-1 : ℝ) 1) ∧
        r = hahnLabelDistance P Q (f ∘ π)}
      (2 * (measurableHahnTV P Q - measurableHahnTV (P.map π) (Q.map π))) := by
  haveI : IsFiniteMeasure (P.map π) := Measure.isFiniteMeasure_map P π
  haveI : IsFiniteMeasure (Q.map π) := Measure.isFiniteMeasure_map Q π
  refine ⟨⟨measurableHahnLabel (P.map π) (Q.map π),
    measurable_measurableHahnLabel _ _, fun z => by
      rw [measurableHahnLabel]; exact hahnSign_mem_Icc _, ?_⟩, ?_⟩
  · rw [hahnLabelDistance_comp P Q hπ (measurable_measurableHahnLabel _ _)
      (fun z => by rw [measurableHahnLabel]; exact hahnSign_mem_Icc _)]
    have h0 : hahnLabelDistance (P.map π) (Q.map π) (measurableHahnLabel (P.map π) (Q.map π))
        = 0 := by
      rw [hahnLabelDistance]
      simp
    rw [h0, add_zero]
  · rintro r ⟨f, hf, hfb, rfl⟩
    rw [hahnLabelDistance_comp P Q hπ hf hfb]
    have := hahnLabelDistance_nonneg (P.map π) (Q.map π) f
    linarith

/-- **(HLA.17) for finite observers.**  Every function on a finite target is admissible. -/
theorem isLeast_finiteObserverLabelDistance (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] [Countable Z] [MeasurableSingletonClass Z] {π : X → Z}
    (hπ : Measurable π) :
    IsLeast {r | ∃ f : Z → ℝ, (∀ z, f z ∈ Icc (-1 : ℝ) 1) ∧ r = hahnLabelDistance P Q (f ∘ π)}
      (2 * (measurableHahnTV P Q - measurableHahnTV (P.map π) (Q.map π))) := by
  have h := isLeast_observerLabelDistance P Q hπ
  have hset : {r | ∃ f : Z → ℝ, (∀ z, f z ∈ Icc (-1 : ℝ) 1) ∧
        r = hahnLabelDistance P Q (f ∘ π)}
      = {r | ∃ f : Z → ℝ, Measurable f ∧ (∀ z, f z ∈ Icc (-1 : ℝ) 1) ∧
        r = hahnLabelDistance P Q (f ∘ π)} := by
    ext r
    constructor
    · rintro ⟨f, hfb, rfl⟩
      exact ⟨f, measurable_of_countable f, hfb, rfl⟩
    · rintro ⟨f, -, hfb, rfl⟩
      exact ⟨f, hfb, rfl⟩
  rw [hset]
  exact h

/-- The observer deficit `D_μ(π) = 2(TV(μ) - TV(π_*μ))`. -/
def hahnObserverDeficit (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (π : X → Z) : ℝ :=
  2 * (measurableHahnTV P Q - measurableHahnTV (P.map π) (Q.map π))

/-- **Theorem 7.2 (HLA.19).**  Observer deficits add along composed observers. -/
theorem hahnObserverDeficit_comp {W : Type*} [MeasurableSpace W] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {π : X → Z} (hπ : Measurable π) {ρ : Z → W}
    (hρ : Measurable ρ) :
    hahnObserverDeficit P Q (ρ ∘ π)
      = hahnObserverDeficit P Q π
        + @hahnObserverDeficit Z _ W _ (P.map π) (Q.map π)
          (Measure.isFiniteMeasure_map P π) (Measure.isFiniteMeasure_map Q π) ρ := by
  rw [hahnObserverDeficit, hahnObserverDeficit, hahnObserverDeficit]
  simp only [Measure.map_map hρ hπ]
  ring

/-- A measurable relabelling preserves total variation. -/
theorem measurableHahnTV_map_equiv {X' : Type*} [MeasurableSpace X'] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (τ : X ≃ᵐ X') :
    @measurableHahnTV X' _ (P.map τ) (Q.map τ) (Measure.isFiniteMeasure_map P τ)
      (Measure.isFiniteMeasure_map Q τ) = measurableHahnTV P Q := by
  haveI : IsFiniteMeasure (P.map τ) := Measure.isFiniteMeasure_map P τ
  haveI : IsFiniteMeasure (Q.map τ) := Measure.isFiniteMeasure_map Q τ
  apply le_antisymm (measurableHahnTV_map_le P Q τ.measurable)
  have h := measurableHahnTV_map_le (P.map τ) (Q.map τ) τ.symm.measurable
  simpa only [Measure.map_map τ.symm.measurable τ.measurable, MeasurableEquiv.symm_comp_self,
    Measure.map_id] using h

/-- **(HLA.20).**  A measurable relabelling transports the Hahn label distance isometrically. -/
theorem hahnLabelDistance_map_equiv {X' : Type*} [MeasurableSpace X'] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (τ : X ≃ᵐ X') {g : X → ℝ} (hg : Measurable g)
    (hgb : ∀ x, g x ∈ Icc (-1 : ℝ) 1) :
    hahnLabelDistance (P.map τ) (Q.map τ) (g ∘ τ.symm) = hahnLabelDistance P Q g := by
  haveI : IsFiniteMeasure (P.map τ) := Measure.isFiniteMeasure_map P τ
  haveI : IsFiniteMeasure (Q.map τ) := Measure.isFiniteMeasure_map Q τ
  have hTV : measurableHahnTV (P.map τ) (Q.map τ) = measurableHahnTV P Q :=
    measurableHahnTV_map_equiv P Q τ
  have hcur : hahnEffectCurrent (P.map τ) (Q.map τ) (g ∘ τ.symm) = hahnEffectCurrent P Q g := by
    rw [hahnEffectCurrent, hahnEffectCurrent, integral_map_equiv, integral_map_equiv]
    simp
  rw [hahnLabelDistance_eq_two_mul _ _ (hg.comp τ.symm.measurable) (fun x => hgb _),
    hahnLabelDistance_eq_two_mul P Q hg hgb, hTV, hcur]

end Observers

/-! ## Tensor formation -/

section Formation

variable {Z : Type*} [MeasurableSpace Z]

/-- The pulled-back effect `e = K^* 1_B`. -/
def formationEffect (K : ProbabilityTheory.Kernel X Z) (B : Set Z) (x : X) : ℝ := (K x B).toReal

theorem measurable_formationEffect (K : ProbabilityTheory.Kernel X Z) {B : Set Z}
    (hB : MeasurableSet B) : Measurable (formationEffect K B) :=
  (K.measurable_coe hB).ennreal_toReal

theorem formationEffect_mem (K : ProbabilityTheory.Kernel X Z) [ProbabilityTheory.IsMarkovKernel K]
    (B : Set Z) (x : X) : formationEffect K B x ∈ Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    rw [formationEffect]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩

theorem integral_formationEffect (μ : Measure X) [IsFiniteMeasure μ]
    (K : ProbabilityTheory.Kernel X Z) [ProbabilityTheory.IsMarkovKernel K] {B : Set Z}
    (hB : MeasurableSet B) : ∫ x, formationEffect K B x ∂μ = (μ.bind K).real B := by
  unfold formationEffect
  rw [Measure.real_def, Measure.bind_apply hB (K.measurable).aemeasurable,
    integral_toReal (K.measurable_coe hB).aemeasurable
      (Eventually.of_forall fun x => measure_lt_top (K x) B)]

/-- **Theorem 6.1 (HLA.14).**  If `K` forms `ρ₀, ρ₁` exactly from singular `μ₀, μ₁` and `B` is a
Neyman–Pearson event, the formed effect has label distance `2(1 - TV(ρ₀, ρ₁))`. -/
theorem hahnLabelDistance_formation (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) (ρ₀ ρ₁ : Measure Z) [IsProbabilityMeasure ρ₀]
    [IsProbabilityMeasure ρ₁] (K : ProbabilityTheory.Kernel X Z)
    [ProbabilityTheory.IsMarkovKernel K] (hK₀ : P.bind K = ρ₀) (hK₁ : Q.bind K = ρ₁)
    {B : Set Z} (hB : MeasurableSet B)
    (hNP : ρ₁.real B - ρ₀.real B = measurableHahnTV ρ₀ ρ₁) :
    hahnLabelDistance P Q (fun x => 2 * formationEffect K B x - 1)
      = 2 * (1 - measurableHahnTV ρ₀ ρ₁) := by
  have h := one_sub_hahnEffectCurrent_of_singular hPQ (measurable_formationEffect K hB)
    (formationEffect_mem K B)
  have hcur : hahnEffectCurrent P Q (formationEffect K B) = measurableHahnTV ρ₀ ρ₁ := by
    rw [hahnEffectCurrent, integral_formationEffect Q K hB, integral_formationEffect P K hB,
      hK₀, hK₁, hNP]
  rw [hcur, ← hahnLabelDistance_eq_of_singular hPQ] at h
  linarith

/-- The Neyman–Pearson event `{h ≥ 0}` of the formed laws realizes Theorem 6.1. -/
theorem hahnLabelDistance_formation_hahnPositiveSet (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) (ρ₀ ρ₁ : Measure Z) [IsProbabilityMeasure ρ₀]
    [IsProbabilityMeasure ρ₁] (K : ProbabilityTheory.Kernel X Z)
    [ProbabilityTheory.IsMarkovKernel K] (hK₀ : P.bind K = ρ₀) (hK₁ : Q.bind K = ρ₁) :
    hahnLabelDistance P Q (fun x => 2 * formationEffect K (hahnPositiveSet ρ₀ ρ₁) x - 1)
      = 2 * (1 - measurableHahnTV ρ₀ ρ₁) := by
  refine hahnLabelDistance_formation P Q hPQ ρ₀ ρ₁ K hK₀ hK₁
    (measurableSet_hahnPositiveSet ρ₀ ρ₁) ?_
  have h := hahnEffectCurrent_hahnPositiveSet ρ₀ ρ₁
  rw [hahnEffectCurrent, integral_indicator_const (1 : ℝ) (measurableSet_hahnPositiveSet ρ₀ ρ₁),
    integral_indicator_const (1 : ℝ) (measurableSet_hahnPositiveSet ρ₀ ρ₁), smul_eq_mul,
    smul_eq_mul, mul_one, mul_one] at h
  exact h

/-- On a finite discrete space, `1 - TV(ρ₀, ρ₁)` is at most the Hellinger affinity. -/
theorem one_sub_measurableHahnTV_le_hellingerAffinity [Fintype Z] [MeasurableSingletonClass Z]
    (ρ₀ ρ₁ : Measure Z) [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ρ₁] :
    1 - measurableHahnTV ρ₀ ρ₁ ≤ hellingerAffinity ρ₀ ρ₁ := by
  classical
  set B : Finset Z := Finset.univ.filter fun z => ρ₀.real {z} ≤ ρ₁.real {z} with hBdef
  have hBm : MeasurableSet (B : Set Z) := (B.finite_toSet).measurableSet
  have hTV := (isGreatest_measurableHahnTV ρ₀ ρ₁).2 ⟨B, hBm, rfl⟩
  have hreal : ∀ (ρ : Measure Z) [IsFiniteMeasure ρ] (s : Finset Z),
      ρ.real s = ∑ z ∈ s, ρ.real {z} := by
    intro ρ _ s
    rw [Measure.real_def, ← sum_measure_singleton, ENNReal.toReal_sum
      (fun z _ => measure_ne_top ρ _)]
    rfl
  have htot : ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ], ∑ z, ρ.real {z} = 1 := by
    intro ρ _
    rw [← hreal ρ Finset.univ, Finset.coe_univ, probReal_univ]
  have hmin : 1 - (ρ₁.real B - ρ₀.real B) = ∑ z, min (ρ₀.real {z}) (ρ₁.real {z}) := by
    rw [hreal ρ₁ B, hreal ρ₀ B, ← htot ρ₁, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun z => ρ₀.real {z} ≤ ρ₁.real {z}) (fun z => ρ₁.real {z}),
      ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun z => ρ₀.real {z} ≤ ρ₁.real {z}) (fun z => min (ρ₀.real {z}) (ρ₁.real {z}))]
    rw [Finset.sum_congr rfl fun z hz => min_eq_left (Finset.mem_filter.mp hz).2,
      Finset.sum_congr rfl fun z hz => min_eq_right (le_of_lt (not_le.mp
        (Finset.mem_filter.mp hz).2))]
    ring
  have hle : ∑ z, min (ρ₀.real {z}) (ρ₁.real {z}) ≤ hellingerAffinity ρ₀ ρ₁ := by
    rw [hellingerAffinity, tsum_fintype]
    refine Finset.sum_le_sum fun z _ => ?_
    have ha : 0 ≤ ρ₀.real {z} := measureReal_nonneg
    have hb : 0 ≤ ρ₁.real {z} := measureReal_nonneg
    rw [← Measure.real_def, ← Measure.real_def]
    rcases le_total (ρ₀.real {z}) (ρ₁.real {z}) with h | h
    · rw [min_eq_left h]
      calc ρ₀.real {z} = Real.sqrt (ρ₀.real {z} * ρ₀.real {z}) := (Real.sqrt_mul_self ha).symm
        _ ≤ Real.sqrt (ρ₀.real {z} * ρ₁.real {z}) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h ha)
    · rw [min_eq_right h]
      calc ρ₁.real {z} = Real.sqrt (ρ₁.real {z} * ρ₁.real {z}) := (Real.sqrt_mul_self hb).symm
        _ ≤ Real.sqrt (ρ₀.real {z} * ρ₁.real {z}) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hb)
  linarith

/-- **Theorem 6.1 (HLA.15).**  Depth-`d` tensor formation approximates the Hahn label with error at
most `2A^d`, `A` the Hellinger affinity of the target pair. -/
theorem hahnLabelDistance_formation_le {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] {d : ℕ} (K : ProbabilityTheory.Kernel X (Fin d → Y))
    [ProbabilityTheory.IsMarkovKernel K] (hK₀ : P.bind K = Measure.pi fun _ => p₀)
    (hK₁ : Q.bind K = Measure.pi fun _ => p₁) {B : Set (Fin d → Y)} (hB : MeasurableSet B)
    (hNP : (Measure.pi fun _ : Fin d => p₁).real B - (Measure.pi fun _ : Fin d => p₀).real B
      = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁)) :
    hahnLabelDistance P Q (fun x => 2 * formationEffect K B x - 1)
      ≤ 2 * hellingerAffinity p₀ p₁ ^ d := by
  rw [hahnLabelDistance_formation P Q hPQ _ _ K hK₀ hK₁ hB hNP, ← hellingerAffinity_pi_const]
  have := one_sub_measurableHahnTV_le_hellingerAffinity (Measure.pi fun _ : Fin d => p₀)
    (Measure.pi fun _ : Fin d => p₁)
  linarith

/-- **Corollary 6.2 (HLA.16).**  A dictionary of label width `ε` can contain the depth-`d` formed
effect only if `A^d ≥ ε/2`; for `0 < A < 1` this bounds the depth by `log(ε/2)/log A`. -/
theorem formation_depth_law {A ε : ℝ} {d : ℕ} (hdist : ε ≤ 2 * A ^ d) :
    ε / 2 ≤ A ^ d := by linarith

theorem formation_depth_le {A ε : ℝ} {d : ℕ} (hA0 : 0 < A) (hA1 : A < 1) (hε : 0 < ε)
    (hdist : ε ≤ 2 * A ^ d) : (d : ℝ) ≤ Real.log (ε / 2) / Real.log A := by
  have h := formation_depth_law hdist
  have hlog : Real.log (ε / 2) ≤ Real.log (A ^ d) := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at hlog
  have hlA : Real.log A < 0 := Real.log_neg hA0 hA1
  rw [le_div_iff_of_neg hlA]
  linarith

end Formation

end GaloisForLFunctions.HTGeometry
