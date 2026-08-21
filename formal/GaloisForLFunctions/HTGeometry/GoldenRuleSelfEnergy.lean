import GaloisForLFunctions.HTGeometry.GoldenRuleLimit
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# The energy-domain face of Fermi's golden rule

Fermi's golden rule has two classical derivations that must agree.  The time-domain one — the one
`GoldenRuleLimit` formalizes — reads the rate off the linear growth of the first-order transition
probability.  The energy-domain (Weisskopf–Wigner) one reads the *same* rate off the imaginary part
of the second-order self-energy of the level,

```text
Σ(E₀ + i ε) = ∫_ℝ ρ(E) / (E₀ + i ε − E) dE ,      Γ = −2 Im Σ(E₀ + i 0⁺) = 2 π ρ(E₀) .
```

This file proves that limit.  The mechanism is the half-plane Poisson kernel — already owned by the
corpus as `halfPlanePoisson c t = c / (π (c² + t²))`, a probability density for every height — which
plays exactly the role the squared cardinal sine plays in the time domain.  The two derivations are
then shown to produce the same number.
-/

open MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Tail estimates for the half-plane Poisson kernel -/

theorem halfPlanePoisson_le_of_tail {ε δ x : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hx : δ ≤ |x|) :
    halfPlanePoisson ε x ≤ ε / (Real.pi * δ ^ 2) := by
  have hpi := Real.pi_pos
  have hx2 : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hstep : δ ^ 2 ≤ ε ^ 2 + x ^ 2 := by nlinarith [sq_nonneg ε]
  have hεπ : (0 : ℝ) ≤ ε * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstep hεπ
  rw [halfPlanePoisson, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hmul]

theorem halfPlanePoisson_le_tail_majorant {ε δ x : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hx : δ ≤ |x|) :
    halfPlanePoisson ε x ≤ ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹ := by
  have hpi := Real.pi_pos
  have hx2 : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hrhs : ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹
      = (ε * (1 + δ ^ 2)) / (Real.pi * δ ^ 2 * (1 + x ^ 2)) := by
    field_simp
  rw [halfPlanePoisson, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hε.le hpi.le) (sub_nonneg.mpr hx2),
    mul_nonneg (mul_nonneg (mul_nonneg hε.le hpi.le) (sq_nonneg ε))
      (by positivity : (0 : ℝ) ≤ 1 + δ ^ 2)]

theorem setIntegral_halfPlanePoisson_compl_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x ≤ ε * (1 + δ ^ 2) / δ ^ 2 := by
  have hpi := Real.pi_pos
  have hmaj : Integrable
      (fun x : ℝ => ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹) (volume : Measure ℝ) :=
    integrable_inv_one_add_sq.const_mul _
  have hmeas : MeasurableSet ((Set.Ioo (-δ) δ)ᶜ) := measurableSet_Ioo.compl
  have h1 : ∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x
      ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹ :=
    MeasureTheory.setIntegral_mono_on ((integrable_halfPlanePoisson hε).integrableOn)
      hmaj.integrableOn hmeas fun x hx =>
        halfPlanePoisson_le_tail_majorant hε hδ (abs_ge_of_notMem_Ioo hδ hx)
  have h2 : ∫ x in (Set.Ioo (-δ) δ)ᶜ, ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹
      ≤ ∫ x : ℝ, ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹ := by
    refine MeasureTheory.setIntegral_le_integral hmaj ?_
    filter_upwards with x
    have h1x : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hcc : (0 : ℝ) ≤ ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) := by positivity
    positivity
  have h3 : ∫ x : ℝ, ε * (1 + δ ^ 2) / (Real.pi * δ ^ 2) * (1 + x ^ 2)⁻¹
      = ε * (1 + δ ^ 2) / δ ^ 2 := by
    rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    field_simp
  linarith

theorem abs_setIntegral_halfPlanePoisson_compl_mul_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {g : ℝ → ℝ} (hg : Integrable g (volume : Measure ℝ)) :
    |∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x * g x|
      ≤ ε / (Real.pi * δ ^ 2) * ∫ x : ℝ, |g x| := by
  have hpi := Real.pi_pos
  have hmeas : MeasurableSet ((Set.Ioo (-δ) δ)ᶜ) := measurableSet_Ioo.compl
  have hbdd : ∀ x : ℝ, ‖halfPlanePoisson ε x‖ ≤ 1 / (Real.pi * ε) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (halfPlanePoisson_pos hε x).le]
    exact halfPlanePoisson_le hε x
  have hPg : Integrable (fun x : ℝ => halfPlanePoisson ε x * g x) (volume : Measure ℝ) :=
    hg.bdd_mul (c := 1 / (Real.pi * ε)) (continuous_halfPlanePoisson hε).aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have habs : Integrable (fun x : ℝ => ε / (Real.pi * δ ^ 2) * |g x|) (volume : Measure ℝ) :=
    (hg.abs).const_mul _
  calc |∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x * g x|
      ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, |halfPlanePoisson ε x * g x| := by
        simpa using MeasureTheory.abs_integral_le_integral_abs
          (μ := (volume : Measure ℝ).restrict ((Set.Ioo (-δ) δ)ᶜ))
          (f := fun x => halfPlanePoisson ε x * g x)
    _ ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, ε / (Real.pi * δ ^ 2) * |g x| := by
        refine MeasureTheory.setIntegral_mono_on hPg.abs.integrableOn habs.integrableOn
          hmeas fun x hx => ?_
        rw [abs_mul, abs_of_nonneg (halfPlanePoisson_pos hε x).le]
        exact mul_le_mul_of_nonneg_right
          (halfPlanePoisson_le_of_tail hε hδ (abs_ge_of_notMem_Ioo hδ hx)) (abs_nonneg _)
    _ ≤ ∫ x : ℝ, ε / (Real.pi * δ ^ 2) * |g x| := by
        refine MeasureTheory.setIntegral_le_integral habs ?_
        filter_upwards with x
        have hcc : (0 : ℝ) ≤ ε / (Real.pi * δ ^ 2) := by positivity
        positivity
    _ = ε / (Real.pi * δ ^ 2) * ∫ x : ℝ, |g x| := MeasureTheory.integral_const_mul _ _

/-! ## The Poisson concentration limit -/

/-- **The half-plane Poisson kernel is an approximate identity as the height goes to zero.** -/
theorem tendsto_halfPlanePoisson_weight {g : ℝ → ℝ} (hg : Integrable g (volume : Measure ℝ))
    (hc : ContinuousAt g 0) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : ℝ, halfPlanePoisson ε x * g x)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (g 0)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  set η : ℝ := e / 4 with hηdef
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → |g x - g 0| ≤ η := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhds_nhds.mp hc η hηpos
    refine ⟨δ, hδpos, fun x hx => le_of_lt ?_⟩
    have hdx : dist x (0 : ℝ) < δ := by simpa [Real.dist_eq] using hx
    simpa [Real.dist_eq] using hδ hdx
  set C₁ : ℝ := (1 + δ ^ 2) / δ ^ 2 with hC₁def
  set C₂ : ℝ := 1 / (Real.pi * δ ^ 2) * ∫ x : ℝ, |g x| with hC₂def
  set M : ℝ := |g 0| * C₁ + C₂ with hMdef
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hC₂nn : 0 ≤ C₂ := by
    have hint : (0 : ℝ) ≤ ∫ x : ℝ, |g x| := MeasureTheory.integral_nonneg fun x => abs_nonneg _
    rw [hC₂def]
    positivity
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact add_nonneg (mul_nonneg (abs_nonneg _) hC₁nn) hC₂nn
  have key : ∀ ε : ℝ, 0 < ε →
      |(∫ x : ℝ, halfPlanePoisson ε x * g x) - g 0| ≤ η + ε * M := by
    intro ε hε
    have hS : MeasurableSet (Set.Ioo (-δ) δ) := measurableSet_Ioo
    have hP : Integrable (halfPlanePoisson ε) (volume : Measure ℝ) :=
      integrable_halfPlanePoisson hε
    have hbdd : ∀ x : ℝ, ‖halfPlanePoisson ε x‖ ≤ 1 / (Real.pi * ε) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (halfPlanePoisson_pos hε x).le]
      exact halfPlanePoisson_le hε x
    have hPg : Integrable (fun x : ℝ => halfPlanePoisson ε x * g x) (volume : Measure ℝ) :=
      hg.bdd_mul (c := 1 / (Real.pi * ε))
        (continuous_halfPlanePoisson hε).aestronglyMeasurable
        (Filter.Eventually.of_forall hbdd)
    have hSfin : (volume : Measure ℝ) (Set.Ioo (-δ) δ) ≠ ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    have hconstOn : IntegrableOn (fun _ : ℝ => g 0) (Set.Ioo (-δ) δ) volume :=
      integrableOn_const hSfin
    have hdiffOn : IntegrableOn (fun x : ℝ => g x - g 0) (Set.Ioo (-δ) δ) volume :=
      hg.integrableOn.sub hconstOn
    have hPdiffOn : IntegrableOn (fun x : ℝ => halfPlanePoisson ε x * (g x - g 0))
        (Set.Ioo (-δ) δ) volume :=
      hdiffOn.bdd_mul (c := 1 / (Real.pi * ε))
        ((continuous_halfPlanePoisson hε).aestronglyMeasurable.restrict)
        (Filter.Eventually.of_forall hbdd)
    have hPconstOn : IntegrableOn (fun x : ℝ => halfPlanePoisson ε x * g 0)
        (Set.Ioo (-δ) δ) volume := hP.integrableOn.mul_const _
    set A : ℝ := ∫ x in Set.Ioo (-δ) δ, halfPlanePoisson ε x * (g x - g 0) with hAdef
    set R : ℝ := ∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x with hRdef
    set B : ℝ := ∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x * g x with hBdef
    have hmass : (∫ x in Set.Ioo (-δ) δ, halfPlanePoisson ε x) = 1 - R := by
      have h := MeasureTheory.integral_add_compl hS hP
      rw [integral_halfPlanePoisson hε] at h
      rw [hRdef]
      linarith
    have hinner : (∫ x in Set.Ioo (-δ) δ, halfPlanePoisson ε x * g x)
        = A + (1 - R) * g 0 := by
      have hpt : ∀ x : ℝ, halfPlanePoisson ε x * g x
          = halfPlanePoisson ε x * (g x - g 0) + halfPlanePoisson ε x * g 0 := by
        intro x; ring
      rw [funext hpt, MeasureTheory.integral_add hPdiffOn hPconstOn,
        MeasureTheory.integral_mul_const, hmass, hAdef]
    have hid : (∫ x : ℝ, halfPlanePoisson ε x * g x) = A + (1 - R) * g 0 + B := by
      have h := MeasureTheory.integral_add_compl hS hPg
      rw [hinner, ← hBdef] at h
      linarith
    have hRnn : 0 ≤ R := by
      rw [hRdef]
      exact MeasureTheory.setIntegral_nonneg hS.compl fun x _ =>
        (halfPlanePoisson_pos hε x).le
    have hRle : R ≤ ε * C₁ := by
      have h := setIntegral_halfPlanePoisson_compl_le hε hδpos
      rw [hRdef, hC₁def]
      calc ∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x
          ≤ ε * (1 + δ ^ 2) / δ ^ 2 := h
        _ = ε * ((1 + δ ^ 2) / δ ^ 2) := by ring
    have hBle : |B| ≤ ε * C₂ := by
      have h := abs_setIntegral_halfPlanePoisson_compl_mul_le hε hδpos hg
      rw [hBdef, hC₂def]
      calc |∫ x in (Set.Ioo (-δ) δ)ᶜ, halfPlanePoisson ε x * g x|
          ≤ ε / (Real.pi * δ ^ 2) * ∫ x : ℝ, |g x| := h
        _ = ε * (1 / (Real.pi * δ ^ 2) * ∫ x : ℝ, |g x|) := by ring
    have hAle : |A| ≤ η := by
      have h1 : |A| ≤ ∫ x in Set.Ioo (-δ) δ, |halfPlanePoisson ε x * (g x - g 0)| := by
        rw [hAdef]
        simpa using MeasureTheory.abs_integral_le_integral_abs
          (μ := (volume : Measure ℝ).restrict (Set.Ioo (-δ) δ))
          (f := fun x => halfPlanePoisson ε x * (g x - g 0))
      have h2 : (∫ x in Set.Ioo (-δ) δ, |halfPlanePoisson ε x * (g x - g 0)|)
          ≤ ∫ x in Set.Ioo (-δ) δ, η * halfPlanePoisson ε x := by
        refine MeasureTheory.setIntegral_mono_on hPdiffOn.abs
          (hP.integrableOn.const_mul _) hS fun x hx => ?_
        have hxabs : |x| < δ := abs_lt.mpr ⟨hx.1, hx.2⟩
        rw [abs_mul, abs_of_nonneg (halfPlanePoisson_pos hε x).le, mul_comm]
        exact mul_le_mul_of_nonneg_right (hδ x hxabs) (halfPlanePoisson_pos hε x).le
      have h3 : (∫ x in Set.Ioo (-δ) δ, η * halfPlanePoisson ε x) = η * (1 - R) := by
        rw [MeasureTheory.integral_const_mul, hmass]
      have h4 : η * (1 - R) ≤ η * 1 := mul_le_mul_of_nonneg_left (by linarith) hηpos.le
      rw [mul_one] at h4
      linarith
    have halg : A + (1 - R) * g 0 + B - g 0 = A - g 0 * R + B := by ring
    rw [hid, halg]
    have h1 : |A - g 0 * R + B| ≤ |A| + |g 0 * R| + |B| := by
      have hA1 := neg_abs_le A
      have hA2 := le_abs_self A
      have hB1 := neg_abs_le B
      have hB2 := le_abs_self B
      have hR1 := neg_abs_le (g 0 * R)
      have hR2 := le_abs_self (g 0 * R)
      rw [abs_le]
      constructor <;> linarith
    have h2 : |g 0 * R| ≤ |g 0| * (ε * C₁) := by
      rw [abs_mul, abs_of_nonneg hRnn]
      exact mul_le_mul_of_nonneg_left hRle (abs_nonneg _)
    rw [hMdef]
    have hexp : ε * (|g 0| * C₁ + C₂) = |g 0| * (ε * C₁) + ε * C₂ := by ring
    rw [hexp]
    linarith
  refine ⟨e / (2 * (M + 1)), by positivity, fun ε hεmem hεdist => ?_⟩
  have hε : 0 < ε := hεmem
  have hεlt : ε < e / (2 * (M + 1)) := by
    simpa [Real.dist_eq, abs_of_pos hε] using hεdist
  rw [Real.dist_eq]
  have hk := key ε hε
  have h2 : ε * M < e / 2 := by
    calc ε * M ≤ ε * (M + 1) := by nlinarith
      _ < e / (2 * (M + 1)) * (M + 1) := mul_lt_mul_of_pos_right hεlt (by positivity)
      _ = e / 2 := by field_simp
  have hη : η = e / 4 := hηdef
  linarith

/-- **The shifted Poisson concentration limit.** -/
theorem tendsto_halfPlanePoisson_density {ρ : ℝ → ℝ} {E₀ : ℝ}
    (hρ : Integrable ρ (volume : Measure ℝ)) (hc : ContinuousAt ρ E₀) :
    Filter.Tendsto (fun ε : ℝ => ∫ E : ℝ, halfPlanePoisson ε (E - E₀) * ρ E)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (ρ E₀)) := by
  set g : ℝ → ℝ := fun x => ρ (x + E₀) with hgdef
  have hmp : MeasurePreserving (fun x : ℝ => x + E₀) volume volume :=
    measurePreserving_add_right volume E₀
  have hgint : Integrable g (volume : Measure ℝ) :=
    (hmp.integrable_comp hρ.aestronglyMeasurable).mpr hρ
  have hg0 : g 0 = ρ E₀ := by simp [hgdef]
  have hgc : ContinuousAt g 0 := by
    have hcont : Continuous (fun x : ℝ => x + E₀) := by fun_prop
    have h1 : Filter.Tendsto (fun x : ℝ => x + E₀) (nhds (0 : ℝ)) (nhds E₀) := by
      simpa using hcont.tendsto (0 : ℝ)
    have h2 : Filter.Tendsto g (nhds (0 : ℝ)) (nhds (ρ E₀)) := Filter.Tendsto.comp hc h1
    show Filter.Tendsto g (nhds (0 : ℝ)) (nhds (g 0))
    rw [hg0]
    exact h2
  have hshift : ∀ ε : ℝ, (∫ E : ℝ, halfPlanePoisson ε (E - E₀) * ρ E)
      = ∫ x : ℝ, halfPlanePoisson ε x * g x := by
    intro ε
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun E : ℝ => halfPlanePoisson ε (E - E₀) * ρ E) E₀
    rw [← h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hgdef]
  have h := tendsto_halfPlanePoisson_weight hgint hgc
  rw [hg0] at h
  refine h.congr fun ε => ?_
  rw [hshift ε]

/-! ## The self-energy of the level -/

/-- The second-order self-energy of the level at complex energy `E₀ + i ε`. -/
def levelSelfEnergy (ρ : ℝ → ℝ) (E₀ ε : ℝ) : ℂ :=
  ∫ E : ℝ, ((ρ E : ℝ) : ℂ) / (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))

/-- **The imaginary part of the self-energy is minus the Poisson average of the density.** -/
theorem im_levelSelfEnergy {ρ : ℝ → ℝ} (hρ : Integrable ρ (volume : Measure ℝ)) {ε : ℝ}
    (hε : 0 < ε) (E₀ : ℝ) :
    (levelSelfEnergy ρ E₀ ε).im
      = -(Real.pi * ∫ E : ℝ, halfPlanePoisson ε (E - E₀) * ρ E) := by
  have hpi := Real.pi_pos
  have hpt : ∀ E : ℝ,
      (((ρ E : ℝ) : ℂ) / (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))).im
        = -(Real.pi * (halfPlanePoisson ε (E - E₀) * ρ E)) := by
    intro E
    have hw : (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))
        = ⟨E₀ - E, ε⟩ := by
      apply Complex.ext <;> simp
    rw [hw, Complex.div_im]
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, zero_div, zero_sub]
    rw [halfPlanePoisson]
    have hns : Complex.normSq (⟨E₀ - E, ε⟩ : ℂ) = (E - E₀) ^ 2 + ε ^ 2 := by
      show (E₀ - E) * (E₀ - E) + ε * ε = (E - E₀) ^ 2 + ε ^ 2
      ring
    rw [hns]
    have hne : (Real.pi * (ε ^ 2 + (E - E₀) ^ 2)) ≠ 0 := by positivity
    field_simp
    ring
  have hnormbd : ∀ E : ℝ,
      ‖((ρ E : ℝ) : ℂ) / (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))‖
        ≤ ε⁻¹ * |ρ E| := by
    intro E
    have hw : (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))
        = ⟨E₀ - E, ε⟩ := by
      apply Complex.ext <;> simp
    rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hden : ε ≤ ‖(⟨E₀ - E, ε⟩ : ℂ)‖ := by
      rw [Complex.norm_def, Complex.normSq_apply]
      have h1 : ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      rw [h1]
      refine Real.sqrt_le_sqrt ?_
      simp
      nlinarith [sq_nonneg (E₀ - E)]
    have hpos : (0 : ℝ) < ‖(⟨E₀ - E, ε⟩ : ℂ)‖ := lt_of_lt_of_le hε hden
    rw [div_le_iff₀ hpos, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith [abs_nonneg (ρ E)]
  have hae : AEStronglyMeasurable
      (fun E : ℝ => ((ρ E : ℝ) : ℂ) / (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ)))
      (volume : Measure ℝ) := by
    have hnum : AEMeasurable (fun E : ℝ => ((ρ E : ℝ) : ℂ)) (volume : Measure ℝ) :=
      Complex.measurable_ofReal.comp_aemeasurable hρ.aemeasurable
    have hden : Measurable
        (fun E : ℝ => (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ))) := by
      fun_prop
    exact (hnum.div hden.aemeasurable).aestronglyMeasurable
  have hint : Integrable
      (fun E : ℝ => ((ρ E : ℝ) : ℂ) / (((E₀ : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * Complex.I - ((E : ℝ) : ℂ)))
      (volume : Measure ℝ) :=
    MeasureTheory.Integrable.mono' ((hρ.abs).const_mul ε⁻¹) hae
      (Filter.Eventually.of_forall hnormbd)
  have hPint : Integrable (fun E : ℝ => halfPlanePoisson ε (E - E₀) * ρ E)
      (volume : Measure ℝ) := by
    have hbdd : ∀ E : ℝ, ‖halfPlanePoisson ε (E - E₀)‖ ≤ 1 / (Real.pi * ε) := by
      intro E
      rw [Real.norm_eq_abs, abs_of_nonneg (halfPlanePoisson_pos hε _).le]
      exact halfPlanePoisson_le hε _
    exact hρ.bdd_mul (c := 1 / (Real.pi * ε))
      (((continuous_halfPlanePoisson hε).comp (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  rw [levelSelfEnergy, ← RCLike.im_eq_complex_im, ← integral_im hint, RCLike.im_eq_complex_im,
    funext hpt, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]

/-- **Fermi's golden rule, energy-domain (Weisskopf–Wigner) form.**  The decay rate is minus twice
the boundary value of the imaginary part of the second-order self-energy. -/
theorem tendsto_levelSelfEnergy_rate {ρ : ℝ → ℝ} {E₀ : ℝ}
    (hρ : Integrable ρ (volume : Measure ℝ)) (hc : ContinuousAt ρ E₀) :
    Filter.Tendsto (fun ε : ℝ => -2 * (levelSelfEnergy ρ E₀ ε).im)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (2 * Real.pi * ρ E₀)) := by
  have h := (tendsto_halfPlanePoisson_density hρ hc).const_mul (2 * Real.pi)
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [im_levelSelfEnergy hρ hε E₀]
  ring

/-- **The two faces of Fermi's golden rule agree.**  The time-domain rate — the slope of the
first-order transition probability — and the energy-domain rate — minus twice the boundary
imaginary part of the self-energy — are the same number `2 π ρ(E₀)`. -/
theorem goldenRule_rate_agreement {ρ : ℝ → ℝ} {E₀ : ℝ} (hρ : Integrable ρ (volume : Measure ℝ))
    (hc : ContinuousAt ρ E₀) :
    Filter.Tendsto (fun t : ℝ => (∫ E : ℝ, goldenRuleKernel t (E - E₀) * ρ E) / t)
        Filter.atTop (nhds (2 * Real.pi * ρ E₀))
      ∧ Filter.Tendsto (fun ε : ℝ => -2 * (levelSelfEnergy ρ E₀ ε).im)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (2 * Real.pi * ρ E₀)) :=
  ⟨tendsto_goldenRuleKernel_density hρ hc, tendsto_levelSelfEnergy_rate hρ hc⟩

end GaloisForLFunctions.HTGeometry
