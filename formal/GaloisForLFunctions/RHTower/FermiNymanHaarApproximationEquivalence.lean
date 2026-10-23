import GaloisForLFunctions.RHTower.FermiNymanWitnessSelfSimilarityCriterion
import GaloisForLFunctions.RHTower.FermiNymanBeurlingHaarTarget

/-!
# The dyadic Haar approximation criterion is exactly the Riemann hypothesis

For the alternating Nyman–Beurling system `φ_a(t) = {1/(at)} − 2{1/(2at)}` (`a ≥ 1`) on `(0,1]` and
the dyadic Haar target `h = −1_{(0,1/2]} + 1_{(1/2,1]}`, the corpus proves
`h ∈ closure span{φ_a} ⟹ RH` (`riemannHypothesis_of_dyadicHaar_approximable`).  This module proves
the converse, so that the producer target of the physical-model route is exactly the Riemann
hypothesis and not stronger.

**Mechanism.**  Write `W` for the square-integrable witnesses (measurable `w` on `(0,1]` with
`∫ φ_a w̄ = 0` for all `a ≥ 1`, no continuity).  Hilbert-space duality gives
`closure span{φ_a} = W^⊥`, so it suffices to show `h ⟂ W` under RH.  The corpus's criterion
`riemannHypothesis_iff_fermiNymanWitness_selfSimilar` needs continuous witnesses.  The bridge is the
*dilation average*

`w_δ(t) = δ⁻¹ ∫_1^{1+δ} w(t/μ) dμ = δ⁻¹ t ∫_{t/(1+δ)}^{t} w(u) u⁻² du`,

which is a continuous square-integrable witness for every measurable square-integrable witness `w`
(the witness class is invariant under every dilation `w ↦ w(·/μ)`, `μ ≥ 1`, and the second form is a
primitive).  Under RH, `w_δ` is dyadically self-similar, and `h` is orthogonal to every self-similar
function, so `⟨h, w_δ⟩ = 0`.  By Fubini `⟨h, w_δ⟩ = δ⁻¹ ∫_1^{1+δ} F(μ) dμ` with
`F(μ) = ∫_0^1 h(t) w̄(t/μ) dt`, and `F` is right-continuous at `1` by dominated convergence, so
`⟨h, w⟩ = F(1) = 0`.

The dilation average is unconditional: it turns every measurable square-integrable witness into a
continuous one, so every rigidity theorem of the corpus stated for continuous witnesses extends to
measurable witnesses.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

/-! ## Measurable square-integrable witnesses and dilations -/

/-- A measurable square-integrable witness of the alternating system (no continuity assumed). -/
structure IsL2FermiWitness (w : ℝ → ℂ) : Prop where
  measurable : Measurable w
  sq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)
  orth : ∀ a : ℝ, 1 ≤ a → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w t) = 0

theorem IsFermiNymanWitness.isL2_of_measurable {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    (hm : Measurable w) : IsL2FermiWitness w :=
  ⟨hm, hw.2.1, hw.2.2⟩

/-- The generators transform exactly under dilation. -/
theorem fermiNymanGen_mul_div (a : ℝ) {μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) :
    fermiNymanGen (a * μ) (t / μ) = fermiNymanGen a t := by
  unfold fermiNymanGen nymanGen
  have h1 : 1 / (a * μ * (t / μ)) = 1 / (a * t) := by
    congr 1
    field_simp
  have h2 : 1 / (2 * (a * μ) * (t / μ)) = 1 / (2 * a * t) := by
    congr 1
    field_simp
  rw [h1, h2]

/-- Dilation of the unit interval: `∫_0^1 f(t/μ) dt = μ ∫_0^{1/μ} f`. -/
theorem integral_Ioc_comp_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    {μ : ℝ} (hμ : 0 < μ) :
    (∫ t in Ioc (0 : ℝ) 1, f (t / μ)) = μ • ∫ u in Ioc (0 : ℝ) (1 / μ), f u := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / μ)]
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) f
    (by positivity : (1 / μ : ℝ) ≠ 0)
  simp only [mul_zero, mul_one] at h
  rw [show (fun t : ℝ => f (t / μ)) = fun t => f (1 / μ * t) by funext t; ring_nf, h]
  simp

/-- Square-integrability on `(0,1]` transports along dilations `t ↦ t/μ`, `μ ≥ 1`. -/
theorem integrableOn_comp_div_of_integrableOn {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 1))
    {μ : ℝ} (hμ : 1 ≤ μ) : IntegrableOn (fun t => f (t / μ)) (Ioc 0 1) := by
  have hμ0 : 0 < μ := by linarith
  have h1 : IntervalIntegrable f volume 0 (1 / μ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact hf.mono_set (Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ))
  have h2 := h1.comp_mul_left (c := 1 / μ) (by simp) (by simp)
  have e0 : (0 : ℝ) / (1 / μ) = 0 := by simp
  have e1 : (1 / μ : ℝ) / (1 / μ) = 1 := div_self (by positivity)
  rw [e0, e1, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h2
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioc
  simp only; ring_nf

/-- **General dilation invariance.**  A square-integrable witness stays orthogonal to every
generator after any dilation `t ↦ t/μ` with `μ ≥ 1`. -/
theorem IsL2FermiWitness.integral_gen_mul_conj_comp_div {w : ℝ → ℂ} (hw : IsL2FermiWitness w)
    {a μ : ℝ} (ha : 1 ≤ a) (hμ : 1 ≤ μ) :
    ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w (t / μ)) = 0 := by
  have hμ0 : 0 < μ := by linarith
  have ha0 : 0 < a := by linarith
  have hpt : ∀ t : ℝ, fermiNymanGen a t = fermiNymanGen (a * μ) (t / μ) := fun t =>
    (fermiNymanGen_mul_div a hμ0.ne' t).symm
  have hstep : (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w (t / μ))) =
      μ • ∫ u in Ioc (0 : ℝ) (1 / μ), fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u) := by
    rw [← integral_Ioc_comp_div (fun u => fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u)) hμ0]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [hpt t]
  have hsupp : (∫ u in Ioc (0 : ℝ) 1, fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u)) =
      ∫ u in Ioc (0 : ℝ) (1 / μ), fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ)) (fun u hu => ?_)
    rcases hu with ⟨hu1, hu2⟩
    simp only [mem_Ioc, not_and, not_le] at hu2
    have hlt : 1 / μ < u := hu2 hu1.1
    rw [fermiNymanGen_eq_zero_of_inv_lt (by positivity) (lt_of_le_of_lt ?_ hlt), zero_mul]
    rw [div_le_div_iff₀ (by positivity) hμ0]
    nlinarith
  rw [hstep, ← hsupp, hw.orth (a * μ) (by nlinarith), smul_zero]

/-- The continuous witness class is invariant under every dilation `t ↦ t/μ`, `μ ≥ 1`
(generalising the dyadic case `halfDilate`). -/
theorem IsFermiNymanWitness.dilate {w : ℝ → ℂ} (hw : IsFermiNymanWitness w) {μ : ℝ} (hμ : 1 ≤ μ) :
    IsFermiNymanWitness (fun t => w (t / μ)) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨hc, hsq, horth⟩ := hw
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · refine hc.comp (continuousOn_id.div_const μ) (fun t ht => ⟨?_, ?_⟩)
    · show 0 < t / μ; exact div_pos ht.1 hμ0
    · show t / μ ≤ 1
      rw [div_le_one hμ0]; linarith [ht.2]
  · exact integrableOn_comp_div_of_integrableOn hsq hμ
  · have hpt : ∀ t : ℝ, fermiNymanGen a t = fermiNymanGen (a * μ) (t / μ) := fun t =>
      (fermiNymanGen_mul_div a hμ0.ne' t).symm
    have hstep : (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w (t / μ))) =
        μ • ∫ u in Ioc (0 : ℝ) (1 / μ), fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u) := by
      rw [← integral_Ioc_comp_div (fun u => fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u)) hμ0]
      refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
      simp only [hpt t]
    have hsupp : (∫ u in Ioc (0 : ℝ) 1, fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u)) =
        ∫ u in Ioc (0 : ℝ) (1 / μ), fermiNymanGen (a * μ) u * (starRingEnd ℂ) (w u) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
        (Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ)) (fun u hu => ?_)
      rcases hu with ⟨hu1, hu2⟩
      simp only [mem_Ioc, not_and, not_le] at hu2
      have hlt : 1 / μ < u := hu2 hu1.1
      rw [fermiNymanGen_eq_zero_of_inv_lt (by positivity) (lt_of_le_of_lt ?_ hlt), zero_mul]
      rw [div_le_div_iff₀ (by positivity) hμ0]
      nlinarith
    rw [hstep, ← hsupp, horth (a * μ) (by nlinarith), smul_zero]

/-! ## The dilation average -/

/-- The dilation average `w_δ(t) = δ⁻¹ ∫_1^{1+δ} w(t/μ) dμ`. -/
def haarDilationAverage (δ : ℝ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  (δ : ℂ)⁻¹ * ∫ μ in Icc (1 : ℝ) (1 + δ), w (t / μ)

theorem measurable_comp_div_prod {w : ℝ → ℂ} (hw : Measurable w) :
    Measurable (fun p : ℝ × ℝ => (starRingEnd ℂ) (w (p.1 / p.2))) :=
  Complex.continuous_conj.measurable.comp (hw.comp (measurable_fst.div measurable_snd))

/-- Pairing of a bounded measurable `g` with `w(·/μ)`: the integral over `(0,1]` is bounded by
`B · μ · ∫_0^1 ‖w‖`. -/
theorem integral_norm_mul_comp_div_le {g w : ℝ → ℂ} {B : ℝ} (hgB : ∀ t, ‖g t‖ ≤ B)
    (hwi : IntegrableOn w (Ioc 0 1)) {μ : ℝ} (hμ : 1 ≤ μ) :
    (∫ t in Ioc (0 : ℝ) 1, ‖g t * (starRingEnd ℂ) (w (t / μ))‖) ≤
      B * μ * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := by
  have hμ0 : 0 < μ := by linarith
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hgB 0)
  have hint : IntegrableOn (fun t => ‖w (t / μ)‖) (Ioc 0 1) :=
    integrableOn_comp_div_of_integrableOn hwi.norm hμ
  calc (∫ t in Ioc (0 : ℝ) 1, ‖g t * (starRingEnd ℂ) (w (t / μ))‖)
      ≤ ∫ t in Ioc (0 : ℝ) 1, B * ‖w (t / μ)‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          (hint.const_mul B) (Eventually.of_forall fun t => ?_)
        simp only [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hgB t) (norm_nonneg _)
    _ = B * (μ * ∫ u in Ioc (0 : ℝ) (1 / μ), ‖w u‖) := by
        rw [integral_const_mul, integral_Ioc_comp_div (fun u => ‖w u‖) hμ0, smul_eq_mul]
    _ ≤ B * (μ * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hμ0.le) hB
        refine setIntegral_mono_set hwi.norm (Eventually.of_forall fun t => norm_nonneg _)
          (Eventually.of_forall ?_)
        exact Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ)
    _ = B * μ * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := by ring

/-- Joint integrability of `(t, μ) ↦ g(t) w̄(t/μ)` on `(0,1] × [1, 1+δ]`. -/
theorem integrable_prod_mul_conj_comp_div {g w : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ t, ‖g t‖ ≤ B) (hw : Measurable w) (hwi : IntegrableOn w (Ioc 0 1)) (δ : ℝ) :
    Integrable (fun p : ℝ × ℝ => g p.1 * (starRingEnd ℂ) (w (p.1 / p.2)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Icc (1 : ℝ) (1 + δ)))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => g p.1 * (starRingEnd ℂ) (w (p.1 / p.2))) :=
    (hg.comp measurable_fst).mul (measurable_comp_div_prod hw)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun μ hμ => ?_
    have hμ1 : 1 ≤ μ := hμ.1
    have hint : IntegrableOn (fun t => ‖w (t / μ)‖) (Ioc 0 1) :=
      integrableOn_comp_div_of_integrableOn hwi.norm hμ1
    refine (hint.const_mul B).mono' ((hg.mul (Complex.continuous_conj.measurable.comp
      (hw.comp (measurable_id.div_const μ)))).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hgB t) (norm_nonneg _)
  · have hsm : StronglyMeasurable (fun q : ℝ × ℝ => ‖g q.2 * (starRingEnd ℂ) (w (q.2 / q.1))‖) :=
      ((hg.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp
        (hw.comp (measurable_snd.div measurable_fst)))).norm.stronglyMeasurable
    have hsm' := hsm.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
    refine (integrable_const (B * (1 + δ) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖)).mono'
      hsm'.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun μ hμ => ?_
    have hμ1 : 1 ≤ μ := hμ.1
    have hB : 0 ≤ B := le_trans (norm_nonneg _) (hgB 0)
    have hw1 : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := integral_nonneg fun t => norm_nonneg _
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    calc (∫ t in Ioc (0 : ℝ) 1, ‖g t * (starRingEnd ℂ) (w (t / μ))‖)
        ≤ B * μ * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := integral_norm_mul_comp_div_le hgB hwi hμ1
      _ ≤ B * (1 + δ) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ := by
          gcongr
          exact hμ.2

/-- **Fubini for the dilation average.**  Pairing a bounded measurable `g` with `w_δ` averages the
pairings with the dilates `w(·/μ)`. -/
theorem integral_mul_conj_dilationAverage {g w : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ t, ‖g t‖ ≤ B) (hw : Measurable w) (hwi : IntegrableOn w (Ioc 0 1)) (δ : ℝ) :
    (∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (haarDilationAverage δ w t)) =
      (δ : ℂ)⁻¹ * ∫ μ in Icc (1 : ℝ) (1 + δ),
        ∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w (t / μ)) := by
  have hpt : ∀ t, g t * (starRingEnd ℂ) (haarDilationAverage δ w t) =
      (δ : ℂ)⁻¹ * ∫ μ in Icc (1 : ℝ) (1 + δ), g t * (starRingEnd ℂ) (w (t / μ)) := by
    intro t
    unfold haarDilationAverage
    rw [map_mul, map_inv₀, Complex.conj_ofReal, ← integral_conj, integral_const_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_prod_mul_conj_comp_div hg hgB hw hwi δ)

/-- The dilation average of a square-integrable witness is orthogonal to every generator. -/
theorem IsL2FermiWitness.integral_gen_mul_conj_dilationAverage {w : ℝ → ℂ}
    (hw : IsL2FermiWitness w) (δ : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (haarDilationAverage δ w t) = 0 := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm (hw.measurable.aestronglyMeasurable)).mpr hw.sq).integrable
      (by norm_num)
  rw [integral_mul_conj_dilationAverage (measurable_fermiNymanGen a) (norm_fermiNymanGen_le a)
    hw.measurable hwi δ]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℂ)) (fun μ hμ =>
    hw.integral_gen_mul_conj_comp_div ha hμ.1), integral_zero, mul_zero]

/-! ## The dilation average as a primitive: continuity -/

/-- Pointwise form of the inversion `μ = 1/x` inside the dilation average. -/
theorem dilationAverage_inversion_integrand {w : ℝ → ℂ} {δ t x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        (Icc (1 : ℝ) (1 + δ)).indicator (fun y => w (t / y)) (x ^ (-1 : ℝ)) =
      (Icc (1 / (1 + δ)) 1).indicator (fun x : ℝ => ((x ^ 2)⁻¹ : ℝ) • w (t * x)) x := by
  have hx' : x ≠ 0 := hx.ne'
  have h1 : (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) = (x ^ 2)⁻¹ := by
    rw [abs_neg, abs_one, one_mul, show ((-1 : ℝ) - 1) = -(2 : ℕ) by norm_num,
      Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [h1, Real.rpow_neg_one]
  have hmem : x⁻¹ ∈ Icc (1 : ℝ) (1 + δ) ↔ x ∈ Icc (1 / (1 + δ)) 1 := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (one_le_inv₀ hx).mp h1⟩
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left h2 hx.le
      rwa [mul_inv_cancel₀ hx'] at this
    · rintro ⟨h1, h2⟩
      refine ⟨(one_le_inv₀ hx).mpr h2, ?_⟩
      rw [inv_le_comm₀ hx (by linarith : (0 : ℝ) < 1 + δ), inv_eq_one_div]
      exact h1
  by_cases hin : x ∈ Icc (1 / (1 + δ)) 1
  · rw [indicator_of_mem hin, indicator_of_mem (hmem.mpr hin), div_inv_eq_mul]
  · rw [indicator_of_notMem hin, indicator_of_notMem (fun h => hin (hmem.mp h)), smul_zero]

/-- The inversion `μ = 1/x` turns the dilation average into an integral over `[1/(1+δ), 1]`. -/
theorem integral_Icc_comp_div_eq_inversion {w : ℝ → ℂ} {δ t : ℝ} (hδ : 0 < δ) :
    (∫ μ in Icc (1 : ℝ) (1 + δ), w (t / μ)) =
      ∫ x in Icc (1 / (1 + δ)) 1, ((x ^ 2)⁻¹ : ℝ) • w (t * x) := by
  have hA := integral_comp_rpow_Ioi (fun y : ℝ => (Icc (1 : ℝ) (1 + δ)).indicator
    (fun y => w (t / y)) y) (p := -1) (by norm_num)
  have hR : (∫ y in Ioi (0 : ℝ), (Icc (1 : ℝ) (1 + δ)).indicator (fun y => w (t / y)) y) =
      ∫ μ in Icc (1 : ℝ) (1 + δ), w (t / μ) := by
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (show Icc (1 : ℝ) (1 + δ) ⊆ Ioi 0 from
        fun y hy => lt_of_lt_of_le one_pos hy.1)]
  have hL : (∫ x in Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
      (Icc (1 : ℝ) (1 + δ)).indicator (fun y => w (t / y)) (x ^ (-1 : ℝ))) =
      ∫ x in Icc (1 / (1 + δ)) 1, ((x ^ 2)⁻¹ : ℝ) • w (t * x) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
      dilationAverage_inversion_integrand hδ hx),
      integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (show Icc (1 / (1 + δ)) (1 : ℝ) ⊆ Ioi 0 from
        fun y hy => lt_of_lt_of_le (by positivity) hy.1)]
  rw [← hR, ← hA, hL]

/-- The dilation average is `δ⁻¹ t ∫_{t/(1+δ)}^{t} w(u) u⁻² du`. -/
theorem integral_Icc_comp_div_eq_primitive {w : ℝ → ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    (∫ μ in Icc (1 : ℝ) (1 + δ), w (t / μ)) =
      (t : ℂ) * ∫ u in Ioc (t / (1 + δ)) t, w u / (u : ℂ) ^ 2 := by
  rw [integral_Icc_comp_div_eq_inversion hδ, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by rw [div_le_one (by linarith)]; linarith)]
  have hcongr : ∀ x : ℝ, ((x ^ 2)⁻¹ : ℝ) • w (t * x) =
      (fun u : ℝ => (((u / t) ^ 2)⁻¹ : ℝ) • w u) (t * x) := by
    intro x
    simp only [mul_div_cancel_left₀ x ht.ne']
  simp_rw [hcongr]
  rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => (((u / t) ^ 2)⁻¹ : ℝ) • w u) ht.ne',
    mul_one, show t * (1 / (1 + δ)) = t / (1 + δ) by ring,
    intervalIntegral.integral_of_le (by rw [div_le_iff₀ (by linarith)]; nlinarith),
    ← integral_const_mul]
  rw [Complex.real_smul]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  have hu0 : (u : ℂ) ≠ 0 := by
    have : 0 < u := lt_trans (by positivity) hu.1
    exact_mod_cast this.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_div]
  field_simp

/-- `u ↦ w(u)/u²` is interval integrable on `[η, 1]` for every `η > 0`. -/
theorem intervalIntegrable_div_sq {w : ℝ → ℂ} (hw : Measurable w) (hwi : IntegrableOn w (Ioc 0 1))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    IntervalIntegrable (fun u : ℝ => w u / (u : ℂ) ^ 2) volume η 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hη1]
  have hmeas : Measurable (fun u : ℝ => w u / (u : ℂ) ^ 2) :=
    hw.div (Complex.measurable_ofReal.pow_const 2)
  refine ((hwi.mono_set (Ioc_subset_Ioc_left hη.le)).norm.const_mul (η ^ 2)⁻¹).mono'
    hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have hu : η < u := hu.1
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- **Continuity.**  The dilation average of an integrable function is continuous on `(0,1]`. -/
theorem continuousOn_dilationAverage {w : ℝ → ℂ} (hw : Measurable w)
    (hwi : IntegrableOn w (Ioc 0 1)) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (haarDilationAverage δ w) (Ioc 0 1) := by
  set P : ℝ → ℂ := fun x => ∫ u in (1 : ℝ)..x, w u / (u : ℂ) ^ 2 with hP
  have hδ1 : 0 < 1 + δ := by linarith
  -- the average as a primitive
  have hform : ∀ t ∈ Ioc (0 : ℝ) 1, haarDilationAverage δ w t =
      (δ : ℂ)⁻¹ * ((t : ℂ) * (P t - P (t / (1 + δ)))) := by
    intro t ht
    unfold haarDilationAverage
    rw [integral_Icc_comp_div_eq_primitive hδ ht.1]
    congr 2
    have h1 : IntervalIntegrable (fun u : ℝ => w u / (u : ℂ) ^ 2) volume 1 t :=
      (intervalIntegrable_div_sq hw hwi ht.1 ht.2).symm
    have h2 : IntervalIntegrable (fun u : ℝ => w u / (u : ℂ) ^ 2) volume 1 (t / (1 + δ)) :=
      (intervalIntegrable_div_sq hw hwi (div_pos ht.1 hδ1)
        (by rw [div_le_one hδ1]; linarith [ht.2])).symm
    rw [hP]
    simp only
    rw [intervalIntegral.integral_interval_sub_left h1 h2,
      intervalIntegral.integral_of_le (by rw [div_le_iff₀ hδ1]; nlinarith [ht.1])]
  -- continuity of the primitive on `[η, 1]`
  have hPcont : ∀ η : ℝ, 0 < η → η ≤ 1 → ContinuousOn P (Icc η 1) := by
    intro η hη hη1
    have := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_div_sq hw hwi hη hη1) (a := 1) (by simp [hη1])
    rwa [uIcc_of_le hη1] at this
  refine fun t₀ ht₀ => ?_
  have hη : 0 < t₀ / 2 := by linarith [ht₀.1]
  have hcont : ContinuousOn (fun t : ℝ => (δ : ℂ)⁻¹ * ((t : ℂ) * (P t - P (t / (1 + δ)))))
      (Icc (t₀ / 2) 1) := by
    have hP1 : ContinuousOn (fun t : ℝ => P t) (Icc (t₀ / 2) 1) :=
      (hPcont (t₀ / 2) hη (by linarith [ht₀.2])).mono (fun x hx => hx)
    have hP2 : ContinuousOn (fun t : ℝ => P (t / (1 + δ))) (Icc (t₀ / 2) 1) := by
      refine (hPcont (t₀ / 2 / (1 + δ)) (by positivity) ?_).comp
        (continuousOn_id.div_const (1 + δ)) (fun x hx => ⟨?_, ?_⟩)
      · rw [div_le_one hδ1]; linarith [ht₀.2]
      · show t₀ / 2 / (1 + δ) ≤ x / (1 + δ)
        exact div_le_div_of_nonneg_right hx.1 hδ1.le
      · show x / (1 + δ) ≤ 1
        rw [div_le_one hδ1]; linarith [hx.2]
    exact continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul (hP1.sub hP2))
  have hmem : Icc (t₀ / 2) 1 ∈ 𝓝[Ioc (0 : ℝ) 1] t₀ := by
    rw [mem_nhdsWithin]
    exact ⟨Ioi (t₀ / 2), isOpen_Ioi, by simp; linarith [ht₀.1],
      fun x hx => ⟨le_of_lt hx.1, hx.2.2⟩⟩
  have hwithin : ContinuousWithinAt (fun t : ℝ => (δ : ℂ)⁻¹ * ((t : ℂ) * (P t - P (t / (1 + δ)))))
      (Ioc (0 : ℝ) 1) t₀ :=
    (hcont t₀ ⟨by linarith [ht₀.1], ht₀.2⟩).mono_of_mem_nhdsWithin hmem
  exact hwithin.congr (fun t ht => hform t ht) (hform t₀ ht₀)

/-! ## Square-integrability of the dilation average -/

theorem enorm_normSq (z : ℂ) : ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := by
  rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Cauchy–Schwarz for lower integrals: `(∫⁻_S f)² ≤ (∫⁻_S f²) · |S|`. -/
theorem lintegral_sq_le_lintegral_sq_mul_measure {f : ℝ → ℝ≥0∞} (hf : Measurable f) (S : Set ℝ) :
    (∫⁻ x in S, f x) ^ 2 ≤ (∫⁻ x in S, f x ^ 2) * volume S := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) Real.HolderConjugate.two_two
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h
  have h2 := ENNReal.pow_le_pow_left h (n := 2)
  rw [mul_pow, show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
    ENNReal.rpow_inv_natCast_pow (by norm_num), ENNReal.rpow_inv_natCast_pow (by norm_num)] at h2
  calc (∫⁻ x in S, f x) ^ 2 ≤ (∫⁻ x in S, f x ^ (2 : ℝ)) * volume S := h2
    _ = (∫⁻ x in S, f x ^ 2) * volume S := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [ENNReal.rpow_two]

/-- Dilation of the unit interval for lower integrals. -/
theorem lintegral_Ioc_comp_div (f : ℝ → ℝ≥0∞) (hf : Measurable f) {μ : ℝ} (hμ : 0 < μ) :
    ∫⁻ t in Ioc (0 : ℝ) 1, f (t / μ) = ENNReal.ofReal μ * ∫⁻ u in Ioc (0 : ℝ) (1 / μ), f u := by
  have hind : ∀ t : ℝ, (Ioc (0 : ℝ) 1).indicator (fun t => f (t / μ)) t =
      (Ioc (0 : ℝ) (1 / μ)).indicator f (μ⁻¹ * t) := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem ht, indicator_of_mem]
      · simp only [div_eq_inv_mul]
      · refine ⟨by have := ht.1; positivity, ?_⟩
        rw [one_div]
        exact mul_le_of_le_one_right (by positivity) ht.2
    · rw [indicator_of_notMem ht, indicator_of_notMem]
      intro h
      apply ht
      refine ⟨?_, ?_⟩
      · have := h.1
        have hμi : 0 < μ⁻¹ := by positivity
        nlinarith [mul_pos hμi (lt_of_not_ge (fun hh => by nlinarith : ¬ t ≤ 0))]
      · have := h.2
        rw [one_div] at this
        have hμi : 0 < μ⁻¹ := by positivity
        exact le_of_mul_le_mul_left (by rwa [mul_one]) hμi
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  simp_rw [hind]
  rw [← lintegral_map (hf.indicator measurableSet_Ioc) (measurable_const_mul μ⁻¹),
    Real.map_volume_mul_left (inv_ne_zero hμ.ne'), lintegral_smul_measure, inv_inv,
    abs_of_pos hμ, smul_eq_mul]

/-- Pointwise bound for the dilation average. -/
theorem enorm_dilationAverage_le {w : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ‖haarDilationAverage δ w t‖ₑ ≤ (ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ := by
  unfold haarDilationAverage
  rw [enorm_mul]
  have h1 : ‖(δ : ℂ)⁻¹‖ₑ = (ENNReal.ofReal δ)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hδ.le,
      ENNReal.ofReal_inv_of_pos hδ]
  rw [h1]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

/-- **Square-integrability.**  The dilation average of a square-integrable function is
square-integrable on `(0,1]`. -/
theorem integrableOn_normSq_dilationAverage {w : ℝ → ℂ} (hw : Measurable w)
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t => ‖haarDilationAverage δ w t‖ ^ 2) (Ioc 0 1) := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mpr hsq).integrable (by norm_num)
  have hδ1 : (0 : ℝ) < 1 + δ := by linarith
  refine ⟨((continuousOn_dilationAverage hw hwi hδ).aestronglyMeasurable
    measurableSet_Ioc).norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [enorm_normSq]
  -- the finite energy of `w`
  have hC : (∫⁻ t in Ioc (0 : ℝ) 1, ‖w t‖ₑ ^ 2) < ⊤ := by
    have := hsq.2
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [enorm_normSq] using this
  set C : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) 1, ‖w t‖ₑ ^ 2 with hCdef
  have hmeas2 : Measurable (fun p : ℝ × ℝ => ‖w (p.1 / p.2)‖ₑ ^ 2) :=
    ((hw.comp (measurable_fst.div measurable_snd)).enorm).pow_const 2
  -- pointwise square bound
  have hpt : ∀ t : ℝ, ‖haarDilationAverage δ w t‖ₑ ^ 2 ≤
      (ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2 := by
    intro t
    have hf : Measurable (fun μ : ℝ => ‖w (t / μ)‖ₑ) :=
      (hw.comp (measurable_const.div measurable_id)).enorm
    calc ‖haarDilationAverage δ w t‖ₑ ^ 2
        ≤ ((ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ) ^ 2 :=
          ENNReal.pow_le_pow_left (enorm_dilationAverage_le hδ t)
      _ = (ENNReal.ofReal δ)⁻¹ ^ 2 * (∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ) ^ 2 := by
          rw [mul_pow]
      _ ≤ (ENNReal.ofReal δ)⁻¹ ^ 2 *
          ((∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2) * volume (Icc (1 : ℝ) (1 + δ))) := by
          gcongr
          exact lintegral_sq_le_lintegral_sq_mul_measure hf _
      _ = (ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2 := by
          rw [Real.volume_Icc, show (1 + δ - 1 : ℝ) = δ by ring, pow_two,
            mul_comm (∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2) (ENNReal.ofReal δ), mul_assoc,
            ← mul_assoc (ENNReal.ofReal δ)⁻¹ (ENNReal.ofReal δ), ENNReal.inv_mul_cancel
            (by simpa using hδ) ENNReal.ofReal_ne_top, one_mul]
  calc (∫⁻ t in Ioc (0 : ℝ) 1, ‖haarDilationAverage δ w t‖ₑ ^ 2)
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (ENNReal.ofReal δ)⁻¹ *
          ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2 := lintegral_mono hpt
    _ = (ENNReal.ofReal δ)⁻¹ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ‖w (t / μ)‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hδ))
    _ = (ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ),
          ∫⁻ t in Ioc (0 : ℝ) 1, ‖w (t / μ)‖ₑ ^ 2 := by
        congr 1
        exact lintegral_lintegral_swap hmeas2.aemeasurable
    _ ≤ (ENNReal.ofReal δ)⁻¹ * ∫⁻ μ in Icc (1 : ℝ) (1 + δ), ENNReal.ofReal (1 + δ) * C := by
        refine mul_le_mul' le_rfl (setLIntegral_mono measurable_const fun μ hμ => ?_)
        have hμ0 : 0 < μ := lt_of_lt_of_le one_pos hμ.1
        rw [lintegral_Ioc_comp_div (fun u => ‖w u‖ₑ ^ 2) (hw.enorm.pow_const 2) hμ0]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal hμ.2) ?_
        exact lintegral_mono_set (Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ.1))
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by simpa using hδ))
          (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC) ENNReal.ofReal_lt_top)

/-- **The dilation average of a square-integrable witness is a continuous witness.** -/
theorem IsL2FermiWitness.dilationAverage_isFermiNymanWitness {w : ℝ → ℂ}
    (hw : IsL2FermiWitness w) {δ : ℝ} (hδ : 0 < δ) :
    IsFermiNymanWitness (haarDilationAverage δ w) := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  exact ⟨continuousOn_dilationAverage hw.measurable hwi hδ,
    integrableOn_normSq_dilationAverage hw.measurable hw.sq hδ,
    fun a ha => hw.integral_gen_mul_conj_dilationAverage δ ha⟩

/-! ## The Haar function is orthogonal to every self-similar function -/

/-- `∫_0^1 h ḡ = 0` for every integrable dyadically self-similar `g` on `(0,1]`: the self-similar
part of the mass is split equally between `(0,1/2]` and `(1/2,1]`. -/
theorem integral_dyadicHaar_mul_conj_of_selfSimilar {g : ℝ → ℂ} (hg : IntegrableOn g (Ioc 0 1))
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, g (t / 2) = g t) :
    ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (g t) = 0 := by
  set G : ℝ → ℂ := fun t => (starRingEnd ℂ) (g t) with hGdef
  have hG : IntegrableOn G (Ioc 0 1) := by
    refine hg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun t => ?_)
    simp [hGdef]
  have hGs : ∀ t ∈ Ioc (0 : ℝ) 1, G (t / 2) = G t := fun t ht => by simp only [hGdef, hs t ht]
  set I : ℂ := ∫ t in Ioc (0 : ℝ) 1, G t with hI
  set J : ℂ := ∫ t in Ioc (0 : ℝ) (1 / 2), G t with hJ
  set K : ℂ := ∫ t in Ioc (1 / 2 : ℝ) 1, G t with hK
  have hJI : I = (2 : ℝ) • J := by
    rw [hI, hJ, ← integral_Ioc_comp_half G]
    exact (setIntegral_congr_fun measurableSet_Ioc (fun t ht => hGs t ht)).symm
  have hIJK : I = J + K := by
    rw [hI, hJ, hK, ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      exact hG.mono_set (Ioc_subset_Ioc_right (by norm_num))
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      exact hG.mono_set (Ioc_subset_Ioc_left (by norm_num))
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * G t) = -I + 2 * K := by
    have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, dyadicHaar t * G t =
        -G t + 2 * (Ioc (1 / 2 : ℝ) 1).indicator G t := by
      intro t ht
      unfold dyadicHaar
      by_cases h : t ≤ 1 / 2
      · rw [if_pos h, indicator_of_notMem (show t ∉ Ioc (1 / 2 : ℝ) 1 from
          fun h' => by linarith [h'.1])]
        ring
      · rw [if_neg h, indicator_of_mem (show t ∈ Ioc (1 / 2 : ℝ) 1 from ⟨lt_of_not_ge h, ht.2⟩)]
        ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add, integral_neg,
      integral_const_mul, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc (1 / 2 : ℝ) 1 ⊆ Ioc 0 1 from Ioc_subset_Ioc_left (by norm_num))]
    · exact hG.neg
    · exact (hG.indicator measurableSet_Ioc).const_mul 2
  have hKJ : K = J := by
    have h := hJI
    rw [hIJK, Complex.real_smul] at h
    push_cast at h
    linear_combination h
  rw [hsplit, hIJK, hKJ]
  ring

/-! ## Under RH the Haar function is orthogonal to every square-integrable witness -/

/-- Pairing of the Haar function with the dilate `w(·/μ)`, in the form adapted to `μ → 1`. -/
theorem integral_dyadicHaar_mul_conj_comp_div_eq {w : ℝ → ℂ} {μ : ℝ} (hμ : 1 ≤ μ) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w (t / μ))) =
      ∫ u in Ioc (0 : ℝ) 1, (Ioc (0 : ℝ) (1 / μ)).indicator
        (fun u => (μ : ℂ) * (dyadicHaar (μ * u) * (starRingEnd ℂ) (w u))) u := by
  have hμ0 : 0 < μ := by linarith
  have h1 : (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w (t / μ))) =
      ∫ t in Ioc (0 : ℝ) 1, dyadicHaar (μ * (t / μ)) * (starRingEnd ℂ) (w (t / μ)) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [mul_div_cancel₀ t hμ0.ne']
  have hsub : Ioc (0 : ℝ) (1 / μ) ⊆ Ioc 0 1 :=
    Ioc_subset_Ioc_right (by rw [div_le_one hμ0]; exact hμ)
  have hLHS : (∫ u in Ioc (0 : ℝ) (1 / μ), dyadicHaar (μ * u) * (starRingEnd ℂ) (w u)) =
      ∫ u in Ioc (0 : ℝ) 1, (Ioc (0 : ℝ) (1 / μ)).indicator
        (fun u => dyadicHaar (μ * u) * (starRingEnd ℂ) (w u)) u := by
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr hsub]
  rw [h1, integral_Ioc_comp_div (fun u => dyadicHaar (μ * u) * (starRingEnd ℂ) (w u)) hμ0, hLHS,
    Complex.real_smul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
  simp only [indicator]
  split_ifs <;> simp

/-- **Right-continuity at `μ = 1`** of the pairing `μ ↦ ∫_0^1 h(t) w̄(t/μ) dt`, by dominated
convergence. -/
theorem tendsto_integral_dyadicHaar_mul_conj_comp_div {w : ℝ → ℂ} (hw : Measurable w)
    (hwi : IntegrableOn w (Ioc 0 1)) :
    Tendsto (fun μ : ℝ => ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w (t / μ)))
      (𝓝[Ici 1] 1) (𝓝 (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t))) := by
  set Φ : ℝ → ℝ → ℂ := fun μ u => (Ioc (0 : ℝ) (1 / μ)).indicator
    (fun u => (μ : ℂ) * (dyadicHaar (μ * u) * (starRingEnd ℂ) (w u))) u with hΦ
  have hμ1 : ∀ᶠ μ : ℝ in 𝓝[Ici 1] 1, 1 ≤ μ := eventually_mem_nhdsWithin
  have hμ2 : ∀ᶠ μ : ℝ in 𝓝[Ici 1] 1, μ ≤ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num))
  have hcongr : (fun μ : ℝ => ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w (t / μ)))
      =ᶠ[𝓝[Ici 1] 1] fun μ => ∫ u in Ioc (0 : ℝ) 1, Φ μ u := by
    filter_upwards [hμ1] with μ hμ
    exact integral_dyadicHaar_mul_conj_comp_div_eq hμ
  refine Tendsto.congr' hcongr.symm ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u => 3 * ‖w u‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun μ => ?_
    refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact measurable_const.mul ((measurable_dyadicHaar.comp (measurable_const_mul μ)).mul
      (Complex.continuous_conj.measurable.comp hw))
  · filter_upwards [hμ1, hμ2] with μ hμ1 hμ2
    refine Eventually.of_forall fun u => ?_
    simp only [hΦ, indicator]
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_conj, norm_dyadicHaar, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact hwi.norm.const_mul 3
  · have h0 : volume ({1 / 2, 1} : Set ℝ) = 0 := Set.Finite.measure_zero (by simp) _
    have hae : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) 1)), u ∉ ({1 / 2, 1} : Set ℝ) :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr h0)
    rw [ae_restrict_iff' measurableSet_Ioc] at hae ⊢
    filter_upwards [hae] with u hu hu1
    have hu' := hu hu1
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu'
    -- eventually `Φ μ u = μ · h(u) w̄(u)`
    have hev : (fun μ : ℝ => Φ μ u) =ᶠ[𝓝[Ici 1] 1]
        fun μ => (μ : ℂ) * (dyadicHaar u * (starRingEnd ℂ) (w u)) := by
      rcases lt_or_gt_of_ne hu'.1 with hlt | hgt
      · -- `u < 1/2`: for `μ < 1/(2u)` the dilate stays in the lower half
        have hnhds : Iio (1 / (2 * u)) ∈ 𝓝[Ici 1] 1 := by
          refine mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ?_)
          rw [lt_div_iff₀ (by linarith [hu1.1])]
          linarith
        filter_upwards [hμ1, hnhds] with μ hμ hμu
        have hμ0 : 0 < μ := by linarith
        have h2 : μ * (2 * u) < 1 := (lt_div_iff₀ (by linarith [hu1.1] : (0 : ℝ) < 2 * u)).mp hμu
        have hmu : μ * u < 1 / 2 := by linarith
        have hmem : u ∈ Ioc (0 : ℝ) (1 / μ) := by
          refine ⟨hu1.1, ?_⟩
          rw [le_div_iff₀ hμ0]
          linarith
        simp only [hΦ, indicator_of_mem hmem]
        unfold dyadicHaar
        rw [if_pos hmu.le, if_pos hlt.le]
      · -- `1/2 < u < 1`: for `μ < 1/u` the dilate stays in the upper half
        have hu1' : u < 1 := lt_of_le_of_ne hu1.2 hu'.2
        have hnhds : Iio (1 / u) ∈ 𝓝[Ici 1] 1 := by
          refine mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ?_)
          rw [lt_div_iff₀ hu1.1]
          linarith
        filter_upwards [hμ1, hnhds] with μ hμ hμu
        have hμ0 : 0 < μ := by linarith
        have hmu : ¬ μ * u ≤ 1 / 2 := by
          intro h
          nlinarith
        have hmem : u ∈ Ioc (0 : ℝ) (1 / μ) := by
          refine ⟨hu1.1, ?_⟩
          rw [le_div_iff₀ hμ0, mul_comm]
          exact ((lt_div_iff₀ hu1.1).mp hμu).le
        simp only [hΦ, indicator_of_mem hmem]
        unfold dyadicHaar
        rw [if_neg hmu, if_neg (not_le.mpr hgt)]
    refine Tendsto.congr' hev.symm ?_
    have hlim : Tendsto (fun μ : ℝ => (μ : ℂ) * (dyadicHaar u * (starRingEnd ℂ) (w u)))
        (𝓝 1) (𝓝 ((1 : ℝ) * (dyadicHaar u * (starRingEnd ℂ) (w u)))) :=
      (Complex.continuous_ofReal.tendsto 1).mul tendsto_const_nhds
    simp only [Complex.ofReal_one, one_mul] at hlim
    exact tendsto_nhdsWithin_of_tendsto_nhds hlim

/-- **Under RH, the Haar function is orthogonal to every square-integrable witness.** -/
theorem integral_dyadicHaar_mul_conj_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    {w : ℝ → ℂ} (hw : IsL2FermiWitness w) :
    ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t) = 0 := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  set F : ℝ → ℂ := fun μ => ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w (t / μ))
    with hF
  have hF1 : F 1 = ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t) := by
    simp only [hF, div_one]
  -- every dilation average is self-similar, hence orthogonal to `h`
  have hzero : ∀ δ : ℝ, 0 < δ → (∫ μ in Icc (1 : ℝ) (1 + δ), F μ) = 0 := by
    intro δ hδ
    have hwit := hw.dilationAverage_isFermiNymanWitness hδ
    have hss := (riemannHypothesis_iff_fermiNymanWitness_selfSimilar.mp hRH) _ hwit
    have hint : IntegrableOn (haarDilationAverage δ w) (Ioc 0 1) :=
      ((memLp_two_iff_integrable_sq_norm (hwit.1.aestronglyMeasurable measurableSet_Ioc)).mpr
        hwit.2.1).integrable (by norm_num)
    have h0 := integral_dyadicHaar_mul_conj_of_selfSimilar hint hss
    rw [integral_mul_conj_dilationAverage measurable_dyadicHaar (fun t => (norm_dyadicHaar t).le)
      hw.measurable hwi δ] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      exact hδ.ne' (by exact_mod_cast inv_eq_zero.mp h)
    · exact h
  -- integrability of `F` on `[1, 1+δ]`
  have hFint : ∀ δ : ℝ, 0 < δ → IntegrableOn F (Icc 1 (1 + δ)) := by
    intro δ hδ
    have := (integrable_prod_mul_conj_comp_div measurable_dyadicHaar
      (fun t => (norm_dyadicHaar t).le) hw.measurable hwi δ).integral_prod_right
    exact this
  have hcont : Tendsto F (𝓝[Ici 1] 1) (𝓝 (F 1)) := by
    rw [hF1]
    exact tendsto_integral_dyadicHaar_mul_conj_comp_div hw.measurable hwi
  rw [← hF1]
  -- `‖F 1‖ ≤ ‖F 1‖/2`
  by_contra hne
  have hpos : 0 < ‖F 1‖ := norm_pos_iff.mpr hne
  obtain ⟨η, hη, hclose⟩ := Metric.tendsto_nhdsWithin_nhds.mp hcont (‖F 1‖ / 2) (by positivity)
  set δ : ℝ := η / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hbound : ‖∫ μ in Icc (1 : ℝ) (1 + δ), (F 1 - F μ)‖ ≤
      ‖F 1‖ / 2 * volume.real (Icc (1 : ℝ) (1 + δ)) := by
    refine norm_setIntegral_le_of_norm_le_const (by simp) fun μ hμ => ?_
    rw [norm_sub_rev, ← dist_eq_norm]
    refine (hclose (mem_Ici.mpr hμ.1) ?_).le
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hμ.1])]
    linarith [hμ.2]
  rw [integral_sub (integrable_const _) (hFint δ hδ0), hzero δ hδ0, sub_zero, integral_const,
    norm_smul] at hbound
  simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, add_sub_cancel_left,
    ENNReal.toReal_ofReal hδ0.le, Real.norm_of_nonneg hδ0.le] at hbound
  have : ‖F 1‖ ≤ ‖F 1‖ / 2 :=
    le_of_mul_le_mul_left (by linarith [hbound] : δ * ‖F 1‖ ≤ δ * (‖F 1‖ / 2)) hδ0
  linarith

/-! ## Hilbert duality: `RH ⟹ h ∈ closure span{φ_a}` -/

theorem conj_fermiNymanGen (a t : ℝ) : (starRingEnd ℂ) (fermiNymanGen a t) = fermiNymanGen a t := by
  unfold fermiNymanGen nymanGen
  simp only [map_sub, map_mul, Complex.conj_ofReal, map_ofNat]

theorem conj_dyadicHaar (t : ℝ) : (starRingEnd ℂ) (dyadicHaar t) = dyadicHaar t := by
  unfold dyadicHaar
  split_ifs <;> simp

theorem memLp_fermiNymanGen_Ioc (a : ℝ) :
    MemLp (fermiNymanGen a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  haveI : Fact (volume (Ioc (0 : ℝ) 1) < ⊤) := ⟨measure_Ioc_lt_top⟩
  exact MemLp.of_bound (measurable_fermiNymanGen a).aestronglyMeasurable 3
    (Eventually.of_forall (norm_fermiNymanGen_le a))

theorem memLp_dyadicHaar_Ioc : MemLp dyadicHaar 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  haveI : Fact (volume (Ioc (0 : ℝ) 1) < ⊤) := ⟨measure_Ioc_lt_top⟩
  exact MemLp.of_bound measurable_dyadicHaar.aestronglyMeasurable 1
    (Eventually.of_forall fun t => (norm_dyadicHaar t).le)

/-- The generator `φ_a` as an element of `L²(0,1]`. -/
def fermiGenLp (a : ℝ) : Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.toLp (fermiNymanGen a) (memLp_fermiNymanGen_Ioc a)

/-- The dyadic Haar function as an element of `L²(0,1]`. -/
def dyadicHaarLp : Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.toLp dyadicHaar memLp_dyadicHaar_Ioc

/-- The span of the generators `φ_a`, `a ≥ 1`, in `L²(0,1]`. -/
def fermiGenSpan : Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))) :=
  Submodule.span ℂ (fermiGenLp '' Ici 1)

/-- Every element of the orthogonal complement of the generator span is (a.e.) a measurable
square-integrable witness. -/
theorem exists_isL2FermiWitness_of_mem_orthogonal {u : Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))}
    (hu : u ∈ fermiGenSpanᗮ) :
    ∃ w : ℝ → ℂ, IsL2FermiWitness w ∧ (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] w := by
  set w : ℝ → ℂ := (Lp.aestronglyMeasurable u).mk u with hwdef
  have hae : (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] w :=
    (Lp.aestronglyMeasurable u).ae_eq_mk
  have hmeas : Measurable w := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable
  have hmem : MemLp w 2 (volume.restrict (Ioc (0 : ℝ) 1)) := (Lp.memLp u).ae_eq hae
  refine ⟨w, ⟨hmeas, (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mp hmem,
    fun a ha => ?_⟩, hae⟩
  have horth : inner ℂ (fermiGenLp a) u = 0 :=
    (Submodule.mem_orthogonal _ _).mp hu _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rw [L2.inner_def] at horth
  have hgen : (fermiGenLp a : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fermiNymanGen a :=
    MemLp.coeFn_toLp _
  have hval : (∫ t, inner ℂ ((fermiGenLp a : ℝ → ℂ) t) ((u : ℝ → ℂ) t)
      ∂(volume.restrict (Ioc (0 : ℝ) 1))) =
      ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t := by
    refine integral_congr_ae ?_
    filter_upwards [hgen, hae] with t h1 h2
    rw [RCLike.inner_apply, h1, h2, conj_fermiNymanGen, mul_comm]
  rw [hval] at horth
  have hconj : (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w t)) =
      (starRingEnd ℂ) (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [map_mul, conj_fermiNymanGen]
  rw [hconj, horth, map_zero]

/-- **Under RH the Haar function lies in the closed span of the generators.** -/
theorem dyadicHaarLp_mem_closure_fermiGenSpan (hRH : RiemannHypothesis) :
    dyadicHaarLp ∈ closure (fermiGenSpan : Set (Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)))) := by
  rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨w, hw, hae⟩ := exists_isL2FermiWitness_of_mem_orthogonal hu
  rw [L2.inner_def]
  have hh : (dyadicHaarLp : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] dyadicHaar :=
    MemLp.coeFn_toLp _
  have hval : (∫ t, inner ℂ ((u : ℝ → ℂ) t) ((dyadicHaarLp : ℝ → ℂ) t)
      ∂(volume.restrict (Ioc (0 : ℝ) 1))) =
      ∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t) := by
    refine integral_congr_ae ?_
    filter_upwards [hh, hae] with t h1 h2
    rw [RCLike.inner_apply, h1, h2]
  rw [hval]
  exact integral_dyadicHaar_mul_conj_eq_zero_of_riemannHypothesis hRH hw

/-- A finite combination of generators in `L²` is (a.e.) the pointwise combination. -/
theorem coeFn_sum_smul_fermiGenLp {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (s : Finset (Fin n)) :
    ((∑ i ∈ s, c i • fermiGenLp (a i) : Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t => ∑ i ∈ s, c i * fermiNymanGen (a i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (c j • fermiGenLp (a j)) (∑ i ∈ s, c i • fermiGenLp (a i)),
      Lp.coeFn_smul (c j) (fermiGenLp (a j)), MemLp.coeFn_toLp (memLp_fermiNymanGen_Ioc (a j)),
      ih] with t h1 h2 h3 h4
    have h3' : (fermiGenLp (a j) : ℝ → ℂ) t = fermiNymanGen (a j) t := h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h4, Finset.sum_insert hj, smul_eq_mul, h3']

/-- **RH ⟹ the dyadic Haar function is approximable by finite generator combinations.** -/
theorem dyadicHaar_approximable_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
      (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp (dyadicHaarLp_mem_closure_fermiGenSpan hRH)
    (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hb
  choose a ha hga using fun i => (g i).2
  refine ⟨n, c, a, fun i => (ha i), ?_⟩
  have hb' : b = ∑ i ∈ Finset.univ, c i • fermiGenLp (a i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hga i]
  -- identify the distance with the integral
  have hcomb : MemLp (fermiNymanCombination c a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    unfold fermiNymanCombination
    exact memLp_finsetSum Finset.univ (f := fun i => fun t => c i * fermiNymanGen (a i) t)
      (fun i _ => (memLp_fermiNymanGen_Ioc (a i)).const_mul (c i))
  have hdiff : MemLp (fun t => dyadicHaar t - fermiNymanCombination c a t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := memLp_dyadicHaar_Ioc.sub hcomb
  have hnorm : dist dyadicHaarLp b = (eLpNorm (fun t => dyadicHaar t - fermiNymanCombination c a t)
      2 (volume.restrict (Ioc (0 : ℝ) 1))).toReal := by
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub dyadicHaarLp b, MemLp.coeFn_toLp memLp_dyadicHaar_Ioc,
      coeFn_sum_smul_fermiGenLp c a Finset.univ] with t h1 h2 h3
    have h2' : (dyadicHaarLp : ℝ → ℂ) t = dyadicHaar t := h2
    rw [h1, Pi.sub_apply, h2', hb', h3]
    rfl
  rw [hnorm, hdiff.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)] at hdist
  have hint : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2 :=
    integral_nonneg fun t => by positivity
  have h2 : ((∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^
      (2 : ℝ≥0∞).toReal) ^ (2 : ℝ≥0∞).toReal⁻¹) =
      Real.sqrt (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [h2, Real.sqrt_lt_sqrt_iff hint] at hdist
  exact hdist

/-- **The dyadic Haar approximation criterion is exactly the Riemann hypothesis.** -/
theorem riemannHypothesis_iff_dyadicHaar_approximable :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
        (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) < ε :=
  ⟨dyadicHaar_approximable_of_riemannHypothesis, riemannHypothesis_of_dyadicHaar_approximable⟩

end RHTower
