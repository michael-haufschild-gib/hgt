import GaloisForLFunctions.HTGeometry.PositiveWolffMeasure
import GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

/-!
# Positive point configurations with band-limited exponential sums

**Theorem** (`exists_positive_configuration_bandLimited`). For every `ε > 0` and every vertical strip
`x₁ < Re w < x₂` there are countably many points `w_i` in the strip and weights `c_i > 0` with
`Σ c_i < ∞` such that

`Σ_i c_i e^{s w_i} = 0` for every real `s` with `|s| ≥ ε`.

**Proof.** Let `g ≥ 0` be continuous and integrable, and let `W ⊆ ℂ × ℝ` be the open set
`x₁ < Re z < x₂, 0 < c < g(Im z)`. In the sup metric the closed balls of `ℂ × ℝ` are cylinders
`D(a, r) × [c − r, c + r]`, and the Besicovitch covering theorem packs almost all of `W` by disjoint
such balls inside `W`. Integrating `e^{sz}` over a cylinder gives `2r · πr² e^{sa}` (mean value of
`e^{sz}` on a disc, from the power series and the disc moments `∫_D z^k = πr²a^k`). Integrating over
`W` gives, by Fubini, `∫_{x₁}^{x₂} e^{sx} dx · ∫ e^{isy} g(y) dy`. So the centres `a` with weights
`2πr³` reproduce `g` exactly on exponentials (`exists_disc_configuration_of_density`). For
`g(y) = sinc(εy/2)²` the second factor is a multiple of the triangle `max(0, 1 − |s|/ε)`
(`BandLimitedPositiveDensity`), which vanishes for `|s| ≥ ε`.
-/

open MeasureTheory Set Complex Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry.BandLimitedPositiveConfiguration

open GaloisForLFunctions.HTGeometry.PositiveWolffMeasure (setIntegral_closedBall_pow)
open GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

/-! ## The mean value of `e^{sz}` on a disc -/

/-- **Discs.** `∫_{D(a,ρ)} e^{sz} = πρ² e^{sa}`. -/
theorem setIntegral_closedBall_cexp (a : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (s : ℂ) :
    ∫ z in closedBall a ρ, cexp (s * z) = ((Real.pi * ρ ^ 2 : ℝ) : ℂ) * cexp (s * a) := by
  have hser : ∀ z : ℂ, cexp (s * z) = ∑' n : ℕ, s ^ n / n.factorial * z ^ n := by
    intro z
    rw [Complex.exp_eq_exp_ℂ, ← (NormedSpace.expSeries_div_hasSum_exp (s * z)).tsum_eq]
    congr 1; funext n; rw [mul_pow]; ring
  set R := ‖a‖ + ρ with hR
  set V := volume.real (closedBall a ρ) with hV
  have hnorm : ∀ z ∈ closedBall a ρ, ‖z‖ ≤ R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hfin : volume (closedBall a ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hint : ∀ n : ℕ,
      Integrable (fun z : ℂ => s ^ n / n.factorial * z ^ n) (volume.restrict (closedBall a ρ)) :=
    fun n => (Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_closedBall _ _)
  have hbound : ∀ n : ℕ, ∫ z in closedBall a ρ, ‖s ^ n / n.factorial * z ^ n‖ ≤
      V * ((‖s‖ * R) ^ n / n.factorial) := by
    intro n
    have hle : ∀ z ∈ closedBall a ρ, ‖s ^ n / n.factorial * z ^ n‖ ≤ (‖s‖ * R) ^ n / n.factorial := by
      intro z hz
      rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast, mul_pow]
      have hz := hnorm z hz
      have : ‖z‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hz n
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
      exact mul_le_mul_of_nonneg_left this (pow_nonneg (norm_nonneg _) _)
    calc ∫ z in closedBall a ρ, ‖s ^ n / n.factorial * z ^ n‖
        ≤ ∫ _z in closedBall a ρ, (‖s‖ * R) ^ n / n.factorial :=
          setIntegral_mono_on (hint n).norm (integrableOn_const hfin) measurableSet_closedBall hle
      _ = V * ((‖s‖ * R) ^ n / n.factorial) := by rw [setIntegral_const, smul_eq_mul]
  have hsum : Summable fun n : ℕ => ∫ z in closedBall a ρ, ‖s ^ n / n.factorial * z ^ n‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound
      ((Real.summable_pow_div_factorial _).mul_left _)
  simp_rw [hser]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ n : ℕ, ∫ z in closedBall a ρ, s ^ n / n.factorial * z ^ n =
      ((Real.pi * ρ ^ 2 : ℝ) : ℂ) * ((s * a) ^ n / n.factorial) := by
    intro n
    rw [integral_const_mul, setIntegral_closedBall_pow a hρ n, mul_pow]; ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1; congr 1; funext n; rw [mul_pow]; ring

/-! ## Packing an open set by disjoint closed balls -/

/-- **Packing.** Almost all of an open set of `ℂ × ℝ` is a countable disjoint union of closed balls
contained in it, and integrals over the set split over the balls. -/
theorem exists_ball_packing {W : Set (ℂ × ℝ)} (hW : IsOpen W) :
    ∃ (t : Set (ℂ × ℝ)) (r : ℂ × ℝ → ℝ), t.Countable ∧ t ⊆ W ∧ (∀ p ∈ t, 0 < r p) ∧
      (∀ p ∈ t, closedBall p (r p) ⊆ W) ∧
      ∀ f : ℂ × ℝ → ℂ, IntegrableOn f W →
        HasSum (fun p : t => ∫ q in closedBall (p : ℂ × ℝ) (r p), f q) (∫ q in W, f q) := by
  classical
  have hε : ∀ p ∈ W, ∃ ε > 0, ball p ε ⊆ W := fun p hp => Metric.isOpen_iff.mp hW p hp
  set R : ℂ × ℝ → ℝ := fun p => if h : p ∈ W then (Classical.choose (hε p h)) / 2 else 1 with hRdef
  have hRpos : ∀ p ∈ W, 0 < R p := by
    intro p hp
    simp only [hRdef, dif_pos hp]
    exact half_pos (Classical.choose_spec (hε p hp)).1
  have hRsub : ∀ p ∈ W, ∀ ρ, ρ < R p → closedBall p ρ ⊆ W := by
    intro p hp ρ hρ
    have hspec := Classical.choose_spec (hε p hp)
    refine (closedBall_subset_ball ?_).trans hspec.2
    have : R p = Classical.choose (hε p hp) / 2 := by simp only [hRdef, dif_pos hp]
    linarith [hspec.1]
  obtain ⟨t, r, htc, htW, hr, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure (ℂ × ℝ)) (fun _ => univ) W
      (fun x _ δ hδ => ⟨δ / 2, mem_univ _, by constructor <;> linarith⟩) R hRpos
  haveI : Countable t := htc.to_subtype
  have hrpos : ∀ p ∈ t, 0 < r p := fun p hp => (hr p hp).2.1
  have hrsub : ∀ p ∈ t, closedBall p (r p) ⊆ W := fun p hp => hRsub p (htW hp) _ (hr p hp).2.2
  refine ⟨t, r, htc, htW, hrpos, hrsub, fun f hf => ?_⟩
  set U := ⋃ p ∈ t, closedBall p (r p) with hUdef
  have hUiU : U = ⋃ i : t, closedBall (i : ℂ × ℝ) (r i) := biUnion_eq_iUnion _ _
  have hUW : U ⊆ W := iUnion₂_subset fun p hp => hrsub p hp
  have hUae : U =ᵐ[volume] W := by
    rw [ae_eq_set, sdiff_eq_empty.mpr hUW, measure_empty]
    exact ⟨rfl, hnull⟩
  have hpd : Pairwise (Function.onFun Disjoint fun i : t => closedBall (i : ℂ × ℝ) (r i)) :=
    fun i j hij => hdisj i.2 j.2 (Subtype.coe_injective.ne hij)
  have h := hasSum_integral_iUnion (μ := volume) (f := f)
    (fun i : t => measurableSet_closedBall) hpd (by rw [← hUiU]; exact hf.mono_set hUW)
  rw [← hUiU, setIntegral_congr_set hUae] at h
  exact h

/-! ## The region under the graph of a density -/

/-- The open region `x₁ < Re z < x₂`, `0 < c < g(Im z)` of `ℂ × ℝ`. -/
def region (g : ℝ → ℝ) (x₁ x₂ : ℝ) : Set (ℂ × ℝ) :=
  {p | x₁ < p.1.re ∧ p.1.re < x₂ ∧ 0 < p.2 ∧ p.2 < g p.1.im}

theorem isOpen_region {g : ℝ → ℝ} (hg : Continuous g) (x₁ x₂ : ℝ) : IsOpen (region g x₁ x₂) := by
  have h1 : Continuous fun p : ℂ × ℝ => p.1.re := Complex.continuous_re.comp continuous_fst
  have h2 : Continuous fun p : ℂ × ℝ => g p.1.im := hg.comp (Complex.continuous_im.comp continuous_fst)
  have : region g x₁ x₂ = {p : ℂ × ℝ | x₁ < p.1.re} ∩ ({p | p.1.re < x₂} ∩
      ({p | 0 < p.2} ∩ {p | p.2 < g p.1.im})) := by
    ext p; simp [region]
  rw [this]
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd h2)))

/-- The strip indicator times the density, as a function on `ℂ`. -/
def stripDensity (g : ℝ → ℝ) (x₁ x₂ : ℝ) (z : ℂ) : ℝ :=
  (Ioo x₁ x₂).indicator (fun _ => 1) z.re * g z.im

theorem preimage_region (g : ℝ → ℝ) (x₁ x₂ : ℝ) (z : ℂ) :
    Prod.mk z ⁻¹' region g x₁ x₂ = if x₁ < z.re ∧ z.re < x₂ then Ioo 0 (g z.im) else ∅ := by
  ext c
  split_ifs with h
  · simp [region, h]
  · simp only [region, mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact fun h' => h ⟨h'.1, h'.2.1⟩

theorem volume_preimage_region (g : ℝ → ℝ) (x₁ x₂ : ℝ) (z : ℂ) :
    volume (Prod.mk z ⁻¹' region g x₁ x₂) = ENNReal.ofReal (stripDensity g x₁ x₂ z) := by
  rw [preimage_region, stripDensity]
  by_cases h : x₁ < z.re ∧ z.re < x₂
  · rw [if_pos h, Real.volume_Ioo, indicator_of_mem (show z.re ∈ Ioo x₁ x₂ from h), one_mul, sub_zero]
  · rw [if_neg h, measure_empty, indicator_of_notMem (show z.re ∉ Ioo x₁ x₂ from h), zero_mul,
      ENNReal.ofReal_zero]

/-- Integrals of functions of `(Re z, Im z)` on `ℂ` as integrals on `ℝ × ℝ`. -/
theorem integral_complex_eq_prod (F : ℝ × ℝ → ℂ) :
    ∫ z : ℂ, F (z.re, z.im) = ∫ p : ℝ × ℝ, F p := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding F
  simpa [Complex.measurableEquivRealProd_apply] using h

theorem lintegral_complex_eq_prod (F : ℝ × ℝ → ENNReal) :
    ∫⁻ z : ℂ, F (z.re, z.im) = ∫⁻ p : ℝ × ℝ, F p := by
  have h := Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding F
  simpa [Complex.measurableEquivRealProd_apply] using h

theorem volume_region_lt_top {g : ℝ → ℝ} (hg : Continuous g)
    (hgi : Integrable g) (x₁ x₂ : ℝ) : volume (region g x₁ x₂) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (isOpen_region hg x₁ x₂).measurableSet]
  simp_rw [volume_preimage_region]
  have hF : ∀ z : ℂ, ENNReal.ofReal (stripDensity g x₁ x₂ z) =
      (fun p : ℝ × ℝ => (Ioo x₁ x₂).indicator (fun _ => (1 : ENNReal)) p.1 *
        ENNReal.ofReal (g p.2)) (z.re, z.im) := by
    intro z
    simp only [stripDensity]
    by_cases h : z.re ∈ Ioo x₁ x₂
    · rw [indicator_of_mem h, indicator_of_mem h, one_mul, one_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul, zero_mul, ENNReal.ofReal_zero]
  simp_rw [hF]
  have hcx := lintegral_complex_eq_prod (fun p : ℝ × ℝ => (Ioo x₁ x₂).indicator (fun _ => (1 : ENNReal)) p.1 *
    ENNReal.ofReal (g p.2))
  simp only at hcx
  rw [hcx, Measure.volume_eq_prod,
    lintegral_prod_mul (aemeasurable_const.indicator measurableSet_Ioo)
      (hg.measurable.ennreal_ofReal.aemeasurable), lintegral_indicator measurableSet_Ioo,
    setLIntegral_const, one_mul]
  refine ENNReal.mul_lt_top measure_Ioo_lt_top ?_
  have := hgi.hasFiniteIntegral
  rw [HasFiniteIntegral] at this
  refine lt_of_le_of_lt (lintegral_mono fun y => ?_) this
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- **Fubini on the region.** For `F` bounded by `C` on the strip,
`∫_W F(z) = ∫_ℂ F(z) 1_{(x₁,x₂)}(Re z) g(Im z) dz`. -/
theorem integral_region {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y) (hgi : Integrable g)
    {x₁ x₂ : ℝ} {F : ℂ → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → ‖F z‖ ≤ C) :
    IntegrableOn (fun p : ℂ × ℝ => F p.1) (region g x₁ x₂) ∧
      ∫ p in region g x₁ x₂, F p.1 = ∫ z : ℂ, F z * (stripDensity g x₁ x₂ z : ℂ) := by
  have hWm : MeasurableSet (region g x₁ x₂) := (isOpen_region hg x₁ x₂).measurableSet
  have hWfin := volume_region_lt_top hg hgi x₁ x₂
  have hInt : IntegrableOn (fun p : ℂ × ℝ => F p.1) (region g x₁ x₂) := by
    refine Measure.integrableOn_of_bounded (M := C) hWfin.ne
      (hF.comp continuous_fst).aestronglyMeasurable ?_
    rw [ae_restrict_iff' hWm]
    exact Filter.Eventually.of_forall fun p hp => hC p.1 hp.1 hp.2.1
  refine ⟨hInt, ?_⟩
  rw [← integral_indicator hWm, Measure.volume_eq_prod,
    integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hInt.integrable_indicator hWm)]
  congr 1
  funext z
  have hfib : (fun c : ℝ => (region g x₁ x₂).indicator (fun p : ℂ × ℝ => F p.1) (z, c)) =
      (Prod.mk z ⁻¹' region g x₁ x₂).indicator (fun _ => F z) := by
    funext c
    by_cases hc : (z, c) ∈ region g x₁ x₂
    · rw [indicator_of_mem hc, indicator_of_mem (show c ∈ Prod.mk z ⁻¹' region g x₁ x₂ from hc)]
    · rw [indicator_of_notMem hc, indicator_of_notMem (show c ∉ Prod.mk z ⁻¹' region g x₁ x₂ from hc)]
  rw [hfib, integral_indicator_const _ ((isOpen_region hg x₁ x₂).measurableSet.preimage
    measurable_prodMk_left), Measure.real, volume_preimage_region,
    ENNReal.toReal_ofReal (by unfold stripDensity; exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (hg0 _)),
    Complex.real_smul, mul_comm]

/-- **Cylinders.** `∫` of `F(z)` over the ball `D(a,r) × [c − r, c + r]` of `ℂ × ℝ` is
`2r ∫_{D(a,r)} F`. -/
theorem integral_closedBall_prod (F : ℂ → ℂ) (p : ℂ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ q in closedBall p r, F q.1 = ((2 * r : ℝ) : ℂ) * ∫ z in closedBall p.1 r, F z := by
  rw [← closedBall_prod_same p.1 p.2 r, Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℝ)) F
    (fun _ : ℝ => (1 : ℂ)) (closedBall p.1 r) (closedBall p.2 r)
  simp only [mul_one] at h
  rw [h, setIntegral_const, Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith),
    Complex.real_smul, mul_one, mul_comm]

/-! ## The configuration -/

/-- **Positive configurations reproducing a density on exponentials.** For a continuous integrable
`g ≥ 0` and a strip `x₁ < Re w < x₂` there are countably many points `w_i` in the strip and weights
`c_i > 0` with `Σ_i c_i e^{s w_i} = ∫_{x₁}^{x₂} e^{sx} dx · ∫ e^{isy} g(y) dy` for every real `s`. -/
theorem exists_disc_configuration_of_density {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    (hgi : Integrable g) (x₁ x₂ : ℝ) :
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℂ) (c : ι → ℝ),
      (∀ i, x₁ < (w i).re ∧ (w i).re < x₂) ∧ (∀ i, 0 < c i) ∧
      ∀ s : ℝ, HasSum (fun i => (c i : ℂ) * cexp (s * w i))
        ((∫ x in Ioo x₁ x₂, cexp (s * x)) * ∫ y : ℝ, cexp ((s * y : ℝ) * I) * (g y : ℂ)) := by
  obtain ⟨t, r, htc, htW, hrpos, hrsub, hsum⟩ := exists_ball_packing (isOpen_region hg x₁ x₂)
  haveI : Countable t := htc.to_subtype
  refine ⟨t, inferInstance, fun p => (p : ℂ × ℝ).1, fun p => 2 * Real.pi * r p ^ 3,
    fun p => ⟨(htW p.2).1, (htW p.2).2.1⟩, fun p => by have := hrpos p p.2; positivity, fun s => ?_⟩
  set F : ℂ → ℂ := fun z => cexp (s * z) with hFdef
  have hFc : Continuous F := by fun_prop
  set C := Real.exp (|s| * max |x₁| |x₂|) with hC
  have hFb : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → ‖F z‖ ≤ C := by
    intro z h1 h2
    rw [hFdef, Complex.norm_exp, hC]
    refine Real.exp_le_exp.mpr ?_
    have hre : (↑s * z).re = s * z.re := by simp
    rw [hre]
    calc s * z.re ≤ |s * z.re| := le_abs_self _
      _ = |s| * |z.re| := abs_mul _ _
      _ ≤ |s| * max |x₁| |x₂| := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact abs_le_max_abs_abs h1.le h2.le
  obtain ⟨hInt, hFub⟩ := integral_region hg hg0 hgi hFc hFb
  have h := hsum (fun q => F q.1) hInt
  rw [hFub] at h
  have hball : ∀ p : t, ∫ q in closedBall (p : ℂ × ℝ) (r p), F q.1 =
      ((2 * Real.pi * r p ^ 3 : ℝ) : ℂ) * cexp (s * (p : ℂ × ℝ).1) := by
    intro p
    rw [integral_closedBall_prod F _ (hrpos p p.2).le, hFdef,
      setIntegral_closedBall_cexp _ (hrpos p p.2).le]
    push_cast; ring
  simp_rw [hball] at h
  convert h using 1
  -- the double integral factorises
  have hfac : ∀ z : ℂ, F z * (stripDensity g x₁ x₂ z : ℂ) =
      (fun q : ℝ × ℝ => ((Ioo x₁ x₂).indicator (fun x : ℝ => cexp (s * x)) q.1) *
        (cexp ((s * q.2 : ℝ) * I) * (g q.2 : ℂ))) (z.re, z.im) := by
    intro z
    simp only [hFdef, stripDensity]
    by_cases hz : z.re ∈ Ioo x₁ x₂
    · rw [indicator_of_mem hz, indicator_of_mem hz, one_mul]
      have : (s : ℂ) * z = (s * z.re : ℝ) + ((s * z.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [this, Complex.exp_add]
      push_cast; ring
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]; simp
  simp_rw [hfac]
  have hcx := integral_complex_eq_prod (fun q : ℝ × ℝ => ((Ioo x₁ x₂).indicator (fun x : ℝ => cexp (s * x)) q.1) *
    (cexp ((s * q.2 : ℝ) * I) * (g q.2 : ℂ)))
  simp only at hcx
  have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => (Ioo x₁ x₂).indicator (fun x : ℝ => cexp (s * x)) x)
    (fun y : ℝ => cexp ((s * y : ℝ) * I) * (g y : ℂ))
  rw [hcx, Measure.volume_eq_prod, hpm, integral_indicator measurableSet_Ioo]

/-! ## Band-limited configurations -/

/-- With `a = ε/2π`: `∫ e^{isy} sinc(πay)² dy = 0` for `|s| ≥ ε`. -/
theorem integral_cexp_mul_sincSq_scaled_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ |s|) :
    ∫ y : ℝ, cexp ((s * y : ℝ) * I) * (sincSq (ε / (2 * Real.pi) * y) : ℂ) = 0 := by
  set a := ε / (2 * Real.pi) with ha
  have ha0 : a ≠ 0 := by rw [ha]; positivity
  set G : ℝ → ℂ := fun u => cexp (((2 * Real.pi * u * (s / ε)) : ℝ) * I) * (sincSq u : ℂ) with hGdef
  have hG : (fun y : ℝ => cexp ((s * y : ℝ) * I) * (sincSq (a * y) : ℂ)) = fun y => G (a * y) := by
    funext y
    simp only [hGdef]
    congr 3
    rw [ha]; field_simp
  rw [hG, Measure.integral_comp_mul_left G a, hGdef, integral_cexp_mul_sincSq_eq_zero, smul_zero]
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε, one_mul]
  exact hs

/-- **Positive configurations with band-limited exponential sums.** For every `ε > 0` and every
strip `x₁ < Re w < x₂` there are countably many points `w_i` in the strip and weights `c_i > 0`,
of total mass `(x₂ − x₁)·2π/ε`, such that `Σ_i c_i e^{s w_i} = 0` for every real `|s| ≥ ε`. -/
theorem exists_positive_configuration_bandLimited {ε x₁ x₂ : ℝ} (hε : 0 < ε) (hx : x₁ < x₂) :
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℂ) (c : ι → ℝ),
      (∀ i, x₁ < (w i).re ∧ (w i).re < x₂) ∧ (∀ i, 0 < c i) ∧
      HasSum c ((x₂ - x₁) * (2 * Real.pi / ε)) ∧
      ∀ s : ℝ, ε ≤ |s| → HasSum (fun i => (c i : ℂ) * cexp (s * w i)) 0 := by
  set a := ε / (2 * Real.pi) with ha
  have ha0 : a ≠ 0 := by rw [ha]; positivity
  set g : ℝ → ℝ := fun y => sincSq (a * y) with hgdef
  have hg : Continuous g := continuous_sincSq.comp (continuous_const.mul continuous_id)
  have hg0 : ∀ y, 0 ≤ g y := fun y => sincSq_nonneg _
  have hgi : Integrable g := integrable_sincSq.comp_mul_left' ha0
  obtain ⟨ι, hι, w, c, hw, hc, hsum⟩ := exists_disc_configuration_of_density hg hg0 hgi x₁ x₂
  refine ⟨ι, hι, w, c, hw, hc, ?_, fun s hs => ?_⟩
  · have h0 := hsum 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, one_mul] at h0
    have hmass : (∫ x in Ioo x₁ x₂, (1 : ℂ)) * ∫ y : ℝ, (g y : ℂ) =
        (((x₂ - x₁) * (2 * Real.pi / ε) : ℝ) : ℂ) := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le hx.le, integral_complex_ofReal, hgdef]
      have hc := Measure.integral_comp_mul_left sincSq a
      rw [hc, integral_sincSq, smul_eq_mul, mul_one, ha, abs_inv, abs_div, abs_of_pos hε,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      rw [Complex.real_smul, mul_one]
      push_cast; field_simp
    rw [hmass] at h0
    exact Complex.hasSum_ofReal.mp h0
  · have h := hsum s
    rw [hgdef] at h
    simp only at h
    rw [integral_cexp_mul_sincSq_scaled_eq_zero hε hs, mul_zero] at h
    exact h

end GaloisForLFunctions.HTGeometry.BandLimitedPositiveConfiguration
