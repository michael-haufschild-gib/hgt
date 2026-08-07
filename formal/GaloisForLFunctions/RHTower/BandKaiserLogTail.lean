import GaloisForLFunctions.RHTower.BandKaiserCentralEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmically sharp exterior tail of the Kaiser trial

The exact exterior transform is a sine quotient.  Splitting the positive angular-frequency tail
into an edge strip of width `1 / c`, a middle region, and a far region gives respectively

```text
4 / c,    4 log(c) / c,    4 / c.
```

Reflection and the Fourier normalization then give a full physical tail bounded by
`(8 + 4 log c) / (pi c)`.  This is the missing tail refinement behind the
`sqrt(c) log(c) exp(-2c)` true ground-prolate leakage bound.
-/

open Filter MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Squared Kaiser cosine transform in angular-frequency normalization. -/
def kaiserAngularDensity (c ω : ℝ) : ℝ :=
  (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)) ^ 2

theorem kaiserAngularDensity_even (c ω : ℝ) :
    kaiserAngularDensity c (-ω) = kaiserAngularDensity c ω := by
  rw [kaiserAngularDensity, kaiserAngularDensity]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change kaiserTrial c x * Real.cos (-ω * x) =
    kaiserTrial c x * Real.cos (ω * x)
  rw [show -ω * x = -(ω * x) by ring, Real.cos_neg]

/-- The angular density is integrable, by the already established physical Plancherel density and
the nonzero linear change of variables `ω = 2*pi*ξ`. -/
theorem integrable_kaiserAngularDensity (c : ℝ) :
    Integrable (kaiserAngularDensity c) := by
  have hphysical := integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hcomp : Integrable (fun ξ : ℝ => kaiserAngularDensity c (2 * Real.pi * ξ)) := by
    refine hphysical.congr ?_
    filter_upwards with ξ
    rw [norm_sq_fourier_bandTrunc_of_even
      (continuous_kaiserTrial c) (kaiserTrial_even c) ξ]
    rfl
  exact (MeasureTheory.integrable_comp_mul_left_iff
    (kaiserAngularDensity c) (by positivity : 2 * Real.pi ≠ 0)).1 hcomp

/-- Uniform edge bound on the squared exterior transform. -/
theorem kaiserAngularDensity_le_four {c ω : ℝ} (hc : 0 ≤ c) (hω : c < ω) :
    kaiserAngularDensity c ω ≤ 4 := by
  have hsq : c ^ 2 < ω ^ 2 := by nlinarith
  have habs := abs_integral_kaiserTrial_cos_le hsq
  have hle := habs.trans (min_le_left _ _)
  rw [kaiserAngularDensity, ← sq_abs]
  nlinarith [abs_nonneg (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x))]

/-- Inverse-quadratic exterior bound retaining the factored denominator. -/
theorem kaiserAngularDensity_le_inv_quad {c ω : ℝ} (hc : 0 ≤ c) (hω : c < ω) :
    kaiserAngularDensity c ω ≤ 4 / (ω ^ 2 - c ^ 2) := by
  have hsq : c ^ 2 < ω ^ 2 := by nlinarith
  have hpos : 0 < ω ^ 2 - c ^ 2 := by linarith
  have hsqrt : 0 < Real.sqrt (ω ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hpos
  have hsqrt_sq : Real.sqrt (ω ^ 2 - c ^ 2) ^ 2 = ω ^ 2 - c ^ 2 :=
    Real.sq_sqrt hpos.le
  have habs := abs_integral_kaiserTrial_cos_le hsq
  have hle := habs.trans (min_le_right _ _)
  rw [kaiserAngularDensity, ← sq_abs]
  calc
    |∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)| ^ 2
        ≤ (2 / Real.sqrt (ω ^ 2 - c ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = 4 / (ω ^ 2 - c ^ 2) := by rw [div_pow, hsqrt_sq]; norm_num

theorem kaiserAngularDensity_le_middle {c ω : ℝ} (hc : 0 < c) (hω : c < ω) :
    kaiserAngularDensity c ω ≤ 2 / c * (1 / (ω - c)) := by
  have hinv := kaiserAngularDensity_le_inv_quad hc.le hω
  have hωc : 0 < ω - c := by linarith
  have hsum : 2 * c ≤ ω + c := by linarith
  have hsumpos : 0 < ω + c := by linarith
  have hdenle : (ω - c) * (2 * c) ≤ (ω - c) * (ω + c) :=
    mul_le_mul_of_nonneg_left hsum hωc.le
  calc
    kaiserAngularDensity c ω ≤ 4 / (ω ^ 2 - c ^ 2) := hinv
    _ = 4 / ((ω - c) * (ω + c)) := by ring_nf
    _ ≤ 4 / ((ω - c) * (2 * c)) :=
      div_le_div_of_nonneg_left (by norm_num)
        (mul_pos hωc (mul_pos (by norm_num) hc)) hdenle
    _ = 2 / c * (1 / (ω - c)) := by field_simp; ring

theorem kaiserAngularDensity_le_far {c ω : ℝ} (hc : 0 ≤ c) (hω : 2 * c < ω) :
    kaiserAngularDensity c ω ≤ 4 / (ω - c) ^ 2 := by
  have hωc : c < ω := by linarith
  have hinv := kaiserAngularDensity_le_inv_quad hc hωc
  have hdiff : 0 < ω - c := by linarith
  have hfactor : (ω - c) ^ 2 ≤ ω ^ 2 - c ^ 2 := by nlinarith
  exact hinv.trans (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hdiff) hfactor)

theorem integral_const_four_Ioc {a b : ℝ} (hab : a ≤ b) :
    (∫ _x in Ioc a b, (4 : ℝ)) = 4 * (b - a) := by
  rw [MeasureTheory.setIntegral_const]
  simp [hab]
  ring

theorem integral_kaiser_middle_envelope {c : ℝ} (hc : 2 ≤ c) :
    (∫ ω in Ioc (c + 1 / c) (2 * c), 2 / c * (1 / (ω - c))) =
      4 * Real.log c / c := by
  have hcpos : 0 < c := by linarith
  have hab : c + 1 / c ≤ 2 * c := by
    have hinv : 1 / c ≤ c := (div_le_iff₀ hcpos).2 (by nlinarith)
    linarith
  have hpos : ∀ ω ∈ Icc (c + 1 / c) (2 * c), 0 < ω - c := by
    intro ω hω
    have hinv : 0 < 1 / c := by positivity
    linarith [hω.1]
  have hcont : ContinuousOn (fun ω : ℝ => 2 / c * Real.log (ω - c))
      (Icc (c + 1 / c) (2 * c)) := by
    exact continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).log fun ω hω => (hpos ω hω).ne')
  have hderiv : ∀ ω ∈ Ioo (c + 1 / c) (2 * c),
      HasDerivAt (fun t : ℝ => 2 / c * Real.log (t - c))
        (2 / c * (1 / (ω - c))) ω := by
    intro ω hω
    have hne : ω - c ≠ 0 := by
      have hinv : 0 < 1 / c := by positivity
      linarith [hω.1]
    simpa only [Function.comp_apply, id_eq, one_div, mul_one] using
      ((Real.hasDerivAt_log hne).comp ω
        ((hasDerivAt_id ω).sub_const c)).const_mul (2 / c)
  have hint : IntervalIntegrable (fun ω : ℝ => 2 / c * (1 / (ω - c))) volume
      (c + 1 / c) (2 * c) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.mul
      (continuousOn_const.div₀ (continuousOn_id.sub continuousOn_const)
        fun ω hω => (hpos ω hω).ne')
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint]
  rw [show 2 * c - c = c by ring, show c + 1 / c - c = 1 / c by ring,
    one_div, Real.log_inv]
  norm_num
  ring

theorem integral_kaiser_far_envelope {c : ℝ} (hc : 0 < c) :
    (∫ ω in Ioi (2 * c), 4 / (ω - c) ^ 2) = 4 / c := by
  let F : ℝ → ℝ := fun ω => -4 / (ω - c)
  let f : ℝ → ℝ := fun ω => 4 / (ω - c) ^ 2
  have hcont : ContinuousWithinAt F (Ici (2 * c)) (2 * c) := by
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop (disch := nlinarith)
  have hderiv : ∀ ω ∈ Ioi (2 * c), HasDerivAt F (f ω) ω := by
    intro ω hω
    dsimp [F, f]
    have hω' : 2 * c < ω := hω
    have hne : ω - c ≠ 0 := ne_of_gt (by linarith [hω', hc])
    change HasDerivAt ((fun _ : ℝ => (-4 : ℝ)) / fun t => t - c)
      (4 / (ω - c) ^ 2) ω
    simpa [Function.comp_def] using
      (hasDerivAt_const ω (-4)).div ((hasDerivAt_id ω).sub_const c) hne
  have hnonneg : ∀ ω ∈ Ioi (2 * c), 0 ≤ f ω := by
    intro ω _
    dsimp [f]
    positivity
  have hlim : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    have hsub : Tendsto (fun ω : ℝ => ω - c) atTop atTop :=
      tendsto_atTop_add_const_right _ (-c) tendsto_id
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsub))
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim]
  dsimp [F]
  field_simp
  ring

/-- Positive angular-frequency tail: edge, logarithmic middle, and far pieces. -/
theorem integral_Ioi_kaiserAngularDensity_le {c : ℝ} (hc : 2 ≤ c) :
    (∫ ω in Ioi c, kaiserAngularDensity c ω) ≤
      (8 + 4 * Real.log c) / c := by
  have hcpos : 0 < c := by linarith
  let s : ℝ := c + 1 / c
  let A : Set ℝ := Ioc c s
  let B : Set ℝ := Ioc s (2 * c)
  let C : Set ℝ := Ioi (2 * c)
  have hcs : c < s := by
    dsimp [s]
    have : 0 < 1 / c := by positivity
    linarith
  have hs2 : s ≤ 2 * c := by
    dsimp [s]
    have hinv : 1 / c ≤ c := (div_le_iff₀ hcpos).2 (by nlinarith)
    linarith
  have hmeasA : MeasurableSet A := measurableSet_Ioc
  have hmeasB : MeasurableSet B := measurableSet_Ioc
  have hmeasC : MeasurableSet C := measurableSet_Ioi
  have hdens := integrable_kaiserAngularDensity c
  have hnear : (∫ ω in A, kaiserAngularDensity c ω) ≤ 4 / c := by
    have hconst : IntegrableOn (fun _ω : ℝ => (4 : ℝ)) A := by
      dsimp [A]
      exact continuous_const.integrableOn_Ioc
    have hmono : (∫ ω in A, kaiserAngularDensity c ω) ≤ ∫ _ω in A, (4 : ℝ) := by
      refine setIntegral_mono_on hdens.integrableOn hconst hmeasA ?_
      intro ω hω
      exact kaiserAngularDensity_le_four hcpos.le hω.1
    rw [integral_const_four_Ioc hcs.le] at hmono
    calc
      (∫ ω in A, kaiserAngularDensity c ω) ≤ 4 * (s - c) := hmono
      _ = 4 / c := by dsimp [s]; field_simp; ring
  have hmiddle : (∫ ω in B, kaiserAngularDensity c ω) ≤ 4 * Real.log c / c := by
    have henv : IntegrableOn (fun ω : ℝ => 2 / c * (1 / (ω - c))) B := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hs2]
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs2]
      apply continuousOn_const.mul
      apply continuousOn_const.div₀ (continuousOn_id.sub continuousOn_const)
      intro ω hω
      have : c < ω := lt_of_lt_of_le hcs hω.1
      simpa only [Pi.sub_apply, id_eq] using (ne_of_gt (sub_pos.mpr this))
    have hmono := setIntegral_mono_on hdens.integrableOn henv hmeasB fun ω hω =>
      kaiserAngularDensity_le_middle hcpos (hcs.trans hω.1)
    simpa only [B, s, integral_kaiser_middle_envelope hc] using hmono
  have hfar : (∫ ω in C, kaiserAngularDensity c ω) ≤ 4 / c := by
    let F : ℝ → ℝ := fun ω => -4 / (ω - c)
    let f : ℝ → ℝ := fun ω => 4 / (ω - c) ^ 2
    have hcont : ContinuousWithinAt F (Ici (2 * c)) (2 * c) := by
      apply ContinuousAt.continuousWithinAt
      dsimp [F]
      fun_prop (disch := nlinarith)
    have hderiv : ∀ ω ∈ Ioi (2 * c), HasDerivAt F (f ω) ω := by
      intro ω hω
      dsimp [F, f]
      have hω' : 2 * c < ω := hω
      have hne : ω - c ≠ 0 := ne_of_gt (by linarith [hω', hcpos])
      change HasDerivAt ((fun _ : ℝ => (-4 : ℝ)) / fun t => t - c)
        (4 / (ω - c) ^ 2) ω
      simpa [Function.comp_def] using
        (hasDerivAt_const ω (-4)).div ((hasDerivAt_id ω).sub_const c) hne
    have hnonneg : ∀ ω ∈ Ioi (2 * c), 0 ≤ f ω := by
      intro ω _
      dsimp [f]
      positivity
    have hlim : Tendsto F atTop (nhds 0) := by
      dsimp [F]
      have hsub : Tendsto (fun ω : ℝ => ω - c) atTop atTop :=
        tendsto_atTop_add_const_right _ (-c) tendsto_id
      simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsub))
    have henv : IntegrableOn f C := by
      exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim
    have hmono := setIntegral_mono_on hdens.integrableOn henv hmeasC fun ω hω =>
      kaiserAngularDensity_le_far hcpos.le hω
    simpa only [C, f, integral_kaiser_far_envelope hcpos] using hmono
  have hAB : Disjoint A B := by
    dsimp [A, B]
    grind
  have hABC : Disjoint (A ∪ B) C := by
    dsimp [A, B, C]
    grind
  have hunion : (A ∪ B) ∪ C = Ioi c := by
    ext ω
    dsimp [A, B, C]
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro ((hω | hω) | hω) <;> linarith
    · intro hω
      rcases le_or_gt ω s with hωs | hsω
      · exact Or.inl (Or.inl ⟨hω, hωs⟩)
      rcases le_or_gt ω (2 * c) with hω2 | h2ω
      · exact Or.inl (Or.inr ⟨hsω, hω2⟩)
      · exact Or.inr h2ω
  have hsplit : (∫ ω in Ioi c, kaiserAngularDensity c ω) =
      (∫ ω in A, kaiserAngularDensity c ω) +
        (∫ ω in B, kaiserAngularDensity c ω) +
          (∫ ω in C, kaiserAngularDensity c ω) := by
    rw [← hunion, setIntegral_union hABC hmeasC
      (hdens.integrableOn.union hdens.integrableOn) hdens.integrableOn,
      setIntegral_union hAB hmeasB hdens.integrableOn hdens.integrableOn]
  rw [hsplit]
  have hlog : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  calc
    (∫ ω in A, kaiserAngularDensity c ω) +
          (∫ ω in B, kaiserAngularDensity c ω) +
            (∫ ω in C, kaiserAngularDensity c ω)
        ≤ 4 / c + 4 * Real.log c / c + 4 / c := by linarith
    _ = (8 + 4 * Real.log c) / c := by ring

/-! ## Transport to the physical Fourier variable -/

/-- Squared Fourier density of the compactly supported Kaiser carrier. -/
def kaiserPhysicalDensity (c ξ : ℝ) : ℝ :=
  ‖FourierTransform.fourier (bandTrunc (kaiserTrial c)) ξ‖ ^ 2

theorem kaiserPhysicalDensity_eq_angular (c ξ : ℝ) :
    kaiserPhysicalDensity c ξ = kaiserAngularDensity c (2 * Real.pi * ξ) := by
  rw [kaiserPhysicalDensity, kaiserAngularDensity,
    norm_sq_fourier_bandTrunc_of_even
      (continuous_kaiserTrial c) (kaiserTrial_even c) ξ]

theorem kaiserPhysicalDensity_even (c ξ : ℝ) :
    kaiserPhysicalDensity c (-ξ) = kaiserPhysicalDensity c ξ := by
  rw [kaiserPhysicalDensity_eq_angular, kaiserPhysicalDensity_eq_angular]
  convert kaiserAngularDensity_even c (2 * Real.pi * ξ) using 1 <;> ring

/-- **Logarithmically sharp physical Kaiser tail.**  In mathlib's Fourier normalization, the
two-sided exterior spectral mass has the explicit `log(c) / c` upper bound. -/
theorem integral_tail_kaiser_log_le {c : ℝ} (hc : 2 ≤ c) :
    (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
        ‖FourierTransform.fourier (bandTrunc (kaiserTrial c)) ξ‖ ^ 2) ≤
    (8 + 4 * Real.log c) / (Real.pi * c) := by
  have hcpos : 0 < c := by linarith
  let r : ℝ := c / (2 * Real.pi)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * Real.pi * r = c := by
    dsimp [r]
    field_simp [Real.pi_ne_zero]
  have hangular := integral_Ioi_kaiserAngularDensity_le hc
  have hright_eq : (∫ ξ in Ioi r, kaiserPhysicalDensity c ξ) =
      (2 * Real.pi)⁻¹ * (∫ ω in Ioi c, kaiserAngularDensity c ω) := by
    calc
      (∫ ξ in Ioi r, kaiserPhysicalDensity c ξ) =
          ∫ ξ in Ioi r, kaiserAngularDensity c (2 * Real.pi * ξ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro ξ _
        exact kaiserPhysicalDensity_eq_angular c ξ
      _ = (2 * Real.pi)⁻¹ •
          (∫ ω in Ioi (2 * Real.pi * r), kaiserAngularDensity c ω) :=
        MeasureTheory.integral_comp_mul_left_Ioi
          (kaiserAngularDensity c) r (by positivity)
      _ = (2 * Real.pi)⁻¹ *
          (∫ ω in Ioi c, kaiserAngularDensity c ω) := by
        rw [hscale]
        rfl
  have hright : (∫ ξ in Ioi r, kaiserPhysicalDensity c ξ) ≤
      (8 + 4 * Real.log c) / (2 * Real.pi * c) := by
    rw [hright_eq]
    have hmul := mul_le_mul_of_nonneg_left hangular
      (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
    calc
      (2 * Real.pi)⁻¹ * (∫ ω in Ioi c, kaiserAngularDensity c ω) ≤
          (2 * Real.pi)⁻¹ * ((8 + 4 * Real.log c) / c) := hmul
      _ = (8 + 4 * Real.log c) / (2 * Real.pi * c) := by field_simp
  have hleft_eq : (∫ ξ in Iio (-r), kaiserPhysicalDensity c ξ) =
      ∫ ξ in Ioi r, kaiserPhysicalDensity c ξ := by
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio,
      ← integral_comp_neg_Ioi r (kaiserPhysicalDensity c)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ _
    exact kaiserPhysicalDensity_even c ξ
  have hleft : (∫ ξ in Iio (-r), kaiserPhysicalDensity c ξ) ≤
      (8 + 4 * Real.log c) / (2 * Real.pi * c) := by
    rw [hleft_eq]
    exact hright
  have hdis : Disjoint (Iio (-r)) (Ioi r) := by
    grind
  have hunion : Iio (-r) ∪ Ioi r = (Icc (-r) r)ᶜ := by
    ext ξ
    simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, mem_Icc]
    constructor
    · rintro (hξ | hξ)
      · exact fun h => by linarith [h.1]
      · exact fun h => by linarith [h.2]
    · intro hξ
      rcases not_and_or.mp hξ with hξ | hξ
      · exact Or.inl (lt_of_not_ge hξ)
      · exact Or.inr (lt_of_not_ge hξ)
  have hdens : Integrable (kaiserPhysicalDensity c) := by
    change Integrable (fun ξ : ℝ =>
      ‖FourierTransform.fourier (bandTrunc (kaiserTrial c)) ξ‖ ^ 2)
    exact integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hsplit : (∫ ξ in (Icc (-r) r)ᶜ, kaiserPhysicalDensity c ξ) =
      (∫ ξ in Iio (-r), kaiserPhysicalDensity c ξ) +
        ∫ ξ in Ioi r, kaiserPhysicalDensity c ξ := by
    rw [← hunion, setIntegral_union hdis measurableSet_Ioi
      hdens.integrableOn hdens.integrableOn]
  change (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
    kaiserPhysicalDensity c ξ) ≤ _
  rw [show c / (2 * Real.pi) = r by rfl]
  rw [hsplit]
  calc
    (∫ ξ in Iio (-r), kaiserPhysicalDensity c ξ) +
          ∫ ξ in Ioi r, kaiserPhysicalDensity c ξ ≤
        (8 + 4 * Real.log c) / (2 * Real.pi * c) +
          (8 + 4 * Real.log c) / (2 * Real.pi * c) := add_le_add hleft hright
    _ = (8 + 4 * Real.log c) / (Real.pi * c) := by field_simp; ring

end GaloisForLFunctions.RHTower

end
