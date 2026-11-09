import GaloisForLFunctions.EulerFETransportTheory.OnlyExceptionalGaussianModesRemain
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# The Gaussian observation boundary

At damping `exp (-a t)` a zero `ρ` contributes an exponential rate
`a (re ρ - σ) / 2 - π / 4` on the observation line `σ + it`.
Upper and reciprocal Gamma bounds establish both sides of this boundary.
The infinite complementary divisor is retained in the prime-current error.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

open EulerFETransportTheory

/-- The horizontal amplification of a Gaussian mode minus its vertical Gamma decay. -/
def gaussianObservationRate (ρ : ℂ) (σ a : ℝ) : ℝ :=
  a * (ρ.re - σ) / 2 - Real.pi / 4

private theorem norm_gaussianMode_exp (ρ : ℂ) (σ a t : ℝ) :
    ‖gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))‖ =
      (1 / 2 : ℝ) * ‖Complex.Gamma ((ρ - ((σ : ℂ) + t * I)) / 2)‖ *
        Real.exp (a * (ρ.re - σ) / 2 * t) := by
  rw [gaussianMBKernel, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _), ← Real.exp_mul]
  norm_num only [norm_div, norm_one, Complex.norm_two]
  congr 1
  congr 1
  simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

/-- Both a mode and its reciprocal have polynomial envelopes with opposite
exponential rates. The constants work for every exponential damping speed. -/
theorem exists_gaussianMode_exponential_bounds (ρ : ℂ) (σ : ℝ) :
    ∃ (C D : ℝ) (N M : ℕ), 0 ≤ C ∧ 0 ≤ D ∧
      ∀ t : ℝ, |ρ.im| + 2 ≤ t → ∀ a : ℝ,
        ‖gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))‖ ≤
          C * t ^ N * Real.exp (gaussianObservationRate ρ σ a * t) ∧
        ‖(gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)))⁻¹‖ ≤
          D * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t)) := by
  obtain ⟨C, N, hC, hb⟩ :=
    HTGeometry.exists_sharp_bound_norm_Gamma_strip ((ρ.re - σ) / 2) ((ρ.re - σ) / 2)
  obtain ⟨D, M, hD, hd⟩ :=
    HTGeometry.exists_bound_norm_inv_Gamma_strip ((ρ.re - σ) / 2) ((ρ.re - σ) / 2)
  refine ⟨C / 2 * Real.exp (Real.pi * ρ.im / 4),
    2 * D * Real.exp (-(Real.pi * ρ.im / 4)), N, M, by positivity, by positivity, ?_⟩
  intro t ht a
  let z : ℂ := (ρ - ((σ : ℂ) + t * I)) / 2
  have hre : z.re = (ρ.re - σ) / 2 := by simp [z]
  have him : |z.im| = (t - ρ.im) / 2 := by
    have hγ : ρ.im ≤ t := by linarith [le_abs_self ρ.im]
    simp only [z, Complex.div_ofNat_im, Complex.sub_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    rw [abs_of_nonpos (by linarith)]
    ring
  have hz : 1 ≤ |z.im| := by rw [him]; linarith [le_abs_self ρ.im]
  have hzt : |z.im| ≤ t := by rw [him]; linarith [neg_le_abs ρ.im]
  have hΓ := hb z (by rw [hre]) (by rw [hre]) hz
  have hiΓ := hd z (by rw [hre]) (by rw [hre]) hz
  constructor
  · rw [norm_gaussianMode_exp]
    change (1 / 2 : ℝ) * ‖Complex.Gamma z‖ * _ ≤ _
    calc
      _ ≤ (1 / 2 : ℝ) *
          (C * t ^ N * Real.exp (-(Real.pi * |z.im| / 2))) *
          Real.exp (a * (ρ.re - σ) / 2 * t) := by
        gcongr
        exact hΓ.trans (by gcongr)
      _ = _ := by
        rw [him]
        have he : -(Real.pi * ((t - ρ.im) / 2) / 2) =
            Real.pi * ρ.im / 4 - Real.pi / 4 * t := by ring
        rw [he, Real.exp_sub, gaussianObservationRate, sub_mul, Real.exp_sub]
        ring
  · rw [norm_inv, norm_gaussianMode_exp, mul_inv, mul_inv]
    change ((1 / 2 : ℝ)⁻¹ * ‖Complex.Gamma z‖⁻¹) * _ ≤ _
    rw [← norm_inv, ← Real.exp_neg]
    norm_num only [one_div, inv_inv]
    calc
      _ ≤ (2 * (D * t ^ M * Real.exp (Real.pi * |z.im| / 2))) *
          Real.exp (-(a * (ρ.re - σ) / 2 * t)) := by
        gcongr
        exact hiΓ.trans (by gcongr)
      _ = _ := by
        rw [him]
        have he : Real.pi * ((t - ρ.im) / 2) / 2 =
            -(Real.pi * ρ.im / 4) + Real.pi / 4 * t := by ring
        rw [he, Real.exp_add]
        simp only [gaussianObservationRate]
        have hex : -( (a * (ρ.re - σ) / 2 - Real.pi / 4) * t) =
            Real.pi / 4 * t + -(a * (ρ.re - σ) / 2 * t) := by ring
        rw [hex, Real.exp_add]
        ring

/-- Below the observation boundary an exceptional Gaussian mode disappears. -/
theorem tendsto_gaussianMode_zero_of_negative_rate (ρ : ℂ) (σ a : ℝ)
    (h : gaussianObservationRate ρ σ a < 0) :
    Tendsto (fun t : ℝ => gaussianMBKernel (Real.exp (-a * t))
      (ρ - ((σ : ℂ) + t * I))) atTop (𝓝 0) := by
  obtain ⟨C, D, N, M, _, _, hb⟩ := exists_gaussianMode_exponential_bounds ρ σ
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp (neg_pos.mpr h)
  filter_upwards [eventually_ge_atTop (|ρ.im| + 2)] with t ht
  simpa only [neg_mul, neg_neg] using (hb t ht a).1

/-- Above the observation boundary the reciprocal mode disappears, giving
growth rather than passage to the continued current. -/
theorem tendsto_inv_gaussianMode_zero_of_positive_rate (ρ : ℂ) (σ a : ℝ)
    (h : 0 < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => (gaussianMBKernel (Real.exp (-a * t))
      (ρ - ((σ : ℂ) + t * I)))⁻¹) atTop (𝓝 0) := by
  obtain ⟨C, D, N, M, _, _, hb⟩ := exists_gaussianMode_exponential_bounds ρ σ
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp h
  filter_upwards [eventually_ge_atTop (|ρ.im| + 2)] with t ht
  exact (hb t ht a).2

private theorem gaussianMode_ne_zero_at_high_height (ρ : ℂ) (σ a t : ℝ)
    (ht : |ρ.im| + 2 ≤ t) :
    gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0)
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, Complex.neg_im,
      Complex.natCast_im, neg_zero] at him
    linarith [le_abs_self ρ.im]
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero (-a * t))]
    exact Complex.exp_ne_zero _

/-- An individual exceptional mode diverges above the boundary. This assertion
does not discard cancellation between different members of a layer. -/
theorem tendsto_norm_gaussianMode_atTop_of_positive_rate (ρ : ℂ) (σ a : ℝ)
    (h : 0 < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => ‖gaussianMBKernel (Real.exp (-a * t))
      (ρ - ((σ : ℂ) + t * I))‖) atTop atTop := by
  have hlim := (tendsto_inv_gaussianMode_zero_of_positive_rate ρ σ a h).norm
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < ‖(gaussianMBKernel (Real.exp (-a * t))
      (ρ - ((σ : ℂ) + t * I)))⁻¹‖ := by
    filter_upwards [eventually_ge_atTop (|ρ.im| + 2)] with t ht
    exact norm_pos_iff.mpr (inv_ne_zero (gaussianMode_ne_zero_at_high_height ρ σ a t ht))
  have hright := tendsto_nhdsWithin_iff.mpr ⟨by simpa only [norm_zero] using hlim, hpos⟩
  simpa only [norm_inv, inv_inv, Function.comp_def] using
    tendsto_inv_nhdsGT_zero.comp hright

/-- Exponential damping removes the complete complementary divisor uniformly
over the high strip. No restriction on the exponential speed is needed after
the specified finite layer is subtracted. -/
theorem not_asymptoticAbscissaLaw_has_exponential_finite_part :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (θ σ : ℝ),
        1 / 2 ≤ θ ∧ θ < σ ∧ σ < 1 ∧
        (∃ q ∈ F, σ < (xiZero q).re) ∧
        (∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) ∧
        ∀ a : ℝ, 0 < a →
          TendstoUniformlyOn (fun t : ℝ => fun u : ℝ =>
            finiteGaussianFinitePartError F ((u : ℂ) + t * I) (Real.exp (-a * t)))
            (fun _ => 0) atTop (Set.Icc σ 1) := by
  intro hnot
  obtain ⟨F, θ, σ, H, C, hθ, hgap, hσ1, hH, hC, hq, hrest, hb, _⟩ :=
    not_asymptoticAbscissaLaw_has_finiteGaussianControl hnot
  refine ⟨F, θ, σ, hθ, hgap, hσ1, hq, hrest, fun a ha => ?_⟩
  let p : ℝ := (σ - θ) / 2
  have hp : 0 < p := by dsimp [p]; linarith only [hgap]
  have hE : Tendsto (fun t : ℝ =>
      C * (t * Real.exp (-(a * t)) + t * Real.exp (-(a * p * t)))) atTop (𝓝 0) := by
    have h₁ := HTGeometry.tendsto_pow_mul_exp_neg_scaled 1 ha
    have h₂ := HTGeometry.tendsto_pow_mul_exp_neg_scaled 1 (mul_pos ha hp)
    simpa only [pow_one, add_zero, mul_zero] using (h₁.add h₂).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (max H 1),
    hE.eventually (eventually_lt_nhds hε)] with t ht hEt
  intro u hu
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hy : 0 < Real.exp (-a * t) := Real.exp_pos _
  have hy1 : Real.exp (-a * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [ha, ht0])
  have hlog : 1 + Real.log t ≤ t := by
    linarith only [Real.log_le_sub_one_of_pos ht0]
  have hbound := hb (Real.exp (-a * t)) hy hy1 ((u : ℂ) + t * I)
    (by simpa using hu.1) (by simpa using hu.2)
    (by simpa using (le_max_left H 1).trans ht)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hbound
  have he : Real.exp (-a * t) ^ p = Real.exp (-(a * p * t)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  change ‖finiteGaussianFinitePartError F ((u : ℂ) + t * I) (Real.exp (-a * t))‖ ≤
    C * (Real.exp (-a * t) + Real.exp (-a * t) ^ p) * (1 + Real.log t) at hbound
  rw [dist_zero_left]
  refine (hbound.trans ?_).trans_lt hEt
  rw [he]
  calc
    _ ≤ C * (Real.exp (-a * t) + Real.exp (-(a * p * t))) * t := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- The actual prime-minus-continuum current passes at exponential damping
whenever every retained mode lies below its observation boundary. -/
theorem not_asymptoticAbscissaLaw_has_exponential_passage :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (σ : ℝ),
        1 / 2 < σ ∧ σ < 1 ∧ (∃ q ∈ F, σ < (xiZero q).re) ∧
        ∀ u : ℝ, σ ≤ u → u ≤ 1 → ∀ a : ℝ, 0 < a →
          (∀ q ∈ F, gaussianObservationRate (xiZero q) u a < 0) →
          Tendsto (fun t : ℝ =>
            gaussianPrimeContinuumGap ((u : ℂ) + t * I) (Real.exp (-a * t)) -
              (Real.exp (-(Real.exp (-a * t))) : ℂ) *
                (gaussianArchimedeanCurrent ((u : ℂ) + t * I) -
                  logDeriv xi ((u : ℂ) + t * I))) atTop (𝓝 0) := by
  intro hnot
  obtain ⟨F, θ, σ, hθ, hgap, hσ1, hq, _, hfinite⟩ :=
    not_asymptoticAbscissaLaw_has_exponential_finite_part hnot
  refine ⟨F, σ, by linarith only [hθ, hgap], hσ1, hq, ?_⟩
  intro u hσu hu1 a ha hr
  have hsum : Tendsto (fun t : ℝ => ∑ q ∈ F,
      gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((u : ℂ) + t * I)))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum F
      (fun q hq => tendsto_gaussianMode_zero_of_negative_rate (xiZero q) u a (hr q hq))
  have hsub := ((hfinite a ha).tendsto_at ⟨hσu, hu1⟩).sub hsum
  simp only [sub_zero] at hsub
  refine hsub.congr fun t => ?_
  dsimp only [finiteGaussianFinitePartError]
  ring

/-- There are actual infinite-current observations beyond the pole's growth
boundary but below every exceptional zero's boundary. Subtracting the
continuum still gives passage there; ignoring its pole mode does not. -/
theorem not_asymptoticAbscissaLaw_has_passage_beyond_pole_boundary :
    ¬ AsymptoticAbscissaLaw →
      ∃ σ a : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < a ∧
        (∃ q : XiZeroCopy, σ < (xiZero q).re) ∧
        Tendsto (fun t : ℝ =>
          gaussianPrimeContinuumGap ((σ : ℂ) + t * I) (Real.exp (-a * t)) -
            (Real.exp (-(Real.exp (-a * t))) : ℂ) *
              (gaussianArchimedeanCurrent ((σ : ℂ) + t * I) -
                logDeriv xi ((σ : ℂ) + t * I))) atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ =>
          ‖gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I))‖)
          atTop atTop := by
  intro hnot
  obtain ⟨F, σ, hσ, hσ1, ⟨q₁, hq₁F, hq₁⟩, hpass⟩ :=
    not_asymptoticAbscissaLaw_has_exponential_passage hnot
  obtain ⟨q₀, hq₀F, hmax⟩ := F.exists_max_image (fun q => (xiZero q).re) ⟨q₁, hq₁F⟩
  let b : ℝ := ((xiZero q₀).re + 1) / 2
  have hq₀1 : (xiZero q₀).re < 1 := xiZeroCopy_re_lt_one q₀
  have hσb : σ < b := by
    have hm := hmax q₁ hq₁F
    dsimp only [b]
    linarith only [hq₁, hm, hq₀1]
  have hb1 : b < 1 := by dsimp only [b]; linarith only [hq₀1]
  let a : ℝ := Real.pi / (2 * (b - σ))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a * (b - σ) = Real.pi / 2 := by
    dsimp only [a]
    field_simp [ne_of_gt (sub_pos.mpr hσb)]
  have hr : ∀ q ∈ F, gaussianObservationRate (xiZero q) σ a < 0 := by
    intro q hq
    have hqb : (xiZero q).re < b := by
      have hm := hmax q hq
      dsimp only [b]
      linarith only [hm, hq₀1]
    have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hqb σ) ha
    rw [hab] at hlt
    dsimp only [gaussianObservationRate]
    linarith only [hlt]
  have hrpole : 0 < gaussianObservationRate 1 σ a := by
    have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hb1 σ) ha
    rw [hab] at hlt
    simp only [gaussianObservationRate, Complex.one_re]
    linarith only [hlt]
  exact ⟨σ, a, hσ, hσ1, ha, ⟨q₁, hq₁⟩,
    hpass σ le_rfl hσ1.le a ha hr,
    tendsto_norm_gaussianMode_atTop_of_positive_rate 1 σ a hrpole⟩

#print axioms exists_gaussianMode_exponential_bounds
#print axioms tendsto_norm_gaussianMode_atTop_of_positive_rate
#print axioms not_asymptoticAbscissaLaw_has_exponential_finite_part
#print axioms not_asymptoticAbscissaLaw_has_exponential_passage
#print axioms not_asymptoticAbscissaLaw_has_passage_beyond_pole_boundary

end GaloisForLFunctions.ExceptionalLayerTheory
