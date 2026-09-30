import GaloisForLFunctions.RHTower.ThetaCuspComplexGaussianEnvelope
import GaloisForLFunctions.RHTower.ThetaPowerWeightedSource

/-!
# A common power-weighted L² majorant for actual complex theta translations

The full Gaussian strip bound supplies one explicit majorant for every
translation in a closed parameter rectangle. Its actual weighted energy
is integrable precisely under the strict Gaussian slack used below.
This gives concrete locally dominated sections for the Hilbert-valued
holomorphic translation orbit.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- Triangle bounds separate the polynomial growth and the Gaussian decay. -/
def thetaRectangleGaussianEnvelope (δ A x : ℝ) : ℝ :=
  Real.exp (9 * (|x| + A) / 2) *
    Real.exp (-(Real.pi * Real.cos (2 * δ)) * Real.exp (2 * (|x| - A)))

/-- A single genuine function bounding every source section in the rectangle. -/
def thetaRectangleGaussianMajorant (δ A x : ℝ) : ℝ :=
  thetaStripGaussianConstant δ * thetaRectangleGaussianEnvelope δ A x

theorem thetaRectangleGaussianMajorant_nonneg (δ A x : ℝ) :
    0 ≤ thetaRectangleGaussianMajorant δ A x :=
  mul_nonneg (thetaStripGaussianConstant_nonneg δ) (by
    unfold thetaRectangleGaussianEnvelope
    positivity)

theorem continuous_thetaRectangleGaussianMajorant (δ A : ℝ) :
    Continuous (thetaRectangleGaussianMajorant δ A) := by
  unfold thetaRectangleGaussianMajorant thetaRectangleGaussianEnvelope
  fun_prop

/-- The literal strip source is bounded uniformly over a closed translation rectangle. -/
theorem norm_thetaCuspStripSource_translate_le_rectangle
    (δ A : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (z : ℂ) (hzR : |z.re| ≤ A) (hzI : |z.im| ≤ δ) (x : ℝ) :
    ‖thetaCuspStripSource ((x : ℂ) + z)‖ ≤ thetaRectangleGaussianMajorant δ A x := by
  let c := Real.pi * Real.cos (2 * δ)
  have hc : 0 < c := mul_pos Real.pi_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩)
  have hupper : |x + z.re| ≤ |x| + A := by
    have h : |x + z.re| ≤ |x| + |z.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le x z.re
    linarith
  have hlower : |x| - A ≤ |x + z.re| := by
    have h : |x| ≤ |x + z.re| + |z.re| := by
      simpa [Real.norm_eq_abs] using norm_add_le (x + z.re) (-z.re)
    linarith
  have hlinear : Real.exp (9 * |x + z.re| / 2) ≤ Real.exp (9 * (|x| + A) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hgauss : Real.exp (-c * Real.exp (2 * |x + z.re|)) ≤
      Real.exp (-c * Real.exp (2 * (|x| - A))) := by
    have he : Real.exp (2 * (|x| - A)) ≤ Real.exp (2 * |x + z.re|) :=
      Real.exp_le_exp.mpr (by linarith)
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left he hc.le
    linarith
  have hsource : ‖thetaCuspStripSource ((x : ℂ) + z)‖ ≤
      thetaStripGaussianConstant δ *
        (Real.exp (9 * |x + z.re| / 2) * Real.exp (-c * Real.exp (2 * |x + z.re|))) := by
    simpa only [thetaStripGaussianEnvelope, Complex.add_re, Complex.ofReal_re] using
      norm_thetaCuspStripSource_le_gaussian_envelope δ hδ0 hδ4 ((x : ℂ) + z)
        (by simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hzI)
  calc
    _ ≤ _ := hsource
    _ ≤ thetaStripGaussianConstant δ *
        (Real.exp (9 * (|x| + A) / 2) * Real.exp (-c * Real.exp (2 * (|x| - A)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hlinear hgauss (Real.exp_pos _).le (Real.exp_pos _).le)
        (thetaStripGaussianConstant_nonneg δ)
    _ = _ := rfl

/-- The exact non-reflected power envelope used at the positive cusp. -/
def thetaRectanglePowerEnvelope (q δ A x : ℝ) : ℝ :=
  (Real.exp (9 * (x + A) / 2) *
    Real.exp (-(Real.pi * Real.cos (2 * δ)) * Real.exp (2 * (x - A)))) ^ 2 *
      thetaEnvelope x ^ (-q)

theorem thetaRectanglePowerEnvelope_pos (q δ A x : ℝ) :
    0 < thetaRectanglePowerEnvelope q δ A x := by
  have h := thetaEnvelope_pos x
  unfold thetaRectanglePowerEnvelope
  positivity

theorem thetaRectanglePowerEnvelope_eq_exp (q δ A x : ℝ) :
    thetaRectanglePowerEnvelope q δ A x =
      Real.exp (9 * (2 - q) * x / 2 + 9 * A -
        Real.pi * (2 * Real.cos (2 * δ) * Real.exp (-2 * A) - q) * Real.exp (2 * x)) := by
  have he : thetaEnvelope x = Real.exp (9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
    unfold thetaEnvelope
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaRectanglePowerEnvelope
  rw [← Real.exp_add, he, ← Real.exp_nat_mul _ 2, ← Real.exp_mul _ (-q), ← Real.exp_add]
  have hshift : Real.exp (2 * (x - A)) = Real.exp (-2 * A) * Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hshift]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem integrable_thetaRectanglePowerEnvelope (q δ A : ℝ) (hq2 : q < 2)
    (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ)) :
    Integrable (thetaRectanglePowerEnvelope q δ A) := by
  have hb : 0 < 9 * (2 - q) / 2 := by linarith
  have hσ : 0 < Real.pi * (2 * Real.cos (2 * δ) * Real.exp (-2 * A) - q) :=
    mul_pos Real.pi_pos (by nlinarith)
  convert (integrable_exp_mul_exp_neg_mul_exp_two_mul hb hσ).const_mul
    (Real.exp (9 * A)) using 1
  funext x
  rw [thetaRectanglePowerEnvelope_eq_exp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The majorant's energy uses the actual complete source in its weight. -/
theorem thetaRectangleGaussianMajorant_energy_ratio (q δ A : ℝ) :
    Tendsto (fun x => thetaPowerWeightedEnergy q (thetaRectangleGaussianMajorant δ A) x /
      thetaRectanglePowerEnvelope q δ A x) atTop
      (𝓝 (thetaStripGaussianConstant δ ^ 2 * (4 * Real.pi ^ 2) ^ (-q))) := by
  have hpower := (Real.continuousAt_rpow_const (4 * Real.pi ^ 2) (-q)
    (Or.inl (by positivity))).tendsto.comp thetaCuspFullSource_div_envelope_tendsto
  have h := hpower.const_mul (thetaStripGaussianConstant δ ^ 2)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def]
  rw [Real.div_rpow (thetaCuspFullSource_pos_all x).le (thetaEnvelope_pos x).le]
  dsimp only [thetaPowerWeightedEnergy, thetaRectangleGaussianMajorant,
    thetaRectangleGaussianEnvelope, thetaRectanglePowerEnvelope]
  rw [abs_of_nonneg hx]
  have hρ : 0 < Real.exp (9 * (x + A) / 2) *
      Real.exp (-(Real.pi * Real.cos (2 * δ)) * Real.exp (2 * (x - A))) := by positivity
  field_simp [hρ.ne', (Real.rpow_pos_of_pos (thetaEnvelope_pos x) (-q)).ne']

private theorem integrable_even_of_ratio_tendsto
    (f g : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (heven : ∀ x, f (-x) = f x) (hg0 : ∀ x, 0 < g x) (hg : Integrable g)
    (L : ℝ) (hlim : Tendsto (fun x => f x / g x) atTop (𝓝 L)) :
    Integrable f := by
  have hupper : L < |L| + 1 := by linarith [le_abs_self L]
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hupper))
  have hp : IntegrableOn f (Ioi R) := by
    refine ((hg.const_mul (|L| + 1)).integrableOn (s := Ioi R)).mono_nonneg
      hf.aestronglyMeasurable (ae_of_all _ hf0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact ((div_lt_iff₀ (hg0 x)).mp (hR x hx.le)).le
  have hflip : IntegrableOn (fun x => f (-x)) (Ioi R) ↔ IntegrableOn f (Iio (-R)) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Iio (-R))
  have hn : IntegrableOn f (Iio (-R)) := hflip.mp (by simpa only [heven] using hp)
  have hm : IntegrableOn f (Icc (-R) R) := hf.integrableOn_Icc
  have hwhole : IntegrableOn f ((Iio (-R) ∪ Icc (-R) R) ∪ Ioi R) :=
    integrableOn_union.mpr ⟨integrableOn_union.mpr ⟨hn, hm⟩, hp⟩
  have hcover : (Iio (-R) ∪ Icc (-R) R) ∪ Ioi R = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hn : x < -R
    · exact Or.inl (Or.inl hn)
    · by_cases hp : R < x
      · exact Or.inr hp
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  rw [hcover] at hwhole
  exact integrableOn_univ.mp hwhole

/-- The Gaussian rectangle majorant includes the unweighted endpoint. -/
theorem thetaRectangleGaussianMajorant_memLp_of_nonneg
    (δ A q : ℝ) (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (_hq : 0 ≤ q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ)) :
    MemLp (thetaRectangleGaussianMajorant δ A) 2 (thetaPowerWeightedMeasure q) := by
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  have he1 : Real.exp (-2 * A) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (by linarith : -2 * A ≤ 0)
  have hproduct := mul_le_mul (Real.cos_le_one (2 * δ)) he1
    (Real.exp_pos (-2 * A)).le (by norm_num : (0 : ℝ) ≤ 1)
  have hq2 : q < 2 := by nlinarith
  rw [memLp_thetaPowerWeightedMeasure_iff q (continuous_thetaRectangleGaussianMajorant δ A)]
  apply integrable_even_of_ratio_tendsto
    (thetaPowerWeightedEnergy q (thetaRectangleGaussianMajorant δ A))
    (thetaRectanglePowerEnvelope q δ A)
    (continuous_thetaPowerWeightedEnergy q (continuous_thetaRectangleGaussianMajorant δ A))
    (thetaPowerWeightedEnergy_nonneg q _) ?_ (thetaRectanglePowerEnvelope_pos q δ A)
    (integrable_thetaRectanglePowerEnvelope q δ A hq2 hmargin) _
    (thetaRectangleGaussianMajorant_energy_ratio q δ A)
  intro x
  simp only [thetaPowerWeightedEnergy, thetaRectangleGaussianMajorant,
    thetaRectangleGaussianEnvelope, abs_neg, thetaCuspFullSource_neg]

/-- The single rectangle majorant belongs to the positive power-weighted carrier. -/
theorem thetaRectangleGaussianMajorant_memLp
    (δ A q : ℝ) (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ)) :
    MemLp (thetaRectangleGaussianMajorant δ A) 2 (thetaPowerWeightedMeasure q) :=
  thetaRectangleGaussianMajorant_memLp_of_nonneg δ A q hA hδ0 hδ4 hq.le hmargin

theorem continuous_thetaCuspStripSource_translation {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    Continuous (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + z)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : (x : ℂ) + z ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, zero_add] using hz
  exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + z)
    (differentiableAt_thetaCuspStripSource hp).continuousAt
    (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + z) x)

/-- Every actual complex source section in the rectangle belongs to its weighted carrier. -/
theorem thetaCuspStripSource_translation_memLp
    (δ A q : ℝ) (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ))
    (z : ℂ) (hzR : |z.re| ≤ A) (hzI : |z.im| ≤ δ) :
    MemLp (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + z)) 2 (thetaPowerWeightedMeasure q) := by
  have hz : z ∈ thetaCuspStrip := by
    dsimp only [thetaCuspStrip, mem_setOf_eq]
    linarith
  exact (thetaRectangleGaussianMajorant_memLp δ A q hA hδ0 hδ4 hq hmargin).mono'
    (continuous_thetaCuspStripSource_translation hz).aestronglyMeasurable
    (ae_of_all _ fun x => norm_thetaCuspStripSource_translate_le_rectangle δ A hδ0 hδ4 z hzR hzI x)

end

end RHTower
