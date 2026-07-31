import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection
import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier uniqueness for complex density measures on the circle

The existing Fourier uniqueness theorem concerns finite positive measures on an additive circle.
This module transports it to the multiplicative circle, decomposes real densities into their
positive and negative parts, and finally recovers a complex density measure from all of its
integer Laurent moments.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two finite positive measures on the multiplicative circle agree when all their Laurent
moments agree. -/
theorem circle_measure_eq_of_forall_zpow_integral_eq
    (mu nu : Measure Circle) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ k : ℤ, (∫ z, (z : ℂ) ^ k ∂mu) = ∫ z, (z : ℂ) ^ k ∂nu) :
    mu = nu := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let mu' : Measure (AddCircle (1 : ℝ)) := Measure.map e.symm mu
  let nu' : Measure (AddCircle (1 : ℝ)) := Measure.map e.symm nu
  letI : IsFiniteMeasure mu' := Measure.isFiniteMeasure_map mu e.symm
  letI : IsFiniteMeasure nu' := Measure.isFiniteMeasure_map nu e.symm
  have hmap : mu' = nu' := by
    apply addCircle_measure_eq_of_fourier_integral_eq
    intro k
    dsimp only [mu', nu']
    rw [integral_map e.symm.continuous.aemeasurable
      (fourier k).continuous.aestronglyMeasurable,
      integral_map e.symm.continuous.aemeasurable
        (fourier k).continuous.aestronglyMeasurable]
    have hfourier (z : Circle) : fourier k (e.symm z) = (z : ℂ) ^ k := by
      rw [fourier_apply, AddCircle.toCircle_zsmul]
      have he : AddCircle.toCircle (e.symm z) = z := by
        rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
        exact e.apply_symm_apply z
      rw [he]
      exact Circle.coe_zpow z k
    simpa only [hfourier] using h k
  exact e.symm.measurableEmbedding.map_injective hmap

/-- The positive-part measure associated to an integrable real density. -/
noncomputable def realPosDensityMeasure (mu : Measure Circle) (a : Circle → ℝ) :
    Measure Circle := mu.withDensity (fun z => ENNReal.ofReal (a z))

/-- The negative-part measure associated to an integrable real density. -/
noncomputable def realNegDensityMeasure (mu : Measure Circle) (a : Circle → ℝ) :
    Measure Circle := mu.withDensity (fun z => ENNReal.ofReal (-a z))

theorem realPosDensityMeasure_finite (mu : Measure Circle) {a : Circle → ℝ}
    (ha : Integrable a mu) : IsFiniteMeasure (realPosDensityMeasure mu a) := by
  unfold realPosDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal ha.2

theorem realNegDensityMeasure_finite (mu : Measure Circle) {a : Circle → ℝ}
    (ha : Integrable a mu) : IsFiniteMeasure (realNegDensityMeasure mu a) := by
  unfold realNegDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal ha.neg.2

/-- The Fourier moment of a real density is the difference of the moments of its positive and
negative density measures. -/
theorem realDensity_fourier_eq_pos_sub_neg
    (mu : Measure Circle) [IsFiniteMeasure mu] {a : Circle → ℝ}
    (ha : Integrable a mu) (k : ℤ) :
    (∫ z, (z : ℂ) ^ k ∂(realPosDensityMeasure mu a)) -
        (∫ z, (z : ℂ) ^ k ∂(realNegDensityMeasure mu a)) =
      ∫ z, (a z : ℂ) * (z : ℂ) ^ k ∂mu := by
  rw [realPosDensityMeasure, realNegDensityMeasure]
  have hpos := integral_withDensity_eq_integral_toReal_smul₀
    ha.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)
    (fun z : Circle => (z : ℂ) ^ k)
  have hneg := integral_withDensity_eq_integral_toReal_smul₀
    ha.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)
    (fun z : Circle => (z : ℂ) ^ k)
  have hneg' :
      (∫ z : Circle, (z : ℂ) ^ k
          ∂mu.withDensity (fun z => ENNReal.ofReal (-a z))) =
        ∫ z : Circle, (ENNReal.ofReal (-a z)).toReal • (z : ℂ) ^ k ∂mu := by
    simpa only [Pi.neg_apply] using hneg
  rw [hpos, hneg']
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with z
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
    rw [← sub_mul, ← Complex.ofReal_sub,
      max_zero_sub_max_neg_zero_eq_self]
  · exact ha.pos_part.ofReal.mul_bdd
      (circleZMonomial_memLp mu k).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [norm_zpow, Circle.norm_coe, one_zpow])
  · exact ha.neg_part.ofReal.mul_bdd
      (circleZMonomial_memLp mu k).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [norm_zpow, Circle.norm_coe, one_zpow])

private theorem integrable_mul_circle_zpow
    (mu : Measure Circle) [IsFiniteMeasure mu] {f : Circle → ℂ}
    (hf : Integrable f mu) (k : ℤ) :
    Integrable (fun z => f z * (z : ℂ) ^ k) mu := by
  exact hf.mul_bdd (circleZMonomial_memLp mu k).aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [norm_zpow, Circle.norm_coe, one_zpow])

private theorem conj_circle_zpow_neg (z : Circle) (k : ℤ) :
    conj ((z : ℂ) ^ (-k)) = (z : ℂ) ^ k := by
  rw [map_zpow₀, ← Complex.inv_eq_conj (Circle.norm_coe z),
    inv_zpow, ← zpow_neg, neg_neg]

/-- The Fourier moment of the real part of a complex density is recovered from the moments at
`k` and `-k`. -/
theorem integral_re_mul_circle_zpow
    (mu : Measure Circle) [IsFiniteMeasure mu] {f : Circle → ℂ}
    (hf : Integrable f mu) (k : ℤ) :
    (∫ z, ((f z).re : ℂ) * (z : ℂ) ^ k ∂mu) =
      (2 : ℂ)⁻¹ * ((∫ z, f z * (z : ℂ) ^ k ∂mu) +
        conj (∫ z, f z * (z : ℂ) ^ (-k) ∂mu)) := by
  have hk := integrable_mul_circle_zpow mu hf k
  have hnk := integrable_mul_circle_zpow mu hf (-k)
  have hnk_conj : Integrable (fun z => conj (f z * (z : ℂ) ^ (-k))) mu :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearMap.integrable_comp hnk
  calc
    (∫ z, ((f z).re : ℂ) * (z : ℂ) ^ k ∂mu) =
        ∫ z, (2 : ℂ)⁻¹ *
          (f z * (z : ℂ) ^ k + conj (f z * (z : ℂ) ^ (-k))) ∂mu := by
      apply integral_congr_ae
      filter_upwards with z
      rw [map_mul, conj_circle_zpow_neg]
      apply Complex.ext <;> simp <;> ring
    _ = (2 : ℂ)⁻¹ * ((∫ z, f z * (z : ℂ) ^ k ∂mu) +
          ∫ z, conj (f z * (z : ℂ) ^ (-k)) ∂mu) := by
      rw [integral_const_mul, integral_add hk hnk_conj]
    _ = _ := by rw [integral_conj]

/-- The Fourier moment of the imaginary part of a complex density is recovered from the moments
at `k` and `-k`. -/
theorem integral_im_mul_circle_zpow
    (mu : Measure Circle) [IsFiniteMeasure mu] {f : Circle → ℂ}
    (hf : Integrable f mu) (k : ℤ) :
    (∫ z, ((f z).im : ℂ) * (z : ℂ) ^ k ∂mu) =
      ((2 : ℂ) * I)⁻¹ * ((∫ z, f z * (z : ℂ) ^ k ∂mu) -
        conj (∫ z, f z * (z : ℂ) ^ (-k) ∂mu)) := by
  have hk := integrable_mul_circle_zpow mu hf k
  have hnk := integrable_mul_circle_zpow mu hf (-k)
  have hnk_conj : Integrable (fun z => conj (f z * (z : ℂ) ^ (-k))) mu :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearMap.integrable_comp hnk
  calc
    (∫ z, ((f z).im : ℂ) * (z : ℂ) ^ k ∂mu) =
        ∫ z, ((2 : ℂ) * I)⁻¹ *
          (f z * (z : ℂ) ^ k - conj (f z * (z : ℂ) ^ (-k))) ∂mu := by
      apply integral_congr_ae
      filter_upwards with z
      rw [map_mul, conj_circle_zpow_neg]
      apply Complex.ext <;> simp <;> ring
    _ = ((2 : ℂ) * I)⁻¹ * ((∫ z, f z * (z : ℂ) ^ k ∂mu) -
          ∫ z, conj (f z * (z : ℂ) ^ (-k)) ∂mu) := by
      rw [integral_const_mul, integral_sub hk hnk_conj]
    _ = _ := by rw [integral_conj]

/-- A difference of real density measures is determined by its Laurent moments. -/
theorem withDensityV_real_sub_eq_of_forall_zpow_integral_eq
    (mu nu rho : Measure Circle)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    {a b c : Circle → ℝ} (ha : Integrable a mu) (hb : Integrable b nu)
    (hc : Integrable c rho)
    (h : ∀ k : ℤ,
      (∫ z, (a z : ℂ) * (z : ℂ) ^ k ∂mu) -
          (∫ z, (b z : ℂ) * (z : ℂ) ^ k ∂nu) =
        ∫ z, (c z : ℂ) * (z : ℂ) ^ k ∂rho) :
    mu.withDensityᵥ a - nu.withDensityᵥ b = rho.withDensityᵥ c := by
  letI : IsFiniteMeasure (realPosDensityMeasure mu a) :=
    realPosDensityMeasure_finite mu ha
  letI : IsFiniteMeasure (realNegDensityMeasure mu a) :=
    realNegDensityMeasure_finite mu ha
  letI : IsFiniteMeasure (realPosDensityMeasure nu b) :=
    realPosDensityMeasure_finite nu hb
  letI : IsFiniteMeasure (realNegDensityMeasure nu b) :=
    realNegDensityMeasure_finite nu hb
  letI : IsFiniteMeasure (realPosDensityMeasure rho c) :=
    realPosDensityMeasure_finite rho hc
  letI : IsFiniteMeasure (realNegDensityMeasure rho c) :=
    realNegDensityMeasure_finite rho hc
  have hmeasure :
      realPosDensityMeasure mu a + realNegDensityMeasure nu b +
          realNegDensityMeasure rho c =
        realNegDensityMeasure mu a + realPosDensityMeasure nu b +
          realPosDensityMeasure rho c := by
    apply circle_measure_eq_of_forall_zpow_integral_eq
    intro k
    have hPma : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realPosDensityMeasure mu a) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    have hNma : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realNegDensityMeasure mu a) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    have hPnb : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realPosDensityMeasure nu b) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    have hNnb : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realNegDensityMeasure nu b) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    have hPrc : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realPosDensityMeasure rho c) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    have hNrc : Integrable (fun z : Circle => (z : ℂ) ^ k)
        (realNegDensityMeasure rho c) :=
      (circleZMonomial_memLp _ k).integrable (by norm_num)
    rw [integral_add_measure (hPma.add_measure hNnb) hNrc,
      integral_add_measure hPma hNnb,
      integral_add_measure (hNma.add_measure hPnb) hPrc,
      integral_add_measure hNma hPnb]
    have hma := realDensity_fourier_eq_pos_sub_neg mu ha k
    have hnb := realDensity_fourier_eq_pos_sub_neg nu hb k
    have hrc := realDensity_fourier_eq_pos_sub_neg rho hc k
    linear_combination hma - hnb - hrc + h k
  have hsigned :
      (realPosDensityMeasure mu a + realNegDensityMeasure nu b +
          realNegDensityMeasure rho c).toSignedMeasure =
        (realNegDensityMeasure mu a + realPosDensityMeasure nu b +
          realPosDensityMeasure rho c).toSignedMeasure := by
    ext s hs
    rw [Measure.toSignedMeasure_apply_measurable hs,
      Measure.toSignedMeasure_apply_measurable hs, hmeasure]
  simp only [Measure.toSignedMeasure_add] at hsigned
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part ha,
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hb,
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hc]
  change
    ((realPosDensityMeasure mu a).toSignedMeasure -
        (realNegDensityMeasure mu a).toSignedMeasure) -
      ((realPosDensityMeasure nu b).toSignedMeasure -
        (realNegDensityMeasure nu b).toSignedMeasure) =
      (realPosDensityMeasure rho c).toSignedMeasure -
        (realNegDensityMeasure rho c).toSignedMeasure
  calc
    _ = (realPosDensityMeasure mu a).toSignedMeasure +
          (realNegDensityMeasure nu b).toSignedMeasure +
          (realNegDensityMeasure rho c).toSignedMeasure -
        ((realNegDensityMeasure mu a).toSignedMeasure +
          (realPosDensityMeasure nu b).toSignedMeasure +
          (realPosDensityMeasure rho c).toSignedMeasure) +
        ((realPosDensityMeasure rho c).toSignedMeasure -
          (realNegDensityMeasure rho c).toSignedMeasure) := by abel
    _ = _ := by rw [hsigned, sub_self, zero_add]

/-- A difference of complex density measures is determined by its Laurent moments. -/
theorem withDensityV_complex_sub_eq_of_forall_zpow_integral_eq
    (mu nu rho : Measure Circle)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] [IsFiniteMeasure rho]
    {f g q : Circle → ℂ} (hf : Integrable f mu) (hg : Integrable g nu)
    (hq : Integrable q rho)
    (h : ∀ k : ℤ,
      (∫ z, f z * (z : ℂ) ^ k ∂mu) -
          (∫ z, g z * (z : ℂ) ^ k ∂nu) =
        ∫ z, q z * (z : ℂ) ^ k ∂rho) :
    mu.withDensityᵥ f - nu.withDensityᵥ g = rho.withDensityᵥ q := by
  have hreMom : ∀ k : ℤ,
      (∫ z, ((f z).re : ℂ) * (z : ℂ) ^ k ∂mu) -
          (∫ z, ((g z).re : ℂ) * (z : ℂ) ^ k ∂nu) =
        ∫ z, ((q z).re : ℂ) * (z : ℂ) ^ k ∂rho := by
    intro k
    rw [integral_re_mul_circle_zpow mu hf k,
      integral_re_mul_circle_zpow nu hg k,
      integral_re_mul_circle_zpow rho hq k]
    have hneg := congrArg conj (h (-k))
    simp only [map_sub] at hneg
    linear_combination (2 : ℂ)⁻¹ * h k + (2 : ℂ)⁻¹ * hneg
  have himMom : ∀ k : ℤ,
      (∫ z, ((f z).im : ℂ) * (z : ℂ) ^ k ∂mu) -
          (∫ z, ((g z).im : ℂ) * (z : ℂ) ^ k ∂nu) =
        ∫ z, ((q z).im : ℂ) * (z : ℂ) ^ k ∂rho := by
    intro k
    rw [integral_im_mul_circle_zpow mu hf k,
      integral_im_mul_circle_zpow nu hg k,
      integral_im_mul_circle_zpow rho hq k]
    have hneg := congrArg conj (h (-k))
    simp only [map_sub] at hneg
    linear_combination ((2 : ℂ) * I)⁻¹ * h k -
      ((2 : ℂ) * I)⁻¹ * hneg
  have hre := withDensityV_real_sub_eq_of_forall_zpow_integral_eq
    mu nu rho hf.re hg.re hq.re hreMom
  have him := withDensityV_real_sub_eq_of_forall_zpow_integral_eq
    mu nu rho hf.im hg.im hq.im himMom
  apply VectorMeasure.ext
  intro s hs
  rw [sub_apply, withDensityᵥ_apply hf hs,
    withDensityᵥ_apply hg hs, withDensityᵥ_apply hq hs]
  apply Complex.ext
  · have hres := congrArg (fun v : SignedMeasure Circle => v s) hre
    change (mu.withDensityᵥ (fun x => (f x).re)) s -
      (nu.withDensityᵥ (fun x => (g x).re)) s =
        (rho.withDensityᵥ (fun x => (q x).re)) s at hres
    rw [withDensityᵥ_apply
        (show Integrable (fun x => (f x).re) mu from hf.re) hs,
      withDensityᵥ_apply
        (show Integrable (fun x => (g x).re) nu from hg.re) hs,
      withDensityᵥ_apply
        (show Integrable (fun x => (q x).re) rho from hq.re) hs] at hres
    rw [Complex.sub_re, ← RCLike.re_eq_complex_re,
      ← integral_re hf.integrableOn, ← integral_re hg.integrableOn,
      ← integral_re hq.integrableOn, RCLike.re_eq_complex_re]
    exact hres
  · have hims := congrArg (fun v : SignedMeasure Circle => v s) him
    change (mu.withDensityᵥ (fun x => (f x).im)) s -
      (nu.withDensityᵥ (fun x => (g x).im)) s =
        (rho.withDensityᵥ (fun x => (q x).im)) s at hims
    rw [withDensityᵥ_apply
        (show Integrable (fun x => (f x).im) mu from hf.im) hs,
      withDensityᵥ_apply
        (show Integrable (fun x => (g x).im) nu from hg.im) hs,
      withDensityᵥ_apply
        (show Integrable (fun x => (q x).im) rho from hq.im) hs] at hims
    rw [Complex.sub_im, ← RCLike.im_eq_complex_im,
      ← integral_im hf.integrableOn, ← integral_im hg.integrableOn,
      ← integral_im hq.integrableOn, RCLike.im_eq_complex_im]
    exact hims

end
end GaloisForLFunctions.HTGeometry
