import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheHybridHeightBoundForSharpMoebiusSections
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ShortSectionsInsideLongCriticalMeans

/-!
# All admissible height exponents for long Möbius moments

Unit length exponent is an open endpoint: the squarefree logarithmic
diagonal excludes it even on sparse sequences of heights. The translated
Perron estimate fills every exponent above one when the zero width vanishes.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)
open _root_.RHTower.Sieve (squarefreeDensity squarefreeDensity_eq)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Critical-line second moment for a Möbius section of polynomial length. -/
def longMoebiusEnergy (θ T : ℝ) : ℝ :=
  ∫ t in (1:ℝ)..T, ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2

/-- A fixed exponent tested along cofinal lengths and unbounded heights.
The constant and the sequence of heights may depend on the length exponent. -/
def admissibleLongHeightExponent (K : ℝ) : Prop :=
  ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∃ᶠ T : ℝ in atTop, longMoebiusEnergy θ T ≤ C*T^K

private theorem squarefree_density_pos : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity

/-- The mean divided by the length of the time interval tends to infinity
at every positive power length, without any assumption on the zeros. -/
theorem long_moebius_mean_diverges {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun T : ℝ => longMoebiusEnergy θ T/T) atTop atTop := by
  let q := squarefreeDensity*min θ 1/2
  have h0 := mul_pos squarefree_density_pos (lt_min hθ zero_lt_one)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hread := logarithmic_floor_of_long_moebius_mean hθ (q := q) (by dsimp only [q]; linarith)
  apply tendsto_atTop.2
  intro B
  filter_upwards [hread,Real.tendsto_log_atTop.eventually_ge_atTop (B/q),eventually_gt_atTop (0:ℝ)] with T hlow hlog hT
  apply (le_div_iff₀ hT).mpr
  have hB := (div_le_iff₀ hq).mp hlog
  exact ((mul_le_mul_of_nonneg_right hB hT.le).trans_eq (by ring)).trans hlow.le

/-- The set of admissible exponents is exactly (1,∞) on RH and empty
if any zeta zero lies off the critical line. -/
theorem admissible_long_height_exponent_iff (K : ℝ) :
    admissibleLongHeightExponent K ↔ RiemannHypothesis ∧ 1 < K := by
  constructor
  · intro h
    obtain ⟨θ,hθ,C,hC,hfreq⟩ := h 1 zero_lt_one
    have hk : 1 < K := by
      by_contra! hK
      have hlarge := (long_moebius_mean_diverges (zero_lt_one.trans_le hθ)).eventually_gt_atTop C
      obtain ⟨T,hb,hbig,hT⟩ := ((hfreq.and_eventually hlarge).and_eventually
        (eventually_ge_atTop (1:ℝ))).exists
      have ht := zero_lt_one.trans_le hT
      have hpow := Real.rpow_le_rpow_of_exponent_le hT hK
      rw [Real.rpow_one] at hpow
      exact (lt_div_iff₀ ht).mp hbig |>.not_ge
        (hb.trans (mul_le_mul_of_nonneg_left hpow hC))
    refine ⟨riemannHypothesis_iff_cofinal_pure_moebius_moment.mpr ⟨K,zero_le_one.trans hk.le,?_⟩,hk⟩
    intro θ₀ hθ₀
    obtain ⟨η,hη,C,hC,hfreq⟩ := h θ₀ hθ₀
    exact ⟨η,hη,C,hC,by simpa only [edPoly_moebiusMollifierCoeff_eq_moebiusPoly,longMoebiusEnergy] using hfreq⟩
  · rintro ⟨hRH,hK⟩ θ₀ hθ₀
    have hw : zetaZeroWidth = 0 := le_antisymm
      ((zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl).mpr
        (_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH)) zetaZeroWidth_nonneg
    obtain ⟨C,hC,hbound⟩ := long_moebius_moment_unit_intercept hθ₀ (sub_pos.mpr hK)
    refine ⟨θ₀,le_rfl,C,hC, (eventually_ge_atTop (1:ℝ)).frequently.mono (fun T hT => ?_)⟩
    simpa only [longMoebiusEnergy,hw,mul_zero,zero_mul,add_zero,add_sub_cancel_left] using hbound T hT

/-- At a fixed positive power length, RH forces ordinary growth order one,
while the normalized mean square still diverges. -/
theorem rh_forces_unit_order_at_every_length : RiemannHypothesis →
    ∀ θ : ℝ, 0 < θ → Tendsto (fun T : ℝ => Real.log (1+longMoebiusEnergy θ T)/Real.log T)
      atTop (𝓝 1) := by
  intro hRH θ hθ
  have hw : zetaZeroWidth = 0 := le_antisymm
    ((zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl).mpr
      (_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH)) zetaZeroWidth_nonneg
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [(long_moebius_mean_diverges hθ).eventually_gt_atTop 1,
      eventually_gt_atTop (1:ℝ)] with T hm hT
    have ht := zero_lt_one.trans hT
    have hlarge := (lt_div_iff₀ ht).mp hm
    have hl := Real.log_lt_log ht (by linarith only [hlarge] : T < 1+longMoebiusEnergy θ T)
    exact ha.trans ((lt_div_iff₀ (Real.log_pos hT)).mpr (by linarith only [hl]))
  · intro b hb
    let e := (b-1)/2
    have he : 0 < e := div_pos (sub_pos.mpr hb) (by norm_num)
    obtain ⟨C,hC,hbound⟩ := long_moebius_moment_unit_intercept hθ he
    filter_upwards [(tendsto_rpow_atTop he).eventually_gt_atTop (C+1),eventually_gt_atTop (1:ℝ)] with T hlarge hT
    have ht := zero_lt_one.trans hT
    have hl := Real.log_pos hT
    have hm := hbound T hT.le
    rw [hw,mul_zero,zero_mul,add_zero] at hm
    change longMoebiusEnergy θ T ≤ C*T^(1+e) at hm
    have hn : 0 ≤ longMoebiusEnergy θ T := intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
    have hu := Real.one_le_rpow hT.le (show 0 ≤ 1+e by positivity)
    have hbnd : 1+longMoebiusEnergy θ T ≤ (C+1)*T^(1+e) := by linarith only [hm,hu]
    have hpow := hbnd.trans_lt (mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos ht _))
    rw [← Real.rpow_add ht, show e+(1+e)=b by dsimp only [e]; ring] at hpow
    have hlog := Real.log_lt_log (by positivity : 0 < 1+longMoebiusEnergy θ T) hpow
    rw [Real.log_rpow ht] at hlog
    exact (div_lt_iff₀ hl).mpr hlog


end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
